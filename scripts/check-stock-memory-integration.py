#!/usr/bin/env python3
"""Check actual Stock memory compilation, initialized native reads and generated proofs."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True, type=Path)
    parser.add_argument('--memory-cfg', action='store_true', help='exercise the captured two-block load class')
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    out = args.output.resolve()
    if out == root or root in out.parents:
        parser.error('output must be outside the source tree')
    out.mkdir(parents=True, exist_ok=False)
    generated = out / 'generated'
    env = dict(os.environ, OMP_NUM_THREADS='2', OMP_THREAD_LIMIT='2', LEAN_NUM_THREADS='2', FV_MEMCAP=os.environ.get('FV_MEMCAP', '8G'))
    records = []
    sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()

    def run(label, argv):
        log = out / (label + '.log')
        with log.open('w') as stream:
            result = subprocess.run([str(root / 'scripts/memcap.sh'), *map(str, argv)], cwd=root,
                                    env=env, stdout=stream, stderr=subprocess.STDOUT)
        records.append(dict(label=label, argv=list(map(str, argv)), returncode=result.returncode,
                            log_sha256=sha(log)))
        if result.returncode:
            raise RuntimeError(f'{label} failed: {log}')
        return log.read_text()

    try:
        run('fixture', [root / '.lake/build/bin/stock-memory-linked', generated, *(['--memory-cfg'] if args.memory_cfg else [])])
        expected = {f'StockMemoryProduction{mode}{policy}{scope}' for mode in ('Plain', 'Cleanup')
                    for policy in ('Strict', 'Fallback') for scope in ('Global', 'Entries')}
        assert {p.stem for p in (generated / 'Crates').glob('*.lean')} == expected
        env['LEAN_PATH'] = str(generated) + ':' + run('lean-path', ['lake', 'env', 'printenv', 'LEAN_PATH']).strip().splitlines()[-1]
        built = {}

        def compile_generated():
            files = {'.'.join(p.relative_to(generated).with_suffix('').parts): p
                     for p in (generated / 'Crates').rglob('*.lean')}
            active = set()

            def visit(module):
                path = files[module]
                digest = sha(path)
                if built.get(module) == digest:
                    return
                if module in active:
                    raise RuntimeError('generated import cycle')
                active.add(module)
                for imported in re.findall(r'^import\s+(\S+)', path.read_text(), re.M):
                    if imported.startswith('Crates.'):
                        visit(imported)
                run('proof-' + module, ['lean', '--root=' + str(generated), '-o', path.with_suffix('.olean'), path])
                built[module] = digest
                active.remove(module)

            for module in sorted(files):
                visit(module)

        compile_generated()
        for mode, flags in [('Plain', ['--no-dead-cleanup']), ('Cleanup', [])]:
            bundle = generated / f'StockMemoryProduction{mode}FallbackGlobal-bundle'
            proof = generated / 'Crates' / f'MemoryCLI{mode}.lean'
            run('cli-check-' + mode, [root / '.lake/build/bin/link-check', bundle, '--lean', proof,
                                     '--module', proof.stem, *flags])
            compile_generated()
            linked = run('verified-link-' + mode, [root / '.lake/build/bin/lean-link', bundle, '--verified', *flags])
            assert 'written by Link.SemanticCompilerWith.compile' in linked
            assert 'attempt_correct_source_peak' in linked

        assembly = out / 'memory-native.s'
        assembly.write_text('''\n.text
.global _start
_start:
  adrp x19, test_data
  add x19, x19, :lo12:test_data
  add x19, x19, #1
  mov w20, #0xa5a5
  movk w20, #0xa5a5, lsl #16
  mov x22, #2048
1:
  str w20, [x19]
  mov x0, x19
  bl memory_load0
  cmp x0, x20
  b.ne 2f
  mov x0, #0xdead
  mov x1, x19
  bl memory_load1
  cmp x0, x20
  b.ne 2f
  mov x0, #0x1234
  bl memory_retained
  mov x21, #0x1234
  cmp x0, x21
  b.ne 2f
  add w20, w20, #123
  ror w20, w20, #7
  subs x22, x22, #1
  b.ne 1b
  mov x0, #0
  b 3f
2:
  mov x0, #1
3:
  mov x8, #93
  svc #0
.data
.balign 16
test_data:
  .quad 0
  .quad 0
''')
        mc = env.get('LLVM_MC', 'llvm-mc')
        lld = env.get('CLIF_NATIVE_LLD', 'ld.lld')
        qemu = env.get('CLIF_NATIVE_QEMU', 'qemu-aarch64')
        linker = [lld] + (['-flavor', 'gnu'] if Path(lld).name in ('lld', 'rust-lld') else [])
        run('native-assemble', [mc, '-triple=aarch64-linux-gnu', '-filetype=obj', assembly, '-o', out / 'memory-native.o'])
        for mode in ('plain', 'cleanup'):
            elf = out / f'native-{mode}.elf'
            run('native-link-' + mode, [*linker, '--threads=1', '-m', 'aarch64elf', '-e', '_start', '-o', elf,
                                       out / 'memory-native.o', generated / f'memory-{mode}.o'])
            run('native-execute-' + mode, [qemu, elf])
        audit = out / 'GeneratedAxioms.lean'
        audit.write_text('\n'.join('import ' + m for m in sorted(built)) + '''
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let generated := fun (name : Name) =>
    let owner := (privateToUserName? name).getD name
    owner.toString.startsWith "Crates.StockMemoryProduction" || owner.toString.startsWith "Crates.MemoryCLI"
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    unless generated name do continue
    for ax in ← collectAxioms name do
      if #[``propext, ``Classical.choice, ``Quot.sound].contains ax then continue
      unless generated ax && (ax.toString.splitOn "._native.native_decide.ax_").length > 1 do
        throwError "unexpected generated-proof axiom {ax} in {name}"
    count := count + 1
  unless count > 0 do throwError "empty generated-proof audit"
  logInfo m!"STOCK_MEMORY_GENERATED_AXIOMS_PASS {count}"
''')
        assert 'STOCK_MEMORY_GENERATED_AXIOMS_PASS ' in run('generated-axioms', ['lean', '--root=' + str(out), audit])
        report = dict(state='passed', generated_sources=built, native_calls=12288, initialized_loads=8192,
                      native_reference='exact stored 32-bit source value, unaligned initialized address; unused first ABI argument',
                      cleanup_modes=2, memory_cfg=args.memory_cfg, generated_roots=sorted(expected), commands=records)
    except BaseException as error:
        report = dict(state='failed', error=repr(error), commands=records)
        raise
    finally:
        report['artifacts'] = {str(p.relative_to(out)): sha(p) for p in out.rglob('*')
                               if p.is_file() and p.suffix in {'.lean', '.clif', '.json', '.o', '.elf', '.s'}}
        (out / 'receipt.json').write_text(json.dumps(report, indent=2) + '\n')
    print('STOCK_MEMORY_INTEGRATION_PASS ' + str(len(records)) + ' commands')


if __name__ == '__main__':
    main()
