#!/usr/bin/env python3
"""Check actual Stock memory compilation, native stores and generated proofs."""
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
    parser.add_argument('--load-type', choices=('i8', 'i16', 'i32', 'i64'), help='exercise mixed load/store functions')
    parser.add_argument('--memory-cfg', action='store_true', help='exercise the complete two-block store class')
    parser.add_argument('--store-type', choices=('i8', 'i16', 'i32', 'i64'), default='i64')
    parser.add_argument('--store-op', choices=('store', 'istore8', 'istore16', 'istore32'), default='store')
    args = parser.parse_args()
    if args.load_type and args.memory_cfg:
        parser.error("load/store and CFG store modes are separate")
    program = "StockMemoryLoadStoreProduction" if args.load_type else "StockMemoryStoreCfgProduction" if args.memory_cfg else "StockMemoryStoreProduction"
    value_bits = int(args.store_type[1:])
    store_bits = value_bits if args.store_op == 'store' else int(args.store_op[6:])
    if store_bits > value_bits:
        parser.error('the store width exceeds the original operand width')
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
        run('fixture', [root / ('.lake/build/bin/stock-memory-load-store-linked' if args.load_type else '.lake/build/bin/stock-memory-store-cfg-linked' if args.memory_cfg else '.lake/build/bin/stock-memory-store-linked'), generated,
                        '--store-type', args.store_type, '--store-op', args.store_op, *(['--load-type', args.load_type] if args.load_type else [])])
        expected = {f'{program}{mode}{policy}{scope}' for mode in ('Plain', 'Cleanup')
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
            bundle = generated / f'{program}{mode}FallbackGlobal-bundle'
            proof = generated / 'Crates' / f'MemoryStoreCLI{mode}.lean'
            run('cli-check-' + mode, [root / '.lake/build/bin/link-check', bundle, '--lean', proof,
                                     '--module', proof.stem, *flags])
            compile_generated()
            linked = run('verified-link-' + mode, [root / '.lake/build/bin/lean-link', bundle, '--verified', *flags])
            assert 'written by Link.SemanticCompilerWith.compile' in linked
            assert 'attempt_correct_source_peak' in linked

        clang = env.get('CLANG', 'clang')
        qemu = env.get('CLIF_NATIVE_QEMU', 'qemu-aarch64')
        for mode in ('plain', 'cleanup'):
            elf = out / f'native-{mode}.elf'
            run('native-link-' + mode, [clang, '--target=aarch64-linux-gnu', '-O2',
                '-ffreestanding', '-nostdlib', '-fno-builtin', '-fno-stack-protector',
                '-static', '-fuse-ld=lld', '-Wl,-e,_start', '-DFV_STORE_FREESTANDING',
                '-DSTORE_BYTES=' + str(store_bits // 8), *(['-DLOAD_BYTES=' + str(int(args.load_type[1:]) // 8)] if args.load_type else []),
                root / ('scripts/testdata/stock-memory-load-store-native.c' if args.load_type else 'scripts/testdata/stock-memory-store-native.c'),
                generated / f'memory-{mode}.o', '-o', elf])
            run('native-execute-' + mode, [qemu, elf])
        audit = out / 'GeneratedAxioms.lean'
        audit.write_text('\n'.join('import ' + m for m in sorted(built)) + '''
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let generated := fun (name : Name) =>
    let owner := (privateToUserName? name).getD name
    owner.toString.startsWith "Crates.StockMemoryStoreProduction" || owner.toString.startsWith "Crates.StockMemoryLoadStoreProduction" || owner.toString.startsWith "Crates.MemoryStoreCLI"
  let mut count : Nat := 0
  for (name, _) in env.constants.toList do
    unless generated name do continue
    for ax in ← collectAxioms name do
      if #[``propext, ``Classical.choice, ``Quot.sound].contains ax then continue
      unless generated ax && (ax.toString.splitOn "._native.native_decide.ax_").length > 1 do
        throwError "unexpected generated-proof axiom {ax} in {name}"
    count := count + 1
  unless count > 0 do throwError "empty generated-proof audit"
  logInfo m!"STOCK_MEMORY_STORE_GENERATED_AXIOMS_PASS {count}"
'''.replace('Crates.StockMemoryStoreProduction', 'Crates.' + program))
        assert 'STOCK_MEMORY_STORE_GENERATED_AXIOMS_PASS ' in run('generated-axioms', ['lean', '--root=' + str(out), audit])
        report = dict(state='passed', generated_sources=built, native_store_calls=88 if args.load_type else 44, retained_calls=2,
                      native_reference=('pre-store load; same/distinct pointers; original argument bytes with arbitrary upper bits; unchanged surrounding bytes' if args.load_type else 'original argument bytes with arbitrary upper bits; unchanged surrounding bytes'),
                      load_type=args.load_type, store_type=args.store_type, store_op=args.store_op, memory_cfg=args.memory_cfg, cleanup_modes=2,
                      operand_orders=2, generated_roots=sorted(expected), commands=records)
    except BaseException as error:
        report = dict(state='failed', error=repr(error), commands=records)
        raise
    finally:
        report['artifacts'] = {str(p.relative_to(out)): sha(p) for p in out.rglob('*')
                               if p.is_file() and p.suffix in {'.lean', '.clif', '.json', '.o', '.elf', '.s'}}
        (out / 'receipt.json').write_text(json.dumps(report, indent=2) + '\n')
    print('STOCK_MEMORY_STORE_INTEGRATION_PASS ' + str(len(records)) + ' commands')


if __name__ == '__main__':
    main()
