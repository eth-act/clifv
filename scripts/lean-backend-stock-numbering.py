#!/usr/bin/env python3
"""Opt-in stock-schedule numbering hints for the unchanged checked Lean backend.

Usage: scripts/lean-backend-stock-numbering.py INPUT OUTPUT [backend options...]
CLIFV_ALIGNMENT_BACKEND/TRACER/ORACLE override the corresponding built executable.
All instructions and allocator constraints remain those of the original backend.
"""
import importlib.util,json,os,pathlib,shlex,subprocess,sys,tempfile
ROOT=pathlib.Path(__file__).resolve().parents[1]

def oracle(path):
 spec=importlib.util.spec_from_file_location('alignment',ROOT/'scripts/register-alignment-probe.py');p=importlib.util.module_from_spec(spec);spec.loader.exec_module(p)
 original=json.loads(pathlib.Path(path).read_text());request=json.loads(json.dumps(original))
 traces={x['name'].lstrip('%'):x['lowering'] for x in json.loads(pathlib.Path(os.environ['CLIFV_ALIGNMENT_TRACE']).read_text()).get('functions',[]) if x.get('status')=='lowered'}
 for f in request['functions']:
  try:m=p.shape_map(f,traces[f['name']]['stock_schedule']['allocator_input']);f.update(p.remap(f,m))
  except (KeyError,ValueError,IndexError,AssertionError):pass
 binary=os.environ.get('CLIFV_ALIGNMENT_ORACLE',str(ROOT/'rust/target/release/lean-regalloc'))
 result=subprocess.run([binary],input=json.dumps(request),text=True,capture_output=True)
 sys.stdout.write(result.stdout);sys.stderr.write(result.stderr);return result.returncode

def main():
 if sys.argv[1:2]==['--alignment-oracle']:
  if len(sys.argv)!=3:return 2
  return oracle(sys.argv[2])
 backend=os.environ.get('CLIFV_ALIGNMENT_BACKEND',str(ROOT/'.lake/build/bin/lean-backend'))
 tracer=os.environ.get('CLIFV_ALIGNMENT_TRACER',str(ROOT/'.lake/build/bin/lean-backend-lowering-trace'))
 if len(sys.argv)<3:return subprocess.call([backend,*sys.argv[1:]])
 with tempfile.TemporaryDirectory(prefix='clifv-register-alignment-') as tmp:
  trace=pathlib.Path(tmp)/'trace.json'
  try:subprocess.run([tracer,sys.argv[1],str(trace),'--stock-schedule'],check=True,stdout=subprocess.DEVNULL,stderr=subprocess.DEVNULL,timeout=60)
  except (OSError,subprocess.CalledProcessError,subprocess.TimeoutExpired):return subprocess.call([backend,*sys.argv[1:]])
  try:
   payload=json.loads(trace.read_text())
   if not isinstance(payload,dict) or not isinstance(payload.get('functions'),list):raise ValueError('invalid trace')
  except (OSError,ValueError):return subprocess.call([backend,*sys.argv[1:]])
  shim=pathlib.Path(tmp)/'oracle';shim.write_text('#!/bin/sh\nexec '+shlex.quote(sys.executable)+' '+shlex.quote(str(pathlib.Path(__file__).resolve()))+' --alignment-oracle "$@"\n');shim.chmod(0o755)
  env={**os.environ,'LEAN_REGALLOC':str(shim),'CLIFV_ALIGNMENT_TRACE':str(trace),'CLIFV_ALIGNMENT_ORACLE':os.environ.get('CLIFV_ALIGNMENT_ORACLE',os.environ.get('LEAN_REGALLOC',str(ROOT/'rust/target/release/lean-regalloc')))}
  return subprocess.call([backend,*sys.argv[1:]],env=env)
if __name__=='__main__':sys.exit(main())
