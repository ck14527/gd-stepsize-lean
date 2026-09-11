#!/usr/bin/env python3
"""Build, export kernel proof metadata, and audit the formalization.
--require-complete also gates full paper coverage; this package intentionally
fails that stronger gate because external GD certificate interfaces are not formalized.
"""
from pathlib import Path
import argparse,os,shutil,subprocess,sys,json,time
from proof_provenance import proof_inputs,record
ROOT=Path(__file__).resolve().parents[1]
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--require-complete',action='store_true');ap.add_argument('--require-scalar-complete',action='store_true');args=ap.parse_args()
 lake=os.environ.get('GD_LAKE_EXE') or shutil.which('lake')
 lean=os.environ.get('GD_LEAN_EXE') or shutil.which('lean')
 if not lake or not lean:print('Install the pinned Lean toolchain and mathlib first.');return 2
 (ROOT/'logs').mkdir(exist_ok=True)
 commands=[('inventory',[sys.executable,'tools/build_inventory.py']),('build',[lake,'build','GD']),('axiom_export',[lake,'env',lean,'GD/Audit.lean']),('coverage',[sys.executable,'tools/make_coverage.py']),('structure',[sys.executable,'tools/verify_structure.py']+(['--require-complete'] if args.require_complete else [])+(['--require-scalar-complete'] if args.require_scalar_complete else []))]
 before=proof_inputs()
 outcomes=[]
 for label,cmd in commands:
  start=time.time();r=subprocess.run(cmd,cwd=ROOT,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
  (ROOT/'logs'/f'{label}.log').write_text(r.stdout)
  outcomes.append({'check':label,'exit_code':r.returncode,'elapsed_seconds':round(time.time()-start,3)})
  print(f'{label}: exit {r.returncode}',flush=True)
  if label=='axiom_export' and r.returncode==0:record(before)
  if r.returncode:
   print(r.stdout[-8000:]);(ROOT/'audit/run_checks.json').write_text(json.dumps(outcomes,indent=2));return r.returncode
 (ROOT/'audit/run_checks.json').write_text(json.dumps(outcomes,indent=2))
 print('Core checks passed. See audit/coverage.json for numbered scalar coverage and the separate external certificate scope.')
 return 0
if __name__=='__main__':sys.exit(main())
