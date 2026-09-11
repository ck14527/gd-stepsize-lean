#!/usr/bin/env python3
"""Audit elaborated declarations, axiom closure, names, coverage and proof DAG.
This does not decide semantic equivalence between prose in a PDF and Lean.
"""
import argparse,hashlib,json,re,sys
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
ALLOWED={'propext','Classical.choice','Quot.sound'}

def source_theorems():
 result={}
 for p in sorted((ROOT/'GD').glob('*.lean')):
  stack=[]
  for line in p.read_text().splitlines():
   s=line.strip()
   if m:=re.match(r'^namespace\s+(\S+)',s):stack.append(('ns',m[1]));continue
   if re.match(r'^(noncomputable\s+)?section\b',s):stack.append(('section',''));continue
   if re.match(r'^end(?:\s+\S+)?\s*$',s):
    if stack:stack.pop()
    continue
   m=re.match(r'^(?:@\[[^]]*\]\s*)?theorem\s+([^\s(:]+)',s)
   if m:
    name='.'.join([v for k,v in stack if k=='ns']+[m[1]])
    if name in result:raise RuntimeError('duplicate source theorem '+name)
    result[name]=p.relative_to(ROOT).as_posix()
 return result

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--require-complete',action='store_true');ap.add_argument('--require-scalar-complete',action='store_true');args=ap.parse_args()
 rows=json.loads((ROOT/'audit/lean_declarations.json').read_text());by={r['name']:r for r in rows}
 cov=json.loads((ROOT/'audit/coverage.json').read_text());inv=json.loads((ROOT/'audit/inventory.json').read_text())
 declared=source_theorems();errors=[];unexpected=set()
 provenance_path=ROOT/'audit/build_provenance.json'
 provenance_ok=True
 if not provenance_path.exists():
  errors.append('Missing proof-export provenance; run tools/run_checks.py.');provenance_ok=False
 else:
  provenance=json.loads(provenance_path.read_text())
  inputs=[ROOT/'GD.lean',ROOT/'lean-toolchain',ROOT/'lakefile.toml',ROOT/'lake-manifest.json',*sorted((ROOT/'GD').glob('*.lean'))]
  actual={p.relative_to(ROOT).as_posix():hashlib.sha256(p.read_bytes()).hexdigest() for p in inputs}
  if actual!=provenance.get('files'):
   errors.append('Proof inputs differ from the checked export; run tools/run_checks.py.');provenance_ok=False
  if hashlib.sha256((ROOT/'audit/lean_declarations.json').read_bytes()).hexdigest()!=provenance.get('elaborated_export_sha256'):
   errors.append('Elaborated export differs from its provenance.');provenance_ok=False
 for n,p in declared.items():
  if n not in by:errors.append('Missing elaborated source theorem: '+n);continue
  r=by[n]
  if r['kind']!='theorem':errors.append('Declaration is not a theorem: '+n)
  if bad:=set(r['axioms'])-ALLOWED:
   unexpected.update(bad);errors.append('Unexpected axioms in '+n+': '+repr(sorted(bad)))
 # Check actual transitive kernel-term references; generated compiler staging
 # functions can be unsafe but must not occur in theorem proof/type closures.
 def closure(start):
  seen=set();todo=[start]
  while todo:
   n=todo.pop()
   if n in seen:continue
   seen.add(n)
   if n in by:todo.extend(by[n]['proof_references']+by[n]['type_references'])
  return seen
 used=set().union(*(closure(n) for n in declared))
 unsafe_used=sorted(n for n in used if n in by and by[n]['safety'] in ['unsafe','partial'])
 if unsafe_used:errors.append('Unsafe or partial code in proof closure: '+repr(unsafe_used))
 for r in cov['results']:
  for n in r['proof_declarations']:
   if n not in by or by[n]['kind']!='theorem':errors.append('Coverage entry lacks theorem proof: '+n)
  td=r['target_definition']
  if td and (td not in by or by[td]['kind']!='definition'):errors.append('Target is missing or misclassified: '+str(td))
  if td and r['status']=='verified_scalar_model':
   if not any(td in by.get(n,{}).get('type_references',[]) for n in r['proof_declarations']):
    errors.append('Verified target lacks a proof with that exact target type: '+td)
 ids=[r['paper_id'] for r in cov['results']]
 expected={n['id'] for n in inv['nodes'] if n['kind'] in ['Theorem','Lemma','Proposition','Corollary']}
 if len(ids)!=36 or len(set(ids))!=36 or set(ids)!=expected:errors.append('36-result coverage mismatch')
 # Collapse generated helper declarations/definitions to named source theorems.
 edges=set()
 for n in declared:
  todo=list(by.get(n,{}).get('proof_references',[]));seen=set()
  while todo:
   dep=todo.pop()
   if dep in seen:continue
   seen.add(dep)
   if dep in declared:
    if dep==n:errors.append('Self-dependent theorem: '+n)
    else:edges.add((dep,n))
   elif dep in by:todo.extend(by[dep]['proof_references']+by[dep]['type_references'])
 pending=set(declared);order=[]
 while pending:
  ready=sorted(n for n in pending if not any(dst==n and src in pending for src,dst in edges))
  if not ready:errors.append('Cycle in theorem dependency graph');break
  order+=ready;pending-=set(ready)
 graph={'basis':'Actual elaborated proof terms; generated helper constants collapsed. Definitions can cause extra dependencies relative to the paper explanation.','nodes':sorted(declared),'edges':[{'from':a,'to':b} for a,b in sorted(edges)],'topological_order':order}
 (ROOT/'audit/lean_theorem_graph.json').write_text(json.dumps(graph,indent=2))
 dot=['digraph lean_proofs {','rankdir=TB;','node [shape=box,fontname="Arial",fontsize=9];']
 dot += [json.dumps(n)+';' for n in sorted(declared)]
 dot += [json.dumps(a)+' -> '+json.dumps(b)+';' for a,b in sorted(edges)]
 dot += ['}'];(ROOT/'graphs/lean_proof_dependencies.dot').write_text('\n'.join(dot))
 signatures=[]
 for n in sorted(declared):
  r=by.get(n)
  if r:signatures.append({'name':n,'file':declared[n],'type_sha256':hashlib.sha256(r['type'].encode()).hexdigest(),'type':r['type'],'axioms':r['axioms']})
 (ROOT/'audit/theorem_signatures.json').write_text(json.dumps(signatures,ensure_ascii=False,indent=2))
 source_hashes={p.relative_to(ROOT).as_posix():hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(ROOT.rglob('*')) if p.is_file() and '.lake' not in p.parts and 'node_modules' not in p.parts and '.git' not in p.parts and p.suffix in ['.lean','.py','.mjs','.toml','.tex','.md','.yml','.yaml','.cff']}
 (ROOT/'audit/source_sha256.json').write_text(json.dumps(source_hashes,indent=2))
 scalar_complete=all(x['status']=='verified_scalar_model' for x in cov['results'])
 complete=scalar_complete and cov['external_GD_certificate_interfaces_formalized']
 summary={'core_structure_pass':not errors,'proof_export_matches_inputs':provenance_ok,'full_paper_ready':complete,'scalar_numbered_results_complete':scalar_complete,'source_theorems':len(declared),'exported_declarations':len(rows),'theorem_dependency_edges':len(edges),'unexpected_axioms':sorted(unexpected), 'allowed_foundational_axioms':sorted(ALLOWED),'unsafe_in_proof_closure':unsafe_used,'generated_unsafe_constants_not_used_in_proofs':sum(r['safety'] in ['unsafe','partial'] and r['name'] not in used for r in rows),'coverage_counts':cov['counts'],'errors':errors,'limits':'Statement-to-paper semantic correspondence is manually reviewed. Proposition definitions alone are not proofs. The numbered scalar results and external GD certificate interfaces are separate scopes.'}
 (ROOT/'audit/structure_check.json').write_text(json.dumps(summary,ensure_ascii=False,indent=2))
 print(json.dumps(summary,ensure_ascii=False,indent=2))
 if errors:return 1
 if args.require_complete and not complete:return 3
 if args.require_scalar_complete and not scalar_complete:return 3
 return 0
if __name__=='__main__':sys.exit(main())
