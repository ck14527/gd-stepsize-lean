#!/usr/bin/env python3
"""Check repository documentation: correspondence, links, citations, and workflow hooks.
This is supplementary to the kernel and axiom checks, not a mathematical prover.
"""
from pathlib import Path
import csv,json,re,sys,xml.etree.ElementTree as ET
ROOT=Path(__file__).resolve().parents[1]
def main():
 errors=[]
 required=['README.md','CITATION.cff','repository.json','GD.lean','lakefile.toml','lean-toolchain','lake-manifest.json','.github/workflows/lean.yml',
 'docs/THEOREMS.md','docs/THEOREMS.csv','docs/VERIFICATION.md','docs/DEPENDENCIES.md','docs/README_zh.md','docs/statement_inventory.json']
 for rel in required:
  if not (ROOT/rel).is_file():errors.append('Missing '+rel)
 cov=json.loads((ROOT/'audit/coverage.json').read_text());audit=json.loads((ROOT/'audit/structure_check.json').read_text())
 rows=list(csv.DictReader((ROOT/'docs/THEOREMS.csv').open(newline='')))
 if {r['paper_id'] for r in rows}!={r['paper_id'] for r in cov['results']} or len(rows)!=36:errors.append('CSV coverage mismatch')
 if not audit['core_structure_pass'] or not audit['scalar_numbered_results_complete']:errors.append('Scalar structure audit did not pass')
 cfg=json.loads((ROOT/'repository.json').read_text());cff=json.loads((ROOT/'CITATION.cff').read_text())
 if cff.get('cff-version')!='1.2.0' or cff.get('authors')!=cfg['paper_authors']:errors.append('Citation metadata mismatch')
 if cff.get('title')!=f"Lean formalization of {cfg['paper_title']}":errors.append('Citation title mismatch')
 if cfg.get('url')!=cff.get('repository-code'):errors.append('Citation repository URL mismatch')
 for p in [ROOT/'README.md',ROOT/'CONTRIBUTING.md',*sorted((ROOT/'docs').glob('*.md'))]:
  text=re.sub(r'```.*?```','',p.read_text(),flags=re.S)
  for target in re.findall(r'!?\[[^\]]*\]\(([^\)]+)\)',text):
   target=target.split(' ',1)[0]
   if target.startswith(('http:','https:','mailto:','#')):continue
   if not (p.parent/target.split('#')[0]).exists():errors.append(f'Broken link in {p.relative_to(ROOT)}: {target}')
  if '/workspace/scratch/' in text:errors.append('Nonportable scratch path in '+str(p.relative_to(ROOT)))
 workflow=(ROOT/'.github/workflows/lean.yml').read_text()
 for snippet in ['pull_request:','workflow_dispatch:','contents: read','leanprover/lean-action@v1','python3 tools/run_checks.py --require-scalar-complete','python3 tools/generate_docs.py --check','actions/upload-artifact@v4']:
  if snippet not in workflow:errors.append('Missing workflow hook: '+snippet)
 if 'continue-on-error: true' in workflow:errors.append('Workflow suppresses an error')
 ns={'s':'http://www.w3.org/2000/svg'}
 expected=[('manuscript_dag',len(json.loads((ROOT/'audit/inventory.json').read_text())['nodes'])),('lean_proof_dependencies_reduced',audit['source_theorems'])]
 for name,count in expected:
  r=ET.parse(ROOT/'graphs'/f'{name}.svg').getroot()
  if len(r.findall('.//s:g[@class="node"]',ns))!=count:errors.append('SVG node count mismatch: '+name)
 result={'passed':not errors,'coverage_rows':len(rows),'numbered_scalar_results':cov['counts']['verified_scalar_model'],'source_theorems':audit['source_theorems'],
 'repository_owner_configured':bool(cfg.get('owner')),'errors':errors}
 (ROOT/'audit/repository_check.json').write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps(result,indent=2));return bool(errors)
if __name__=='__main__':sys.exit(main())
