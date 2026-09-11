#!/usr/bin/env python3
"""Validate the reviewed manuscript registry and emit its dependency DAG.
The registry contains numbered statement excerpts and their mathematical dependencies.
"""
from pathlib import Path
import json
ROOT=Path(__file__).resolve().parents[1]
def main():
 raw=json.loads((ROOT/'docs/statement_inventory.json').read_text())
 nodes=raw['nodes'];by={n['id']:n for n in nodes}
 assert len(by)==len(nodes),'Duplicate inventory ID'
 for n in nodes:
  assert all(d in by for d in n['depends_on']),n['id']
 order=[];pending=set(by)
 while pending:
  ready=sorted(k for k in pending if all(d in order for d in by[k]['depends_on']))
  assert ready,'Cycle in manuscript dependency graph'
  order.extend(ready);pending.difference_update(ready)
 raw['topological_order']=order
 for n in nodes:n['formal_status']='external' if n['kind']=='External' else 'pending'
 count=sum(n['kind'] in ['Theorem','Lemma','Proposition','Corollary'] for n in nodes)
 assert count==36,count
 (ROOT/'audit').mkdir(exist_ok=True)
 (ROOT/'audit/inventory.json').write_text(json.dumps(raw,ensure_ascii=False,indent=2)+'\n')
 result={'nodes':len(nodes),'edges':sum(len(n['depends_on']) for n in nodes),'numbered_results':count,'acyclic':True,'all_numbered_results_accounted_for':True,'important_distinction':'Acyclicity is not proof correctness; this is the reviewed mathematical graph.'}
 (ROOT/'audit/dag_check.json').write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps(result))
if __name__=='__main__':main()
