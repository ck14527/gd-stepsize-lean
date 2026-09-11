#!/usr/bin/env python3
"""Generate public tables and citation metadata from actual checked declarations.
--check is read-only and fails if tracked generated documentation is stale.
"""
from pathlib import Path
import argparse,csv,io,json,sys
ROOT=Path(__file__).resolve().parents[1]

def render(root):
 cfg=json.loads((root/'repository.json').read_text())
 cov=json.loads((root/'audit/coverage.json').read_text())
 audit=json.loads((root/'audit/structure_check.json').read_text())
 sig={x['name']:x for x in json.loads((root/'audit/theorem_signatures.json').read_text())}
 inv=json.loads((root/'audit/inventory.json').read_text())
 rows=cov['results'];counts=cov['counts']
 url=cfg['url']
 paper_url=cfg['paper_url']
 paper_pdf_url=f"https://arxiv.org/pdf/{cfg['paper_arxiv_id']}"
 lean_version=(root/'lean-toolchain').read_text().strip().split(':v')[-1]
 mathlib_rev=next(p['rev'] for p in json.loads((root/'lake-manifest.json').read_text())['packages'] if p['name']=='mathlib')
 groups=[
 ('Sections 2--4','Composition kernels and optimal trees',lambda k:k[0] in '234',['GD.theorem_3_1','GD.theorem_4_5_balanced']),
 ('Section 5','Symmetric recursion and dyadic phase laws',lambda k:k.startswith('5.'),['GD.theorem_5_5','GD.theorem_5_8_scalar']),
 ('Section 6','Asymmetric recursion and phase bounds',lambda k:k.startswith('6.'),['GD.theorem_6_3','GD.theorem_6_5']),
 ('Appendix B','Counting optimal trees',lambda k:k.startswith('B.'),['GD.theorem_B_1']),
 ('Appendix C','Regularity and exact finite-grid certificates',lambda k:k.startswith('C.'),['GD.theorem_C_1','GD.theorem_C_3']),
 ('Appendix D','Auxiliary bounds and phase separation',lambda k:k.startswith('D.'),['GD.lemma_D_2','GD.proposition_D_9'])]
 assert len(rows)==36
 assert all(n in sig for r in rows for n in r['proof_declarations'])
 overview=['| Paper section | Topic | Checked / numbered | Selected Lean entry points |','|---|---|---:|---|']
 for title,topic,pred,names in groups:
  rs=[r for r in rows if pred(r['paper_id'])]
  links=', '.join(f'[`{n.removeprefix("GD.")}`]({sig[n]["file"]})' for n in names)
  overview.append(f'| {title} | {topic} | {sum(r["status"]=="verified_scalar_model" for r in rs)} / {len(rs)} | {links} |')
 table=['# Statement-by-statement correspondence','',
 'Each “Checked” entry refers to the precise real-number, recursion, or combinatorial statement listed below. It does not certify every sentence of the manuscript or reprove external optimization certificates.',
 '', '[Scope and trust boundary](VERIFICATION.md) · [Machine-readable coverage](../audit/coverage.json) · [CSV table](THEOREMS.csv)', '',
 '| Paper result | Description | Status | Proof declaration(s) and source |','|---|---|---|---|']
 csvbuf=io.StringIO(newline='');w=csv.writer(csvbuf,lineterminator="\n")
 w.writerow(['paper_id','kind','description','pdf_page','status','proof_declarations','source_files','target_definition','scope_note'])
 for r in rows:
  names=r['proof_declarations'];files=list(dict.fromkeys(sig[n]['file'] for n in names))
  links=', '.join(f'[`{n}`](../{sig[n]["file"]})' for n in names)
  status='Checked (scalar interface)' if r['paper_id'] in ['2.5','5.8'] else 'Checked'
  if r['status']!='verified_scalar_model':status=r['status']
  table.append(f'| {r["kind"]} {r["paper_id"]} | {r["title"]} | {status} | {links} |')
  w.writerow([r['paper_id'],r['kind'],r['title'],r['page'],r['status'],'; '.join(names),'; '.join(files),r['target_definition'] or '',r['scope_note']])
 table += ['', '## Exact scope notes', '', '| Result | Mathematical correspondence / limitation |','|---|---|']
 for r in rows:table.append(f'| {r["paper_id"]} | {r["scope_note"]} |')
 table += ['', 'For a listed `GD.Targets` definition, the audit requires an actual theorem whose return type directly mentions that exact target. A `def ... : Prop` alone is never counted as a proof. Other entries use the documented equivalent formulations and named supporting theorems.',
 '', 'Numbering is pinned to the manuscript SHA-256 in `repository.json`; update the registry and correspondence if the paper is renumbered.', '']
 badge=f'[![Lean proofs and audit]({url}/actions/workflows/lean.yml/badge.svg)]({url}/actions/workflows/lean.yml)\n\n'
 readme=f'''# Gradient descent stepsize composition in Lean 4

{badge}Companion Lean 4 formalization for **[{cfg['paper_title']}]({paper_url})**, by Yu Liu, Kang Chen, Rujun Jiang, and Tianyu Wang.

**Paper:** [arXiv:{cfg['paper_arxiv_id']}]({paper_url}) · [PDF]({paper_pdf_url}). This repository formalizes the paper's scalar and combinatorial results within the [documented verification scope](docs/VERIFICATION.md).

**{counts['verified_scalar_model']}/36 numbered scalar/combinatorial statements checked; {audit['source_theorems']} named source theorems.** The formalization covers composition kernels, optimal trees, recursive values, phase laws, regularity, and exact finite-grid certificates.

**Lean {lean_version}** · **mathlib `{mathlib_rev}`**. The root library is [GD.lean](GD.lean); [GD/Targets.lean](GD/Targets.lean) records the named scalar targets used by the audit.

[中文说明](docs/README_zh.md) · [All 36 results](docs/THEOREMS.md) · [Verification scope](docs/VERIFICATION.md) · [Dependency graphs](docs/DEPENDENCIES.md)

## Formalized results

{chr(10).join(overview)}

Declaration names above have namespace `GD`. The [complete correspondence table](docs/THEOREMS.md) and [CSV](docs/THEOREMS.csv) give every numbered result, its proof declarations, source files, and scope notes. Counts refer to numbered statements; {audit['source_theorems']} includes their supporting theorems.

The formalization starts with the manuscript's scalar kernels, recurrences, and tree model. External smooth-convex gradient-descent certificate interfaces are outside this model; Proposition 2.5 and Theorem 5.8 are checked at their scalar interfaces. The optional level-17 decimal enclosure is not a Lean-certified interval result. See the [verification scope](docs/VERIFICATION.md).

## Reproduce the verification

Install [Lean through elan](https://lean-lang.org/install/) and Python 3.11+. Clone the repository and run the checks from its root:

```bash
git clone {url}.git
cd {cfg['name']}
lake exe cache get
python3 tools/run_checks.py --require-scalar-complete
python3 tools/generate_docs.py --check
python3 tools/check_repository.py
```

The pinned [lean-toolchain](lean-toolchain), [lakefile.toml](lakefile.toml), and [lake-manifest.json](lake-manifest.json) select the checked toolchain and dependency revisions. Initial downloads require network access. Python scripts use only the standard library. On Windows PowerShell, set `$env:PYTHONUTF8 = '1'` and use `python` in place of `python3`.

For compilation alone, run `lake build GD`. The full runner also checks the mathematical inventory, exports elaborated declarations through [GD/Audit.lean](GD/Audit.lean), and audits all numbered results. Successful completion prints `Core checks passed.` followed by the coverage report location.

## Verification checks

| Check | What it establishes |
|---|---|
| `tools/run_checks.py --require-scalar-complete` | Builds every proof, exports elaborated declarations, and checks coverage, exact target references, transitive axioms, proof safety, source provenance, and theorem dependencies. |
| `tools/generate_docs.py --check` | Confirms that the committed correspondence tables, README files, and citation metadata match the audit data. |
| `tools/check_repository.py` | Checks required repository files, local documentation links, citations, graph node counts, and CI verification steps. |

The proof audit allows only Lean's standard foundational axioms `propext`, `Classical.choice`, and `Quot.sound`. It found no `sorryAx`, custom research axioms, or unsafe constants in theorem proof/type closures. Lean checks the formal statements; correspondence with the manuscript is a separate mathematical review, documented in the [scope notes](docs/VERIFICATION.md).

GitHub Actions runs the same checks and regenerates the dependency graphs. Fresh logs and audit records are attached to each run. Local logs are written to `logs/` and are excluded from Git; check the workflow result for the commit you use.

## Repository structure

| Path | Purpose |
|---|---|
| `GD.lean`, `GD/*.lean` | All mathematical definitions and proofs, plus the elaborated-environment exporter |
| `docs/THEOREMS.md`, `docs/THEOREMS.csv` | Complete 36-result correspondence and exact scope notes |
| `docs/statement_inventory.json` | Reviewed statement excerpts and mathematical dependencies |
| `docs/VERIFICATION.md`, `docs/DEPENDENCIES.md` | Verification scope, audit interpretation, and graph reproduction |
| `graphs/` | Mathematical DAG and actual Lean DAG in SVG, DOT, JSON-linked HTML |
| `audit/` | Checked declarations, signatures, axioms, source hashes and run summaries |
| `tools/` | Reproduction, correspondence checks, graph generation and rational certificate generation |
| `.github/workflows/lean.yml` | CI that rebuilds and audits on pushes, pull requests and version tags |
| `CITATION.cff` | Software citation metadata; the paper remains the mathematical reference |

The [dependency guide](docs/DEPENDENCIES.md) links to the mathematical graph ({len(inv['nodes'])} nodes) and the actual Lean theorem graph ({audit['source_theorems']} nodes, {audit['theorem_dependency_edges']} edges), with SVG and interactive views. Development and regeneration commands are in [CONTRIBUTING.md](CONTRIBUTING.md).

## Citation and license

Cite the [mathematical paper (arXiv:{cfg['paper_arxiv_id']})]({paper_url}) and, when identifying the formal artifact, use [CITATION.cff](CITATION.cff) with a fixed release tag and its exact commit. Published versions are listed on the [Releases page]({url}/releases). No software DOI has been assigned here.

A repository license has not yet been selected by the authors. Lean, mathlib, and other dependencies retain their own licenses.
'''
 cff={'cff-version':'1.2.0','message':'Please cite the accompanying mathematical paper and this version of its Lean formalization.','type':'software','title':f"Lean formalization of {cfg['paper_title']}",'authors':cfg['paper_authors'],'version':cfg['version'].removeprefix('v'),'keywords':['Lean 4','formal verification','gradient descent','stepsize schedules','dyadic phase']}
 if cfg.get('url'):cff['repository-code']=cfg['url']
 cff['references']=[{'type':'article','title':cfg['paper_title'],'authors':cfg['paper_authors'],'year':cfg['paper_year'],'url':paper_url}]
 # JSON is a YAML-compatible serialization and avoids ambiguous scalar escaping.
 cff_text=json.dumps(cff,ensure_ascii=False,indent=2)+'\n'
 zh=f'''# 中文使用说明

本仓库是论文 **[{cfg['paper_title']}]({paper_url})** 的 Lean 形式化代码。

**论文链接：**[arXiv:{cfg['paper_arxiv_id']}]({paper_url}) · [PDF 全文]({paper_pdf_url})。形式化针对该论文的标量与组合结论，具体覆盖范围见[验证说明](VERIFICATION.md)。

已核验 **{counts['verified_scalar_model']}/36 项编号标量／组合结论、{audit['source_theorems']} 个源码定理**，覆盖组合核、最优树、递推、相位律、正则性和精确有限网格证书。

工具链固定为 Lean {lean_version}，依赖版本由 `lake-manifest.json` 固定。验证范围从论文的标量递推和组合模型开始；外部光滑凸梯度下降证书接口不属于本形式化。

- [全部 36 项结论](THEOREMS.md)：逐项列出定理入口、源码和精确范围。
- [验证范围与复现说明](VERIFICATION.md)：公理检查、来源校验与数学对应关系。
- 数学依赖图和实际代码图：[DEPENDENCIES.md](DEPENDENCIES.md)。

复现命令见 [README](../README.md#reproduce-the-verification)。请查看所用 commit 在 Actions 中 `Lean proofs and audit` 的实际结果；每次运行的日志和审计附件随工作流保存。
'''
 return {'README.md':readme,'docs/THEOREMS.md':'\n'.join(table),'docs/THEOREMS.csv':csvbuf.getvalue(),'docs/README_zh.md':zh,'CITATION.cff':cff_text}

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--check',action='store_true');args=ap.parse_args()
 out=render(ROOT);stale=[]
 for rel,data in out.items():
  p=ROOT/rel
  if args.check:
   if not p.exists() or p.read_bytes()!=data.encode():stale.append(rel)
  else:p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data.encode())
 if stale:print('Stale generated files: '+', '.join(stale));return 1
 print(('Checked' if args.check else 'Generated')+f' {len(out)} documentation/metadata files.');return 0
if __name__=='__main__':sys.exit(main())
