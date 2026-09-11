# Gradient descent stepsize composition in Lean 4

[![Lean proofs and audit](https://github.com/ck14527/gd-stepsize-lean/actions/workflows/lean.yml/badge.svg)](https://github.com/ck14527/gd-stepsize-lean/actions/workflows/lean.yml)

Companion Lean 4 formalization for **[Optimal Recursive Composition and Dyadic Phase Laws for Gradient Descent with Predetermined Stepsizes](https://arxiv.org/abs/2609.11788)**, by Yu Liu, Kang Chen, Rujun Jiang, and Tianyu Wang.

**Paper:** [arXiv:2609.11788](https://arxiv.org/abs/2609.11788) · [PDF](https://arxiv.org/pdf/2609.11788). This repository formalizes the paper's scalar and combinatorial results within the [documented verification scope](docs/VERIFICATION.md).

**36/36 numbered scalar/combinatorial statements checked; 569 named source theorems.** The formalization covers composition kernels, optimal trees, recursive values, phase laws, regularity, and exact finite-grid certificates.

**Lean 4.19.0** · **mathlib `c44e0c8ee63ca166450922a373c7409c5d26b00b`**. The root library is [GD.lean](GD.lean); [GD/Targets.lean](GD/Targets.lean) records the named scalar targets used by the audit.

[中文说明](docs/README_zh.md) · [All 36 results](docs/THEOREMS.md) · [Verification scope](docs/VERIFICATION.md) · [Dependency graphs](docs/DEPENDENCIES.md)

## Formalized results

| Paper section | Topic | Checked / numbered | Selected Lean entry points |
|---|---|---:|---|
| Sections 2--4 | Composition kernels and optimal trees | 12 / 12 | [`theorem_3_1`](GD/Rearrangement.lean), [`theorem_4_5_balanced`](GD/Conjugacy.lean) |
| Section 5 | Symmetric recursion and dyadic phase laws | 7 / 7 | [`theorem_5_5`](GD/PhaseTheorem.lean), [`theorem_5_8_scalar`](GD/ObjectivePhase.lean) |
| Section 6 | Asymmetric recursion and phase bounds | 4 / 4 | [`theorem_6_3`](GD/OBSInterpolation.lean), [`theorem_6_5`](GD/ContactPhase.lean) |
| Appendix B | Counting optimal trees | 1 / 1 | [`theorem_B_1`](GD/TreeCounts.lean) |
| Appendix C | Regularity and exact finite-grid certificates | 3 / 3 | [`theorem_C_1`](GD/DerivativeTheorem.lean), [`theorem_C_3`](GD/GridAlgorithm.lean) |
| Appendix D | Auxiliary bounds and phase separation | 9 / 9 | [`lemma_D_2`](GD/DiscreteModulus.lean), [`proposition_D_9`](GD/OBSUpperBarrier.lean) |

Declaration names above have namespace `GD`. The [complete correspondence table](docs/THEOREMS.md) and [CSV](docs/THEOREMS.csv) give every numbered result, its proof declarations, source files, and scope notes. Counts refer to numbered statements; 569 includes their supporting theorems.

The formalization starts with the manuscript's scalar kernels, recurrences, and tree model. External smooth-convex gradient-descent certificate interfaces are outside this model; Proposition 2.5 and Theorem 5.8 are checked at their scalar interfaces. The optional level-17 decimal enclosure is not a Lean-certified interval result. See the [verification scope](docs/VERIFICATION.md).

## Reproduce the verification

Install [Lean through elan](https://lean-lang.org/install/) and Python 3.11+. Clone the repository and run the checks from its root:

```bash
git clone https://github.com/ck14527/gd-stepsize-lean.git
cd gd-stepsize-lean
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

The [dependency guide](docs/DEPENDENCIES.md) links to the mathematical graph (66 nodes) and the actual Lean theorem graph (569 nodes, 3852 edges), with SVG and interactive views. Development and regeneration commands are in [CONTRIBUTING.md](CONTRIBUTING.md).

## Citation and license

Cite the [mathematical paper (arXiv:2609.11788)](https://arxiv.org/abs/2609.11788) and, when identifying the formal artifact, use [CITATION.cff](CITATION.cff) with a fixed release tag and its exact commit. Published versions are listed on the [Releases page](https://github.com/ck14527/gd-stepsize-lean/releases). No software DOI has been assigned here.

A repository license has not yet been selected by the authors. Lean, mathlib, and other dependencies retain their own licenses.
