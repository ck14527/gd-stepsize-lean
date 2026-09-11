# Verification scope and trust boundary

All 36 numbered **scalar/combinatorial statements in the correspondence table** have checked Lean proofs. The last verified snapshot contains 569 named source theorems and 1,455 elaborated project declarations. These are different counts: principal results often require many auxiliary theorems, and Lean generates additional declarations.

## What is formalized

The model starts with exact real kernels `K` and `A`, the actual recursive values `U` and `W`, and finite composition trees. The development proves rearrangement and equality cases, balanced optimality and all optimal tree structures, interpolation and phase laws, differentiability and one-sided derivatives, finite-grid certificates, support inequalities, deficit concentration, and strict OBS-F phase separation. Limits are proved for the actual recursions and canonical profiles.

The complete [36-result table](THEOREMS.md) links to every entry point and records equivalent formulations and scope adjustments. The correspondence is based on the manuscript snapshot identified by SHA-256 in `repository.json`; that hash identifies the audited snapshot and does not certify later manuscript revisions.

## What the result does not certify

| Boundary | Exact meaning |
|---|---|
| External GD certificates | Smooth-convex function classes, gradient-descent trajectories, and imported composition/tightness certificates are not developed in this project. |
| Proposition 2.5 | Treewise/scalar conjugacies, recursive optima and associated scalar identities are proved. Connecting certificate-valid schedules to those scalar objects remains an external interface. |
| Theorem 5.8 | The scalar coefficient identity, uniform remainder and cluster interval are proved. The external worst-case GD construction and its tightness semantics are not reproved. |
| Optional level-17 decimals | General C.3 grid bounds and convergence are proved, but the printed decimal example after C.3 / in Remark 5.6 has no Lean interval certificate. C.2's finite rational certificate is fully checked. |
| Real-RAM complexity | C.3's cached array algorithm has a proved `30 * 2^k` bound in its explicit scalar-operation model, counting real powers as primitive operations. This is not bit complexity or a floating-point implementation. |
| Prose correspondence | Kernel checking proves the Lean types. The claim that these types express the intended manuscript statements requires a mathematical comparison; it is not established automatically by parsing the PDF. |
| Broader optimality | The formalization does not assert minimax optimality over every positive predetermined stepsize schedule. |

The verification establishes the registered scalar and combinatorial statements within these boundaries.

## Reproducible checks

```bash
lake exe cache get
python3 tools/run_checks.py --require-scalar-complete
```

The pipeline validates the reviewed mathematical inventory, builds all proof modules, exports the compiled environment, regenerates coverage, and audits names, exact target references, axiom closures, proof safety, and the actual theorem dependency DAG. All stages must exit 0. A bare `lake build` alone does not establish correspondence coverage or absence of admitted proofs.

Where a result has a `GD.Targets` declaration, the structure audit requires a theorem returning that exact target type. A proposition definition is never counted as a proof. For older algebraic and combinatorial entries with several entry points, the table states the precise equivalent formulation and supporting theorem names.

The current source-theorem dependency graph has 569 nodes and 3,852 edges. Its display applies transitive reduction to 1,101 edges; the full JSON is retained. The separate mathematical graph has 66 nodes and 154 edges and includes external interfaces and definitions. The two graphs need not have identical edges.

## Foundation and trusted components

The toolchain is the official Lean 4.19.0 release. The fixed mathlib commit is `c44e0c8ee63ca166450922a373c7409c5d26b00b`; all transitive dependency revisions are in `lake-manifest.json`.

The allowed foundational axioms are `propext`, `Classical.choice`, and `Quot.sound`. The exported axiom closure contains no other axiom for a named source theorem: in particular no `sorryAx`, custom mathematical axioms, or `native_decide` oracle. The audit also checks the transitive project-constant closure of theorem proofs and types for `unsafe` and `partial` definitions. Compiler-generated runtime constants outside those closures are counted separately and are not mathematical proof assumptions.

This is a Lean-kernel verification, not a claimed independent implementation of Lean's type checker. The audit script uses Lean's actual elaborated types and proof terms; the mathematical correspondence registry and Python auditing code remain reviewable components of the workflow.

## Completion flags

```bash
python3 tools/verify_structure.py --require-scalar-complete
```

This checks an existing export and is expected to return 0 for the checked snapshot. For fresh proof evidence after editing Lean files, run the full pipeline above.

```bash
python3 tools/verify_structure.py --require-complete
```

This deliberately checks a broader boundary including external GD certificate interfaces and returns 3 in this repository. CI uses the explicit scalar-completion gate and does not mislabel the broader gate as passed.

## Artifact provenance

`audit/build_provenance.json` binds the checked proof export to the exact source and toolchain inputs, and `audit/source_sha256.json` records source and documentation hashes. The public workflow rebuilds and audits a GitHub checkout and attaches fresh verification records to each run.

Build logs are generated in `logs/` and retained in CI artifacts. Downloadable toolchains, dependency caches, and local build logs are not committed here.
