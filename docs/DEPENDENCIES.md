# Mathematical and Lean proof dependencies

Arrows go from a prerequisite to a dependent result. The mathematical graph records the reviewed relationships between statements, definitions, and external interfaces. The Lean graph is extracted from elaborated proof terms, with generated helper constants collapsed to named source theorems. Their edges need not coincide.

## Complete graph files

| Graph | Nodes / edges | File |
|---|---|---|
| Reviewed mathematical DAG | 66 / 154 | [SVG](../graphs/manuscript_dag.svg), [DOT](../graphs/manuscript_dag.dot), [interactive HTML](../graphs/manuscript_dag.html) |
| Actual Lean source-theorem DAG | 569 / 3,852 | [JSON with topological order](../audit/lean_theorem_graph.json), [DOT](../graphs/lean_proof_dependencies.dot) |
| Transitive reduction of Lean DAG | 569 / 1,101 | [SVG](../graphs/lean_proof_dependencies_reduced.svg), [DOT](../graphs/lean_proof_dependencies_reduced.dot) |

Open SVGs at full size to zoom. For the interactive mathematical graph, download the repository and open `graphs/manuscript_dag.html` in a browser; it works offline. GitHub renders Markdown/Mermaid and SVG, but its source viewer does not run arbitrary HTML scripts.

The mathematical DAG includes definitions, bridges, and externally cited interfaces. Green result nodes mean that the corresponding scalar/combinatorial statement is checked; they do not prove the external interface nodes. The [scope table](VERIFICATION.md) is part of interpreting this graph.

All numbered results use the same coverage convention. The [correspondence table](THEOREMS.md) links each result to its Lean declarations and records any scope limitation. The mathematical registry is [statement_inventory.json](statement_inventory.json); the actual theorem graph is [lean_theorem_graph.json](../audit/lean_theorem_graph.json).

## Regeneration

```bash
python3 tools/build_inventory.py
python3 tools/make_coverage.py
npm ci --prefix tools
node tools/render_graph.mjs .
node tools/render_proof_graph.mjs .
```

Regenerate the compiled Lean DAG first with `python3 tools/run_checks.py --require-scalar-complete` after editing proofs. Graph rendering uses the fixed `@viz-js/viz` package in `tools/package-lock.json` and checks the embedded browser script before writing the interactive page. Node.js is needed only for rendering graphs, not for checking the Lean mathematics.
