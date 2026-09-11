# Contributing to the formalization

Use the pinned `lean-toolchain` and `lake-manifest.json`. Keep mathematical changes separate from claim-numbering or documentation updates where practical.

After changing proofs, run:

```bash
lake exe cache get
python3 tools/run_checks.py --require-scalar-complete
python3 tools/generate_docs.py
python3 tools/check_repository.py
```

For a new or reformulated manuscript result, update `docs/statement_inventory.json` and the explicit correspondence in `tools/make_coverage.py`. A new proposition definition does not count as a proof; include a theorem with the full intended target and explain any extra hypotheses or scope restriction.

The axiom allowlist is the usual `propext`, `Classical.choice`, and `Quot.sound`. Do not add admitted proofs, custom axioms for pending mathematical facts, or unsafe evaluation in proof closures. Keep external certificate assumptions explicit.

Regenerate dependency graphics with the commands in `docs/DEPENDENCIES.md` after the audit. Commit the corresponding tables and checked metadata. Cite an immutable commit or release when associating an artifact with a paper version.
