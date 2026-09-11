"""Bind a successful proof export to the exact Lean and dependency inputs.
Called by run_checks.py after the build/export succeeds; not a stand-alone verifier.
"""
from pathlib import Path
import hashlib,json
ROOT=Path(__file__).resolve().parents[1]
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def proof_inputs(root=ROOT):
 paths=[root/'GD.lean',root/'lean-toolchain',root/'lakefile.toml',root/'lake-manifest.json',*sorted((root/'GD').glob('*.lean'))]
 return {p.relative_to(root).as_posix():digest(p) for p in paths}
def record(before,root=ROOT):
 after=proof_inputs(root)
 if before!=after:raise RuntimeError('Proof inputs changed during build/export. Run verification again.')
 result={'method':'Written after successful build and elaborated-environment export; proof inputs checked unchanged during the run.',
 'files':after,'elaborated_export_sha256':digest(root/'audit/lean_declarations.json')}
 (root/'audit/build_provenance.json').write_text(json.dumps(result,indent=2)+'\n')
 return result
