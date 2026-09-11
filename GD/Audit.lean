import GD
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts

open Lean Elab Command

/- Export actual elaborated types, proof references, and transitive axioms.
This inspects compiled terms, rather than searching source text for keywords. -/
run_cmd do
  let env ← getEnv
  let mut rows : Array Json := #[]
  for (name, info) in env.constants.toList do
    if "GD.".isPrefixOf name.toString then
      let kind := match info with
        | .thmInfo _ => "theorem"
        | .defnInfo _ => "definition"
        | .axiomInfo _ => "axiom"
        | .opaqueInfo _ => "opaque"
        | _ => "other"
      if kind != "other" then
        let typ ← liftTermElabM do
          return (← Meta.ppExpr info.type).pretty
        let used := match info.value? with
          | some v => v.getUsedConstants
          | none => #[]
        let refs := used.filter (fun n => "GD.".isPrefixOf n.toString)
        let axioms ← Lean.collectAxioms name
        let safety := match info with
          | .defnInfo d => match d.safety with
            | .safe => "safe"
            | .unsafe => "unsafe"
            | .partial => "partial"
          | _ => "kernel"
        rows := rows.push <| Json.mkObj [
          ("name",toJson name.toString),
          ("kind",toJson kind),
          ("type",toJson typ),
          ("safety",toJson safety),
          ("proof_references",toJson (refs.map Name.toString)),
          ("type_references",toJson ((info.type.getUsedConstants.filter (fun n => "GD.".isPrefixOf n.toString)).map Name.toString)),
          ("axioms",toJson (axioms.map Name.toString))]
  liftIO <| IO.FS.createDirAll "audit"
  liftIO <| IO.FS.writeFile "audit/lean_declarations.json" (Json.pretty (toJson rows))
  logInfo m!"Exported {rows.size} GD declarations to audit/lean_declarations.json"
