import Lean
import TCSlib.Cryptography.Obfuscation.StructuredSeed.Samplers
open Lean Elab Command
run_cmd do
  let c ← getConstInfo ``LawfulFunctor.comp_map
  let kind := match c with
    | .thmInfo _ => "theorem"
    | .defnInfo _ => "def"
    | _ => "other"
  IO.println ("EXPORT_ALIAS_KIND " ++ (Json.mkObj [("alias", toJson "comp_map"),
    ("name", toJson "LawfulFunctor.comp_map"), ("kind", toJson kind)]).compress)
