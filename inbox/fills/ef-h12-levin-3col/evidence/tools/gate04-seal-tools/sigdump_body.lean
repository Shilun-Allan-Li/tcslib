/- Elaborated-signature dump (gate 04 round 5). For every non-auxiliary constant declared in each
target module: its kind, its number of universe parameters, and hashes of
* `strict`: its type with binder names erased (binder info kept), metadata stripped, and universe
  parameters renamed by position (`u_0, u_1, …`);
* `erased`: the same with the universe arguments of referenced constants also erased (so a
  constant whose universe arity changed but that is used at the same level counts as unchanged);
* `value`: for definitions only, the normalised value (strict).
Private names are reported under their user name. -/
open Lean

namespace G04R5Sig

partial def norm (eraseConstLevels : Bool) : Expr → Expr
  | .forallE _ t b bi => .forallE `_ (norm eraseConstLevels t) (norm eraseConstLevels b) bi
  | .lam _ t b bi => .lam `_ (norm eraseConstLevels t) (norm eraseConstLevels b) bi
  | .letE _ t v b nd => .letE `_ (norm eraseConstLevels t) (norm eraseConstLevels v) (norm eraseConstLevels b) nd
  | .mdata _ e => norm eraseConstLevels e
  | .app f a => .app (norm eraseConstLevels f) (norm eraseConstLevels a)
  | .proj s i e => .proj s i (norm eraseConstLevels e)
  | .const n ls => if eraseConstLevels then .const n [] else .const n ls
  | e => e

def numSuffix (s pre : String) : Bool :=
  s.startsWith pre && (s.drop pre.length).length > 0 && (s.drop pre.length).all Char.isDigit

def isAux : Name → Bool
  | .str p s => s.startsWith "_" || numSuffix s "match_" || numSuffix s "proof_" || numSuffix s "eq_" ||
      s == "eq_def" || s == "eq_unfold" || isAux p
  | .num _ _ => true
  | .anonymous => false

def kindOf : ConstantInfo → String
  | .defnInfo _ => "def" | .thmInfo _ => "thm" | .axiomInfo _ => "axiom" | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quot" | .inductInfo _ => "inductive" | .ctorInfo _ => "ctor" | .recInfo _ => "rec"

def h (e : Expr) : UInt64 := hash (toString e)

end G04R5Sig

open G04R5Sig in
run_cmd do
  let env ← getEnv
  let mut out : Array String := #[]
  for m in targetMods do
    let some idx := env.getModuleIdx? m | continue
    let data := env.header.moduleData[idx.toNat]!
    for ci in data.constants do
      let user := (privateToUserName? ci.name).getD ci.name
      if isAux user then continue
      let ps := ci.levelParams
      let lv := (List.range ps.length).map fun i => Level.param (Name.mkSimple s!"u_{i}")
      let ty := ci.type.instantiateLevelParams ps lv
      let val := match ci with
        | .defnInfo d => toString (h (norm false (d.value.instantiateLevelParams ps lv)))
        | _ => "-"
      out := out.push s!"{m}\t{user}\t{kindOf ci}\t{ps.length}\t{h (norm false ty)}\t{h (norm true ty)}\t{val}"
  IO.FS.writeFile outFile ("\n".intercalate out.toList ++ "\n")
