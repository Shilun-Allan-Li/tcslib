import Lean
import TCSlib.Cryptography.Candidates.DiscreteLog
import TCSlib.Cryptography.Hashing.FromDiscreteLog.Encoding
import TCSlib.Cryptography.Hashing.FromDiscreteLog.Algebra
import TCSlib.Cryptography.Hashing.FromDiscreteLog

set_option maxHeartbeats 0
set_option maxRecDepth 65536
open Lean Elab Command
#print axioms TCSlib.Cryptography.Authentication.dlHash_crh
def owners : List Name := [`TCSlib.Cryptography.Candidates.DiscreteLog, `TCSlib.Cryptography.Hashing.FromDiscreteLog.Encoding, `TCSlib.Cryptography.Hashing.FromDiscreteLog.Algebra, `TCSlib.Cryptography.Hashing.FromDiscreteLog]
def nameMap : Std.HashMap String String := {}

def normName (n : Name) : String := ((Lean.privateToUserName? n).getD n).toString

def kindOf : ConstantInfo → String
  | .axiomInfo _ => "axiom" | .defnInfo _ => "def" | .thmInfo _ => "theorem" | .opaqueInfo _ => "opaque"
  | .quotInfo _ => "quotient" | .inductInfo _ => "inductive" | .ctorInfo _ => "constructor" | .recInfo _ => "recursor"

def abbrevOf : ConstantInfo → String
  | .defnInfo d => (match d.hints with | .abbrev => "abbrev" | _ => "-")
  | _ => "-"

def renameE (e : Expr) : Expr := e.replace fun x => match x with
  | .const n ls =>
    let s := normName n
    some (.const (Name.mkSimple ((nameMap[s]?).getD s)) ls)
  | _ => none

run_cmd do
  let env ← getEnv
  let names := env.header.moduleNames
  let simps := Lean.Meta.simpExtension.getState env
  let mut n := 0
  for (c, ci) in env.constants.toList do
    let some mi := env.getModuleIdxFor? c | continue
    let home := names[mi.toNat]!
    unless owners.contains home do continue
    let axs ← liftCoreM (Lean.collectAxioms c)
    let axs := (axs.map (·.toString)).qsort (· < ·)
    let red := match Lean.getReducibilityStatusCore env c with
      | .reducible => "reducible" | .semireducible => "semireducible" | .irreducible => "irreducible"
    let abbr := abbrevOf ci
    IO.println s!"C\t{normName c}\t{c.isInternal || (Lean.privateToUserName? c).isSome}\t{(Lean.privateToUserName? c).isSome}\t{home}\t{kindOf ci}\t{(renameE ci.type).hash}\t{red}\t{abbr}\t{simps.isLemma (.decl c)}\t{Lean.Meta.isInstanceCore env c}\t{isProtected env c}\t{axs.toList}"
    n := n + 1
  IO.println s!"C-COUNT {n}"
