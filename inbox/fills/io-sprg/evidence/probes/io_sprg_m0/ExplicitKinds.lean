import Lean
import TCSlib.Cryptography.Obfuscation.StructuredSeed.LPN
import TCSlib.Cryptography.Obfuscation.StructuredSeed.PolyTerms
import TCSlib.Cryptography.Obfuscation.StructuredSeed.BoolPRG
import TCSlib.Cryptography.Obfuscation.StructuredSeed.Degree
import TCSlib.Cryptography.Obfuscation.StructuredSeed.Defs
import TCSlib.Cryptography.Obfuscation.StructuredSeed.Params
import TCSlib.Cryptography.Obfuscation.StructuredSeed.Encoding
import TCSlib.Cryptography.Obfuscation.StructuredSeed.Buckets
import TCSlib.Cryptography.Obfuscation.StructuredSeed.SparseFactor
import TCSlib.Cryptography.Obfuscation.StructuredSeed.Polys
import TCSlib.Cryptography.Obfuscation.StructuredSeed.Samplers
import TCSlib.Cryptography.Obfuscation.StructuredSeed.Correctness
import TCSlib.Cryptography.Obfuscation.StructuredSeed.Stretch
import TCSlib.Cryptography.Obfuscation.StructuredSeed.Claim42.Load
import TCSlib.Cryptography.Obfuscation.StructuredSeed.Claim42
import TCSlib.Cryptography.Obfuscation.StructuredSeed.Hybrids
import TCSlib.Cryptography.Obfuscation.StructuredSeed.Reductions.LPN
import TCSlib.Cryptography.Obfuscation.StructuredSeed.Reductions.PRG
import TCSlib.Cryptography.Obfuscation.StructuredSeed.Security
import TCSlib.Cryptography.Obfuscation.StructuredSeed.Targets
import TCSlib.Cryptography.Obfuscation.StructuredSeed
import TCSlib.Cryptography.Obfuscation

set_option maxHeartbeats 0
open Lean Elab Command

def candsPayload : String := "Complexity.Nat.mul_comm\nComplexity.pow_succ\nNat.mul_comm\nTCSlib.Complexity.Nat.mul_comm\nTCSlib.Complexity.pow_succ\nTCSlib.Cryptography.CoinSampling.Nat.mul_comm\nTCSlib.Cryptography.CoinSampling.pow_succ\nTCSlib.Cryptography.Complexity.Nat.mul_comm\nTCSlib.Cryptography.Complexity.pow_succ\nTCSlib.Cryptography.Games.Nat.mul_comm\nTCSlib.Cryptography.Games.pow_succ\nTCSlib.Cryptography.Nat.mul_comm\nTCSlib.Cryptography.Obfuscation.Complexity.Nat.mul_comm\nTCSlib.Cryptography.Obfuscation.Complexity.pow_succ\nTCSlib.Cryptography.Obfuscation.Nat.mul_comm\nTCSlib.Cryptography.Obfuscation.StructuredSeed.Complexity.Nat.mul_comm\nTCSlib.Cryptography.Obfuscation.StructuredSeed.Complexity.pow_succ\nTCSlib.Cryptography.Obfuscation.StructuredSeed.Nat.mul_comm\nTCSlib.Cryptography.Obfuscation.StructuredSeed.TCSlib.Cryptography.CoinSampling.Nat.mul_comm\nTCSlib.Cryptography.Obfuscation.StructuredSeed.TCSlib.Cryptography.CoinSampling.pow_succ\nTCSlib.Cryptography.Obfuscation.StructuredSeed.TCSlib.Cryptography.Games.Nat.mul_comm\nTCSlib.Cryptography.Obfuscation.StructuredSeed.TCSlib.Cryptography.Games.pow_succ\nTCSlib.Cryptography.Obfuscation.StructuredSeed.Turing.Nat.mul_comm\nTCSlib.Cryptography.Obfuscation.StructuredSeed.Turing.pow_succ\nTCSlib.Cryptography.Obfuscation.StructuredSeed.pow_succ\nTCSlib.Cryptography.Obfuscation.TCSlib.Cryptography.CoinSampling.Nat.mul_comm\nTCSlib.Cryptography.Obfuscation.TCSlib.Cryptography.CoinSampling.pow_succ\nTCSlib.Cryptography.Obfuscation.TCSlib.Cryptography.Games.Nat.mul_comm\nTCSlib.Cryptography.Obfuscation.TCSlib.Cryptography.Games.pow_succ\nTCSlib.Cryptography.Obfuscation.Turing.Nat.mul_comm\nTCSlib.Cryptography.Obfuscation.Turing.pow_succ\nTCSlib.Cryptography.Obfuscation.pow_succ\nTCSlib.Cryptography.TCSlib.Cryptography.CoinSampling.Nat.mul_comm\nTCSlib.Cryptography.TCSlib.Cryptography.CoinSampling.pow_succ\nTCSlib.Cryptography.TCSlib.Cryptography.Games.Nat.mul_comm\nTCSlib.Cryptography.TCSlib.Cryptography.Games.pow_succ\nTCSlib.Cryptography.Turing.Nat.mul_comm\nTCSlib.Cryptography.Turing.pow_succ\nTCSlib.Cryptography.pow_succ\nTCSlib.Nat.mul_comm\nTCSlib.TCSlib.Cryptography.CoinSampling.Nat.mul_comm\nTCSlib.TCSlib.Cryptography.CoinSampling.pow_succ\nTCSlib.TCSlib.Cryptography.Games.Nat.mul_comm\nTCSlib.TCSlib.Cryptography.Games.pow_succ\nTCSlib.Turing.Nat.mul_comm\nTCSlib.Turing.pow_succ\nTCSlib.pow_succ\nTuring.Nat.mul_comm\nTuring.pow_succ\n_private.TCSlib.Cryptography.Obfuscation.StructuredSeed.Defs.0.Nat.mul_comm\n_private.TCSlib.Cryptography.Obfuscation.StructuredSeed.Defs.0.TCSlib.Cryptography.Nat.mul_comm\n_private.TCSlib.Cryptography.Obfuscation.StructuredSeed.Defs.0.TCSlib.Cryptography.Obfuscation.Nat.mul_comm\n_private.TCSlib.Cryptography.Obfuscation.StructuredSeed.Defs.0.TCSlib.Cryptography.Obfuscation.StructuredSeed.Nat.mul_comm\n_private.TCSlib.Cryptography.Obfuscation.StructuredSeed.Defs.0.TCSlib.Cryptography.Obfuscation.StructuredSeed.pow_succ\n_private.TCSlib.Cryptography.Obfuscation.StructuredSeed.Defs.0.TCSlib.Cryptography.Obfuscation.pow_succ\n_private.TCSlib.Cryptography.Obfuscation.StructuredSeed.Defs.0.TCSlib.Cryptography.pow_succ\n_private.TCSlib.Cryptography.Obfuscation.StructuredSeed.Defs.0.TCSlib.Nat.mul_comm\n_private.TCSlib.Cryptography.Obfuscation.StructuredSeed.Defs.0.TCSlib.pow_succ\n_private.TCSlib.Cryptography.Obfuscation.StructuredSeed.Defs.0.pow_succ\npow_succ"

run_cmd do
  let cands := candsPayload.splitOn "\n"
  let env ← getEnv
  let mut byStr : Std.HashMap String Name := {}
  for (n, _) in env.constants.toList do
    byStr := byStr.insert n.toString n
  for s in cands do
    let some n := byStr[s]? | continue
    let some ci := env.find? n | continue
    let home := (env.getModuleIdxFor? n).map fun i => env.header.moduleNames[i.toNat]!.toString
    let kind := match ci with
      | .defnInfo _ => "def" | .thmInfo _ => "theorem" | .opaqueInfo _ => "opaque"
      | .ctorInfo _ => "constructor" | .recInfo _ => "recursor"
      | .inductInfo _ => "inductive" | .axiomInfo _ => "axiom" | .quotInfo _ => "quotient"
    let abbrevFlag := match ci with
      | .defnInfo d => match d.hints with | .abbrev => true | _ => false
      | _ => false
    let status := match Lean.getReducibilityStatusCore env n with
      | .reducible => "reducible" | .semireducible => "semireducible" | .irreducible => "irreducible"
    IO.println ("EXPLICIT_KIND " ++ (Json.mkObj [("spelling", toJson s), ("name", toJson n.toString), ("home", toJson home),
      ("kind", toJson kind), ("abbrev", toJson abbrevFlag), ("status", toJson status),
      ("projection", toJson (env.isProjectionFn n)), ("instance", toJson (Lean.Meta.isInstanceCore env n))]).compress)
  IO.println s!"EXPLICIT_KIND_DONE {cands.length}"
