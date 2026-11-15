/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.SpecialEncryption
import TCSlib.Cryptography.Encryption.PrivateKey.FromPRF.ReductionMachine
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut requested := 0
  let mut excluded := 0
  for (name, ci) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let home := env.header.moduleNames[idx.toNat]!
      if home.toString.startsWith "TCSlib." then
        if let .defnInfo d := ci then
          let status ← liftCoreM <| Lean.getReducibilityStatus name
          let matcher := Lean.Meta.isMatcherCore env name
          let rec body : Nat → Expr → Expr
            | 0, e => e
            | fuel+1, .lam _ _ b _ => body fuel b
            | fuel+1, .letE _ _ v b _ => body fuel (b.instantiate1 v)
            | _, e => e
          let ty := d.type.getForallBody.getAppFn.constName?
          let val := body 64 d.value
          let coe := ty == some `CoeFun || ty == some `Coe
          let map := if val.getAppArgs.isEmpty then val else val.getAppArgs.back!
          let projection := match (body 64 map).getAppFn with
            | .proj .. => true
            | .const n _ => env.isProjectionFn n
            | _ => false
          let isNotation : Bool := (name == `Complexity.PolyExpr.eval && false) ||
            (true && coe && projection)
          if isNotation || (status == .reducible && !matcher) then
            excluded := excluded + 1
            logInfo m!"EXCLUDED\t{home}\t{name}"
          else
            let id := mkIdent name
            if status != .irreducible then
              elabCommand (← `(command| attribute [local irreducible] $id:ident))
            let installed ← liftCoreM <| Lean.getReducibilityStatus name
            unless installed == .irreducible do
              throwError "seal not installed: {name}"
            requested := requested + 1
            logInfo m!"SEALED\t{home}\t{name}"
  logInfo m!"SEAL_COUNTS requested={requested} excluded={excluded}"

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The zero-prefix mask of special encryption

## Main definitions

This module adds no definitions.

## Main results

* `SecureComputation.spEncStr_eq_zeroPrefixMask`: the full ciphertext body is the XOR of
  a zero-prefix message with the pad.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §6.2.2, Algorithm 157.2.
-/

namespace TCSlib.Cryptography.SecureComputation

open Complexity Turing TCSlib.Cryptography

/-- Special encryption masks the zero-prefix message:
`spEncStr E k m r = ⟨r, (0^{|r|} ++ m) ⊕ E(⟨k,r⟩)⟩`, whenever the pad has at least
`|r| + |m|` bits. [PS10, §6.2.2, Algorithm 157.2]

**Proof sketch.** Split the pad after the nonce length. Split XOR at the same boundary;
its prefix is unchanged by the zero mask, and its suffix is the encrypted message.
The pad-length hypothesis makes the prefix exactly as long as the nonce. -/
theorem spEncStr_eq_zeroPrefixMask (E : List Bool → List Bool) (k m r : List Bool)
    (hp : r.length + m.length ≤ (E (pairEncode k r)).length) :
    spEncStr E k m r = pairEncode r
      (List.zipWith xor (List.replicate r.length false ++ m) (E (pairEncode k r))) := by
  rw [spEncStr_eq]
  congr 1
  have hlen : ((E (pairEncode k r)).take r.length).length = r.length := by
    rw [List.length_take, Nat.min_eq_left (by omega)]
  conv_rhs => rw [← List.take_append_drop r.length (E (pairEncode k r))]
  rw [List.zipWith_append (by rw [List.length_replicate, hlen])]
  congr 1
  rw [List.zipWith_comm_of_comm Bool.xor_comm]
  simpa only [hlen] using
    (MultiMsg.zipWith_xor_replicate_false ((E (pairEncode k r)).take r.length)).symm

end TCSlib.Cryptography.SecureComputation
