/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean
import TCSlib.Cryptography.Games.Efficiency
import TCSlib.Cryptography.Asymptotic.EnsemblesLemmas
import TCSlib.Cryptography.Foundations.BitLists
import TCSlib.Cryptography.Encryption.PublicKey.OracleSecurity
import TCSlib.Cryptography.Encryption.PrivateKey.OracleSecurity
/- DLC-SEAL SealControlsSealedEvalOpen: whole-file closure seal of `lean_proof/dlc/SealControls.lean` (PolyExpr.eval open). -/
set_option maxHeartbeats 0 in
run_cmd do
  let env ← Lean.getEnv
  let excl : List Lean.Name := [`Complexity.PolyExpr.eval]
  let mut sealed : Array Lean.Name := #[]
  let mut abbrevs : Nat := 0
  let mut already : Nat := 0
  let mut excluded : Nat := 0
  for (n, ci) in env.constants.map₁.toList do
    let some mi := env.getModuleIdxFor? n | continue
    let m := env.header.moduleNames[mi.toNat]!
    unless (`TCSlib).isPrefixOf m do continue
    let .defnInfo d := ci | continue
    if excl.contains n then
      excluded := excluded + 1
      continue
    match d.hints with
    | .abbrev =>
      abbrevs := abbrevs + 1
      continue
    | _ => pure ()
    let st ← Lean.Elab.Command.liftCoreM <| Lean.getReducibilityStatus n
    if st == .irreducible then
      already := already + 1
      sealed := sealed.push n
      continue
    Lean.Elab.Command.elabCommand (← `(command| attribute [local irreducible] $(Lean.mkIdent n):ident))
    let st' ← Lean.Elab.Command.liftCoreM <| Lean.getReducibilityStatus n
    unless st' == .irreducible do throwError "DLC-SEAL: not sealed {n}"
    sealed := sealed.push n
  Lean.modifyEnv fun cur =>
    Lean.Meta.globalInstanceExtension.modifyState cur fun s => sealed.foldl (fun s n => s.erase n) s
  let env' ← Lean.getEnv
  for n in sealed do
    if Lean.Meta.isGlobalInstance env' n then throwError "DLC-SEAL: instance unfolding kept for {n}"
  Lean.logInfo m!"DLC-SEAL SealControlsSealedEvalOpen: sealed={sealed.size} (already irreducible {already}) abbrev-excluded={abbrevs} excluded={excluded}"


/-! Paired controls of the dl-consolidation seal: each example reads one TCSlib definition
through its body (`rfl`), so it must pass unsealed and fail under the whole-file seal. They cover
the definitions that the promoted lemmas and published readers are about. -/

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games
open TCSlib.Cryptography.Composability

example (n : ℕ) : (PolyExpr.const 3).eval n = 3 := rfl
example (ℓ : ℕ) (w : List Bool) (i : Fin ℓ) : padFin ℓ w i = w.getD i false := rfl
example (d : ℕ) (j : Fin d) : zeroBits d j = false := rfl
example (q ℓ : ℕ) (x : Fin (q * ℓ) → Bool) (i : Fin q) (j : Fin ℓ) :
    FunFamily.blocks q ℓ x i j = x (finProdFinEquiv (i, j)) := rfl
example (k : ℕ) (a : List Bool) : EnsembleLemmas.padL k a = List.ofFn (padFin k a) := rfl
example (v y : Fin 2 → Bool) : xorPerm v y = fun i => xor (y i) (v i) := rfl
example (w : List Bool) : InteractiveHandler.rU w = pairFstD (pairFstD w) := rfl
example (S : FixedLengthPKScheme) (n : ℕ) :
    S.indCodec n = bitCodec (S.inLens n) (S.outLens n) 1 := rfl
example (S : FixedLengthScheme) (n : ℕ) :
    S.indCodec n = bitCodec (S.inLens n) (S.outLens n) 1 := rfl
example {m : ℕ} (y : Fin (m + m) → Bool) :
    (FixedLengthScheme.splitHalf y).1 = fun i => y (Fin.castAdd m i) := rfl
