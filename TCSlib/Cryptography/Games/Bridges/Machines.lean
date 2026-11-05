/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.Machines
import TCSlib.Cryptography.Games.Bridges.QueryTree
import TCSlib.Cryptography.Asymptotic.PRF

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The ch. 2–4 next-query machines as an instance of the machine decoder

The ch. 2–4 layer's `NUPPT.toOracleAdversary` turns a next-query machine (one oracle on bit
strings, a Boolean verdict) into a query tree. That tree is the generic decoder
`NUPPT.toComp` (`TCSlib.Cryptography.Games.Machines`) with the codec `singleCodec`, built from the
layer's own move decoding `decodeOracleMove` and history encoding `encodeHist`. So
`OracleEnsemble.Indist` (via `oracleDist`) is a statement about framework computations.

## Main definitions

* `Games.singleCodec ℓ₁ ℓ₂`: the codec of the ch. 2–4 next-query machines.

## Main results

* `Games.toComp_singleCodec`: `toOracleAdversary` is the one-oracle instance of `toComp`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §3.8.1 and Definition 96.1 (oracle machines).
-/

namespace TCSlib.Cryptography.Games

open Complexity Turing

/-! ### The ch. 2–4 next-query machines are an instance -/

/-- The codec of the ch. 2–4 next-query machines: one oracle on bit strings, a Boolean verdict,
moves decoded by `decodeOracleMove`, entries encoded as in `encodeHist`, and the verdict `false`
when the budget runs out. -/
def singleCodec (ℓ₁ ℓ₂ : ℕ) :
    MachineCodec (singleSpec (Fin ℓ₁ → Bool) (Fin ℓ₂ → Bool)) Bool where
  decodeMove w := match decodeOracleMove ℓ₁ w with
    | .query x => .query () x
    | .ret b => .ret b
  encodeEntry e := pairEncode (List.ofFn e.2.1) (List.ofFn e.2.2)
  timeout := false

/-- The ch. 2–4 history of a one-oracle log: the list of its (query, answer) pairs. -/
def toHist {ℓ₁ ℓ₂ : ℕ} (h : QueryLog (singleSpec (Fin ℓ₁ → Bool) (Fin ℓ₂ → Bool))) :
    List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool)) :=
  h.map fun e => (e.2.1, e.2.2)

/-- The codec's log encoding is the ch. 2–4 history encoding. -/
theorem encodeLog_singleCodec {ℓ₁ ℓ₂ : ℕ}
    (h : QueryLog (singleSpec (Fin ℓ₁ → Bool) (Fin ℓ₂ → Bool))) :
    (singleCodec ℓ₁ ℓ₂).encodeLog h = encodeHist (toHist h) := by
  induction h with
  | nil => rfl
  | cons e h ih =>
    simp only [MachineCodec.encodeLog, List.foldr_cons, toHist, List.map_cons, encodeHist] at ih ⊢
    rw [ih]
    rfl

/-- One step of the correspondence: the framework's computation from a log is the ch. 2–4 tree
from the corresponding history. -/
theorem buildComp_singleCodec {ℓ₁ ℓ₂ : ℕ}
    (next : List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool)) → OracleMove ℓ₁) :
    ∀ (q : ℕ) (hist : QueryLog (singleSpec (Fin ℓ₁ → Bool) (Fin ℓ₂ → Bool))),
      buildComp (fun h => match next (toHist h) with
          | .query x => .query () x
          | .ret b => .ret b) false q hist =
        buildTree next q (toHist hist)
  | 0, hist => by
    unfold buildComp buildTree
    cases next (toHist hist) <;> rfl
  | q + 1, hist => by
    unfold buildComp buildTree
    cases hn : next (toHist hist) with
    | ret b => rfl
    | query x =>
      dsimp only
      congr 1
      funext y
      rw [buildComp_singleCodec next q]
      simp [toHist]

/-- **The ch. 2–4 decoder is an instance:** the oracle adversary `D.toOracleAdversary` of a
next-query machine is its computation under `singleCodec`. So
`OracleEnsemble.Indist` (via `oracleDist`) is a statement about framework computations. -/
theorem toComp_singleCodec (D : NUPPT) (n ℓ₁ ℓ₂ q : ℕ) (r : D.Coins n) :
    D.toComp (singleCodec ℓ₁ ℓ₂) n q r =
      D.toOracleAdversary n ℓ₁ ℓ₂ q r := by
  have h := buildComp_singleCodec (ℓ₁ := ℓ₁) (ℓ₂ := ℓ₂)
    (fun hist => decodeOracleMove ℓ₁ (D.runAt n (encodeHist hist) r)) q []
  have hnext : (fun hist => (singleCodec ℓ₁ ℓ₂).decodeMove
      (D.runAt n ((singleCodec ℓ₁ ℓ₂).encodeLog hist) r)) =
      (fun h => match decodeOracleMove ℓ₁ (D.runAt n (encodeHist (toHist h)) r) with
        | .query x => Move.query () x
        | .ret b => Move.ret b) := by
    funext hist
    rw [encodeLog_singleCodec]
    rfl
  simp only [NUPPT.toComp, NUPPT.toOracleAdversary]
  rw [hnext]
  exact h

end TCSlib.Cryptography.Games
