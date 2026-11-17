/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyen
import TCSlib.Cryptography.Games.Hopping

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The BB1 simulator with its challenge coins drawn at the challenge

Helper module of `AdvancedEncryption/IdentityBased/BonehBoyenSecurity.lean` (steps 1 and 2 of
[BB04, proof of Theorem 4.1] at depth `ℓ = 1`). The simulator `bb1SimImpl` of
`AdvancedEncryption/IdentityBased/BonehBoyen.lean` receives the challenge coins `(Z, T)` before
the game starts, but uses them only at the first valid `Challenge` [BB04, proof of Theorem 4.1,
*Challenge*]. `bb1SimLazy` is the same simulator with coins `zt u` drawn at that call, for a
uniform `u` in any nonempty finite type `U`: step 1 draws `u = c ∈ Z_p` with
`zt c = (g^c, e(g, g)^{a b' c})`, step 2 draws `u = T ∈ G_T` with `zt T = (Z, T)`. The two
simulators simulate alike (`expect_simulate_bb1SimLazy`, an instance of
`Games.expect_simulate_eager`).

The module also reads the game's query and answer types from their published equations
(`sidSpec_dom_zero`, …), so that its consumers never reduce `IBEScheme.inLens` or
`IBEScheme.outLens`.

## Main definitions

* `BB1Sim.bb1SimLazyChal` — the simulator's `Challenge` with its coins drawn at the call.
* `BB1Sim.bb1SimLazy` — the simulator's oracles with that `Challenge`.

## Main results

* `BB1Sim.bb1SimLazy_zero`, `bb1SimLazy_one`, `bb1SimLazy_two_fresh`, `bb1SimLazy_two_of_not` —
  `bb1SimLazy` call by call, against `bb1SimImpl`.
* `BB1Sim.bb1SimImpl_two_of_not` — away from the first valid `Challenge`, `bb1SimImpl` does not
  read its coins.
* `BB1Sim.expect_simulate_bb1SimLazy` — the lazy simulator simulates like `bb1SimImpl` with coins
  drawn in advance.

## References

* [BB04] D. Boneh, X. Boyen, *Efficient Selective-ID Secure Identity Based Encryption Without
  Random Oracles*, full version, Cryptology ePrint Archive, Report 2004/172, December 2004
  (extended abstract: EUROCRYPT 2004, LNCS 3027, pp. 223–238). §4.2 (pp. 6–8): the algorithm
  `B` in the proof of Theorem 4.1.
-/

namespace TCSlib.Cryptography.AdvancedEncryption.IdentityBased

open Complexity Turing TCSlib.Cryptography.Games TCSlib.Cryptography.Pairing
  TCSlib.Cryptography.Composability

namespace BB1Sim

/-! ### The game's query and answer types, from published equations -/

section Types

variable (S : IBEScheme) (κ : ℕ)

/-- `Init` queries are identities: `(S.sidSpec κ).dom 0 = (Fin (S.idLen.eval κ) → Bool)`
(`sidSpec_eq`, `bitSpec_dom`, `inLens_zero`). Glue for the game's types. -/
theorem sidSpec_dom_zero : (S.sidSpec κ).dom 0 = (Fin (S.idLen.eval κ) → Bool) := by
  rw [IBEScheme.sidSpec_eq, bitSpec_dom, IBEScheme.inLens_zero]

/-- `KeyGen` queries are identities: `(S.sidSpec κ).dom 1 = (Fin (S.idLen.eval κ) → Bool)`
(`sidSpec_eq`, `bitSpec_dom`, `inLens_one`). Glue for the game's types. -/
theorem sidSpec_dom_one : (S.sidSpec κ).dom 1 = (Fin (S.idLen.eval κ) → Bool) := by
  rw [IBEScheme.sidSpec_eq, bitSpec_dom, IBEScheme.inLens_one]

/-- `Challenge` queries are two messages:
`(S.sidSpec κ).dom 2 = (Fin (S.msgLen.eval κ + S.msgLen.eval κ) → Bool)` (`sidSpec_eq`,
`bitSpec_dom`, `inLens_two`). Glue for the game's types. -/
theorem sidSpec_dom_two :
    (S.sidSpec κ).dom 2 = (Fin (S.msgLen.eval κ + S.msgLen.eval κ) → Bool) := by
  rw [IBEScheme.sidSpec_eq, bitSpec_dom, IBEScheme.inLens_two]

/-- `Init` answers parameters: `(S.sidSpec κ).rng 0 = (Fin (S.ppLen.eval κ) → Bool)`
(`sidSpec_eq`, `bitSpec_rng`, `outLens_zero`). Glue for the game's types. -/
theorem sidSpec_rng_zero : (S.sidSpec κ).rng 0 = (Fin (S.ppLen.eval κ) → Bool) := by
  rw [IBEScheme.sidSpec_eq, bitSpec_rng, IBEScheme.outLens_zero]

/-- `KeyGen` answers a bit and a key: `(S.sidSpec κ).rng 1 = (Fin (S.skLen.eval κ + 1) → Bool)`
(`sidSpec_eq`, `bitSpec_rng`, `outLens_one`). Glue for the game's types. -/
theorem sidSpec_rng_one : (S.sidSpec κ).rng 1 = (Fin (S.skLen.eval κ + 1) → Bool) := by
  rw [IBEScheme.sidSpec_eq, bitSpec_rng, IBEScheme.outLens_one]

/-- `Challenge` answers a ciphertext: `(S.sidSpec κ).rng 2 = (Fin (S.ctLen.eval κ) → Bool)`
(`sidSpec_eq`, `bitSpec_rng`, `outLens_two`). Glue for the game's types. -/
theorem sidSpec_rng_two : (S.sidSpec κ).rng 2 = (Fin (S.ctLen.eval κ) → Bool) := by
  rw [IBEScheme.sidSpec_eq, bitSpec_rng, IBEScheme.outLens_two]

/-- The `⊥` word of a width equal to `m`, cast: `zeroBits n = cast e (zeroBits m)` for `n = m`.
Glue for the game's types. -/
theorem zeroBits_eq_cast {n m : ℕ} (hnm : n = m) (e : (Fin m → Bool) = (Fin n → Bool)) :
    zeroBits n = cast e (zeroBits m) := by
  subst hnm
  rfl

end Types

/-! ### The lazy simulator -/

section Lazy

variable (G : BilinearGen) (ℓ : PolyExpr)

open Classical in
/-- **The simulator's `Challenge` with its coins drawn at the call** [BB04, proof of Theorem 4.1,
*Challenge*]: with `ID*` recorded, no challenge yet, and both messages `M₀, M₁` encodings of
`G_T`, draw `u ∈ U` and answer as `bb1SimChal` on the coins `zt u = (Z, T)`; otherwise answer
as `bb1SimChal` on the coins `(1, 1)`, which it does not read there. -/
noncomputable def bb1SimLazyChal (b : Bool) (κ : ℕ) (d : List Bool) (g X Y : (G.group κ d).G)
    {U : Type} [Fintype U] [Nonempty U] (zt : U → (G.group κ d).G × (G.group κ d).GT)
    (mm : Fin ((bb1Scheme G ℓ).msgLen.eval κ + (bb1Scheme G ℓ).msgLen.eval κ) → Bool)
    (s : BB1SimState G ℓ κ d) :
    ProbComp ((Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool) × BB1SimState G ℓ κ d) :=
  if s.1.isSome ∧ s.2 = none ∧
      ((∃ u, List.ofFn ((G.group κ d).encT u) = List.ofFn (FixedLengthScheme.splitHalf mm).1) ∧
        ∃ u, List.ofFn ((G.group κ d).encT u) = List.ofFn (FixedLengthScheme.splitHalf mm).2)
  then (ProbComp.sample U).bind fun u => bb1SimChal G ℓ b κ d g X Y (zt u).1 (zt u).2 mm s
  else bb1SimChal G ℓ b κ d g X Y 1 1 mm s

/-- At the first valid `Challenge`, `bb1SimLazyChal` draws `u` and answers as `bb1SimChal` on
`zt u`: for `s.1` some, `s.2 = none` and both messages encodings of `G_T`,
`bb1SimLazyChal … zt mm s = (sample U).bind fun u => bb1SimChal … (zt u).1 (zt u).2 mm s`. -/
theorem bb1SimLazyChal_fresh (b : Bool) (κ : ℕ) (d : List Bool) (g X Y : (G.group κ d).G)
    {U : Type} [Fintype U] [Nonempty U] (zt : U → (G.group κ d).G × (G.group κ d).GT)
    (mm : Fin ((bb1Scheme G ℓ).msgLen.eval κ + (bb1Scheme G ℓ).msgLen.eval κ) → Bool)
    (s : BB1SimState G ℓ κ d)
    (h : s.1.isSome ∧ s.2 = none ∧
      ((∃ u, List.ofFn ((G.group κ d).encT u) = List.ofFn (FixedLengthScheme.splitHalf mm).1) ∧
        ∃ u, List.ofFn ((G.group κ d).encT u) = List.ofFn (FixedLengthScheme.splitHalf mm).2)) :
    bb1SimLazyChal G ℓ b κ d g X Y zt mm s =
      (ProbComp.sample U).bind fun u => bb1SimChal G ℓ b κ d g X Y (zt u).1 (zt u).2 mm s := by
  rw [bb1SimLazyChal, if_pos h]

/-- Away from the first valid `Challenge`, `bb1SimLazyChal` answers as `bb1SimChal` on the
coins `(1, 1)`: `bb1SimLazyChal … zt mm s = bb1SimChal … 1 1 mm s`. -/
theorem bb1SimLazyChal_of_not (b : Bool) (κ : ℕ) (d : List Bool) (g X Y : (G.group κ d).G)
    {U : Type} [Fintype U] [Nonempty U] (zt : U → (G.group κ d).G × (G.group κ d).GT)
    (mm : Fin ((bb1Scheme G ℓ).msgLen.eval κ + (bb1Scheme G ℓ).msgLen.eval κ) → Bool)
    (s : BB1SimState G ℓ κ d)
    (h : ¬ (s.1.isSome ∧ s.2 = none ∧
      ((∃ u, List.ofFn ((G.group κ d).encT u) = List.ofFn (FixedLengthScheme.splitHalf mm).1) ∧
        ∃ u, List.ofFn ((G.group κ d).encT u) = List.ofFn (FixedLengthScheme.splitHalf mm).2))) :
    bb1SimLazyChal G ℓ b κ d g X Y zt mm s = bb1SimChal G ℓ b κ d g X Y 1 1 mm s := by
  rw [bb1SimLazyChal, if_neg h]

/-- **The simulator with its challenge coins drawn at the challenge** [BB04, proof of
Theorem 4.1]: the oracles `oracleImpl` of the simulator's `Init` (`bb1SimInit`) and `KeyGen`
(`bb1SimKeyQ`) and of `bb1SimLazyChal`, with challenge bit `b` on `g, X, Y` and the coin map
`zt : U → G × G_T`. -/
noncomputable def bb1SimLazy (b : Bool) (κ : ℕ) (d : List Bool) (g X Y : (G.group κ d).G)
    {U : Type} [Fintype U] [Nonempty U] (zt : U → (G.group κ d).G × (G.group κ d).GT) :
    QueryImpl ((bb1Scheme G ℓ).sidSpec κ) (BB1SimState G ℓ κ d) unifSpec :=
  (bb1Scheme G ℓ).oracleImpl κ (bb1SimInit G ℓ κ d g X Y) (bb1SimKeyQ G ℓ κ d g X Y)
    (bb1SimLazyChal G ℓ b κ d g X Y zt)

/-- `bb1SimLazy` is `oracleImpl` of `bb1SimInit`, `bb1SimKeyQ` and `bb1SimLazyChal`. -/
theorem bb1SimLazy_eq (b : Bool) (κ : ℕ) (d : List Bool) (g X Y : (G.group κ d).G)
    {U : Type} [Fintype U] [Nonempty U] (zt : U → (G.group κ d).G × (G.group κ d).GT) :
    bb1SimLazy G ℓ b κ d g X Y zt =
      (bb1Scheme G ℓ).oracleImpl κ (bb1SimInit G ℓ κ d g X Y) (bb1SimKeyQ G ℓ κ d g X Y)
        (bb1SimLazyChal G ℓ b κ d g X Y zt) := rfl

variable (b : Bool) (κ : ℕ) (d : List Bool) (g X Y : (G.group κ d).G) {U : Type} [Fintype U]
  [Nonempty U] (zt : U → (G.group κ d).G × (G.group κ d).GT)

/-- `Init` of `bb1SimImpl` does not read the challenge coins:
`bb1SimImpl … Z T 0 x s = bb1SimImpl … Z' T' 0 x s`. -/
theorem bb1SimImpl_zero_coins (Z Z' : (G.group κ d).G) (T T' : (G.group κ d).GT)
    (x : ((bb1Scheme G ℓ).sidSpec κ).dom 0) (s : BB1SimState G ℓ κ d) :
    bb1SimImpl G ℓ b κ d g X Y Z T 0 x s = bb1SimImpl G ℓ b κ d g X Y Z' T' 0 x s := by
  rw [bb1SimImpl_eq, bb1SimImpl_eq, IBEScheme.oracleImpl_zero_onSpec,
    IBEScheme.oracleImpl_zero_onSpec]

/-- `KeyGen` of `bb1SimImpl` does not read the challenge coins:
`bb1SimImpl … Z T 1 x s = bb1SimImpl … Z' T' 1 x s`. -/
theorem bb1SimImpl_one_coins (Z Z' : (G.group κ d).G) (T T' : (G.group κ d).GT)
    (x : ((bb1Scheme G ℓ).sidSpec κ).dom 1) (s : BB1SimState G ℓ κ d) :
    bb1SimImpl G ℓ b κ d g X Y Z T 1 x s = bb1SimImpl G ℓ b κ d g X Y Z' T' 1 x s := by
  rw [bb1SimImpl_eq, bb1SimImpl_eq, IBEScheme.oracleImpl_one_onSpec,
    IBEScheme.oracleImpl_one_onSpec]

/-- `Init` of the lazy simulator is `Init` of `bb1SimImpl`:
`bb1SimLazy … zt 0 x s = bb1SimImpl … 1 1 0 x s`. -/
theorem bb1SimLazy_zero (x : ((bb1Scheme G ℓ).sidSpec κ).dom 0) (s : BB1SimState G ℓ κ d) :
    bb1SimLazy G ℓ b κ d g X Y zt 0 x s = bb1SimImpl G ℓ b κ d g X Y 1 1 0 x s := by
  rw [bb1SimLazy_eq, bb1SimImpl_eq, IBEScheme.oracleImpl_zero_onSpec,
    IBEScheme.oracleImpl_zero_onSpec]

/-- `KeyGen` of the lazy simulator is `KeyGen` of `bb1SimImpl`:
`bb1SimLazy … zt 1 x s = bb1SimImpl … 1 1 1 x s`. -/
theorem bb1SimLazy_one (x : ((bb1Scheme G ℓ).sidSpec κ).dom 1) (s : BB1SimState G ℓ κ d) :
    bb1SimLazy G ℓ b κ d g X Y zt 1 x s = bb1SimImpl G ℓ b κ d g X Y 1 1 1 x s := by
  rw [bb1SimLazy_eq, bb1SimImpl_eq, IBEScheme.oracleImpl_one_onSpec,
    IBEScheme.oracleImpl_one_onSpec]

/-- **The first valid `Challenge` of the lazy simulator** draws `u` and calls `bb1SimImpl` on the
coins `zt u`: for `s.1` some, `s.2 = none`, and both messages of the query `x` (read as two
messages) encodings of `G_T`,
`bb1SimLazy … zt 2 x s = (sample U).bind fun u => bb1SimImpl … (zt u).1 (zt u).2 2 x s`. -/
theorem bb1SimLazy_two_fresh (x : ((bb1Scheme G ℓ).sidSpec κ).dom 2) (s : BB1SimState G ℓ κ d)
    (h : s.1.isSome ∧ s.2 = none ∧
      ((∃ u, List.ofFn ((G.group κ d).encT u) =
          List.ofFn (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two _ κ) x)).1) ∧
        ∃ u, List.ofFn ((G.group κ d).encT u) =
          List.ofFn (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two _ κ) x)).2)) :
    bb1SimLazy G ℓ b κ d g X Y zt 2 x s =
      (ProbComp.sample U).bind fun u =>
        bb1SimImpl G ℓ b κ d g X Y (zt u).1 (zt u).2 2 x s := by
  rw [bb1SimLazy_eq, IBEScheme.oracleImpl_two_onSpec, bb1SimLazyChal_fresh _ _ _ _ _ _ _ _ _ _ _
    h, OracleComp.bind_assoc]
  refine congrArg _ (funext fun u => ?_)
  rw [bb1SimImpl_eq, IBEScheme.oracleImpl_two_onSpec]

/-- **`Challenge` of the lazy simulator away from the first valid one** is `Challenge` of
`bb1SimImpl` on the coins `(1, 1)`: `bb1SimLazy … zt 2 x s = bb1SimImpl … 1 1 2 x s`. -/
theorem bb1SimLazy_two_of_not (x : ((bb1Scheme G ℓ).sidSpec κ).dom 2) (s : BB1SimState G ℓ κ d)
    (h : ¬ (s.1.isSome ∧ s.2 = none ∧
      ((∃ u, List.ofFn ((G.group κ d).encT u) =
          List.ofFn (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two _ κ) x)).1) ∧
        ∃ u, List.ofFn ((G.group κ d).encT u) =
          List.ofFn (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two _ κ) x)).2))) :
    bb1SimLazy G ℓ b κ d g X Y zt 2 x s = bb1SimImpl G ℓ b κ d g X Y 1 1 2 x s := by
  rw [bb1SimLazy_eq, bb1SimImpl_eq, IBEScheme.oracleImpl_two_onSpec,
    IBEScheme.oracleImpl_two_onSpec, bb1SimLazyChal_of_not _ _ _ _ _ _ _ _ _ _ _ h]

/-- **Away from the first valid `Challenge`, `bb1SimImpl` does not read its coins**, and keeps the
recorded challenge: unless `s.1` is some, `s.2 = none` and both messages are encodings of `G_T`,
`bb1SimImpl … Z T 2 x s = bb1SimImpl … 1 1 2 x s`, and every outcome has the challenge `s.2`.

**Proof sketch.** Read both calls by `oracleImpl_two_onSpec`. Before `Init` both answer `⊥`
(`bb1SimChal_none`); after a recorded challenge both repeat it (`bb1SimChal_repeat`); at a first
`Challenge` with a message outside the message space both answer `⊥` (`bb1SimChal_invalid`,
`bb1Scheme_msgSpace_iff`). -/
theorem bb1SimImpl_two_of_not (Z : (G.group κ d).G) (T : (G.group κ d).GT)
    (x : ((bb1Scheme G ℓ).sidSpec κ).dom 2) (s : BB1SimState G ℓ κ d)
    (h : ¬ (s.1.isSome ∧ s.2 = none ∧
      ((∃ u, List.ofFn ((G.group κ d).encT u) =
          List.ofFn (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two _ κ) x)).1) ∧
        ∃ u, List.ofFn ((G.group κ d).encT u) =
          List.ofFn (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two _ κ) x)).2))) :
    bb1SimImpl G ℓ b κ d g X Y Z T 2 x s = bb1SimImpl G ℓ b κ d g X Y 1 1 2 x s ∧
      (bb1SimImpl G ℓ b κ d g X Y Z T 2 x s).AllOutputs fun p => p.2.2 = s.2 := by
  sorry

/-- **The first valid `Challenge` records a challenge**: for `s.1` some and `s.2 = none`, and
both messages encodings of `G_T`, every outcome of `bb1SimImpl … Z T 2 x s` has a recorded
challenge. -/
theorem bb1SimImpl_two_fresh_allOutputs (Z : (G.group κ d).G) (T : (G.group κ d).GT)
    (x : ((bb1Scheme G ℓ).sidSpec κ).dom 2) (s : BB1SimState G ℓ κ d)
    (h : s.1.isSome ∧ s.2 = none ∧
      ((∃ u, List.ofFn ((G.group κ d).encT u) =
          List.ofFn (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two _ κ) x)).1) ∧
        ∃ u, List.ofFn ((G.group κ d).encT u) =
          List.ofFn (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two _ κ) x)).2)) :
    (bb1SimImpl G ℓ b κ d g X Y Z T 2 x s).AllOutputs fun p => p.2.2.isSome := by
  sorry

/-- **`Init` and `KeyGen` keep the recorded challenge**: for `i ≠ 2`, every outcome of
`bb1SimImpl … Z T i x s` has the challenge `s.2`. -/
theorem bb1SimImpl_allOutputs_of_ne_two (Z : (G.group κ d).G) (T : (G.group κ d).GT)
    (i : Fin 3) (hi : i ≠ 2) (x : ((bb1Scheme G ℓ).sidSpec κ).dom i) (s : BB1SimState G ℓ κ d) :
    (bb1SimImpl G ℓ b κ d g X Y Z T i x s).AllOutputs fun p => p.2.2 = s.2 := by
  sorry

/-- **The lazy simulator simulates like `bb1SimImpl` with its coins drawn in advance**: from a
state with no recorded challenge (`s.2 = none`), for every computation `c` and every `F`,
`𝔼[F] (simulate (bb1SimLazy … zt) c s) =
𝔼_{u ← U} 𝔼[F] (simulate (bb1SimImpl … (zt u).1 (zt u).2) c s)`. Glue: an instance of
`Games.expect_simulate_eager`, with the coins spent at the first valid `Challenge`.

**Proof sketch.** Apply `Games.expect_simulate_eager` with `O := bb1SimLazy … zt`,
`OE u := bb1SimImpl … (zt u)` and `used v := v.2` some. `Init` and `KeyGen` do not read the
coins (`bb1SimLazy_zero`, `bb1SimLazy_one`, `bb1SimImpl_zero_coins`, `bb1SimImpl_one_coins`)
and keep the recorded challenge (`bb1SimImpl_allOutputs_of_ne_two`). A `Challenge` other than
the first valid one does not read them either and keeps the recorded challenge
(`bb1SimLazy_two_of_not`, `bb1SimImpl_two_of_not`); the first valid one draws them
(`bb1SimLazy_two_fresh`) and records a challenge (`bb1SimImpl_two_fresh_allOutputs`). -/
theorem expect_simulate_bb1SimLazy {α : Type} (c : OracleComp ((bb1Scheme G ℓ).sidSpec κ) α)
    (F : α × BB1SimState G ℓ κ d → ℝ) {s : BB1SimState G ℓ κ d} (hs : s.2 = none) :
    ProbComp.expect (simulate (bb1SimLazy G ℓ b κ d g X Y zt) c s) F =
      ProbComp.expect (ProbComp.sample U) fun u =>
        ProbComp.expect (simulate (bb1SimImpl G ℓ b κ d g X Y (zt u).1 (zt u).2) c s) F := by
  sorry

end Lazy

end BB1Sim

end TCSlib.Cryptography.AdvancedEncryption.IdentityBased
