/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyenSecurity.Lazy
import TCSlib.Cryptography.Games.Relational

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The BB1 simulator on a random `T` does not depend on the challenge bit

Helper module of `AdvancedEncryption/IdentityBased/BonehBoyenSecurity.lean` (step 2 of
[BB04, proof of Theorem 4.1] at depth `ℓ = 1`): "when `T` is uniform and independent in `G_1`
… `C` is independent of `b` in the adversary's view" [BB04, proof of Theorem 4.1, *Challenge*].
`T` is used only at the first valid `Challenge`, so it can be drawn there
(`expect_simulate_bb1SimLazy`, step E-T); at that call, `T ↦ M_1^{−1} M_0 T` turns the answer
`M_0 · T` of the simulator with challenge bit `0` into the answer `M_1 · T'` of the one with
challenge bit `1`, and every other call is the same for both bits.

## Main definitions

None.

## Main results

* `BB1Sim.bb1SimLazy_random_call` — the lazy simulators with challenge bits `0` and `1` and
  `T` drawn at the challenge give equal expectations, call by call.
* `BB1Sim.expect_bb1SimImpl_random` — on a uniform `T`, the simulators with challenge bits `0`
  and `1` simulate alike.

## References

* [BB04] D. Boneh, X. Boyen, *Efficient Selective-ID Secure Identity Based Encryption Without
  Random Oracles*, full version, Cryptology ePrint Archive, Report 2004/172, December 2004
  (extended abstract: EUROCRYPT 2004, LNCS 3027, pp. 223–238). §4.2 (pp. 6–8): the proof of
  Theorem 4.1.
-/

namespace TCSlib.Cryptography.AdvancedEncryption.IdentityBased

open Complexity Turing TCSlib.Cryptography.Games TCSlib.Cryptography.Pairing
  TCSlib.Cryptography.Composability

namespace BB1Sim

variable (G : BilinearGen) (ℓ : PolyExpr) (κ : ℕ) (d : List Bool) (g X Y Z : (G.group κ d).G)

/-- **The challenge bit is hidden by a random `T`, call by call** [BB04, proof of Theorem 4.1,
*Challenge*]: with `T` drawn at the first valid `Challenge` (`zt T = (Z, T)`), every call of the
lazy simulators with challenge bits `0` and `1` gives the same expectation to every `F`:
`𝔼[F] (bb1SimLazy false … i x s) = 𝔼[F] (bb1SimLazy true … i x s)`.

**Proof sketch.** `Init` and `KeyGen` do not depend on the bit (`bb1SimLazy_zero`,
`bb1SimLazy_one`, `bb1SimImpl_eq`, `IBEScheme.oracleImpl_zero_onSpec`,
`IBEScheme.oracleImpl_one_onSpec`). A `Challenge` other than the first valid one answers `⊥` or
repeats the recorded challenge (`bb1SimLazy_two_of_not`, `bb1SimChal_none`, `bb1SimChal_repeat`,
`bb1SimChal_invalid`). At the first valid one, `ProbComp.expect_sample_rel` with `R := Eq` along
`T ↦ decodeT(M_1)^{−1} decodeT(M_0) T` (`bb1SimLazy_two_fresh`, `bb1SimChal_fresh`,
`ofFn_bb1SimCt`). -/
theorem bb1SimLazy_random_call (i : Fin 3) (x : ((bb1Scheme G ℓ).sidSpec κ).dom i)
    (s : BB1SimState G ℓ κ d) (F : ((bb1Scheme G ℓ).sidSpec κ).rng i × BB1SimState G ℓ κ d → ℝ) :
    ProbComp.expect (bb1SimLazy G ℓ false κ d g X Y (fun T : (G.group κ d).GT => (Z, T)) i x s) F =
      ProbComp.expect
        (bb1SimLazy G ℓ true κ d g X Y (fun T : (G.group κ d).GT => (Z, T)) i x s) F := by
  have h012 : ∀ i : Fin 3, i = 0 ∨ i = 1 ∨ i = 2 := by decide
  rcases h012 i with rfl | rfl | rfl
  -- `Init` and `KeyGen` do not depend on the bit
  · rw [bb1SimLazy_zero, bb1SimLazy_zero, bb1SimImpl_eq, bb1SimImpl_eq,
      IBEScheme.oracleImpl_zero_onSpec, IBEScheme.oracleImpl_zero_onSpec]
  · rw [bb1SimLazy_one, bb1SimLazy_one, bb1SimImpl_eq, bb1SimImpl_eq,
      IBEScheme.oracleImpl_one_onSpec, IBEScheme.oracleImpl_one_onSpec]
  by_cases hf : (s.1.isSome ∧ s.2 = none ∧
        ((∃ u, List.ofFn ((G.group κ d).encT u) =
            List.ofFn (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two _ κ) x)).1) ∧
          ∃ u, List.ofFn ((G.group κ d).encT u) =
            List.ofFn (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two _ κ) x)).2))
  -- the first valid `Challenge`: reindex `T` by `T ↦ M₁⁻¹ M₀ T`
  · rw [bb1SimLazy_two_fresh G ℓ false κ d g X Y _ x s hf,
      bb1SimLazy_two_fresh G ℓ true κ d g X Y _ x s hf]
    obtain ⟨s₁, s₂⟩ := s
    obtain ⟨h₁, h₂, hv⟩ := hf
    rcases s₁ with _ | ⟨t, α₁⟩
    · exact absurd h₁ Bool.false_ne_true
    subst h₂
    set m := (FixedLengthScheme.splitHalf (cast (sidSpec_dom_two _ κ) x)) with hm
    have key : ∀ (b : Bool) (T : (G.group κ d).GT),
        bb1SimImpl G ℓ b κ d g X Y Z T 2 x (some (t, α₁), none) =
          .pure (cast (sidSpec_rng_two _ κ).symm
              (bb1SimCt G ℓ κ d Z T α₁ (if b then m.2 else m.1)),
            (some (t, α₁), some (bb1SimCt G ℓ κ d Z T α₁ (if b then m.2 else m.1)))) :=
      fun b T => by
        rw [bb1SimImpl_eq, IBEScheme.oracleImpl_two_onSpec, bb1SimChal_fresh G ℓ b κ d g X Y Z T _
          t α₁ ⟨(bb1Scheme_msgSpace_iff G ℓ κ d _ _).2 hv.1,
            (bb1Scheme_msgSpace_iff G ℓ κ d _ _).2 hv.2⟩, OracleComp.pure_bind]
    simp only [key]
    have hct : ∀ T, bb1SimCt G ℓ κ d Z T α₁ m.1 =
        bb1SimCt G ℓ κ d Z (Equiv.mulLeft ((BB1.decodeT (G.group κ d)
          (padFin _ (List.ofFn m.2)))⁻¹ * BB1.decodeT (G.group κ d)
            (padFin _ (List.ofFn m.1))) T) α₁ m.2 := fun T => by
      simp only [Equiv.coe_mulLeft]
      rw [List.ofFn_injective (ofFn_bb1SimCt G ℓ κ d _ _ _ _),
        List.ofFn_injective (ofFn_bb1SimCt G ℓ κ d _ _ _ _), mul_assoc, mul_inv_cancel_left]
    refine ProbComp.expect_sample_rel Eq (Equiv.mulLeft ((BB1.decodeT (G.group κ d)
      (padFin _ (List.ofFn m.2)))⁻¹ * BB1.decodeT (G.group κ d) (padFin _ (List.ofFn m.1)))) _ _
      (fun T => ⟨?_, ?_⟩) F F (fun y s' t' h => by rw [h]) <;>
    simp only [Bool.false_eq_true, ↓reduceIte, hct]
  -- every other `Challenge` does not depend on the bit
  · rw [bb1SimLazy_two_of_not G ℓ false κ d g X Y _ x s hf,
      bb1SimLazy_two_of_not G ℓ true κ d g X Y _ x s hf,
      (bb1SimImpl_two_of_not G ℓ true κ d g X Y 1 1 x s hf).1]

/-- **On a random `T`, the simulator does not depend on the challenge bit** [BB04, proof of
Theorem 4.1, *Challenge*, "when `T` is uniform and independent in `G_1` … `C` is independent of
`b` in the adversary's view"]: for every computation `c` and every `F` of its output,
`𝔼_{T ← G_T} 𝔼[F ∘ fst] (simulate (bb1SimImpl false … Z T) c (none, none)) =
𝔼_{T ← G_T} 𝔼[F ∘ fst] (simulate (bb1SimImpl true … Z T) c (none, none))`.

**Proof sketch.** Draw `T` at the first valid `Challenge` on both sides
(`expect_simulate_bb1SimLazy`, step E-T), then compare the lazy simulators call by call
(`ProbComp.expect_simulate_congr` with `bb1SimLazy_random_call`). -/
theorem expect_bb1SimImpl_random {β : Type} (c : OracleComp ((bb1Scheme G ℓ).sidSpec κ) β)
    (F : β → ℝ) :
    ProbComp.expect (ProbComp.sample (G.group κ d).GT) (fun T => ProbComp.expect
        (simulate (bb1SimImpl G ℓ false κ d g X Y Z T) c (none, none)) (fun p => F p.1)) =
      ProbComp.expect (ProbComp.sample (G.group κ d).GT) (fun T => ProbComp.expect
        (simulate (bb1SimImpl G ℓ true κ d g X Y Z T) c (none, none)) (fun p => F p.1)) := by
  rw [← expect_simulate_bb1SimLazy G ℓ false κ d g X Y (fun T : (G.group κ d).GT => (Z, T)) c _
    rfl, ← expect_simulate_bb1SimLazy G ℓ true κ d g X Y (fun T : (G.group κ d).GT => (Z, T)) c _
    rfl]
  exact ProbComp.expect_simulate_congr _ _
    (fun i x s F => bb1SimLazy_random_call G ℓ κ d g X Y Z i x s F) c _ _

end BB1Sim

end TCSlib.Cryptography.AdvancedEncryption.IdentityBased
