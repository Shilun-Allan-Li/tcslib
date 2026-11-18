/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Obfuscation.StructuredSeed.Correctness
import TCSlib.Cryptography.Obfuscation.StructuredSeed.Claim42
import TCSlib.Cryptography.Games.Hopping

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The JLS security hybrid distributions

## Main definitions

* `HybridStage`: the four main security distributions.
* `Params.hyb`, `Params.chainGame`: exact main and LPN-chain games.
* `Params.publicSeed`: public-vector and error-flag packing.

## Main results

* The endpoint readers identify the raw games and initial chains.
* Statistical hops are bounded by the exact error probability.

## References

* [JLS26] A. Jain, H. Lin, A. Sahai, *Indistinguishability Obfuscation from
  Well-Founded Assumptions*, J. ACM 73(1), Article 1, February 2026, §§2-4.
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes,
  3rd ed., January 2010, Definition 26.8 (non-uniform PPT adversaries).
-/

namespace TCSlib.Cryptography.Obfuscation.StructuredSeed

open Complexity Turing
open TCSlib.Cryptography.Games

/-- The four distributions are real output, PRG output with zero error flag,
uniform output with zero error flag, and the random comparison game
[JLS26, Proposition 4.1, pp. 18-19]. Dv8 also publishes the independent bucket map. -/
inductive HybridStage where
  | real
  | prg
  | uniform
  | random

namespace Params

/-- A public seed packs κ vectors and one Boolean error flag
[JLS26, Proposition 4.1, pp. 18-19]. Dv15 uses the fixed public-coordinate equivalence. -/
noncomputable def publicSeed (P : Params) (κ : ℕ) (pp : PrimeParam κ)
    (bs : Fin κ → Fin (P.n κ) → ZMod pp.p) (err : Bool) :
    Fin (P.pubLen κ) → ZMod pp.p :=
  fun i => match (P.pubEquiv κ).symm i with
    | .inl (k, q) => bs k q
    | .inr _ => (err.toNat : ZMod pp.p)

/-- Public seed packing follows the explicit vector/flag coordinate split; glue. -/
theorem publicSeed_eq (P : Params) (κ : ℕ) (pp : PrimeParam κ)
    (bs : Fin κ → Fin (P.n κ) → ZMod pp.p) (err : Bool) :
    P.publicSeed κ pp bs err = fun i => match (P.pubEquiv κ).symm i with
      | .inl (k, q) => bs k q
      | .inr _ => (err.toNat : ZMod pp.p) := rfl

/-- The ith chain public component replaces exactly the first i LPN vectors by uniforms
[JLS26, Lemma 4.2, p. 19]. Dv8 retains the bucket map; no core computes a Boolean tail. -/
noncomputable def chainPublic (P : Params) (κ : ℕ) (pp : PrimeParam κ)
    (I : P.Idx' κ pp) (d : P.Draw κ pp)
    (u : Fin κ → Fin (P.n κ) → ZMod pp.p) (i : ℕ) :
    Fin κ → Fin (P.n κ) → ZMod pp.p :=
  fun k => if k.val < i then u k else
    P.lpnVector κ pp I.2.2 d.1 (d.2 k).1 (d.2 k).2

/-- Chain public vectors follow the first-i replacement rule; glue. -/
theorem chainPublic_eq (P : Params) (κ : ℕ) (pp : PrimeParam κ)
    (I : P.Idx' κ pp) (d : P.Draw κ pp)
    (u : Fin κ → Fin (P.n κ) → ZMod pp.p) (i : ℕ) :
    P.chainPublic κ pp I d u i = fun k => if k.val < i then u k else
      P.lpnVector κ pp I.2.2 d.1 (d.2 k).1 (d.2 k).2 := rfl

/-- A chain game chooses either the PRG tail or a uniform Boolean tail, and publishes
zero as its error flag [JLS26, Lemma 4.2, p. 19]. Dv8 retains independent buckets;
Dv12 prepares the two advice-based hybrid chains used by the reductions. -/
noncomputable def chainGame (P : Params) (A : NUPPT) (tailReal : Bool) (i κ : ℕ)
    (pp : PrimeParam κ) : ProbComp Bool :=
  (P.idSamp' κ pp).bind fun I =>
  (ProbComp.sample (P.Draw κ pp)).bind fun d =>
  (ProbComp.sample (Fin κ → Fin (P.n κ) → ZMod pp.p)).bind fun u =>
  (ProbComp.sample (Fin (P.m κ) → Bool)).bind fun w =>
  (ProbComp.sample (A.Coins κ)).bind fun r =>
    pure (A.distinguisherL κ
      (P.challengeStr κ pp I (P.publicSeed κ pp (P.chainPublic κ pp I d u i) false)
        (if tailReal then fun j => P.G.eval (P.n κ) I.1 d.1 (P.outputIndex κ j) else w)) r)

/-- The chain game is its explicit sequence of exact finite laws; glue. -/
theorem chainGame_eq (P : Params) (A : NUPPT) (tailReal : Bool) (i κ : ℕ)
    (pp : PrimeParam κ) : P.chainGame A tailReal i κ pp =
      (P.idSamp' κ pp).bind fun I =>
      (ProbComp.sample (P.Draw κ pp)).bind fun d =>
      (ProbComp.sample (Fin κ → Fin (P.n κ) → ZMod pp.p)).bind fun u =>
      (ProbComp.sample (Fin (P.m κ) → Bool)).bind fun w =>
      (ProbComp.sample (A.Coins κ)).bind fun r =>
        pure (A.distinguisherL κ
          (P.challengeStr κ pp I (P.publicSeed κ pp (P.chainPublic κ pp I d u i) false)
            (if tailReal then fun j => P.G.eval (P.n κ) I.1 d.1
              (P.outputIndex κ j) else w)) r) := rfl

/-- The packed core publishes its instance vectors and its actual error bit; glue. [JLS26,
SdSamp′, pp. 15-16]. This theorem compares the deterministic vector maps.

**Proof sketch.** Read the core fields, public packing equation, and publicSeed coordinate
equation. Both sides then have the same explicit sum-coordinate match. -/
theorem sdCore_publicSeed (P : Params) (κ : ℕ) (pp : PrimeParam κ)
    (I : P.Idx' κ pp) (d : P.Draw κ pp) :
    (P.sdCore κ pp I d).seed.1 =
      P.publicSeed κ pp (fun k => ((P.sdCore κ pp I d).instances k).pub)
        (P.sdCore κ pp I d).err := by
  rw [P.sdCore_seed, P.publicSeed_eq, P.sdCore_instances, P.sdCore_err,
    P.packSeed_fst]
  rfl

/-- H0-H3 sample the actual index and seed law and alter only error flag and output
[JLS26, Proposition 4.1, pp. 18-19]. Dv8 includes the bucket map in all challenges. -/
noncomputable def hyb (P : Params) (A : NUPPT) (stage : HybridStage) (κ : ℕ)
    (pp : PrimeParam κ) : ProbComp Bool :=
  (P.idSamp' κ pp).bind fun I => (P.sdSampFull κ pp I).bind fun x =>
  (ProbComp.sample (Fin (P.m κ) → Bool)).bind fun w =>
  (ProbComp.sample (A.Coins κ)).bind fun r =>
    let clean := P.publicSeed κ pp (fun k => (x.instances k).pub) false
    let out := match stage with
      | .real => (x.seed.1, P.eval' κ pp I x.seed)
      | .prg => (clean, fun j => P.G.eval (P.n κ) I.1 x.σ (P.outputIndex κ j))
      | .uniform => (clean, w)
      | .random => (x.seed.1, w)
    pure (A.distinguisherL κ (P.challengeStr κ pp I out.1 out.2) r)

/-- The four hybrids have their displayed error-flag/output substitutions; glue. -/
theorem hyb_eq (P : Params) (A : NUPPT) (stage : HybridStage) (κ : ℕ)
    (pp : PrimeParam κ) : P.hyb A stage κ pp =
      (P.idSamp' κ pp).bind fun I => (P.sdSampFull κ pp I).bind fun x =>
      (ProbComp.sample (Fin (P.m κ) → Bool)).bind fun w =>
      (ProbComp.sample (A.Coins κ)).bind fun r =>
        let clean := P.publicSeed κ pp (fun k => (x.instances k).pub) false
        let out := match stage with
          | .real => (x.seed.1, P.eval' κ pp I x.seed)
          | .prg => (clean, fun j => P.G.eval (P.n κ) I.1 x.σ (P.outputIndex κ j))
          | .uniform => (clean, w)
          | .random => (x.seed.1, w)
        pure (A.distinguisherL κ (P.challengeStr κ pp I out.1 out.2) r) := rfl

/-- H0 equals the real raw sPRG game [JLS26, Proposition 4.1, pp. 18-19]. Dv18 uses Raw.

**Proof sketch.** Read the raw game, construction fields and exact sampler projection laws. -/
theorem hyb_real_eq_raw (P : Params) (π : PrimeSchedule) (A : NUPPT) (κ : ℕ) :
    P.hyb A .real κ (π κ) = (jlsSPRG_raw P π).game A true κ := by
  simp only [hyb_eq, SPRG.Raw.game_eq, jlsSPRG_raw_eq,
    SPRG.Raw.idSamp_eq, SPRG.Raw.sdSamp_eq, SPRG.Raw.instIdDrawFintype_eq,
    SPRG.Raw.instSdDrawFintype_eq, Params.idSamp'_eq, Params.sdSampFull_eq,
    OracleComp.map_eq_bind, OracleComp.bind_assoc, OracleComp.pure_bind,
    SPRG.Raw.challengeStr_eq, Params.challengeStr_eq, SPRG.Raw.encPP_eq,
    PrimeParam.enc_eq, PolyExpr.eval_add, PolyExpr.eval_var, PolyExpr.eval_const, ite_true]

/-- H3 equals the random raw sPRG game [JLS26, Proposition 4.1, pp. 18-19]. Dv18 uses Raw.

**Proof sketch.** Read the raw game and sampler projection laws; the tail is the same uniform. -/
theorem hyb_random_eq_raw (P : Params) (π : PrimeSchedule) (A : NUPPT) (κ : ℕ) :
    P.hyb A .random κ (π κ) = (jlsSPRG_raw P π).game A false κ := by
  simp only [hyb_eq, SPRG.Raw.game_eq, jlsSPRG_raw_eq,
    SPRG.Raw.idSamp_eq, SPRG.Raw.sdSamp_eq, SPRG.Raw.instIdDrawFintype_eq,
    SPRG.Raw.instSdDrawFintype_eq, Params.idSamp'_eq, Params.sdSampFull_eq,
    OracleComp.map_eq_bind, OracleComp.bind_assoc, OracleComp.pure_bind,
    SPRG.Raw.challengeStr_eq, Params.challengeStr_eq, SPRG.Raw.encPP_eq,
    PrimeParam.enc_eq, PolyExpr.eval_add, PolyExpr.eval_var, PolyExpr.eval_const,
    Bool.false_eq_true, ite_false]

/-- H1 and the real-tail chain's initial game have equal acceptance probabilities
[JLS26, Lemma 4.2, p. 19]. Dv8 includes buckets. Pre-M0 repair SP-W2 compares
probabilities: the free oracle programs differ by an unused uniform-vector query.

**Proof sketch.** Read the core's public vectors, pass to acceptance expectations, and
sum out the unused uniform vectors using the existing exact uniform expectation law. -/
theorem hyb_prg_accept_eq_chain_zero (P : Params) (A : NUPPT) (κ : ℕ)
    (pp : PrimeParam κ) :
    accept (P.hyb A .prg κ pp) = accept (P.chainGame A true 0 κ pp) := by
  simp only [accept_eq, hyb_eq, chainGame_eq, ProbComp.prob_bind,
    Params.sdSampFull_eq, ProbComp.expect_map,
    Params.chainPublic_eq, Params.sdCore_instances, Params.sdCore_σ,
    Params.oneSd_pub, Params.lpnVector_eq, Nat.not_lt_zero,
    if_false, ite_true, ProbComp.expect_const]

/-- H2 and the uniform-tail chain's initial game have equal acceptance probabilities
[JLS26, Lemma 4.2, p. 19]. Pre-M0 repair SP-W2 compares probabilities rather than
free oracle syntax, since the chain makes an additional unused uniform-vector query.

**Proof sketch.** Read the public vectors and use the uniform expectation law to
marginalize the unused draw inside acceptance probability. -/
theorem hyb_uniform_accept_eq_chain_zero (P : Params) (A : NUPPT) (κ : ℕ)
    (pp : PrimeParam κ) :
    accept (P.hyb A .uniform κ pp) = accept (P.chainGame A false 0 κ pp) := by
  simp only [accept_eq, hyb_eq, chainGame_eq, ProbComp.prob_bind,
    Params.sdSampFull_eq, ProbComp.expect_map,
    Params.chainPublic_eq, Params.sdCore_instances,
    Params.oneSd_pub, Params.lpnVector_eq, Nat.not_lt_zero,
    if_false, Bool.false_eq_true, ProbComp.expect_const]

/-- H0 and H1 disagree only on the error event [JLS26, Proposition 4.1, pp. 18-19].
Dv7 retains the exact error probability at every parameter.

**Proof sketch.** Couple the two games with the same draws and coins. Correctness and the
packing readers show agreement off err=true; use the existing agree-off-bad bound. -/
theorem hyb_real_prg_le (P : Params) (A : NUPPT) (κ : ℕ) (pp : PrimeParam κ) :
    advantage (P.hyb A .real κ pp) (P.hyb A .prg κ pp) ≤ P.errProb κ pp := by
  classical
  let Ω := P.IdDraw κ pp ×
    (P.Draw κ pp × ((Fin (P.m κ) → Bool) × A.Coins κ))
  let c : ProbComp Ω :=
    (ProbComp.sample (P.IdDraw κ pp)).bind fun a =>
    (ProbComp.sample (P.Draw κ pp)).bind fun d =>
    (ProbComp.sample (Fin (P.m κ) → Bool)).bind fun w =>
    (ProbComp.sample (A.Coins κ)).bind fun r => pure (a, d, w, r)
  let ix : Ω → P.Idx' κ pp := fun z => P.idCore κ pp z.1
  let x : Ω → P.SdCoreOut κ pp := fun z => P.sdCore κ pp (ix z) z.2.1
  let bad : Ω → Prop := fun z => (x z).err = true
  let er : Ω → Prop := fun z =>
    A.distinguisherL κ (P.challengeStr κ pp (ix z) (x z).seed.1
      (P.eval' κ pp (ix z) (x z).seed)) z.2.2.2 = true
  let ep : Ω → Prop := fun z =>
    A.distinguisherL κ (P.challengeStr κ pp (ix z)
      (P.publicSeed κ pp (fun k => ((x z).instances k).pub) false)
      (fun j => P.G.eval (P.n κ) (ix z).1 z.2.1.1 (P.outputIndex κ j)))
        z.2.2.2 = true
  have hr : accept (P.hyb A .real κ pp) = ProbComp.prob c er := ?_
  swap
  · simp only [accept_eq, P.hyb_eq, P.idSamp'_eq, P.sdSampFull_eq,
      ProbComp.prob_eq_expect, ProbComp.expect_bind, ProbComp.expect_map,
      OracleComp.pure_eq_pure, ProbComp.expect_pure, c, er, ix, x]
  have hp : accept (P.hyb A .prg κ pp) = ProbComp.prob c ep := ?_
  swap
  · simp only [accept_eq, P.hyb_eq, P.idSamp'_eq, P.sdSampFull_eq,
      ProbComp.prob_eq_expect, ProbComp.expect_bind, ProbComp.expect_map,
      OracleComp.pure_eq_pure, ProbComp.expect_pure,
      P.sdCore_σ, c, ep, ix, x]
  have he : ProbComp.prob c bad = P.errProb κ pp := ?_
  swap
  · simp only [P.errProb_eq, P.idSamp'_eq, P.sdSampFull_eq,
      ProbComp.prob_eq_expect, ProbComp.expect_bind, ProbComp.expect_map,
      OracleComp.pure_eq_pure, ProbComp.expect_pure,
      c, bad, ix, x]
    dsimp only
    simp only [ProbComp.expect_const]
  have hagree : ∀ z, ¬ bad z → (er z ↔ ep z) := ?_
  swap
  · intro z hz
    have herr : (x z).err = false := Bool.eq_false_iff.mpr hz
    have hpub : (x z).seed.1 =
        P.publicSeed κ pp (fun k => ((x z).instances k).pub) false := ?_
    swap
    · have h := P.sdCore_publicSeed κ pp (ix z) z.2.1
      change (x z).seed.1 =
        P.publicSeed κ pp (fun k => ((x z).instances k).pub) (x z).err at h
      rwa [herr] at h
    have htail : P.eval' κ pp (ix z) (x z).seed =
        fun j => P.G.eval (P.n κ) (ix z).1 z.2.1.1 (P.outputIndex κ j) := ?_
    swap
    · funext j
      rw [P.eval'_eq]
      change decide (MvPolynomial.eval (Sum.elim (x z).seed.1 (x z).seed.2)
        (P.G4 κ pp (ix z) j) = 1) = _
      have h := P.G4_eval_sdCore κ pp (ix z) z.2.1 j
      change MvPolynomial.eval (Sum.elim (x z).seed.1 (x z).seed.2)
        (P.G4 κ pp (ix z) j) =
          if (x z).err then 0 else
            ((P.G.eval (P.n κ) (ix z).1 z.2.1.1 (P.outputIndex κ j)).toNat :
              ZMod pp.p) at h
      rw [h, herr]
      cases P.G.eval (P.n κ) (ix z).1 z.2.1.1 (P.outputIndex κ j) <;> simp
    dsimp only [er, ep]
    rw [hpub, htail]
  rw [advantage_eq, hr, hp]
  exact (ProbComp.abs_prob_sub_le_of_agree c hagree).trans_eq he

/-- H2 and H3 disagree only on the error event [JLS26, Proposition 4.1, pp. 18-19].
Dv7 retains the exact error probability at every parameter.

**Proof sketch.** Couple the same draws and uniform output. The public seeds agree when
err=false; apply the existing agree-off-bad bound. -/
theorem hyb_uniform_random_le (P : Params) (A : NUPPT) (κ : ℕ) (pp : PrimeParam κ) :
    advantage (P.hyb A .uniform κ pp) (P.hyb A .random κ pp) ≤ P.errProb κ pp := by
  classical
  let Ω := P.IdDraw κ pp ×
    (P.Draw κ pp × ((Fin (P.m κ) → Bool) × A.Coins κ))
  let c : ProbComp Ω :=
    (ProbComp.sample (P.IdDraw κ pp)).bind fun a =>
    (ProbComp.sample (P.Draw κ pp)).bind fun d =>
    (ProbComp.sample (Fin (P.m κ) → Bool)).bind fun w =>
    (ProbComp.sample (A.Coins κ)).bind fun r => pure (a, d, w, r)
  let ix : Ω → P.Idx' κ pp := fun z => P.idCore κ pp z.1
  let x : Ω → P.SdCoreOut κ pp := fun z => P.sdCore κ pp (ix z) z.2.1
  let bad : Ω → Prop := fun z => (x z).err = true
  let eu : Ω → Prop := fun z =>
    A.distinguisherL κ (P.challengeStr κ pp (ix z)
      (P.publicSeed κ pp (fun k => ((x z).instances k).pub) false) z.2.2.1)
        z.2.2.2 = true
  let er : Ω → Prop := fun z =>
    A.distinguisherL κ (P.challengeStr κ pp (ix z) (x z).seed.1 z.2.2.1)
      z.2.2.2 = true
  have hu : accept (P.hyb A .uniform κ pp) = ProbComp.prob c eu := ?_
  swap
  · simp only [accept_eq, P.hyb_eq, P.idSamp'_eq, P.sdSampFull_eq,
      ProbComp.prob_eq_expect, ProbComp.expect_bind, ProbComp.expect_map,
      OracleComp.pure_eq_pure, ProbComp.expect_pure, c, eu, ix, x]
  have hr : accept (P.hyb A .random κ pp) = ProbComp.prob c er := ?_
  swap
  · simp only [accept_eq, P.hyb_eq, P.idSamp'_eq, P.sdSampFull_eq,
      ProbComp.prob_eq_expect, ProbComp.expect_bind, ProbComp.expect_map,
      OracleComp.pure_eq_pure, ProbComp.expect_pure, c, er, ix, x]
  have he : ProbComp.prob c bad = P.errProb κ pp := ?_
  swap
  · simp only [P.errProb_eq, P.idSamp'_eq, P.sdSampFull_eq,
      ProbComp.prob_eq_expect, ProbComp.expect_bind, ProbComp.expect_map,
      OracleComp.pure_eq_pure, ProbComp.expect_pure,
      c, bad, ix, x]
    dsimp only
    simp only [ProbComp.expect_const]
  have hagree : ∀ z, ¬ bad z → (eu z ↔ er z) := ?_
  swap
  · intro z hz
    have herr : (x z).err = false := Bool.eq_false_iff.mpr hz
    have hpub : (x z).seed.1 =
        P.publicSeed κ pp (fun k => ((x z).instances k).pub) false := ?_
    swap
    · have h := P.sdCore_publicSeed κ pp (ix z) z.2.1
      change (x z).seed.1 =
        P.publicSeed κ pp (fun k => ((x z).instances k).pub) (x z).err at h
      rwa [herr] at h
    dsimp only [eu, er]
    rw [hpub]
  rw [advantage_eq, hu, hr]
  exact (ProbComp.abs_prob_sub_le_of_agree c hagree).trans_eq he

end Params
end TCSlib.Cryptography.Obfuscation.StructuredSeed
