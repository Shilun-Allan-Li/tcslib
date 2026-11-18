/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.ZeroKnowledge.LevinHardness.Verifier
import TCSlib.Cryptography.ZeroKnowledge.LevinHardness.CircuitWitness
import TCSlib.Cryptography.ZeroKnowledge.LevinHardness.ColoringParse
import TCSlib.Cryptography.ZeroKnowledge.LevinHardness.ColoringWitness
import TCSlib.Cryptography.ZeroKnowledge.LevinHardness.Soundness
import TCSlib.Cryptography.ZeroKnowledge.LevinHardness.Padding
import TCSlib.Cryptography.ZeroKnowledge.NP

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# `3COL` is NP-hard with Levin reductions

The assembly of the Levin reduction `(L, R) → (3COL, R_3COL)` for every witness relation, along
the circuit route [AB09, Lemmas 6.10 and 6.11, p. 111] followed by the 3SAT → 3-colouring gadget
of the course material:

* `f₁ = tabInst …` prints the tableau circuit of the verifier (`Verifier.lean`), witness map the
  certificate `certOf q x y`;
* `f₂ = dagCktSatToSAT3`, the Tseitin map, witness map the wire values (`CircuitWitness.lean`);
* `f₃ = colorInst`, the gadget graph of the decoded 3-CNF (`ColoringGraph.lean`,
  `ColoringParse.lean`), witness map the explicit colouring `colorWord` (`ColoringWitness.lean`);
  soundness is the course theorem transported along a homomorphism (`Soundness.lean`);
* padding with isolated vertices to exactly `B(|x|)` vertices (`Padding.lean`), where
  `B(n) = A (n + 1)^a + n + 1` and `A (n + 1)^a` bounds the length `N²` of the unpadded graph's
  encoding (`PolyTimeComputable.output_length_le` of `f₃ ∘ f₂ ∘ f₁`), so that `|f x| = B(|x|)²`
  for every `x` and the length polynomial `p = B²` dominates the identity.

This proves `LevinNPHard L3COL R3COL` ([PS10, §4.7, Theorem 124.1, step 2]; the hypothesis of
`zk_proof_of_witnessRelation` and `zk_proof_of_mem_NP` in `ZeroKnowledge/NP.lean`), and with it
the unconditional forms of [PS10, Theorem 124.1].

## Main results

* `TCSlib.Cryptography.LevinHardness.polyTimeComputable_certOf` — the certificate map.
* `TCSlib.Cryptography.LevinHardness.exists_R_3SAT_iff_padWord`,
  `TCSlib.Cryptography.LevinHardness.R3COL_padWord` — step 3 with padding, string level.
* `TCSlib.Cryptography.levinNPHard_L3COL` — **`LevinNPHard L3COL R3COL`**.
* `TCSlib.Cryptography.zk_proof_of_witnessRelation_of_owp_unconditional`,
  `TCSlib.Cryptography.zk_proof_of_mem_NP_of_owp_unconditional` — [PS10, Theorem 124.1] without
  the hypothesis.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Cambridge
  University Press, 2009. (§2.3; §6.1.2, Lemmas 6.10 and 6.11, p. 111.)
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§4.7, Theorem 124.1, step 2.)
* CS 294-268 course material (UC Berkeley, Spring 2026, V. Guruswami), the 3SAT → 3-colouring
  reduction of `Complexity/NPReductions/ThreeSATToColoring.lean`.
-/

namespace TCSlib.Cryptography.LevinHardness

open Complexity Turing BoolCircuit Std.Sat

/-! ### The certificate map -/

/-- **The certificate map is polynomial-time** on `⟨x, y⟩`:
`z ↦ certOf q (pairFstD z) (pairSndD z) = y ++ 1 0^{q(|x|) - |y|}`. -/
theorem polyTimeComputable_certOf (q : PolyExpr) :
    PolyTimeComputable fun z => certOf q (pairFstD z) (pairSndD z) := by
  have hz : PolyTimeComputable fun z =>
      List.replicate (q.eval (pairFstD z).length - (pairSndD z).length) false :=
    EncodingMachines.zeros_poly (L := fun z => q.eval (pairFstD z).length - (pairSndD z).length)
      (EncodingMachines.unarySub_poly (f := fun z => q.eval (pairFstD z).length)
        (g := fun z => (pairSndD z).length)
        ((polyTimeComputable_unaryPoly q).comp polyTimeComputable_pairFstD)
        (EncodingMachines.unaryLength_poly polyTimeComputable_pairSndD))
  refine (polyTimeComputable_pairSndD.append
    ((polyTimeComputable_const [true]).append hz)).congr fun z => ?_
  rw [certOf_eq]
  rfl

/-! ### Step 3 with padding, at the string level -/

/-- **A witness of `R_3SAT` passes the width test and gives a proper colouring**: if
`R_3SAT s a`, then `goodS s = true` and the colouring `gadgetColor |s| (a.getD · false)` of
`ColoringWitness.lean` is proper on `gadgetGraph |s| (memS s)`.

**Proof sketch.** Every clause of `CNF.decode s` is satisfied, hence nonempty
(`clause_eval_eq_true_iff`), and has at most three literals (`R_3SAT_iff`, read through
`Bridge.widthAtMost_iff`), so `goodS s` (`goodS_iff`); every clause code accepted by `memS s` is
satisfied (`clauseSat_of_memS`), so the colouring is proper (`properColoring_gadgetColor`). -/
theorem goodS_and_properColoring_of_R_3SAT {s a : List Bool} (h : R_3SAT s a) :
    goodS s = true ∧ ProperColoring (gadgetGraph s.length (memS s))
      (fun u => gadgetColor s.length (fun v => a.getD v false) u) := by
  obtain ⟨hw, he⟩ := (R_3SAT_iff s a).1 h
  have hall := (cnf_eval_eq_true_iff _ _).1 he
  refine ⟨(goodS_iff s).2 fun C hC => ⟨?_, (Bridge.widthAtMost_iff _ _).1 hw C hC⟩,
    properColoring_gadgetColor _ _ _ fun c hc => clauseSat_of_memS he hc⟩
  obtain ⟨ℓ, hℓ, -⟩ := (clause_eval_eq_true_iff _ _).1 (hall C hC)
  exact List.length_pos_of_mem hℓ

/-- **A 3-colourable gadget graph of a good string has a witness of `R_3SAT`**: if
`goodS s = true` and `ThreeColorable (gadgetGraph |s| (memS s))`, then `∃ a, R_3SAT s a`.

**Proof sketch.** Soundness transported from the course theorem
(`exists_clauseSat_of_colorable`) gives `val`, `false` beyond `|s|`, satisfying every accepted
clause code. Every clause `C` of `CNF.decode s` has one to three literals (`goodS_iff`) over
variables `< |s|` (`var_lt_length_of_mem_decode`), so its code is accepted (`memS_iff`) and below
`(2|s|)³` (`clauseCode_lt`), and `clauseSat` of its code is `C.eval val`
(`clauseSat_clauseCode`). The word `a = [val 0, …, val (|s| - 1)]` reads back `val`. -/
theorem exists_R_3SAT_of_colorable {s : List Bool} (hg : goodS s = true)
    (hc : ThreeColorable (gadgetGraph s.length (memS s))) : ∃ a, R_3SAT s a := by
  obtain ⟨val, hval0, hsat⟩ :=
    exists_clauseSat_of_colorable ((threeColorable_gadgetGraph_iff _ _).1 hc)
  refine ⟨(List.range s.length).map val, (R_3SAT_iff _ _).2
    ⟨(Bridge.widthAtMost_iff _ _).2 fun C hC => ((goodS_iff s).1 hg C hC).2, ?_⟩⟩
  have hget : (fun v => ((List.range s.length).map val).getD v false) = val := by
    funext v
    by_cases hv : v < s.length
    · simp [List.getD_eq_getElem?_getD, hv]
    · rw [hval0 v (Nat.not_lt.1 hv)]
      simp [List.getD_eq_getElem?_getD, hv]
  rw [hget, cnf_eval_eq_true_iff]
  intro C hC
  obtain ⟨h1, h3⟩ := (goodS_iff s).1 hg C hC
  have hK : ∀ ℓ ∈ C, ℓ.1 < s.length := fun ℓ hℓ => var_lt_length_of_mem_decode hC hℓ
  rw [← clauseSat_clauseCode val hK h1 h3]
  exact hsat _ (clauseCode_lt hK h1) ((memS_iff s _).2 ⟨C, hC, h1, h3, rfl⟩)

/-- **Membership of the padded instance** (glue): for `|colorInst s| ≤ B`,
`padWord (colorInst s) B ∈ L3COL ↔ goodS s = true ∧ ThreeColorable (gadgetGraph |s| (memS s))`
(`colorInst_eq`, `padWord_encGraph`, `encGraph_mem_L3COL_iff`, `threeColorable_padGraph_iff`, and
`not_threeColorable_k4` for a string failing the width test). -/
theorem padWord_colorInst_mem_iff {s : List Bool} {B : ℕ} (hB : (colorInst s).length ≤ B) :
    padWord (colorInst s) B ∈ L3COL ↔
      goodS s = true ∧ ThreeColorable (gadgetGraph s.length (memS s)) := by
  by_cases hg : goodS s = true
  · have hc : colorInst s = encGraph (gadgetGraph s.length (memS s)) := by
      rw [colorInst_eq, if_pos hg]
    rw [hc] at hB ⊢
    rw [length_encGraph] at hB
    rw [padWord_encGraph, encGraph_mem_L3COL_iff,
      threeColorable_padGraph_iff _ ((Nat.le_mul_self _).trans hB)]
    exact ⟨fun h => ⟨hg, h⟩, fun h => h.2⟩
  · have hc : colorInst s = encGraph k4 := by rw [colorInst_eq, if_neg hg]
    rw [hc] at hB ⊢
    rw [length_encGraph] at hB
    rw [padWord_encGraph, encGraph_mem_L3COL_iff,
      threeColorable_padGraph_iff _ ((Nat.le_mul_self _).trans hB)]
    exact iff_of_false not_threeColorable_k4 fun h => hg h.1

/-- **Step 3 with padding, membership**: for `|colorInst s| ≤ B`,
`(∃ a, R_3SAT s a) ↔ padWord (colorInst s) B ∈ L3COL`
(`goodS_and_properColoring_of_R_3SAT`, `exists_R_3SAT_of_colorable`). -/
theorem exists_R_3SAT_iff_padWord {s : List Bool} {B : ℕ} (hB : (colorInst s).length ≤ B) :
    (∃ a, R_3SAT s a) ↔ padWord (colorInst s) B ∈ L3COL := by
  rw [padWord_colorInst_mem_iff hB]
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨hg, hp⟩ := goodS_and_properColoring_of_R_3SAT ha
    exact ⟨hg, (threeColorable_iff _).2 ⟨_, hp⟩⟩
  · rintro ⟨hg, hc⟩
    exact exists_R_3SAT_of_colorable hg hc

/-- **Step 3 with padding, witness**: for `|colorInst s| ≤ B`, `R_3SAT s a` implies
`R3COL (padWord (colorInst s) B) (padColWord (colorWord s a) B)`: the padded colouring of
`gadgetColor` (`padColWord_encColoring`) is proper on the padded graph
(`properColoring_padGraph`). -/
theorem R3COL_padWord {s a : List Bool} {B : ℕ} (ha : R_3SAT s a)
    (hB : (colorInst s).length ≤ B) :
    R3COL (padWord (colorInst s) B) (padColWord (colorWord s a) B) := by
  obtain ⟨hg, hp⟩ := goodS_and_properColoring_of_R_3SAT ha
  have hc : colorInst s = encGraph (gadgetGraph s.length (memS s)) := by
    rw [colorInst_eq, if_pos hg]
  rw [hc] at hB ⊢
  rw [length_encGraph] at hB
  have hN : gadgetN s.length ≤ B := (Nat.le_mul_self _).trans hB
  refine (R3COL_iff _ _).2 ⟨B, padGraph (gadgetGraph s.length (memS s)) B,
    padColoring (fun u => gadgetColor s.length (fun v => a.getD v false) u) B,
    padWord_encGraph _ _, ?_, properColoring_padGraph B hp⟩
  rw [colorWord_eq, padColWord_encColoring _ hN]

/-- The padded word has length `B²`: `|padWord w B| = B * B` (`padWord_eq`). Glue. -/
theorem length_padWord (w : List Bool) (B : ℕ) : (padWord w B).length = B * B := by
  rw [padWord_eq, List.length_map, List.length_range]

end TCSlib.Cryptography.LevinHardness

namespace TCSlib.Cryptography

open Complexity Turing BoolCircuit LevinHardness

/-- **`3COL` is NP-hard with Levin reductions** [PS10, §4.7, Theorem 124.1, step 2 (the
hypothesis of the "every language in NP" form)]; [AB09, Lemmas 6.10 and 6.11, p. 111] for the
circuit route and the course 3SAT → 3-colouring reduction: every language `L` with a witness
relation `R` has a Levin reduction `(f, w)` to `(3COL, R_3COL)` with length polynomial `p ≥ id`,
`LevinNPHard L3COL R3COL`.

**Proof sketch.** Let `q, M, C, c` and the tableau instance map `f₁` come from
`exists_tabReduction`; `f₂ = dagCktSatToSAT3`, `f₃ = colorInst`. The composite `f₃ ∘ f₂ ∘ f₁` is
polynomial-time, so its output length is at most `A (n + 1)^a`; put
`B(n) = A (n + 1)^a + n + 1` and `f x = padWord (f₃ (f₂ (f₁ x))) B(|x|)`, of length exactly
`B(|x|)²` (`length_padWord`), with `p = B² ≥ id`. Membership:
`x ∈ L ↔` the tableau circuit is satisfiable `↔ ∃ a, R_3SAT (f₂ (f₁ x)) a` (`exists_R_3SAT_iff`,
the instance being the circuit's description) `↔ f x ∈ L3COL` (`exists_R_3SAT_iff_padWord`).
Witnesses: `R x y` gives `R_CKT (f₁ x) (certOf q x y)`, then `R_3SAT` of the wire values
(`R_3SAT_wireValues`), then `R3COL` of the padded colouring (`R3COL_padWord`). The witness map
`⟨x, y⟩ ↦ padColWord (colorWord (f₂ (f₁ x)) (wireValues (f₁ x) (certOf q x y))) B(|x|)` is a
composition of polynomial-time maps on pairs (`polyTimeComputable_certOf`,
`polyTimeComputable_wireValues`, `polyTimeComputable_colorWord`,
`polyTimeComputable_padColWord`). -/
theorem levinNPHard_L3COL : LevinNPHard L3COL R3COL := by
  refine (Bridge.levinNPHard_iff _ _).2 fun L R hR => ?_
  obtain ⟨q, M, C, c, hf1, henc, hfan, hmem, hwit⟩ := exists_tabReduction hR
  generalize tabInst M (q.add (.const 1)) (verTime C c (q.add (.const 1))) = f₁ at *
  -- the composite instance map and its length bound
  have hs : PolyTimeComputable fun x => dagCktSatToSAT3 (f₁ x) :=
    polyTimeComputable_dagCktSatToSAT3.comp hf1
  have hg : PolyTimeComputable fun x => colorInst (dagCktSatToSAT3 (f₁ x)) :=
    polyTimeComputable_colorInst.comp hs
  obtain ⟨A, a, hA⟩ := hg.output_length_le
  let Bp : PolyExpr := (PolyExpr.normal A a).add (PolyExpr.var.add (.const 1))
  have hBp : ∀ n, Bp.eval n = A * (n + 1) ^ a + (n + 1) := fun n => by
    simp only [Bp, PolyExpr.eval_add, PolyExpr.eval_normal, PolyExpr.eval_var,
      PolyExpr.eval_const]
  have hB : ∀ x : List Bool, (colorInst (dagCktSatToSAT3 (f₁ x))).length ≤ Bp.eval x.length :=
    fun x => by rw [hBp]; have := hA x; omega
  refine ⟨fun x => padWord (colorInst (dagCktSatToSAT3 (f₁ x))) (Bp.eval x.length),
    fun x y => padColWord (colorWord (dagCktSatToSAT3 (f₁ x))
      (wireValues (f₁ x) (certOf q x y))) (Bp.eval x.length),
    Bp.mul Bp, ⟨?_, ?_, fun x => ?_, fun x y hxy => ?_, fun x => ?_, fun N => ?_⟩⟩
  · -- the instance map is polynomial-time
    exact (polyTimeComputable_padWord.comp (hg.pairEncode (polyTimeComputable_unaryPoly Bp))).congr
      fun x => by
        simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode,
          List.length_replicate]
  · -- the witness map is polynomial-time on ⟨x, y⟩
    have hwv : PolyTimeComputable fun z =>
        wireValues (f₁ (pairFstD z)) (certOf q (pairFstD z) (pairSndD z)) :=
      (polyTimeComputable_wireValues.comp
        ((hf1.comp polyTimeComputable_pairFstD).pairEncode (polyTimeComputable_certOf q))).congr
        fun z => by simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
    have hcw : PolyTimeComputable fun z => colorWord (dagCktSatToSAT3 (f₁ (pairFstD z)))
        (wireValues (f₁ (pairFstD z)) (certOf q (pairFstD z) (pairSndD z))) :=
      (polyTimeComputable_colorWord.comp
        ((hs.comp polyTimeComputable_pairFstD).pairEncode hwv)).congr
        fun z => by simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
    exact (polyTimeComputable_padColWord.comp (hcw.pairEncode
      ((polyTimeComputable_unaryPoly Bp).comp polyTimeComputable_pairFstD))).congr
      fun z => by
        simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode,
          List.length_replicate]
  · -- membership
    rw [hmem x, ← exists_R_3SAT_iff _ (hfan x), ← henc x]
    exact exists_R_3SAT_iff_padWord (hB x)
  · -- witnesses
    exact R3COL_padWord (R_3SAT_wireValues (hwit x y hxy)) (hB x)
  · -- exact length `B(|x|)²`
    rw [length_padWord, PolyExpr.eval_mul]
  · -- `B² ≥ id`
    rw [PolyExpr.eval_mul, hBp]
    exact (Nat.le_add_left (N + 1) _).trans' (Nat.le_succ N) |>.trans (Nat.le_mul_self _)

/-- **[PS10, Theorem 124.1], "if one-way permutations exist then every language in NP has a
zero-knowledge proof", for every witness relation, unconditionally**: the conclusion of
`zk_proof_of_witnessRelation_of_owp` without its hypothesis `LevinNPHard L3COL R3COL`, which is
`levinNPHard_L3COL`. -/
theorem zk_proof_of_witnessRelation_of_owp_unconditional
    (how : ∃ P : PermFamily, OneWayPermutation P) {L : Language Bool}
    {R : List Bool → List Bool → Prop} (hR : WitnessRelation L R) :
    ∃ (Com : List Bool → List Bool) (ℓ : PolyExpr), Commitment Com ℓ ∧
      ∃ (f : List Bool → List Bool) (w : List Bool → List Bool → List Bool) (p : PolyExpr),
        LevinReduction L L3COL R R3COL f w p ∧ (∀ N, N ≤ p.eval N) ∧
        EfficientProverProof ((colProtocolRep Com ℓ).pullback f w p) L R ∧
        ZK ((colProtocol Com ℓ).pullback f w p) R ∧
        EfficientProverProofErr ((colProtocol Com ℓ).pullback f w p) L R
          (fun N => 1 - 1 / (p.eval N : ℝ) + (1 / 2 : ℝ) ^ p.eval N) :=
  zk_proof_of_witnessRelation_of_owp levinNPHard_L3COL how hR

/-- **[PS10, Theorem 124.1], "if one-way permutations exist then every language in NP has a
zero-knowledge proof", one-iteration form, unconditionally**: the conclusion of
`zk_proof_of_mem_NP_of_owp` without its hypothesis `LevinNPHard L3COL R3COL`, which is
`levinNPHard_L3COL`. -/
theorem zk_proof_of_mem_NP_of_owp_unconditional
    (how : ∃ (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool),
      OneWayPermutation P ∧ P.HardCore h)
    {L : Language Bool} (hL : L ∈ NP) :
    ∃ R : List Bool → List Bool → Prop, WitnessRelation L R ∧
      (∃ π : Protocol, EfficientProverProof π L R) ∧
      ∃ (π : Protocol) (p : PolyExpr), (∀ N, N ≤ p.eval N) ∧ ZK π R ∧
        EfficientProverProofErr π L R
          (fun N => 1 - 1 / (p.eval N : ℝ) + (1 / 2 : ℝ) ^ p.eval N) :=
  zk_proof_of_mem_NP_of_owp levinNPHard_L3COL how hL

end TCSlib.Cryptography
