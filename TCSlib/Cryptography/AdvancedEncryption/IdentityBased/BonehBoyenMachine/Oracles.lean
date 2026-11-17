/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyenMachine.Reduction

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The simulator's oracles with fresh exponents, and the simulation against the machine

Helper module of `AdvancedEncryption/IdentityBased/BonehBoyenMachine.lean` (step 3 of
[BB04, proof of Theorem 4.1] at depth `ℓ = 1`). Fix the group described by `d = desc(κ, r)` and
the Decision BDH tuple `(g, X, Y, Z, T)`.
* Call by call, the simulator's oracles `bb1SimImpl` (ideal uniform exponents, on the game's query
  and answer types) have the law of `drawStep` with a fresh uniform exponent per query, read on
  the game's lengths (`castImpl` of `ETTGame.freshImpl`). This step reads the game's oracles and
  the scheme's encodings through the readers `IBEScheme.oracleImpl_zero_onSpec`, `_one_onSpec`,
  `_two_onSpec`, `ofFn_bb1Scheme_encPP`, `ofFn_bb1Scheme_encSK`, `bb1Scheme_msgSpace_iff` and
  `ofFn_bb1SimCt`.
* Hence, on one tuple, the probability that `A` outputs `1` against the simulator and the
  probability that the machine of the handler theorem T1 accepts the tuple's string differ by at
  most `q(κ) · (1/2)^n` (`abs_expect_bb1Sim_sub_distinguisherL_le`), by
  `expect_castImpl_freshImpl`, `expect_handlerMachine` and `abs_expect_runAccept_sub_le`.

## Main definitions

None.

## Main results

* `BB1Machine.abs_expect_bb1Sim_sub_distinguisherL_le` — the simulation against the machine on
  one Decision BDH tuple.

## References

* [BB04] D. Boneh, X. Boyen, *Efficient Selective-ID Secure Identity Based Encryption Without
  Random Oracles*, full version, Cryptology ePrint Archive, Report 2004/172, December 2004
  (extended abstract: EUROCRYPT 2004, LNCS 3027, pp. 223–238). §4.2 (pp. 6–8): the algorithm
  `B` in the proof of Theorem 4.1.
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (Definition 26.8, non-uniform PPT.)
-/

namespace TCSlib.Cryptography.AdvancedEncryption.IdentityBased

open Complexity Turing TCSlib.Cryptography.Games TCSlib.Cryptography.Pairing
  TCSlib.Cryptography.Composability TCSlib.Cryptography.Candidates

namespace BB1Machine

variable (G : BilinearGen) (ℓ : PolyExpr)

/-- A cast between bit-vector types of equal widths is the padding of the vector's word. -/
private theorem cast_eq_padFin {a c : ℕ} (hac : a = c) (h : (Fin a → Bool) = (Fin c → Bool))
    (f : Fin a → Bool) : cast h f = padFin c (List.ofFn f) := by
  subst hac
  rw [cast_eq, padFin_ofFn]

/-- The word of a padded word of the right length: `⟦padFin m ⟦v⟧⟧ = ⟦v⟧` when `|v| = m`. -/
private theorem ofFn_padFin_ofFn {n m : ℕ} (h : n = m) (v : Fin n → Bool) :
    List.ofFn (padFin m (List.ofFn v)) = List.ofFn v :=
  ofFn_padFin_of_length (by rw [List.length_ofFn, h])

/-- The word of a validity bit followed by a key: `⟦decAnswer (some v)⟧ = 1 :: ⟦v⟧`. -/
private theorem ofFn_decAnswer_some {n : ℕ} (v : Fin n → Bool) :
    List.ofFn (FixedLengthScheme.decAnswer (some v)) = true :: List.ofFn v := by
  rw [FixedLengthScheme.decAnswer_some, List.ofFn_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]

/-- The `KeyGen` answer type of the game, from published readers:
`(S.sidSpec κ).rng 1 = (Fin (S.skLen.eval κ + 1) → Bool)` (`sidSpec_eq`, `bitSpec_rng`,
`outLens_one`). -/
private theorem sidSpec_rng_one' (S : IBEScheme) (κ : ℕ) :
    (S.sidSpec κ).rng 1 = (Fin (S.skLen.eval κ + 1) → Bool) := by
  rw [IBEScheme.sidSpec_eq, bitSpec_rng, IBEScheme.outLens_one]

/-- The `Challenge` answer type of the game, from published readers:
`(S.sidSpec κ).rng 2 = (Fin (S.ctLen.eval κ) → Bool)` (`sidSpec_eq`, `bitSpec_rng`,
`outLens_two`). -/
private theorem sidSpec_rng_two' (S : IBEScheme) (κ : ℕ) :
    (S.sidSpec κ).rng 2 = (Fin (S.ctLen.eval κ) → Bool) := by
  rw [IBEScheme.sidSpec_eq, bitSpec_rng, IBEScheme.outLens_two]

section Glue

variable (b : Bool) (κ : ℕ) (r : G.gen.Coins κ) (g X Y Z : (G.group κ (G.desc κ r)).G)
  (T : (G.group κ (G.desc κ r)).GT)

/-- **The simulator's oracles have the law of the oracles with fresh exponents**, call by call: for
every oracle `i`, query `x`, state `st` and `F`,
`𝔼[F | bb1SimImpl … i x st] = 𝔼[F | castImpl (freshImpl (drawStep …)) i x st]`, the right side
being `drawStep` with a fresh uniform exponent, read on the game's lengths.

**Proof sketch.** Unfold both sides one call deep (`bb1SimImpl_eq`, `castImpl_eq`,
`ETTGame.freshImpl_apply`) and split on the oracle and the state. The game's oracle is read at
the game's query type by `IBEScheme.oracleImpl_{zero,one,two}_onSpec`, and every cast between
bit-vector types of equal width is the padding of the vector's word (`cast_eq_padFin`; widths
from `inLens_*`, `outLens_*`, `qLen_*`, `aLen_*`). In each case (`Init`: parameters drawn or
recorded; `KeyGen`: before `Init`, the target identity, another identity; `Challenge`: before
`Init`, a valid or invalid first challenge, a repeated one) the simulator's case lemma
(`bb1SimInit_*`, `bb1SimKeyQ_*`, `bb1SimChal_*`) and `drawStep`'s case lemma draw the same
uniform exponent (or none), and the answers have the same words: the parameters by
`ofFn_bb1Scheme_encPP`, the key by `ofFn_decAnswer_some` and `ofFn_bb1Scheme_encSK`, the
challenge by `ofFn_bb1SimCt`, the message-space test by `bb1Scheme_msgSpace_iff`, and `⊥` by
`ofFn_zeroBits`. Vectors with equal words are equal (`ofFn_padFin_of_length`). -/
private theorem expect_bb1SimImpl (i : Fin 3) (x : ((bb1Scheme G ℓ).sidSpec κ).dom i)
    (st : BB1SimState G ℓ κ (G.desc κ r))
    (F : ((bb1Scheme G ℓ).sidSpec κ).rng i × BB1SimState G ℓ κ (G.desc κ r) → ℝ) :
    ProbComp.expect (bb1SimImpl G ℓ b κ (G.desc κ r) g X Y Z T i x st) F =
      ProbComp.expect (castImpl (ins := (bb1Scheme G ℓ).inLens κ)
        (outs := (bb1Scheme G ℓ).outLens κ)
        (ETTGame.freshImpl (spec := bitSpecAt (BB1Machine.qLen G ℓ) (BB1Machine.aLen G ℓ) κ)
          (BB1Machine.drawStep G ℓ b κ (G.desc κ r) g X Y Z T)) i x st) F := by
  rw [bb1SimImpl_eq, castImpl_eq, ETTGame.freshImpl_apply, OracleComp.bind_assoc]
  obtain ⟨o, c⟩ := st
  match i, x, F with
  | 0, x, F =>
    -- `Init`: the parameters, drawn with a fresh exponent or recorded
    have hq : (bb1Scheme G ℓ).inLens κ 0 = (BB1Machine.qLen G ℓ 0).eval κ := by
      rw [IBEScheme.inLens_zero, BB1Machine.qLen_zero]
    have hx : padFin ((bb1Scheme G ℓ).idLen.eval κ)
        (List.ofFn (padFin ((BB1Machine.qLen G ℓ 0).eval κ) (List.ofFn x))) =
        padFin ((bb1Scheme G ℓ).idLen.eval κ) (List.ofFn x) := by
      rw [ofFn_padFin_ofFn hq]
    rw [IBEScheme.oracleImpl_zero_onSpec,
      cast_eq_padFin (IBEScheme.inLens_zero (bb1Scheme G ℓ) κ) _ x]
    have hlen : ∀ h : (G.group κ (G.desc κ r)).G,
        (G.desc κ r ++ List.ofFn ((G.group κ (G.desc κ r)).encG g) ++
          List.ofFn ((G.group κ (G.desc κ r)).encG X) ++
          List.ofFn ((G.group κ (G.desc κ r)).encG Y) ++
          List.ofFn ((G.group κ (G.desc κ r)).encG h)).length = (bb1Scheme G ℓ).ppLen.eval κ := by
      intro h
      simp only [List.length_append, List.length_ofFn, G.length_desc]
      rw [bb1Scheme_ppLen, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]
      ring
    rcases o with _ | ⟨t, α₁⟩
    · rw [bb1SimInit_none, OracleComp.bind_assoc]
      simp only [OracleComp.pure_bind, ProbComp.expect_bind, ProbComp.expect_pure,
        BB1Machine.drawStep_zero, Option.getD_none, hx]
      refine congrArg _ (funext fun a => congrArg F (Prod.ext ?_ rfl))
      rw [cast_eq_padFin (IBEScheme.outLens_zero (bb1Scheme G ℓ) κ).symm _ _,
        ofFn_bb1Scheme_encPP, bb1SimParams_eq, ofFn_padFin_of_length (hlen _),
        ofFn_padFin_of_length (by rw [hlen, BB1Machine.aLen_zero])]
    · rw [bb1SimInit_some, OracleComp.pure_bind, ProbComp.expect_pure]
      simp only [OracleComp.pure_bind, ProbComp.expect_bind, ProbComp.expect_pure,
        BB1Machine.drawStep_zero, Option.getD_some]
      rw [ProbComp.expect_const, cast_eq_padFin (IBEScheme.outLens_zero (bb1Scheme G ℓ) κ).symm _ _,
        ofFn_bb1Scheme_encPP, bb1SimParams_eq, ofFn_padFin_of_length (hlen _),
        ofFn_padFin_of_length (by rw [hlen, BB1Machine.aLen_zero])]
  | 1, x, F =>
    -- `KeyGen`: `⊥` before `Init` and on the target identity, else a key with a fresh exponent
    have hq : (bb1Scheme G ℓ).inLens κ 1 = (BB1Machine.qLen G ℓ 1).eval κ := by
      rw [IBEScheme.inLens_one, BB1Machine.qLen_one]
    have hx : padFin ((bb1Scheme G ℓ).idLen.eval κ)
        (List.ofFn (padFin ((BB1Machine.qLen G ℓ 1).eval κ) (List.ofFn x))) =
        padFin ((bb1Scheme G ℓ).idLen.eval κ) (List.ofFn x) := by
      rw [ofFn_padFin_ofFn hq]
    have hxl : List.ofFn (padFin ((BB1Machine.qLen G ℓ 1).eval κ) (List.ofFn x)) = List.ofFn x :=
      ofFn_padFin_ofFn hq x
    have hidl : (bb1Scheme G ℓ).inLens κ 1 = (bb1Scheme G ℓ).idLen.eval κ :=
      IBEScheme.inLens_one _ κ
    have hzero : ∀ e : ℕ, padFin ((bb1Scheme G ℓ).outLens κ 1) (List.ofFn (zeroBits e)) =
        cast (sidSpec_rng_one' (bb1Scheme G ℓ) κ).symm (zeroBits _) := by
      intro e
      rw [cast_eq_padFin (IBEScheme.outLens_one (bb1Scheme G ℓ) κ).symm _ _, ofFn_zeroBits,
        ofFn_zeroBits, padFin_replicate_false, padFin_replicate_false]
    rw [IBEScheme.oracleImpl_one_onSpec, cast_eq_padFin hidl _ x]
    rcases o with _ | ⟨t, α₁⟩
    · rw [bb1SimKeyQ_none, OracleComp.pure_bind, ProbComp.expect_pure]
      simp only [OracleComp.pure_bind, ProbComp.expect_bind, ProbComp.expect_pure,
        BB1Machine.drawStep_one_none]
      rw [ProbComp.expect_const, hzero]
    · by_cases ht : List.ofFn x = List.ofFn t
      · have ht' : padFin ((bb1Scheme G ℓ).idLen.eval κ) (List.ofFn x) = t := by
          rw [ht, padFin_ofFn]
        rw [ht', bb1SimKeyQ_target, OracleComp.pure_bind, ProbComp.expect_pure]
        simp only [OracleComp.pure_bind, ProbComp.expect_bind, ProbComp.expect_pure,
          BB1Machine.drawStep_one_target G ℓ b κ _ g X Y Z T _ t α₁ c _ (hxl.trans ht)]
        rw [ProbComp.expect_const, hzero]
      · have ht' : padFin ((bb1Scheme G ℓ).idLen.eval κ) (List.ofFn x) ≠ t := by
          intro h
          apply ht
          rw [← h, ofFn_padFin_ofFn hidl]
        rw [bb1SimKeyQ_ne G ℓ κ _ g X Y _ t α₁ c ht', OracleComp.bind_assoc]
        simp only [OracleComp.pure_bind, ProbComp.expect_bind, ProbComp.expect_pure,
          BB1Machine.drawStep_one_key G ℓ b κ _ g X Y Z T _ t α₁ c _ (fun h => ht (hxl ▸ h)),
          hx]
        refine congrArg _ (funext fun u => congrArg F (Prod.ext ?_ rfl))
        rw [cast_eq_padFin (IBEScheme.outLens_one (bb1Scheme G ℓ) κ).symm _ _, ofFn_decAnswer_some,
          ofFn_bb1Scheme_encSK, bb1SimKey_eq, BB1.F_eq, bb1SimParams_eq]
        have hsk : (List.ofFn ((G.group κ (G.desc κ r)).encG
            (Y ^ (-α₁ / (BB1.idToZ (G.group κ (G.desc κ r))
                (padFin ((bb1Scheme G ℓ).idLen.eval κ) (List.ofFn x)) -
              BB1.idToZ (G.group κ (G.desc κ r)) t)).val *
            (X ^ (BB1.idToZ (G.group κ (G.desc κ r))
                (padFin ((bb1Scheme G ℓ).idLen.eval κ) (List.ofFn x))).val *
              (X ^ (-BB1.idToZ (G.group κ (G.desc κ r)) t).val * g ^ α₁.val)) ^ u.val)) ++
            List.ofFn ((G.group κ (G.desc κ r)).encG
              (Y ^ (-1 / (BB1.idToZ (G.group κ (G.desc κ r))
                (padFin ((bb1Scheme G ℓ).idLen.eval κ) (List.ofFn x)) -
                BB1.idToZ (G.group κ (G.desc κ r)) t)).val * g ^ u.val))).length =
            (bb1Scheme G ℓ).skLen.eval κ := by
          simp only [List.length_append, List.length_ofFn]
          rw [bb1Scheme_skLen, PolyExpr.eval_mul, PolyExpr.eval_const]
          ring
        rw [ofFn_padFin_of_length hsk, ofFn_padFin_of_length (by
          rw [List.length_cons, hsk, BB1Machine.aLen_one, PolyExpr.eval_add, PolyExpr.eval_const])]
  | 2, x, F =>
    -- `Challenge`: `⊥` before `Init` and on invalid messages, else the recorded challenge
    have hq : (bb1Scheme G ℓ).inLens κ 2 = (BB1Machine.qLen G ℓ 2).eval κ := by
      rw [IBEScheme.inLens_two, BB1Machine.qLen_two, PolyExpr.eval_add]
    have hxl : List.ofFn (padFin ((BB1Machine.qLen G ℓ 2).eval κ) (List.ofFn x)) = List.ofFn x :=
      ofFn_padFin_ofFn hq x
    have hml : (bb1Scheme G ℓ).inLens κ 2 =
        (bb1Scheme G ℓ).msgLen.eval κ + (bb1Scheme G ℓ).msgLen.eval κ :=
      IBEScheme.inLens_two _ κ
    have hmm : List.ofFn (padFin ((bb1Scheme G ℓ).msgLen.eval κ + (bb1Scheme G ℓ).msgLen.eval κ)
        (List.ofFn x)) = List.ofFn x := ofFn_padFin_ofFn hml x
    have hzero : ∀ e : ℕ, padFin ((bb1Scheme G ℓ).outLens κ 2) (List.ofFn (zeroBits e)) =
        cast (sidSpec_rng_two' (bb1Scheme G ℓ) κ).symm (zeroBits _) := by
      intro e
      rw [cast_eq_padFin (IBEScheme.outLens_two (bb1Scheme G ℓ) κ).symm _ _, ofFn_zeroBits,
        ofFn_zeroBits, padFin_replicate_false, padFin_replicate_false]
    rw [IBEScheme.oracleImpl_two_onSpec, cast_eq_padFin hml _ x]
    rcases o with _ | ⟨t, α₁⟩
    · rw [bb1SimChal_none, OracleComp.pure_bind, ProbComp.expect_pure]
      simp only [OracleComp.pure_bind, ProbComp.expect_bind, ProbComp.expect_pure,
        BB1Machine.drawStep_two_none]
      rw [ProbComp.expect_const, hzero]
    · rcases c with _ | w
      · -- the halves of the query, read in the game and by `drawStep`
        have h1 : List.ofFn (FixedLengthScheme.splitHalf (padFin ((bb1Scheme G ℓ).msgLen.eval κ +
            (bb1Scheme G ℓ).msgLen.eval κ) (List.ofFn x))).1 =
            (List.ofFn x).take ((bb1Scheme G ℓ).msgLen.eval κ) := by
          rw [FixedLengthScheme.ofFn_splitHalf_fst, hmm]
        have h2 : List.ofFn (FixedLengthScheme.splitHalf (padFin ((bb1Scheme G ℓ).msgLen.eval κ +
            (bb1Scheme G ℓ).msgLen.eval κ) (List.ofFn x))).2 =
            (List.ofFn x).drop ((bb1Scheme G ℓ).msgLen.eval κ) := by
          rw [FixedLengthScheme.ofFn_splitHalf_snd, hmm]
        by_cases hc : (∃ v, List.ofFn ((G.group κ (G.desc κ r)).encT v) =
              (List.ofFn x).take ((bb1Scheme G ℓ).msgLen.eval κ)) ∧
            (∃ v, List.ofFn ((G.group κ (G.desc κ r)).encT v) =
              (List.ofFn x).drop ((bb1Scheme G ℓ).msgLen.eval κ))
        · have hc1 := (bb1Scheme_msgSpace_iff G ℓ κ (G.desc κ r) (bb1SimParams G ℓ g X Y t α₁)
            (FixedLengthScheme.splitHalf (padFin ((bb1Scheme G ℓ).msgLen.eval κ +
              (bb1Scheme G ℓ).msgLen.eval κ) (List.ofFn x))).1).2 (by rw [h1]; exact hc.1)
          have hc2 := (bb1Scheme_msgSpace_iff G ℓ κ (G.desc κ r) (bb1SimParams G ℓ g X Y t α₁)
            (FixedLengthScheme.splitHalf (padFin ((bb1Scheme G ℓ).msgLen.eval κ +
              (bb1Scheme G ℓ).msgLen.eval κ) (List.ofFn x))).2).2 (by rw [h2]; exact hc.2)
          rw [bb1SimChal_fresh G ℓ b κ _ g X Y Z T _ t α₁ ⟨hc1, hc2⟩, OracleComp.pure_bind,
            ProbComp.expect_pure]
          simp only [OracleComp.pure_bind, ProbComp.expect_bind, ProbComp.expect_pure,
            BB1Machine.drawStep_two_fresh G ℓ b κ _ g X Y Z T _ t α₁ _ (hxl ▸ hc), hxl]
          rw [ProbComp.expect_const]
          -- the challenge words agree
          have hsel : List.ofFn (if b then (FixedLengthScheme.splitHalf
              (padFin ((bb1Scheme G ℓ).msgLen.eval κ + (bb1Scheme G ℓ).msgLen.eval κ)
                (List.ofFn x))).2 else (FixedLengthScheme.splitHalf
              (padFin ((bb1Scheme G ℓ).msgLen.eval κ + (bb1Scheme G ℓ).msgLen.eval κ)
                (List.ofFn x))).1) =
              if b then (List.ofFn x).drop ((bb1Scheme G ℓ).msgLen.eval κ)
              else (List.ofFn x).take ((bb1Scheme G ℓ).msgLen.eval κ) := by
            cases b
            · exact h1
            · exact h2
          have hct := ofFn_bb1SimCt G ℓ κ (G.desc κ r) Z T α₁
            (if b then (FixedLengthScheme.splitHalf
              (padFin ((bb1Scheme G ℓ).msgLen.eval κ + (bb1Scheme G ℓ).msgLen.eval κ)
                (List.ofFn x))).2 else (FixedLengthScheme.splitHalf
              (padFin ((bb1Scheme G ℓ).msgLen.eval κ + (bb1Scheme G ℓ).msgLen.eval κ)
                (List.ofFn x))).1)
          rw [hsel] at hct
          have hrec := List.ofFn_injective (hct.trans rfl)
          refine congrArg F (Prod.ext ?_ (congrArg (fun w => (some (t, α₁), some w)) hrec))
          rw [cast_eq_padFin (IBEScheme.outLens_two (bb1Scheme G ℓ) κ).symm _ _, hrec,
            ofFn_padFin_of_length, ofFn_padFin_of_length]
          · simp only [List.length_append, List.length_ofFn]
            rw [BB1Machine.aLen_two, bb1Scheme_ctLen, PolyExpr.eval_add, PolyExpr.eval_mul,
              PolyExpr.eval_const]
            ring
          · simp only [List.length_append, List.length_ofFn]
            rw [bb1Scheme_ctLen, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]
            ring
        · rw [bb1SimChal_invalid G ℓ b κ _ g X Y Z T
            (padFin ((bb1Scheme G ℓ).msgLen.eval κ + (bb1Scheme G ℓ).msgLen.eval κ) (List.ofFn x))
            t α₁ (fun h => hc ⟨h1 ▸ (bb1Scheme_msgSpace_iff G ℓ κ (G.desc κ r)
              (bb1SimParams G ℓ g X Y t α₁) _).1 h.1, h2 ▸ (bb1Scheme_msgSpace_iff G ℓ κ
              (G.desc κ r) (bb1SimParams G ℓ g X Y t α₁) _).1 h.2⟩), OracleComp.pure_bind,
            ProbComp.expect_pure]
          simp only [OracleComp.pure_bind, ProbComp.expect_bind, ProbComp.expect_pure,
            BB1Machine.drawStep_two_invalid G ℓ b κ _ g X Y Z T _ t α₁ _ (hxl ▸ hc)]
          rw [ProbComp.expect_const, hzero]
      · rw [bb1SimChal_repeat G ℓ b κ _ g X Y Z T _ (t, α₁) w, OracleComp.pure_bind,
          ProbComp.expect_pure]
        simp only [OracleComp.pure_bind, ProbComp.expect_bind, ProbComp.expect_pure,
          BB1Machine.drawStep_two_repeat]
        rw [ProbComp.expect_const,
          cast_eq_padFin (IBEScheme.outLens_two (bb1Scheme G ℓ) κ).symm _ _,
          ofFn_padFin_ofFn (by rw [BB1Machine.aLen_two])]

end Glue

/-- **The simulation and the machine on one Decision BDH tuple**: with arithmetic `H`, operations
`O`, an adversary `A`, its `toCompOn` form `A'`, budget `q`, bit `b`, security parameter `κ`, a
coin bijection `φ'` with `A'.toCompOn codec κ q x (φ' ρ) = A.toComp codec κ q ρ` (`hφ'`), and a
machine `B` realizing `handler … b q` for `A'` (coin bijection `φ`, `hφ`: the conclusion of T1),
for the generator's coins `r` and every tuple `(g, X, Y, Z, T)`,
`|𝔼_{ρ ← A.Coins} 𝔼[[guess = 1] | simulate (bb1SimImpl … b κ d g X Y Z T)
(A.toComp sidCodec κ q(κ) ρ) (⊥, ⊥)] −
Pr_{ρ ← B.Coins}[B.distinguisherL κ ⟨d, g, X, Y, Z, T⟩ ρ]| ≤ q(κ) · (1/2)^n`, with
`d = desc(κ, r)` and `n = blockLen(κ)`.

**Proof sketch.** Call by call, `bb1SimImpl` has the law of `drawStep` with fresh exponents read
on the game's lengths (`expect_bb1SimImpl`), so the run against the simulator has the law of the
run against `castImpl (freshImpl drawStep)` (`ProbComp.expect_simulate_congr`). By `hφ'` and
`sidCodec_eq` it is the run of `A'`, which accepts with `𝔼_U runAccept (φ' ρ) U`
(`expect_castImpl_freshImpl`). The machine accepts with `𝔼_ρ 𝔼_V runAccept ρ (draw ∘ V)`
(`expect_handlerMachine`). Move `A`'s coins to `A'`'s along `φ'` (`expect_sample_equiv`), and
conclude by `abs_expect_runAccept_sub_le`. -/
theorem abs_expect_bb1Sim_sub_distinguisherL_le (H : ArithmeticFP) (O : G.Ops) (A A' : NUPPT)
    (q : PolyExpr) (b : Bool) (κ : ℕ) (φ' : A.Coins κ ≃ A'.Coins κ)
    (hφ' : ∀ {ι α : Type} {spec : OracleSpec ι} (codec : MachineCodec spec α) (q : ℕ)
      (x : List Bool) (r : A.Coins κ), A'.toCompOn codec κ q x (φ' r) = A.toComp codec κ q r)
    (B : NUPPT)
    (φ : (Fin ((BB1Machine.handler G ℓ O b q H).seedLen.eval κ) → Bool) × A'.Coins κ ≃ B.Coins κ)
    (hφ : ∀ (z : List Bool) (ω : Fin ((BB1Machine.handler G ℓ O b q H).seedLen.eval κ) → Bool)
      (ρ : A'.Coins κ), ∃ (a : Fin ((PolyExpr.const 1).eval κ) → Bool)
        (s : Fin ((BB1Machine.handler G ℓ O b q H).stateLen.eval κ) → Bool),
        simulate ((BB1Machine.handler G ℓ O b q H).impl κ z ω)
            (A'.toCompOn (bitCodec (fun i => (BB1Machine.qLen G ℓ i).eval κ)
              (fun i => (BB1Machine.aLen G ℓ i).eval κ) ((PolyExpr.const 1).eval κ)) κ (q.eval κ)
              ((BB1Machine.handler G ℓ O b q H).advInput κ z ω) ρ)
            ((BB1Machine.handler G ℓ O b q H).init κ) = .pure (a, s) ∧
          B.runAt κ z (φ (ω, ρ)) = (BB1Machine.handler G ℓ O b q H).result κ z ω s a)
    (r : G.gen.Coins κ) (g X Y Z : (G.group κ (G.desc κ r)).G)
    (T : (G.group κ (G.desc κ r)).GT) :
    |ProbComp.expect (ProbComp.sample (A.Coins κ)) (fun ρ =>
        ProbComp.expect (simulate (bb1SimImpl G ℓ b κ (G.desc κ r) g X Y Z T)
          (A.toComp ((bb1Scheme G ℓ).sidCodec κ) κ (q.eval κ) ρ) (none, none))
          (fun res => if res.1 0 = true then 1 else 0)) -
      ProbComp.expect (ProbComp.sample (B.Coins κ)) (fun ρ => if B.distinguisherL κ
        (tupleStr (G.group κ (G.desc κ r)) (G.desc κ r) g X Y Z T) ρ = true then 1 else 0)| ≤
      q.eval κ * (1 / 2 : ℝ) ^ (BB1Machine.blockLen G).eval κ := by
  have hid : (fun ρ => ProbComp.expect (simulate (bb1SimImpl G ℓ b κ (G.desc κ r) g X Y Z T)
      (A.toComp ((bb1Scheme G ℓ).sidCodec κ) κ (q.eval κ) ρ) (none, none))
      (fun res => if res.1 0 = true then (1 : ℝ) else 0)) = fun ρ =>
      ProbComp.expect (ProbComp.sample (Fin (q.eval κ) → ZMod (G.group κ (G.desc κ r)).order))
        fun U => BB1Machine.runAccept G ℓ b q A' κ r g X Y Z T (φ' ρ) U := by
    funext ρ
    rw [ProbComp.expect_simulate_congr _ _ (expect_bb1SimImpl G ℓ b κ r g X Y Z T),
      ← hφ' ((bb1Scheme G ℓ).sidCodec κ) (q.eval κ) [] ρ, IBEScheme.sidCodec_eq,
      BB1Machine.expect_castImpl_freshImpl]
  have e := ProbComp.expect_sample_equiv φ' (fun ρ => ProbComp.expect (ProbComp.sample
    (Fin (q.eval κ) → ZMod (G.group κ (G.desc κ r)).order))
      fun U => BB1Machine.runAccept G ℓ b q A' κ r g X Y Z T ρ U)
  beta_reduce at e
  rw [hid, BB1Machine.expect_handlerMachine G ℓ b q A' κ r g X Y Z T O H B φ hφ, e,
    abs_sub_comm]
  exact BB1Machine.abs_expect_runAccept_sub_le G ℓ b q A' κ r g X Y Z T

end BB1Machine

end TCSlib.Cryptography.AdvancedEncryption.IdentityBased
