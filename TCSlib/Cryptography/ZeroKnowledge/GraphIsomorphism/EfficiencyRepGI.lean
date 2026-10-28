/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.EfficiencyRep

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The `|x|`-fold graph isomorphism protocol: efficiency of the parties

The polynomial-time machines behind the parties of the `|x|`-fold graph isomorphism protocol
[PS10, Protocol 120.6, repeated] (`giProverRep`, `giVerifierRep`; inventory item Inf-4.2),
proved for the shadow strategies of `GraphIsomorphism/Proofs.lean` with the loop
infrastructure of `GraphIsomorphism/EfficiencyRep.lean`: the half count and parity of the
history (`halfLoop_poly`), the last message received (`lastMsg_poly`), the coin block of the
current iteration (`coinSlice_poly`), and the verdict scan over the `|x|` iterations
(`iterUnary_poly` on `giStep`).

## Main definitions

* `TCSlib.Cryptography.GI.giBlock` — the coin polynomial `(N + 1)²` of one iteration.
* `TCSlib.Cryptography.GI.giStep` — one round of the verifier's verdict scan.

## Main results

* `TCSlib.Cryptography.GI.giProverRep_efficient`, `GI.giVerifierRep_efficient` — the parties of
  the `|x|`-fold graph isomorphism protocol are PPT strategies.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§4.5 Interactive proofs, pp. 117–120.)
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Cambridge
  University Press, 2009. (§2.2, the class FP.)
-/

namespace TCSlib.Cryptography.GI

open Complexity Turing Complexity.StateLoop

/-! ### The prover of the `|x|`-fold graph isomorphism protocol -/

/-- The coin polynomial of one iteration of the graph isomorphism protocol, `(N + 1)²`. -/
def giBlock : PolyExpr := .normal 1 2

/-- The block length evaluates to `(N + 1)²`. -/
theorem giBlock_eval (N : ℕ) : giBlock.eval N = (N + 1) ^ 2 := by
  simp [giBlock, PolyExpr.eval_normal]

/-- The half count of the layout's history, in unary. -/
theorem halfCnt_poly : PolyTimeComputable fun w => List.replicate (halfCount (argM w)) true :=
  ptc_congr (polyTimeComputable_pairSndD.comp (halfLoop_poly.comp argM_poly)) fun w => by simp

/-- The remainder of the half loop on the layout's history (empty exactly for an even number of
messages). -/
theorem halfRem_poly : PolyTimeComputable fun w =>
    (fun v => pairSndD (pairSndD v))^[halfCount (argM w)] (argM w) :=
  ptc_congr (polyTimeComputable_pairFstD.comp (halfLoop_poly.comp argM_poly)) fun w => by simp

/-- The parity test "an even number of messages" of the layout. -/
theorem even_poly : PolyTimeComputable fun w =>
    [decide ((fun v => pairSndD (pairSndD v))^[halfCount (argM w)] (argM w) = [])] :=
  isNil_poly.comp halfRem_poly

/-- The parity test "an odd number of messages" of the layout. -/
theorem odd_poly : PolyTimeComputable fun w =>
    [decide (¬ (fun v => pairSndD (pairSndD v))^[halfCount (argM w)] (argM w) = [])] :=
  ptc_congr (not_poly even_poly) fun w => by simp only [decide_not]

/-- The remainder of the half loop on `encodeMsgs hist` (after `|hist| / 2` rounds) is empty iff
`|hist|` is even. -/
theorem halfRem_nil_iff (hist : List (List Bool)) :
    (fun v => pairSndD (pairSndD v))^[hist.length / 2] (Strategy.encodeMsgs hist) = [] ↔
      hist.length % 2 = 0 := by
  rw [iterate_sndD_two_encodeMsgs, encodeMsgs_eq_nil_iff, List.drop_eq_nil_iff]
  omega

/-- The remainder of the half loop on `encodeMsgs hist` is nonempty iff `|hist|` is odd. -/
theorem halfRem_ne_nil_iff (hist : List (List Bool)) :
    (¬ (fun v => pairSndD (pairSndD v))^[hist.length / 2] (Strategy.encodeMsgs hist) = []) ↔
      hist.length % 2 = 1 := by
  rw [halfRem_nil_iff]
  omega

/-- The coin block of the current iteration of the `|x|`-fold graph isomorphism prover:
`coinSlice ((|x|+1)²) (|hist| / 2) r`. -/
theorem giSlice_poly : PolyTimeComputable fun w =>
    coinSlice (giBlock.eval (NUPPT.inParam w).length) (halfCount (argM w)) (NUPPT.inCoins w) :=
  ptc_congr (coinSlice_poly giBlock NUPPT.polyTimeComputable_inParam halfCnt_poly
    NUPPT.polyTimeComputable_inCoins) fun w => by simp

/-- The first bit of the last message of the layout's history. -/
theorem lastBit_poly : PolyTimeComputable fun w =>
    [(pairFstD (pairSndD^[lastSteps (argM w)] (argM w))).headD false] :=
  headBit_poly.comp (lastMsg_poly.comp argM_poly)

/-- The prover of the `|x|`-fold graph isomorphism protocol is a PPT strategy (Inf-4.2).

**Proof sketch.** `efficient_of_polyTime`: the half count `|hist| / 2` and the parity by the
half loop (`halfLoop_poly`), the coin block of the current iteration (`giSlice_poly`), the
sampled permutation (`sampleStr_poly`), the graph message by `relabel_poly` and the reply by
`mulInvStr_poly` or the identity according to the first bit of the last message
(`lastMsg_poly`); the equation with `giProverRep.next` is `halfCount_encodeMsgs`,
`halfRem_nil_iff` and `lastMsg_encodeMsgs`. -/
theorem giProverRep_efficient : giProverRep.Efficient := by
  have hπ : PolyTimeComputable fun w => sampleStr (pairFstD (argX w))
      (coinSlice (giBlock.eval (NUPPT.inParam w).length) (halfCount (argM w)) (NUPPT.inCoins w)) :=
    ptc_congr (sampleStr_poly.comp (w₀_poly.pairEncode giSlice_poly)) fun w => by simp
  have heven := relabel_poly w₀_poly hπ
  have hmul : PolyTimeComputable fun w => mulInvStr (sampleStr (pairFstD (argX w))
      (coinSlice (giBlock.eval (NUPPT.inParam w).length) (halfCount (argM w)) (NUPPT.inCoins w))) (argZ w) :=
    ptc_congr (mulInvStr_poly.comp (hπ.pairEncode argZ_poly)) fun w => by simp
  have hodd := polyTimeComputable_ite lastBit_poly hmul hπ
  refine efficient_of_polyTime giProverRep (polyTimeComputable_ite even_poly heven hodd) ?_
  intro x z r hist
  show (if hist.length % 2 = 0 then _ else _) = _
  simp only [argM_ilayout, halfCount_encodeMsgs, halfRem_nil_iff, inParam_ilayout, List.length_replicate,
    inCoins_ilayout, argX_ilayout, argZ_ilayout, vcount_ilayout, giBlock_eval, decide_eq_true_eq,
    lastMsg_encodeMsgs]
  by_cases hev : hist.length % 2 = 0
  · rw [if_pos hev, if_pos hev, relabelAt_replicate, sampleStr, decPerm_encPerm]
    rfl
  · rw [if_neg hev, if_neg hev, sampleStr, mulInvStr_encPerm]
    split_ifs <;> rfl

/-! ### The verifier of the `|x|`-fold graph isomorphism protocol -/

/-- The test `|hist| < 2|x|` (the iterations are not over). -/
theorem ltLen2_poly : PolyTimeComputable fun w =>
    [decide (msgCount (argM w) < (PolyExpr.mul (.const 2) .var).eval (NUPPT.inParam w).length)] := by
  refine ptc_congr (not_poly (lenLe_comp cnt_poly
    (unaryPoly_comp (.mul (.const 2) .var) NUPPT.polyTimeComputable_inParam))) fun w => ?_
  simp only [List.length_replicate]
  exact congrArg (fun b => [b]) (by rw [← decide_not]; exact decide_eq_decide.2 not_le.symm)

/-- The challenge of the `|x|`-fold graph isomorphism verifier: coin `|hist| / 2`. -/
theorem challenge_poly : PolyTimeComputable fun w =>
    [((NUPPT.inCoins w).drop (halfCount (argM w))).headD false] :=
  ptc_congr (headBit_poly.comp ((polyTimeComputable_pairDropPoly .var).comp
    (halfCnt_poly.pairEncode NUPPT.polyTimeComputable_inCoins))) fun w => by simp

/-- One round of the verdict scan of the `|x|`-fold graph isomorphism verifier, on the state
word `⟨x₀, ⟨S, ⟨remMsgs, ⟨remCoins, [bit]⟩⟩⟩⟩` with the static data `S = ⟨1^n, x⟩`: peel two
messages `H, γ`, drop one coin `b`, and conjoin the check `γ(G_b) = H`. -/
noncomputable def giStep (st : List Bool) : List Bool :=
  pairEncode (pairFstD (pairSndD st))
    (pairEncode (pairSndD (pairSndD (pairFstD (pairSndD (pairSndD st)))))
      (pairEncode (pairFstD (pairSndD (pairSndD (pairSndD st)))).tail
        [(pairSndD (pairSndD (pairSndD (pairSndD st)))).headD false &&
          decide (relabelAt (pairFstD (pairFstD (pairSndD st)))
            (if (pairFstD (pairSndD (pairSndD (pairSndD st)))).headD false then
              pairSndD (pairSndD (pairFstD (pairSndD st))) else pairFstD (pairSndD (pairFstD (pairSndD st))))
            (pairFstD (pairSndD (pairFstD (pairSndD (pairSndD st))))) =
              pairFstD (pairFstD (pairSndD (pairSndD st))))]))

/-- The scan round is polynomial-time.

**Proof sketch.** Projections of the state word, `relabelAt_poly` on `⟨1^n, ⟨G_b, γ⟩⟩` with
`G_b` selected by `polyTimeComputable_ite` on the first coin, the comparison with `H` by
`polyTimeComputable_pairEq`, and the conjunction with the carried bit
(`polyTimeComputable_and`). -/
theorem giStep_poly : PolyTimeComputable giStep := by
  have hS : PolyTimeComputable fun st => pairFstD (pairSndD st) :=
    polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD
  have hM : PolyTimeComputable fun st => pairFstD (pairSndD (pairSndD st)) :=
    polyTimeComputable_pairFstD.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)
  have hC : PolyTimeComputable fun st => pairFstD (pairSndD (pairSndD (pairSndD st))) :=
    polyTimeComputable_pairFstD.comp (polyTimeComputable_pairSndD.comp
      (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD))
  have hB : PolyTimeComputable fun st => pairSndD (pairSndD (pairSndD (pairSndD st))) :=
    polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp
      (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD))
  have hsel : PolyTimeComputable fun st =>
      if (pairFstD (pairSndD (pairSndD (pairSndD st)))).headD false then
        pairSndD (pairSndD (pairFstD (pairSndD st))) else pairFstD (pairSndD (pairFstD (pairSndD st))) :=
    polyTimeComputable_ite (headBit_poly.comp hC)
      (polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp hS))
      (polyTimeComputable_pairFstD.comp (polyTimeComputable_pairSndD.comp hS))
  have hcheck : PolyTimeComputable fun st => [decide (relabelAt (pairFstD (pairFstD (pairSndD st)))
      (if (pairFstD (pairSndD (pairSndD (pairSndD st)))).headD false then
        pairSndD (pairSndD (pairFstD (pairSndD st))) else pairFstD (pairSndD (pairFstD (pairSndD st))))
      (pairFstD (pairSndD (pairFstD (pairSndD (pairSndD st))))) = pairFstD (pairFstD (pairSndD (pairSndD st))))] :=
    ptc_congr (polyTimeComputable_pairEq.comp ((relabelAt_poly.comp
      ((polyTimeComputable_pairFstD.comp hS).pairEncode
        (hsel.pairEncode (polyTimeComputable_pairFstD.comp (polyTimeComputable_pairSndD.comp hM))))).pairEncode
      (polyTimeComputable_pairFstD.comp hM))) fun st => by simp
  exact hS.pairEncode ((polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp hM)).pairEncode
    ((tail_poly.comp hC).pairEncode (polyTimeComputable_and (headBit_poly.comp hB) hcheck)))

/-- The scan after `k` rounds from the input `⟨u, ⟨S, ⟨M, ⟨R, [b]⟩⟩⟩⟩`: the static data, the
remaining messages (two peeled per round), the remaining coins and the conjunction of the first
`k` checks with the initial bit `b`. -/
theorem giIter_eq (u S M R : List Bool) (b : Bool) (k : ℕ) :
    (fun s => giStep (pairEncode (pairEncode u (pairEncode S (pairEncode M (pairEncode R [b])))) s))^[k]
        (pairSndD (pairEncode u (pairEncode S (pairEncode M (pairEncode R [b]))))) =
      pairEncode S (pairEncode ((fun v => pairSndD (pairSndD v))^[k] M) (pairEncode (R.drop k)
        [b && decide (∀ j < k, relabelAt (pairFstD S)
          (if (R.drop j).headD false then pairSndD (pairSndD S) else pairFstD (pairSndD S))
          (pairFstD (pairSndD ((fun v => pairSndD (pairSndD v))^[j] M))) =
            pairFstD ((fun v => pairSndD (pairSndD v))^[j] M))])) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [giStep, pairFstD_pairEncode, pairSndD_pairEncode, List.headD_cons, List.tail_drop,
      Function.iterate_succ_apply', Nat.forall_lt_succ_right, Bool.decide_and, Bool.and_assoc]

/-- The scan from an arbitrary input has, after at least one round, the shape of `giIter_eq`
with the components read off the input (the bit being unspecified).

**Proof sketch.** Induction on the number of rounds: the first round reads the components off
the input word; every later round peels two messages, drops one coin and keeps the static
data (`List.tail_drop`, `Function.iterate_succ_apply'`). -/
theorem giIter_shape (x₀ : List Bool) (k : ℕ) (hk : 1 ≤ k) :
    ∃ b : Bool, (fun s => giStep (pairEncode x₀ s))^[k] (pairSndD x₀) =
      pairEncode (pairFstD (pairSndD x₀))
        (pairEncode ((fun v => pairSndD (pairSndD v))^[k] (pairFstD (pairSndD (pairSndD x₀))))
          (pairEncode ((pairFstD (pairSndD (pairSndD (pairSndD x₀)))).drop k) [b])) := by
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · exact ⟨(pairSndD (pairSndD (pairSndD (pairSndD x₀)))).headD false &&
        decide (relabelAt (pairFstD (pairFstD (pairSndD x₀)))
          (if (pairFstD (pairSndD (pairSndD (pairSndD x₀)))).headD false then
            pairSndD (pairSndD (pairFstD (pairSndD x₀))) else pairFstD (pairSndD (pairFstD (pairSndD x₀))))
          (pairFstD (pairSndD (pairFstD (pairSndD (pairSndD x₀))))) = pairFstD (pairFstD (pairSndD (pairSndD x₀)))),
        by simp only [Nat.zero_add, Function.iterate_one, giStep, pairSndD_pairEncode, List.drop_one]⟩
    · obtain ⟨b, hb⟩ := ih hpos
      refine ⟨b && decide (relabelAt (pairFstD (pairFstD (pairSndD x₀)))
        (if ((pairFstD (pairSndD (pairSndD (pairSndD x₀)))).drop k).headD false then
          pairSndD (pairSndD (pairFstD (pairSndD x₀))) else pairFstD (pairSndD (pairFstD (pairSndD x₀))))
        (pairFstD (pairSndD ((fun v => pairSndD (pairSndD v))^[k] (pairFstD (pairSndD (pairSndD x₀)))))) =
          pairFstD ((fun v => pairSndD (pairSndD v))^[k] (pairFstD (pairSndD (pairSndD x₀))))), ?_⟩
      rw [Function.iterate_succ_apply', hb]
      simp only [giStep, pairFstD_pairEncode, pairSndD_pairEncode, List.tail_drop,
        Function.iterate_succ_apply', List.headD_cons]

/-- The scan states are bounded by `6|x₀| + 7`.

**Proof sketch.** Round `0` is `pairSndD x₀`; afterwards the shape `giIter_shape` has three
components (`static`, remaining messages, remaining coins), each no longer than `x₀`
(`length_pairFstD_le`, `length_pairSndD_le`, `List.length_drop`), and one bit. -/
theorem giIter_bound (x₀ : List Bool) (k : ℕ) :
    ((fun s => giStep (pairEncode x₀ s))^[k] (pairSndD x₀)).length ≤
      (PolyExpr.add (.mul (.const 6) .var) (.const 7)).eval x₀.length := by
  simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have := length_pairSndD_le x₀
    simp only [Function.iterate_zero, id]
    omega
  · obtain ⟨b, hb⟩ := giIter_shape x₀ k hk
    rw [hb, length_pairEncode, length_pairEncode, length_pairEncode, List.length_singleton]
    have h0 : (pairFstD (pairSndD x₀)).length ≤ x₀.length :=
      (length_pairFstD_le _).trans (length_pairSndD_le _)
    have h1 := length_iterate_le (fun w => (length_pairSndD_le _).trans (length_pairSndD_le w))
      (pairFstD (pairSndD (pairSndD x₀))) k
    have h2 : (pairFstD (pairSndD (pairSndD x₀))).length ≤ x₀.length :=
      (length_pairFstD_le _).trans ((length_pairSndD_le _).trans (length_pairSndD_le _))
    have h3 : ((pairFstD (pairSndD (pairSndD (pairSndD x₀)))).drop k).length ≤ x₀.length := by
      rw [List.length_drop]
      exact (Nat.sub_le _ _).trans ((length_pairFstD_le _).trans
        ((length_pairSndD_le _).trans ((length_pairSndD_le _).trans (length_pairSndD_le _))))
    omega

/-- The verdict scan of the `|x|`-fold graph isomorphism verifier is polynomial-time: the
one-bit word `[decide (∀ j < |x|, γ_j(G_{b_j}) = H_j)]` (`iterUnary_poly` on `giStep` from
`⟨1^{|x|}, ⟨⟨1^n, x⟩, ⟨msgs, ⟨r, [true]⟩⟩⟩⟩`, closed form `giIter_eq`). -/
theorem giScan_poly : PolyTimeComputable fun w =>
    [decide (∀ j < (NUPPT.inParam w).length, relabelAt (List.replicate (vcount w) true)
      (if ((NUPPT.inCoins w).drop j).headD false then pairSndD (argX w) else pairFstD (argX w))
      (pairFstD (pairSndD ((fun v => pairSndD (pairSndD v))^[j] (argM w)))) =
        pairFstD ((fun v => pairSndD (pairSndD v))^[j] (argM w)))] := by
  have hx₀ : PolyTimeComputable fun w => pairEncode (NUPPT.inParam w)
      (pairEncode (pairEncode (List.replicate (vcount w) true) (argX w))
        (pairEncode (argM w) (pairEncode (NUPPT.inCoins w) [true]))) :=
    NUPPT.polyTimeComputable_inParam.pairEncode ((vcount_poly.pairEncode argX_poly).pairEncode
      (argM_poly.pairEncode (NUPPT.polyTimeComputable_inCoins.pairEncode (polyTimeComputable_const [true]))))
  have h := (polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)).comp
    ((iterUnary_poly giStep_poly _ (fun x₀ k _ => giIter_bound x₀ k)).comp hx₀)
  refine ptc_congr h fun w => ?_
  simp only [Function.comp_apply, pairFstD_pairEncode]
  rw [giIter_eq, pairSndD_pairEncode, pairSndD_pairEncode, pairSndD_pairEncode, Bool.true_and,
    pairFstD_pairEncode, pairSndD_pairEncode]

/-- The verdict condition of the `|x|`-fold graph isomorphism verifier, read through the scan:
messages `2j` and `2j+1` are the two components of `(pairSndD ∘ pairSndD)^[j] msgs`, coin `j` is
the first bit of `r.drop j`, and `relabelAt` is `encGraph (γ(G_b))`. -/
theorem gi_verdict_iff (x : List Bool) (hist : List (List Bool)) (r : List Bool) (N : ℕ) :
    (∀ j : Fin N, encGraph (permGraph (if r.getD j false then instanceG₁ x else instanceG₀ x)
        (decPerm (instanceVertexCount x) (hist.getD (2 * j + 1) []))) = hist.getD (2 * j) []) ↔
      ∀ j < N, relabelAt (List.replicate (Nat.sqrt (pairFstD x).length) true)
        (if (r.drop j).headD false then pairSndD x else pairFstD x)
        (pairFstD (pairSndD ((fun v => pairSndD (pairSndD v))^[j] (Strategy.encodeMsgs hist)))) =
          pairFstD ((fun v => pairSndD (pairSndD v))^[j] (Strategy.encodeMsgs hist)) := by
  rw [Fin.forall_iff]
  refine forall_congr' fun j => forall_congr' fun _ => ?_
  rw [Fin.val_mk, iterate_sndD_two_encodeMsgs, pairSndD_encodeMsgs, Strategy.pairFstD_encodeMsgs,
    Strategy.pairFstD_encodeMsgs, List.drop_drop, relabelAt_replicate, ← getD_eq_headD_drop,
    ← getD_eq_headD_drop, ← getD_eq_headD_drop]
  cases r.getD j false <;> exact Iff.rfl

/-- The verifier of the `|x|`-fold graph isomorphism protocol is a PPT strategy (Inf-4.2).

**Proof sketch.** `efficient_of_polyTime`: the parity of the message count (`odd_poly`), the
challenge `r_{|hist|/2}` (`challenge_poly`), the test `|hist| < 2|x|` (`ltLen2_poly`), and the
well-formedness test conjoined with the verdict scan (`giScan_poly`); the equation with
`giVerifierRep.next` is `halfRem_ne_nil_iff`, `halfCount_encodeMsgs`, `msgCount_encodeMsgs` and
`gi_verdict_iff`. -/
theorem giVerifierRep_efficient : giVerifierRep.Efficient := by
  have hwf : PolyTimeComputable fun w => [wellFormedInstance (argX w)] := wellFormed_poly.comp argX_poly
  have hverdict := polyTimeComputable_and hwf giScan_poly
  have hF := polyTimeComputable_ite odd_poly challenge_poly
    (polyTimeComputable_ite ltLen2_poly (polyTimeComputable_const []) hverdict)
  refine efficient_of_polyTime giVerifierRep hF ?_
  intro x z r hist
  show (if hist.length % 2 = 1 then _ else if hist.length < 2 * x.length then _ else _) = _
  simp only [argM_ilayout, halfCount_encodeMsgs, halfRem_ne_nil_iff, msgCount_encodeMsgs, inParam_ilayout,
    List.length_replicate, inCoins_ilayout, argX_ilayout, vcount_ilayout, PolyExpr.eval_mul,
    PolyExpr.eval_const, PolyExpr.eval_var, decide_eq_true_eq]
  by_cases hodd : hist.length % 2 = 1
  · rw [if_pos hodd, if_pos hodd, getD_eq_headD_drop]
  · rw [if_neg hodd, if_neg hodd]
    by_cases hlt : hist.length < 2 * x.length
    · rw [if_pos hlt, if_pos hlt]
    · rw [if_neg hlt, if_neg hlt, Bool.decide_and, Bool.decide_eq_true]
      congr 2
      exact decide_eq_decide.2 (gi_verdict_iff x hist r x.length)

end TCSlib.Cryptography.GI
