/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.EfficiencyRep
import TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.Machines

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Polynomial-time operations for sequential repetition

The next-message machines for the sequential repetition construction use unary arithmetic,
encoded-history slices, and one activation of an efficient strategy. The registered iteration
hosts and the existing graph-protocol machines provide these operations.

## Main definitions

## Main results

* `SeqEfficiency.take_encodeMsgs`: recover a prefix of an encoded message history by a bit cut.
* `SeqEfficiency.takeMsgs_poly`: the encoded-history prefix cut is polynomial-time.
* `SeqEfficiency.phase_poly`, `phase_efficient`: an efficient strategy gives efficient phase moves.
* `SeqEfficiency.verdict_poly`, `verifier_efficient`: all-phase verdicts and repeated verification
  are efficient.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Theorem 175.1, efficiency of sequential repetition.
-/

namespace TCSlib.Cryptography.Composability.SeqEfficiency

open Complexity Turing

/-- For a history `hist` and count `c`, cutting its encoding immediately before the encoding
of `hist.drop c` gives `Strategy.encodeMsgs (hist.take c)`.
`(Strategy.encodeMsgs hist).take ((Strategy.encodeMsgs hist).length - (pairSndD^[c]
(Strategy.encodeMsgs hist)).length) = Strategy.encodeMsgs (hist.take c)`. -/
theorem take_encodeMsgs (hist : List (List Bool)) (c : ℕ) :
    (Strategy.encodeMsgs hist).take ((Strategy.encodeMsgs hist).length -
      (pairSndD^[c] (Strategy.encodeMsgs hist)).length) = Strategy.encodeMsgs (hist.take c) := by
  rw [GI.iterate_pairSndD_encodeMsgs]
  have h := congrArg Strategy.encodeMsgs (List.take_append_drop c hist)
  rw [CommitmentLemmas.encodeMsgs_append] at h
  rw [← h]
  simp only [List.length_append, Nat.add_sub_cancel_right, List.take_left]

/-- For polynomial-time `M` and a unary polynomial-time count `c`, the word
`(M w).take ((M w).length - (pairSndD^[c w] (M w)).length)` is polynomial-time. On an
encoded history it is the encoding of the first `c w` messages (`take_encodeMsgs`).
`PolyTimeComputable fun w => (M w).take ((M w).length - (pairSndD^[c w] (M w)).length)`. -/
theorem takeMsgs_poly {M : List Bool → List Bool} (hM : PolyTimeComputable M)
    {c : List Bool → ℕ} (hc : PolyTimeComputable fun w => List.replicate (c w) true) :
    PolyTimeComputable fun w =>
      (M w).take ((M w).length - (pairSndD^[c w] (M w)).length) :=
  EncodingMachines.truncate_poly hM
    (EncodingMachines.unarySub_poly (EncodingMachines.unaryLength_poly hM)
      (EncodingMachines.unaryLength_poly (ColMachines.iterSnd_poly hM hc)))

/-- If `P` is efficient, a polynomial-time word function computes the padded phase message
on every interactive layout. For `g = if previousFirst then 2|hist|-1 else 2|hist|` and
`j = g / (2k(|x|))`, the message is `P.next x z (coinBlock (P.coinLen |x|) j r)
(hist.drop (j*k(|x|)))` when `g % (2k(|x|)) < k(|x|)`, and `[]` otherwise.
[PS10, Theorem 175.1, efficiency of a repeated party].

**Proof sketch.** Recover the history length in unary, compute its move index, phase and
position using the existing unary arithmetic machines, and drop the earlier encoded messages.
Slice the random tape with the existing coin-block machine. Assemble the original strategy's
machine layout and run its polynomial-time output function; a conditional emits `[]` in a
filler position. All malformed word inputs are handled by the existing total projections.
The equation on actual layouts follows from the published message-count and suffix readers. -/
theorem phase_poly (P : Strategy) (k : PolyExpr) (previousFirst : Bool) (hP : P.Efficient) :
    ∃ F : List Bool → List Bool, PolyTimeComputable F ∧
      ∀ (x z r : List Bool) (hist : List (List Bool)),
      let g := if previousFirst then 2 * hist.length - 1 else 2 * hist.length
      let j := g / (2 * k.eval x.length)
      F (GI.ilayout x z hist r) =
        if g % (2 * k.eval x.length) < k.eval x.length then
          P.next x z (coinBlock (P.coinLen x.length) j r)
            (hist.drop (j * k.eval x.length))
        else [] := by
  obtain ⟨A, hA, _, hnext⟩ := (Strategy.efficient_iff P).1 hP
  let K : List Bool → ℕ := fun w => k.eval (GI.argX w).length
  let index : List Bool → ℕ := fun w =>
    if previousFirst then 2 * GI.msgCount (GI.argM w) - 1
    else 2 * GI.msgCount (GI.argM w)
  let phase : List Bool → ℕ := fun w => index w / (2 * K w)
  -- The index and phase are computed entirely by the unary arithmetic toolkit.
  have hK : PolyTimeComputable fun w => List.replicate (K w) true :=
    EncodingMachines.unaryPolyOf_poly k (EncodingMachines.unaryLength_poly GI.argX_poly)
  have hdouble := EncodingMachines.unaryMul_poly (EncodingMachines.unaryConst_poly 2)
    GI.cnt_poly
  have hindex : PolyTimeComputable fun w => List.replicate (index w) true := by
    cases previousFirst
    · exact hdouble
    · exact EncodingMachines.unarySub_poly hdouble (EncodingMachines.unaryConst_poly 1)
  have hden := EncodingMachines.unaryMul_poly (EncodingMachines.unaryConst_poly 2) hK
  have hphase : PolyTimeComputable fun w => List.replicate (phase w) true := by
    simpa only [EncodingMachines.divNum_eq] using EncodingMachines.divNum_poly hindex hden
  have hmod : PolyTimeComputable fun w => List.replicate (index w % (2 * K w)) true := by
    simpa only [EncodingMachines.modNum_eq] using EncodingMachines.modNum_poly hindex hden
  have htest := EncodingMachines.ltTest_poly hmod hK
  -- Reuse the encoded-list iteration and the coin slicing machines.
  have hdrop := ColMachines.iterSnd_poly GI.argM_poly
    (EncodingMachines.unaryMul_poly hphase hK)
  have hcoins : PolyTimeComputable fun w =>
      coinBlock (P.coins.eval (GI.argX w).length) (phase w) (NUPPT.inCoins w) := by
    simpa only [List.length_replicate] using
      GI.coinSlice_poly P.coins GI.argX_poly hphase NUPPT.polyTimeComputable_inCoins
  have hlay := NUPPT.polyTimeComputable_layout
    (EncodingMachines.unaryLength_poly GI.argX_poly)
    ((GI.argX_poly.pairEncode GI.argZ_poly).pairEncode hdrop)
    (polyTimeComputable_const []) hcoins
  let F : List Bool → List Bool := fun w =>
    if index w % (2 * K w) < K w then
      A.output (NUPPT.layout (List.replicate (GI.argX w).length true)
        (pairEncode (pairEncode (GI.argX w) (GI.argZ w))
          (pairSndD^[phase w * K w] (GI.argM w))) []
        (coinBlock (P.coins.eval (GI.argX w).length) (phase w) (NUPPT.inCoins w)))
    else []
  have hF : PolyTimeComputable F := by
    simpa only [decide_eq_true_eq] using
      polyTimeComputable_ite htest (A.polyTimeComputable_output.comp hlay)
        (polyTimeComputable_const [])
  refine ⟨F, hF, ?_⟩
  intro x z r hist
  dsimp only [F, phase, index, K]
  simp only [GI.argX_ilayout, GI.argZ_ilayout, GI.argM_ilayout, GI.inCoins_ilayout,
    GI.msgCount_encodeMsgs, GI.iterate_pairSndD_encodeMsgs]
  rw [hnext, Strategy.ofNUPPT_next, NUPPT.runAtL_eq_output_layout, hA.advice_eq,
    Strategy.coinLen_eq]

/-- For strategies `S, P`, a round polynomial `k` and orientation `previousFirst`, if `P`
is efficient and every message of `S` is the padded phase message of `P`, then `S.Efficient`.
The equation hypothesis uses `g = if previousFirst then 2|hist|-1 else 2|hist|` and
`j = g / (2k(|x|))`; no hypothesis on the random-tape polynomial of `S` is required.
[PS10, Theorem 175.1, efficiency of a repeated party]. -/
theorem phase_efficient (S P : Strategy) (k : PolyExpr) (previousFirst : Bool)
    (hP : P.Efficient)
    (hnext : ∀ (x z r : List Bool) (hist : List (List Bool)),
      let g := if previousFirst then 2 * hist.length - 1 else 2 * hist.length
      let j := g / (2 * k.eval x.length)
      S.next x z r hist =
        if g % (2 * k.eval x.length) < k.eval x.length then
          P.next x z (coinBlock (P.coinLen x.length) j r)
            (hist.drop (j * k.eval x.length))
        else []) : S.Efficient := by
  obtain ⟨F, hF, heq⟩ := phase_poly P k previousFirst hP
  apply GI.efficient_of_polyTime S hF
  intro x z r hist
  exact (hnext x z r hist).trans (heq x z r hist).symm

/-- If `V` is efficient, a polynomial-time word function computes `[true]` exactly when
all `Q(|x|)` phase verdicts are `[true]`. Phase `j` uses coin block `j` and the first
`p = if verifierFirst then k(|x|)/2 else (k(|x|)+1)/2` messages after the first `j*k(|x|)`
messages. [PS10, Theorem 175.1, efficiency of the repeated verifier].

**Proof sketch.** For a unary phase index, drop the earlier encoded messages and cut out the
real messages using `takeMsgs_poly`. Run the original verifier's uniform machine on that
history and the selected coin block. The published bounded first-index search finds the first
verdict different from `[true]`; its search bound is the unary polynomial `Q(|x|)`. The
output is `[true]` exactly when the search is exhausted. The empty search is exhausted too,
so the construction covers `Q(|x|) = 0` and `k(|x|) = 0`. -/
theorem verdict_poly (V : Strategy) (k Q : PolyExpr) (verifierFirst : Bool)
    (hV : V.Efficient) :
    ∃ F : List Bool → List Bool, PolyTimeComputable F ∧
      ∀ (x z r : List Bool) (hist : List (List Bool)),
      F (GI.ilayout x z hist r) =
        if ∀ j < Q.eval x.length,
          V.next x z (coinBlock (V.coinLen x.length) j r)
            ((hist.drop (j * k.eval x.length)).take
              (if verifierFirst then k.eval x.length / 2 else (k.eval x.length + 1) / 2)) =
                [true]
        then [true] else [false] := by
  classical
  obtain ⟨A, hA, _, hnext⟩ := (Strategy.efficient_iff V).1 hV
  let K : List Bool → ℕ := fun w => k.eval (GI.argX w).length
  let count : List Bool → ℕ := fun w =>
    if verifierFirst then K w / 2 else (K w + 1) / 2
  let act : List Bool → ℕ → List Bool := fun w j =>
    let M := pairSndD^[j * K w] (GI.argM w)
    A.output (NUPPT.layout (List.replicate (GI.argX w).length true)
      (pairEncode (pairEncode (GI.argX w) (GI.argZ w))
        (M.take (M.length - (pairSndD^[count w] M).length))) []
      (coinBlock (V.coins.eval (GI.argX w).length) j (NUPPT.inCoins w)))
  have hK : PolyTimeComputable fun w => List.replicate (K w) true :=
    EncodingMachines.unaryPolyOf_poly k (EncodingMachines.unaryLength_poly GI.argX_poly)
  have hcount : PolyTimeComputable fun w => List.replicate (count w) true := by
    cases verifierFirst
    · simpa only [EncodingMachines.divNum_eq] using EncodingMachines.divNum_poly
        (EncodingMachines.unaryAdd_poly hK (EncodingMachines.unaryConst_poly 1))
        (EncodingMachines.unaryConst_poly 2)
    · simpa only [EncodingMachines.divNum_eq] using
        EncodingMachines.divNum_poly hK (EncodingMachines.unaryConst_poly 2)
  -- The search test is one original verifier activation on a phase slice.
  have hX := GI.argX_poly.comp polyTimeComputable_pairSndD
  have hZ := GI.argZ_poly.comp polyTimeComputable_pairSndD
  have hR := NUPPT.polyTimeComputable_inCoins.comp polyTimeComputable_pairSndD
  have hJ := EncodingMachines.unaryLength_poly polyTimeComputable_pairFstD
  have hdrop := ColMachines.iterSnd_poly (GI.argM_poly.comp polyTimeComputable_pairSndD)
    (EncodingMachines.unaryMul_poly hJ (hK.comp polyTimeComputable_pairSndD))
  have htake := takeMsgs_poly hdrop (hcount.comp polyTimeComputable_pairSndD)
  have hcoins : PolyTimeComputable fun w =>
      coinBlock (V.coins.eval (GI.argX (pairSndD w)).length) (pairFstD w).length
        (NUPPT.inCoins (pairSndD w)) :=
    GI.coinSlice_poly V.coins hX polyTimeComputable_pairFstD hR
  have hact : PolyTimeComputable fun w => act (pairSndD w) (pairFstD w).length :=
    A.polyTimeComputable_output.comp (NUPPT.polyTimeComputable_layout
      (EncodingMachines.unaryLength_poly hX)
      ((hX.pairEncode hZ).pairEncode htake) (polyTimeComputable_const []) hcoins)
  have heq : PolyTimeComputable fun w =>
      [decide (act (pairSndD w) (pairFstD w).length = [true])] := by
    refine (polyTimeComputable_pairEq.comp
      (hact.pairEncode (polyTimeComputable_const [true]))).congr fun w => ?_
    rw [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  have hbad : PolyTimeComputable fun w =>
      [decide (act (pairSndD w) (pairFstD w).length ≠ [true])] := by
    simpa only [decide_not] using polyTimeComputable_not heq
  have hQ := EncodingMachines.unaryPolyOf_poly Q
    (EncodingMachines.unaryLength_poly GI.argX_poly)
  have hfirst := EncodingMachines.polyTimeComputable_firstIdx
    (p := fun w j => decide (act w j ≠ [true])) hbad hQ
  let F : List Bool → List Bool := fun w =>
    if EncodingMachines.firstIdx (fun j => decide (act w j ≠ [true]))
        (Q.eval (GI.argX w).length) = Q.eval (GI.argX w).length
    then [true] else [false]
  have hF : PolyTimeComputable F := by
    simpa only [decide_eq_true_eq] using polyTimeComputable_ite
      (EncodingMachines.eqTest_poly hfirst hQ)
      (polyTimeComputable_const [true]) (polyTimeComputable_const [false])
  -- On an actual layout, all operations are read through published equations.
  have hact_eq : ∀ x z r hist j, act (GI.ilayout x z hist r) j =
      V.next x z (coinBlock (V.coinLen x.length) j r)
        ((hist.drop (j * k.eval x.length)).take
          (if verifierFirst then k.eval x.length / 2 else (k.eval x.length + 1) / 2)) := by
    intro x z r hist j
    dsimp only [act, K, count]
    simp only [GI.argX_ilayout, GI.argZ_ilayout, GI.argM_ilayout, GI.inCoins_ilayout]
    rw [GI.iterate_pairSndD_encodeMsgs (j * k.eval x.length) hist, take_encodeMsgs]
    rw [hnext, Strategy.ofNUPPT_next, NUPPT.runAtL_eq_output_layout, hA.advice_eq,
      Strategy.coinLen_eq]
  refine ⟨F, hF, ?_⟩
  intro x z r hist
  dsimp only [F]
  rw [GI.argX_ilayout]
  have he : (EncodingMachines.firstIdx
      (fun j => decide (act (GI.ilayout x z hist r) j ≠ [true])) (Q.eval x.length) =
        Q.eval x.length) ↔
      ∀ j < Q.eval x.length,
        V.next x z (coinBlock (V.coinLen x.length) j r)
          ((hist.drop (j * k.eval x.length)).take
            (if verifierFirst then k.eval x.length / 2 else (k.eval x.length + 1) / 2)) =
              [true] := by
    rw [EncodingMachines.firstIdx_eq_iff]
    simp only [decide_eq_false_iff_not, not_not, hact_eq]
  simp only [he]

/-- For strategies `S, V`, round/count polynomials `k, Q` and an orientation `verifierFirst`,
if `V` is efficient and `S` computes the repeated terminal verdict when `|hist| = Q(|x|)k(|x|)`
and the padded phase message otherwise, then `S.Efficient`.
The terminal verdict is `[true]` iff every phase's original verdict is `[true]`.
[PS10, Theorem 175.1, efficiency of the repeated verifier].

**Proof sketch.** Use `phase_poly` for the nonterminal branch and `verdict_poly` for the
terminal branch. The branch test compares the encoded history's unary message count with
the unary product `Q(|x|)k(|x|)`. The polynomial-time conditional computes `S` on every actual
interactive layout, so `GI.efficient_of_polyTime` supplies its uniform machine. -/
theorem verifier_efficient (S V : Strategy) (k Q : PolyExpr) (verifierFirst : Bool)
    (hV : V.Efficient)
    (hnext : ∀ (x z r : List Bool) (hist : List (List Bool)),
      let g := if verifierFirst then 2 * hist.length else 2 * hist.length - 1
      let j := g / (2 * k.eval x.length)
      S.next x z r hist =
        if hist.length = Q.eval x.length * k.eval x.length then
          if ∀ i < Q.eval x.length,
            V.next x z (coinBlock (V.coinLen x.length) i r)
              ((hist.drop (i * k.eval x.length)).take
                (if verifierFirst then k.eval x.length / 2 else (k.eval x.length + 1) / 2)) =
                  [true]
          then [true] else [false]
        else if g % (2 * k.eval x.length) < k.eval x.length then
          V.next x z (coinBlock (V.coinLen x.length) j r)
            (hist.drop (j * k.eval x.length))
        else []) : S.Efficient := by
  classical
  obtain ⟨Fp, hFp, hep⟩ := phase_poly V k (!verifierFirst) hV
  obtain ⟨Fv, hFv, hev⟩ := verdict_poly V k Q verifierFirst hV
  have hQ := EncodingMachines.unaryPolyOf_poly Q
    (EncodingMachines.unaryLength_poly GI.argX_poly)
  have hk := EncodingMachines.unaryPolyOf_poly k
    (EncodingMachines.unaryLength_poly GI.argX_poly)
  let F : List Bool → List Bool := fun w =>
    if GI.msgCount (GI.argM w) = Q.eval (GI.argX w).length * k.eval (GI.argX w).length
    then Fv w else Fp w
  have hF : PolyTimeComputable F := by
    simpa only [decide_eq_true_eq] using polyTimeComputable_ite
      (EncodingMachines.eqTest_poly GI.cnt_poly (EncodingMachines.unaryMul_poly hQ hk))
      hFv hFp
  apply GI.efficient_of_polyTime S hF
  intro x z r hist
  dsimp only [F]
  rw [GI.argM_ilayout, GI.msgCount_encodeMsgs, GI.argX_ilayout, hep, hev, hnext]
  cases verifierFirst <;> rfl

end TCSlib.Cryptography.Composability.SeqEfficiency
