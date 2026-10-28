/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.Efficiency

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The graph protocols: efficiency of the repeated parties

The loop infrastructure for the polynomial-time machines behind the `|x|`-fold parties of
[PS10, Protocols 118.3 and 120.6] (inventory item Inf-4.2), and the machine of the
`|x|`-fold graph non-isomorphism verifier `gniVerifierRep`, proved for the shadow strategies
of `GraphIsomorphism/Proofs.lean` (the `|x|`-fold graph isomorphism parties are in
`GraphIsomorphism/EfficiencyRepGI.lean`). The repeated parties read the
*number* of messages received (to select the coin block of the current iteration and to
decide whether the protocol is over), the parity of that number and the last message
received, and the verifiers' verdicts scan the `|x|` iterations. All of these are **peeling
loops** over the nested-pair encoding `encodeMsgs hist = ⟨m₀, ⟨m₁, …⟩⟩` of the history
(`peelLoop_poly`: iterate a shrinking map until a test holds, counting the rounds in unary)
and one **unary-count loop** (`iterUnary_poly`: iterate a step `|u|` times for a unary count
`u` read from the input), both instances of the state-loop lemma `GI.stateFind`.

## Main definitions

* `TCSlib.Cryptography.GI.peelSteps` — the rounds of a peeling loop (with fuel).
* `TCSlib.Cryptography.GI.msgCount`, `GI.halfCount`, `GI.lastSteps` — the number of messages,
  half of it, and the rounds to the last message of an encoded history.

## Main results

* `TCSlib.Cryptography.GI.peelLoop_poly`, `GI.iterUnary_poly` — the two loop schemes.
* `TCSlib.Cryptography.GI.msgCount_poly`, `GI.halfLoop_poly`, `GI.lastMsg_poly` — the
  number of messages in unary, the half count with the remainder (parity), the last message.
* `TCSlib.Cryptography.GI.unaryMul_poly`, `GI.coinSlice_poly` — unary multiplication and the
  coin block of a given iteration.
* `TCSlib.Cryptography.GI.gniVerifierRep_efficient` — the `|x|`-fold graph non-isomorphism
  verifier is a PPT strategy.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§4.5 Interactive proofs, pp. 117–120.)
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Cambridge
  University Press, 2009. (§2.2, the class FP.)
-/

namespace TCSlib.Cryptography.GI

open Complexity Turing Complexity.StateLoop

/-! ### Peeling the nested-pair encoding -/

/-- The second component of a nonempty word is shorter than the word. -/
theorem length_pairSndD_lt {w : List Bool} (h : w ≠ []) : (pairSndD w).length < w.length := by
  cases hw : pairDecode w with
  | none =>
    simp only [pairSndD, hw, Option.map_none, Option.getD_none, List.length_nil]
    exact List.length_pos_of_ne_nil h
  | some ab =>
    obtain ⟨a, b⟩ := ab
    have hz := eq_pairEncode_of_pairDecode w a b hw
    subst hz
    rw [pairSndD_pairEncode, length_pairEncode]
    omega

/-- The second component of a word is no longer than the word. -/
theorem length_pairSndD_le (w : List Bool) : (pairSndD w).length ≤ w.length := by
  rcases eq_or_ne w [] with rfl | h
  · rfl
  · exact (length_pairSndD_lt h).le

/-- Iterating a length-non-increasing map never lengthens. -/
theorem length_iterate_le {f : List Bool → List Bool} (hle : ∀ w, (f w).length ≤ w.length)
    (w : List Bool) : ∀ k, (f^[k] w).length ≤ w.length
  | 0 => le_rfl
  | k + 1 => by
    rw [Function.iterate_succ_apply']
    exact (hle _).trans (length_iterate_le hle w k)

/-- Peeling the empty word gives the empty word. -/
theorem iterate_pairSndD_nil : ∀ k : ℕ, pairSndD^[k] [] = []
  | 0 => rfl
  | k + 1 => by rw [Function.iterate_succ_apply]; exact iterate_pairSndD_nil k

/-- Peeling the encoding of a history drops its first message. -/
theorem pairSndD_encodeMsgs (hist : List (List Bool)) :
    pairSndD (Strategy.encodeMsgs hist) = Strategy.encodeMsgs (hist.drop 1) := by
  cases hist with
  | nil => rfl
  | cons m h => rw [Strategy.encodeMsgs_cons, pairSndD_pairEncode, List.drop_succ_cons, List.drop_zero]

/-- Peeling the encoding of a history `k` times leaves the encoding of the history without its
first `k` messages. -/
theorem iterate_pairSndD_encodeMsgs : ∀ (k : ℕ) (hist : List (List Bool)),
    pairSndD^[k] (Strategy.encodeMsgs hist) = Strategy.encodeMsgs (hist.drop k)
  | 0, _ => rfl
  | k + 1, hist => by
    rw [Function.iterate_succ_apply, pairSndD_encodeMsgs, iterate_pairSndD_encodeMsgs k, List.drop_drop]
    congr 2
    omega

/-- The encoding of a history is empty exactly when the history is. -/
theorem encodeMsgs_eq_nil_iff (hist : List (List Bool)) : Strategy.encodeMsgs hist = [] ↔ hist = [] := by
  cases hist with
  | nil => simp
  | cons m h => simp [pairEncode_ne_nil]

/-- The rounds of a peeling loop, with fuel: `0` once `stop` holds, else one more than from
`f w`. -/
def peelStepsAux (f : List Bool → List Bool) (stop : List Bool → Bool) : ℕ → List Bool → ℕ
  | 0, _ => 0
  | n + 1, w => if stop w then 0 else peelStepsAux f stop n (f w) + 1

/-- The rounds of a peeling loop from `w` (fuel `|w| + 1`): the first round at which `stop`
holds along the orbit of `f`, provided `f` shortens every word that is not stopped. -/
def peelSteps (f : List Bool → List Bool) (stop : List Bool → Bool) (w : List Bool) : ℕ :=
  peelStepsAux f stop (w.length + 1) w

/-- With enough fuel the round count is the first round at which `stop` holds, and it is at
most `|w|`.

**Proof sketch.** Induction on the fuel: if `stop w` holds the count is `0`; otherwise `f w` is
shorter than `w` (`hdec`), the induction hypothesis applies to it, and the three clauses shift
by one round (`Function.iterate_succ_apply`). -/
theorem peelStepsAux_spec (f : List Bool → List Bool) (stop : List Bool → Bool)
    (hdec : ∀ w, stop w = false → (f w).length < w.length) :
    ∀ n w, w.length < n →
      (∀ k < peelStepsAux f stop n w, stop (f^[k] w) = false) ∧
        stop (f^[peelStepsAux f stop n w] w) = true ∧ peelStepsAux f stop n w ≤ w.length := by
  intro n
  induction n with
  | zero => intro w hw; omega
  | succ n ih =>
    intro w hw
    by_cases hs : stop w = true
    · simp only [peelStepsAux, hs, if_true]
      exact ⟨fun k hk => absurd hk (Nat.not_lt_zero _), by simpa using hs, Nat.zero_le _⟩
    · have hs' : stop w = false := by simpa using hs
      have hlt := hdec w hs'
      obtain ⟨h1, h2, h3⟩ := ih (f w) (by omega)
      simp only [peelStepsAux, hs', Bool.false_eq_true, if_false]
      refine ⟨fun k hk => ?_, ?_, by omega⟩
      · cases k with
        | zero => simpa using hs'
        | succ k => rw [Function.iterate_succ_apply]; exact h1 k (by omega)
      · rw [Function.iterate_succ_apply]; exact h2

/-- The specification of `peelSteps`. -/
theorem peelSteps_spec (f : List Bool → List Bool) (stop : List Bool → Bool)
    (hdec : ∀ w, stop w = false → (f w).length < w.length) (w : List Bool) :
    (∀ k < peelSteps f stop w, stop (f^[k] w) = false) ∧
      stop (f^[peelSteps f stop w] w) = true ∧ peelSteps f stop w ≤ w.length :=
  peelStepsAux_spec f stop hdec _ w (Nat.lt_succ_self _)

/-- `peelSteps` is the first round at which `stop` holds. -/
theorem peelSteps_eq (f : List Bool → List Bool) (stop : List Bool → Bool)
    (hdec : ∀ w, stop w = false → (f w).length < w.length) {w : List Bool} {k : ℕ}
    (hk : ∀ j < k, stop (f^[j] w) = false) (hk' : stop (f^[k] w) = true) :
    peelSteps f stop w = k := by
  obtain ⟨h1, h2, -⟩ := peelSteps_spec f stop hdec w
  rcases lt_trichotomy (peelSteps f stop w) k with h | h | h
  · have := hk _ h
    rw [h2] at this
    exact absurd this (by decide)
  · exact h
  · have := h1 _ h
    rw [hk'] at this
    exact absurd this (by decide)

/-- **Peeling loop:** iterate a length-non-increasing polynomial-time map `f` from `w` until
the polynomial-time test `stop` holds (within `|w|` rounds, as `f` shortens unstopped words),
returning the final word paired with the round count in unary.

**Proof sketch.** `stateFind` on the state `⟨rem, 1^k⟩` from `⟨w, []⟩` with the step
`⟨f rem, 1^{k+1}⟩`, the test `stop rem` and the output `⟨rem, 1^k⟩`; the orbit is
`⟨f^[k] w, 1^k⟩`, of length at most `3|w| + 2`, and `peelSteps_spec` gives the first round. -/
theorem peelLoop_poly {f : List Bool → List Bool} (hf : PolyTimeComputable f)
    (hle : ∀ w, (f w).length ≤ w.length) {stop : List Bool → Bool}
    (hstop : PolyTimeComputable fun w => [stop w])
    (hdec : ∀ w, stop w = false → (f w).length < w.length) :
    PolyTimeComputable fun w =>
      pairEncode (f^[peelSteps f stop w] w) (List.replicate (peelSteps f stop w) true) := by
  have horbit : ∀ (w : List Bool) (k : ℕ),
      orbit (fun w => pairEncode w [])
        (fun st => pairEncode (f (pairFstD (pairSndD st))) (true :: pairSndD (pairSndD st))) w k =
        pairEncode (f^[k] w) (List.replicate k true) := by
    intro w k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [orbit_succ, ih, pairSndD_pairEncode, pairFstD_pairEncode, pairSndD_pairEncode,
        Function.iterate_succ_apply', List.replicate_succ]
  have hstart : PolyTimeComputable fun w => pairEncode w [] :=
    polyTimeComputable_id.pairEncode (polyTimeComputable_const [])
  have hstep : PolyTimeComputable fun st =>
      pairEncode (f (pairFstD (pairSndD st))) (true :: pairSndD (pairSndD st)) :=
    (hf.comp (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD)).pairEncode
      ((cons_poly true).comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD))
  have hacc : PolyTimeComputable fun st => [stop (pairFstD (pairSndD st))] :=
    hstop.comp (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD)
  have h := stateFind hstart hstep hacc
    polyTimeComputable_pairSndD .var (.add (.mul (.const 3) .var) (.const 2)) (peelSteps f stop)
    (fun w => (peelSteps_spec f stop hdec w).2.2)
    (fun w k hk => by
      rw [horbit, length_pairEncode, List.length_replicate]
      have h1 := length_iterate_le hle w k
      have h2 := (peelSteps_spec f stop hdec w).2.2
      simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
      omega)
    (fun w k hk => by
      show stop (pairFstD (pairSndD (pairEncode w _))) = false
      rw [horbit, pairSndD_pairEncode, pairFstD_pairEncode]
      exact (peelSteps_spec f stop hdec w).1 k hk)
    (fun w => by
      show stop (pairFstD (pairSndD (pairEncode w _))) = true
      rw [horbit, pairSndD_pairEncode, pairFstD_pairEncode]
      exact (peelSteps_spec f stop hdec w).2.1)
  refine ptc_congr h fun w => ?_
  rw [horbit, pairSndD_pairEncode]

/-! ### The number of messages, its half and parity, the last message -/

/-- Peeling `pairSndD` until the word is empty shortens every unstopped word. -/
theorem dec_sndD_nil : ∀ w : List Bool, decide (w = []) = false → (pairSndD w).length < w.length :=
  fun w hw => length_pairSndD_lt (by simpa using hw)

/-- The number of messages of an encoded history: the rounds of peeling until empty. -/
def msgCount (w : List Bool) : ℕ := peelSteps pairSndD (fun v => decide (v = [])) w

/-- The number of messages of `encodeMsgs hist` is `|hist|`. -/
theorem msgCount_encodeMsgs (hist : List (List Bool)) : msgCount (Strategy.encodeMsgs hist) = hist.length := by
  apply peelSteps_eq _ _ dec_sndD_nil
  · intro j hj
    rw [iterate_pairSndD_encodeMsgs]
    simp [encodeMsgs_eq_nil_iff, List.drop_eq_nil_iff, hj]
  · rw [iterate_pairSndD_encodeMsgs]
    simp

/-- The number of messages in unary is polynomial-time (`peelLoop_poly`). -/
theorem msgCount_poly : PolyTimeComputable fun w => List.replicate (msgCount w) true :=
  ptc_congr (polyTimeComputable_pairSndD.comp
    (peelLoop_poly polyTimeComputable_pairSndD length_pairSndD_le isNil_poly dec_sndD_nil))
    fun w => by simp [msgCount]

/-- Peeling two messages at a time until at most one is left shortens every unstopped word. -/
theorem dec_sndD_two : ∀ w : List Bool, (decide (w = []) || decide (pairSndD w = [])) = false →
    (pairSndD (pairSndD w)).length < w.length := by
  intro w hw
  simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at hw
  exact (length_pairSndD_lt hw.2).trans (length_pairSndD_lt hw.1)

/-- Half the number of messages of an encoded history: the rounds of peeling two messages at a
time until at most one is left. -/
def halfCount (w : List Bool) : ℕ :=
  peelSteps (fun v => pairSndD (pairSndD v)) (fun v => decide (v = []) || decide (pairSndD v = [])) w

/-- Peeling two messages `k` times drops `2k` messages. -/
theorem iterate_sndD_two_encodeMsgs (k : ℕ) (hist : List (List Bool)) :
    (fun v => pairSndD (pairSndD v))^[k] (Strategy.encodeMsgs hist) =
      Strategy.encodeMsgs (hist.drop (2 * k)) := by
  induction k generalizing hist with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    show (fun v => pairSndD (pairSndD v))^[k] (pairSndD^[2] (Strategy.encodeMsgs hist)) = _
    rw [iterate_pairSndD_encodeMsgs, ih, List.drop_drop]
    congr 2
    ring

/-- The half count of `encodeMsgs hist` is `|hist| / 2`. -/
theorem halfCount_encodeMsgs (hist : List (List Bool)) :
    halfCount (Strategy.encodeMsgs hist) = hist.length / 2 := by
  apply peelSteps_eq _ _ dec_sndD_two
  · intro j hj
    rw [iterate_sndD_two_encodeMsgs]
    have h1 : ¬ hist.drop (2 * j) = [] := by
      rw [List.drop_eq_nil_iff]; omega
    have h2 : ¬ (hist.drop (2 * j)).drop 1 = [] := by
      rw [List.drop_drop, List.drop_eq_nil_iff]; omega
    simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not, encodeMsgs_eq_nil_iff, h1,
      not_false_eq_true, true_and, pairSndD_encodeMsgs]
    exact h2
  · rw [iterate_sndD_two_encodeMsgs]
    simp only [Bool.or_eq_true, decide_eq_true_eq, encodeMsgs_eq_nil_iff, pairSndD_encodeMsgs,
      List.drop_drop, List.drop_eq_nil_iff]
    omega

/-- The remainder after the half loop on `encodeMsgs hist`: the history without its first
`2 (|hist| / 2)` messages (empty exactly when `|hist|` is even). -/
theorem halfRem_encodeMsgs (hist : List (List Bool)) :
    (fun v => pairSndD (pairSndD v))^[halfCount (Strategy.encodeMsgs hist)] (Strategy.encodeMsgs hist) =
      Strategy.encodeMsgs (hist.drop (2 * (hist.length / 2))) := by
  rw [halfCount_encodeMsgs, iterate_sndD_two_encodeMsgs]

/-- The half loop (remainder paired with the half count in unary) is polynomial-time. -/
theorem halfLoop_poly : PolyTimeComputable fun w =>
    pairEncode ((fun v => pairSndD (pairSndD v))^[halfCount w] w) (List.replicate (halfCount w) true) :=
  peelLoop_poly (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)
    (fun w => (length_pairSndD_le _).trans (length_pairSndD_le w))
    (or_poly isNil_poly (isNil_poly.comp polyTimeComputable_pairSndD)) dec_sndD_two

/-- Peeling until the second component is empty shortens every unstopped word. -/
theorem dec_sndD_last : ∀ w : List Bool, decide (pairSndD w = []) = false → (pairSndD w).length < w.length := by
  intro w hw
  apply length_pairSndD_lt
  rintro rfl
  exact (by simpa using hw : ¬ pairSndD ([] : List Bool) = []) rfl

/-- The rounds to the last message of an encoded history. -/
def lastSteps (w : List Bool) : ℕ := peelSteps pairSndD (fun v => decide (pairSndD v = [])) w

/-- The rounds to the last message of `encodeMsgs hist` are `|hist| - 1`. -/
theorem lastSteps_encodeMsgs (hist : List (List Bool)) :
    lastSteps (Strategy.encodeMsgs hist) = hist.length - 1 := by
  apply peelSteps_eq _ _ dec_sndD_last
  · intro j hj
    rw [iterate_pairSndD_encodeMsgs, pairSndD_encodeMsgs]
    simp only [decide_eq_false_iff_not, encodeMsgs_eq_nil_iff, List.drop_drop, List.drop_eq_nil_iff]
    omega
  · rw [iterate_pairSndD_encodeMsgs, pairSndD_encodeMsgs]
    simp only [decide_eq_true_eq, encodeMsgs_eq_nil_iff, List.drop_drop, List.drop_eq_nil_iff]
    omega

/-- The first component of the remainder after `lastSteps` rounds is the last message. -/
theorem lastMsg_encodeMsgs (hist : List (List Bool)) :
    pairFstD (pairSndD^[lastSteps (Strategy.encodeMsgs hist)] (Strategy.encodeMsgs hist)) =
      hist.getLastD [] := by
  rw [lastSteps_encodeMsgs, iterate_pairSndD_encodeMsgs, Strategy.pairFstD_encodeMsgs,
    List.headD_eq_head?, List.head?_drop, List.getLastD_eq_getLast?, List.getLast?_eq_getElem?]

/-- The last message of an encoded history is polynomial-time (`peelLoop_poly`). -/
theorem lastMsg_poly : PolyTimeComputable fun w => pairFstD (pairSndD^[lastSteps w] w) :=
  ptc_congr (polyTimeComputable_pairFstD.comp (polyTimeComputable_pairFstD.comp
    (peelLoop_poly polyTimeComputable_pairSndD length_pairSndD_le (isNil_poly.comp polyTimeComputable_pairSndD)
      dec_sndD_last))) fun w => by simp [lastSteps]

/-! ### Unary multiplication and coin blocks -/

/-- Unary multiplication `⟨u, v⟩ ↦ 1^{|u| · |v|}` is polynomial-time
(`Turing.FinTM.computesFunInTime_unaryMul`). -/
theorem unaryMul_poly : PolyTimeComputable fun z => match pairDecode z with
    | some (u, v) => List.replicate (u.length * v.length) true
    | none => [] := by
  obtain ⟨M, c, hM⟩ := Turing.FinTM.computesFunInTime_unaryMul
  exact ⟨M, c, 2, hM⟩

/-- The product of two unary counts given by polynomial-time maps. -/
theorem unaryMul_comp {f g : List Bool → ℕ} (hf : PolyTimeComputable fun w => List.replicate (f w) true)
    (hg : PolyTimeComputable fun w => List.replicate (g w) true) :
    PolyTimeComputable fun w => List.replicate (f w * g w) true :=
  ptc_congr (unaryMul_poly.comp (hf.pairEncode hg)) fun w => by simp [pairDecode_pairEncode]

/-- The coin block `coinSlice c i r` for a block length `c = p(|u|)` and an index `i` given in
unary by polynomial-time maps (`polyTimeComputable_pairDropPoly`, `polyTimeComputable_pairTakePoly`). -/
theorem coinSlice_poly (p : PolyExpr) {u i r : List Bool → List Bool} (hu : PolyTimeComputable u)
    (hi : PolyTimeComputable i) (hr : PolyTimeComputable r) :
    PolyTimeComputable fun w => coinSlice (p.eval (u w).length) (i w).length (r w) := by
  have hic : PolyTimeComputable fun w => List.replicate ((i w).length * p.eval (u w).length) true :=
    unaryMul_comp (ptc_congr (polyTimeComputable_unary.comp hi) fun w => rfl) (unaryPoly_comp p hu)
  have hdrop : PolyTimeComputable fun w => (r w).drop ((i w).length * p.eval (u w).length) :=
    ptc_congr ((polyTimeComputable_pairDropPoly .var).comp (hic.pairEncode hr)) fun w => by simp
  refine ptc_congr ((polyTimeComputable_pairTakePoly p).comp (hu.pairEncode hdrop)) fun w => ?_
  simp [coinSlice]

/-! ### Iterating a step a unary number of times -/

/-- **Unary-count loop:** on `x₀ = ⟨u, s₀⟩`, iterate `s ↦ step ⟨x₀, s⟩` exactly `|u|` times from
`s₀` (the step may read `x₀`), provided the orbit stays within the bound `B|x₀|`.

**Proof sketch.** `stateFind` on the state `⟨s, 1^k⟩` from `⟨x₀, ⟨s₀, []⟩⟩` with the test
`|u| ≤ |1^k|`, which fires first at round `|u| ≤ |x₀|`. -/
theorem iterUnary_poly {step : List Bool → List Bool} (hstep : PolyTimeComputable step) (B : PolyExpr)
    (hbound : ∀ x₀ k, k ≤ (pairFstD x₀).length →
      ((fun s => step (pairEncode x₀ s))^[k] (pairSndD x₀)).length ≤ B.eval x₀.length) :
    PolyTimeComputable fun x₀ => (fun s => step (pairEncode x₀ s))^[(pairFstD x₀).length] (pairSndD x₀) := by
  have horbit : ∀ (x₀ : List Bool) (k : ℕ),
      orbit (fun x₀ => pairEncode (pairSndD x₀) [])
        (fun st => pairEncode (step (pairEncode (pairFstD st) (pairFstD (pairSndD st))))
          (true :: pairSndD (pairSndD st))) x₀ k =
        pairEncode ((fun s => step (pairEncode x₀ s))^[k] (pairSndD x₀)) (List.replicate k true) := by
    intro x₀ k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [orbit_succ, ih, pairSndD_pairEncode, pairFstD_pairEncode, pairFstD_pairEncode,
        pairSndD_pairEncode, Function.iterate_succ_apply', List.replicate_succ]
  have hstart : PolyTimeComputable fun x₀ => pairEncode (pairSndD x₀) [] :=
    polyTimeComputable_pairSndD.pairEncode (polyTimeComputable_const [])
  have hstep' : PolyTimeComputable fun st =>
      pairEncode (step (pairEncode (pairFstD st) (pairFstD (pairSndD st)))) (true :: pairSndD (pairSndD st)) :=
    (hstep.comp (polyTimeComputable_pairFstD.pairEncode
      (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD))).pairEncode
      ((cons_poly true).comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD))
  have hacc : PolyTimeComputable fun st =>
      [decide ((pairFstD (pairFstD st)).length ≤ (pairSndD (pairSndD st)).length)] :=
    lenLe_comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)
      (polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD)
  have hout : PolyTimeComputable fun st => pairFstD (pairSndD st) :=
    polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD
  have h := stateFind hstart hstep' hacc hout .var
    (.add (.mul (.const 2) B) (.add (.const 2) .var)) (fun x₀ => (pairFstD x₀).length)
    (fun x₀ => length_pairFstD_le x₀)
    (fun x₀ k hk => by
      rw [horbit, length_pairEncode, List.length_replicate]
      have hk' : k ≤ (pairFstD x₀).length := hk
      have h1 := hbound x₀ k hk'
      have h2 := length_pairFstD_le x₀
      simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
      omega)
    (fun x₀ k hk => by
      show decide ((pairFstD (pairFstD (pairEncode x₀ _))).length ≤
        (pairSndD (pairSndD (pairEncode x₀ _))).length) = false
      rw [horbit, pairFstD_pairEncode, pairSndD_pairEncode, pairSndD_pairEncode, List.length_replicate]
      simpa using hk)
    (fun x₀ => by
      show decide ((pairFstD (pairFstD (pairEncode x₀ _))).length ≤
        (pairSndD (pairSndD (pairEncode x₀ _))).length) = true
      rw [horbit, pairFstD_pairEncode, pairSndD_pairEncode, pairSndD_pairEncode, List.length_replicate]
      simp)
  refine ptc_congr h fun x₀ => ?_
  rw [horbit, pairSndD_pairEncode, pairFstD_pairEncode]

/-! ### The verifier of the `|x|`-fold graph non-isomorphism protocol -/

/-- The number of messages of the layout's history, in unary. -/
theorem cnt_poly : PolyTimeComputable fun w => List.replicate (msgCount (argM w)) true :=
  msgCount_poly.comp argM_poly

/-- The test `|hist| < |x|` (the protocol is not over), as the negated length comparison of
`1^{|x|}` with the message count. -/
theorem ltLen_poly : PolyTimeComputable fun w => [decide (msgCount (argM w) < (NUPPT.inParam w).length)] := by
  refine ptc_congr (not_poly (lenLe_comp cnt_poly NUPPT.polyTimeComputable_inParam)) fun w => ?_
  simp only [List.length_replicate]
  exact congrArg (fun b => [b]) (by rw [← decide_not]; exact decide_eq_decide.2 not_le.symm)

/-- The coin polynomial of one iteration of the graph non-isomorphism protocol,
`1 + (N + 1)²`. -/
def gniBlock : PolyExpr := .add (.const 1) (.normal 1 2)

/-- The block length evaluates to `1 + (N + 1)²`. -/
theorem gniBlock_eval (N : ℕ) : gniBlock.eval N = 1 + (N + 1) ^ 2 := by
  simp [gniBlock, PolyExpr.eval_normal]

/-- The coin block of the current iteration of the `|x|`-fold graph non-isomorphism verifier:
`coinSlice (1 + (|x|+1)²) |hist| r`. -/
theorem gniSlice_poly : PolyTimeComputable fun w =>
    coinSlice (gniBlock.eval (NUPPT.inParam w).length) (msgCount (argM w)) (NUPPT.inCoins w) :=
  ptc_congr (coinSlice_poly gniBlock NUPPT.polyTimeComputable_inParam cnt_poly
    NUPPT.polyTimeComputable_inCoins) fun w => by simp

/-- One round of the verdict scan of the `|x|`-fold graph non-isomorphism verifier, on the
state word `⟨x₀, ⟨remMsgs, ⟨remCoins, [bit]⟩⟩⟩` (with `x₀ = ⟨1^{|x|}, …⟩`): peel one message,
drop one coin block, and conjoin the comparison of the message's first bit with the block's
first bit. -/
def gniStep (st : List Bool) : List Bool :=
  pairEncode (pairSndD (pairFstD (pairSndD st)))
    (pairEncode ((pairFstD (pairSndD (pairSndD st))).drop (gniBlock.eval (pairFstD (pairFstD st)).length))
      [(pairSndD (pairSndD (pairSndD st))).headD false &&
        decide ((pairFstD (pairFstD (pairSndD st))).headD false =
          (pairFstD (pairSndD (pairSndD st))).headD false)])

/-- The scan round is polynomial-time. -/
theorem gniStep_poly : PolyTimeComputable gniStep := by
  have hM : PolyTimeComputable fun st => pairFstD (pairSndD st) :=
    polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD
  have hR : PolyTimeComputable fun st => pairFstD (pairSndD (pairSndD st)) :=
    polyTimeComputable_pairFstD.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)
  have hB : PolyTimeComputable fun st => pairSndD (pairSndD (pairSndD st)) :=
    polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)
  have hu : PolyTimeComputable fun st => pairFstD (pairFstD st) :=
    polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD
  have hdrop : PolyTimeComputable fun st =>
      (pairFstD (pairSndD (pairSndD st))).drop (gniBlock.eval (pairFstD (pairFstD st)).length) :=
    ptc_congr ((polyTimeComputable_pairDropPoly gniBlock).comp (hu.pairEncode hR)) fun st => by simp
  have hbit : PolyTimeComputable fun st => [(pairSndD (pairSndD (pairSndD st))).headD false &&
      decide ((pairFstD (pairFstD (pairSndD st))).headD false = (pairFstD (pairSndD (pairSndD st))).headD false)] :=
    polyTimeComputable_and (headBit_poly.comp hB)
      (ptc_congr (polyTimeComputable_pairEq.comp
        ((headBit_poly.comp (polyTimeComputable_pairFstD.comp hM)).pairEncode (headBit_poly.comp hR)))
        fun st => by simp)
  exact (polyTimeComputable_pairSndD.comp hM).pairEncode (hdrop.pairEncode hbit)

/-- The scan after `k` rounds from the input `⟨u, ⟨M, ⟨R, [b]⟩⟩⟩` (with `c = 1 + (|u|+1)²`):
the remaining messages, the remaining coins and the conjunction of the first `k` comparisons
with the initial bit `b`. -/
theorem gniIter_eq (u M R : List Bool) (b : Bool) (k : ℕ) :
    (fun s => gniStep (pairEncode (pairEncode u (pairEncode M (pairEncode R [b]))) s))^[k]
        (pairSndD (pairEncode u (pairEncode M (pairEncode R [b])))) =
      pairEncode (pairSndD^[k] M) (pairEncode (R.drop (k * gniBlock.eval u.length))
        [b && decide (∀ j < k, (pairFstD (pairSndD^[j] M)).headD false =
          (R.drop (j * gniBlock.eval u.length)).headD false)]) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [gniStep, pairFstD_pairEncode, pairSndD_pairEncode, List.headD_cons, List.drop_drop,
      Function.iterate_succ_apply', Nat.forall_lt_succ_right, Bool.decide_and, Bool.and_assoc, Nat.succ_mul]

/-- The scan from an arbitrary input has, after at least one round, the shape of `gniIter_eq`
with the components read off the input (the bit being unspecified). -/
theorem gniIter_shape (x₀ : List Bool) (k : ℕ) (hk : 1 ≤ k) :
    ∃ b : Bool, (fun s => gniStep (pairEncode x₀ s))^[k] (pairSndD x₀) =
      pairEncode (pairSndD^[k] (pairFstD (pairSndD x₀)))
        (pairEncode ((pairFstD (pairSndD (pairSndD x₀))).drop (k * gniBlock.eval (pairFstD x₀).length)) [b]) := by
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · exact ⟨(pairSndD (pairSndD (pairSndD x₀))).headD false &&
        decide ((pairFstD (pairFstD (pairSndD x₀))).headD false = (pairFstD (pairSndD (pairSndD x₀))).headD false),
        by simp only [Nat.zero_add, Function.iterate_one, gniStep, pairFstD_pairEncode, pairSndD_pairEncode,
          Nat.one_mul]⟩
    · obtain ⟨b, hb⟩ := ih hpos
      refine ⟨b && decide ((pairFstD (pairSndD^[k] (pairFstD (pairSndD x₀)))).headD false =
        ((pairFstD (pairSndD (pairSndD x₀))).drop (k * gniBlock.eval (pairFstD x₀).length)).headD false), ?_⟩
      rw [Function.iterate_succ_apply', hb]
      simp only [gniStep, pairFstD_pairEncode, pairSndD_pairEncode, List.drop_drop,
        Function.iterate_succ_apply', Nat.succ_mul, List.headD_cons]

/-- The scan states are bounded by `4|x₀| + 5`. -/
theorem gniIter_bound (x₀ : List Bool) (k : ℕ) :
    ((fun s => gniStep (pairEncode x₀ s))^[k] (pairSndD x₀)).length ≤
      (PolyExpr.add (.mul (.const 4) .var) (.const 5)).eval x₀.length := by
  simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have := length_pairSndD_le x₀
    simp only [Function.iterate_zero, id]
    omega
  · obtain ⟨b, hb⟩ := gniIter_shape x₀ k hk
    rw [hb, length_pairEncode, length_pairEncode, List.length_singleton]
    have h1 := length_iterate_le length_pairSndD_le (pairFstD (pairSndD x₀)) k
    have h2 : (pairFstD (pairSndD x₀)).length ≤ x₀.length :=
      (length_pairFstD_le _).trans (length_pairSndD_le _)
    have h3 : ((pairFstD (pairSndD (pairSndD x₀))).drop (k * gniBlock.eval (pairFstD x₀).length)).length ≤
        x₀.length := by
      rw [List.length_drop]
      exact (Nat.sub_le _ _).trans
        ((length_pairFstD_le _).trans ((length_pairSndD_le _).trans (length_pairSndD_le _)))
    omega

/-- The verdict scan of the `|x|`-fold graph non-isomorphism verifier is polynomial-time: the
one-bit word `[decide (∀ j < |x|, bit of message j = bit of coin block j)]`
(`iterUnary_poly` on `gniStep` from `⟨1^{|x|}, ⟨msgs, ⟨r, [true]⟩⟩⟩`, closed form `gniIter_eq`). -/
theorem gniScan_poly : PolyTimeComputable fun w =>
    [decide (∀ j < (NUPPT.inParam w).length, (pairFstD (pairSndD^[j] (argM w))).headD false =
      ((NUPPT.inCoins w).drop (j * gniBlock.eval (NUPPT.inParam w).length)).headD false)] := by
  have hx₀ : PolyTimeComputable fun w =>
      pairEncode (NUPPT.inParam w) (pairEncode (argM w) (pairEncode (NUPPT.inCoins w) [true])) :=
    NUPPT.polyTimeComputable_inParam.pairEncode (argM_poly.pairEncode
      (NUPPT.polyTimeComputable_inCoins.pairEncode (polyTimeComputable_const [true])))
  have h := (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD).comp
    ((iterUnary_poly gniStep_poly _ (fun x₀ k _ => gniIter_bound x₀ k)).comp hx₀)
  refine ptc_congr h fun w => ?_
  simp only [Function.comp_apply, pairFstD_pairEncode]
  rw [gniIter_eq, pairSndD_pairEncode, pairSndD_pairEncode, Bool.true_and]

/-- The first bit of a nonempty prefix is the first bit of the word. -/
theorem headD_take {c : ℕ} (hc : 0 < c) (l : List Bool) : (l.take c).headD false = l.headD false := by
  cases l with
  | nil => simp
  | cons a l =>
    cases c with
    | zero => omega
    | succ c => simp

/-- An entry of a list with default is the first entry of the corresponding suffix. -/
theorem getD_eq_headD_drop {α : Type*} (l : List α) (j : ℕ) (d : α) : l.getD j d = (l.drop j).headD d := by
  rw [List.headD_eq_head?, List.head?_drop, List.getD_eq_getElem?_getD]

/-- The verdict condition of the `|x|`-fold graph non-isomorphism verifier, read through the
scan: message `j` is `pairFstD (pairSndD^[j] msgs)` and the first bit of coin block `j` is the
first bit of `r.drop (j c)`. -/
theorem gni_verdict_iff (hist : List (List Bool)) (r : List Bool) (N c : ℕ) (hc : 0 < c) :
    (∀ j : Fin N, (hist.getD j []).headD false = (coinSlice c j r).headD false) ↔
      ∀ j < N, (pairFstD (pairSndD^[j] (Strategy.encodeMsgs hist))).headD false =
        (r.drop (j * c)).headD false := by
  rw [Fin.forall_iff]
  refine forall_congr' fun j => forall_congr' fun _ => ?_
  rw [iterate_pairSndD_encodeMsgs, Strategy.pairFstD_encodeMsgs, coinSlice, headD_take hc, Fin.val_mk,
    getD_eq_headD_drop]

/-- The verifier of the `|x|`-fold graph non-isomorphism protocol is a PPT strategy (Inf-4.2).

**Proof sketch.** `efficient_of_polyTime`: the message count `1^{|hist|}` (`cnt_poly`), the
test `|hist| < |x|` (`ltLen_poly`), the coin block of the current iteration (`gniSlice_poly`)
and the message `relabel_poly` of `G_b` by the sampled permutation on the one hand, the
well-formedness test conjoined with the verdict scan (`gniScan_poly`) on the other; the
equation with `gniVerifierRep.next` is `msgCount_encodeMsgs`, `gniBlock_eval` and
`gni_verdict_iff`. -/
theorem gniVerifierRep_efficient : gniVerifierRep.Efficient := by
  have hri := gniSlice_poly
  have hsel : PolyTimeComputable fun w =>
      if (coinSlice (gniBlock.eval (NUPPT.inParam w).length) (msgCount (argM w)) (NUPPT.inCoins w)).headD false
        then pairSndD (argX w) else pairFstD (argX w) :=
    polyTimeComputable_ite (headBit_poly.comp hri) w₁_poly w₀_poly
  have hσ : PolyTimeComputable fun w => sampleStr (pairFstD (argX w))
      (coinSlice (gniBlock.eval (NUPPT.inParam w).length) (msgCount (argM w)) (NUPPT.inCoins w)).tail :=
    ptc_congr (sampleStr_poly.comp (w₀_poly.pairEncode (tail_poly.comp hri))) fun w => by simp
  have hmsg := relabel_poly hsel hσ
  have hwf : PolyTimeComputable fun w => [wellFormedInstance (argX w)] := wellFormed_poly.comp argX_poly
  have hverdict := polyTimeComputable_and hwf gniScan_poly
  refine efficient_of_polyTime gniVerifierRep (polyTimeComputable_ite ltLen_poly hmsg hverdict) ?_
  intro x z r hist
  show (if hist.length < x.length then _ else _) = _
  simp only [argM_ilayout, msgCount_encodeMsgs, inParam_ilayout, List.length_replicate, inCoins_ilayout,
    argX_ilayout, vcount_ilayout, gniBlock_eval, decide_eq_true_eq]
  by_cases hlt : hist.length < x.length
  · rw [if_pos hlt, if_pos hlt, relabelAt_replicate, sampleStr, decPerm_encPerm, List.drop_one]
    split_ifs <;> rfl
  · rw [if_neg hlt, if_neg hlt, Bool.decide_and, Bool.decide_eq_true]
    congr 2
    exact decide_eq_decide.2 (gni_verdict_iff hist r x.length _ (by positivity))

end TCSlib.Cryptography.GI
