/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.CircuitComplexity.Advice
import TCSlib.Complexity.CircuitComplexity.CircuitEval
import TCSlib.Complexity.CircuitComplexity.PPoly
import TCSlib.Complexity.ClassNP.PolyTimePairing

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# `P/poly` languages are decided by polynomial-time machines with polynomial advice

The inclusion `P/poly ⊆ ⋃_{c,d} DTIME(n^c)/n^d` of [AB09, Thm 6.18], by the book's
proof (p. 113): "We can just use the description of `Cₙ` as an advice string on inputs of
size `n`, where the TM is simply the polynomial-time TM `M` that on input a string `x` and
a string representing an `n`-input circuit `C` outputs `C(x)`."
The advice for inputs of length `n` is the description `C_n.encode`
(`BoolCircuit.DAGCircuit.encode`) of the length-`n` circuit, padded to an exact
polynomial length; the machine strips the padding, rearranges the pair, and runs the
circuit-value machine `BoolCircuit.CircuitEval.evalTM`.

## Main results

* `Complexity.mem_DTIMEAdvice_of_inSIZE` — a language with fan-in-two circuits of size
  `a · (n + 1)^k` is in `DTIME(n^c + 1) / ((12a² + 1) · (n + 1)^(2k))` for some `c`.
* `Complexity.PPoly_subset_PAdvicePoly` — `P/poly ⊆ PAdvicePoly`, the direction `⊆` of
  [AB09, Thm 6.18].
* `Complexity.mem_DTIMEAdvice_pow_of_inSIZE` — the same with advice of length exactly
  `n^d`, the book's advice length (the circuits for `n ≤ 1`, where `n^d` is too short
  for a description, are hard-coded in the machine).

## The machine

On the pair `⟨x, αₙ⟩ = Turing.pairEncode x αₙ` with `αₙ = C_n.encode ++ 1 0^m`:

1. strip the advice at its last `1` (`Turing.FinTM.computesFunInTime_stripLast`), giving
   `⟨x, C_n.encode⟩`;
2. rebuild the pair in the evaluator's order, `⟨C_n.encode, x⟩`
   (`Complexity.PolyTimeComputable.pairEncode` applied to the two component
   extractors) — the advice machine receives its input first, the evaluator expects
   the description first;
3. run the circuit-value machine with `exact = true`; its verdict on
   `⟨C_n.encode, x⟩` is `C_n(x)` (`BoolCircuit.CircuitEval.verdict_pairEncode`).

Each stage is polynomial in the input length `2n + 2 + |αₙ|`, itself polynomial in `n`.

## Divergences from [AB09, Thm 6.18]

* **Only `⊆` is proved here.** The converse `PAdvicePoly ⊆ P/poly` (a tableau circuit
  for the advice machine, with the advice hard-wired) and the resulting equality are
  `Complexity.PAdvicePoly_subset_PPoly` and `Complexity.PPoly_eq_PAdvicePoly` in
  `CircuitComplexity/PAdviceSubsetPPoly.lean`.
* **Padding.** `Complexity.DTIMEAdvice` demands advice of length *exactly* `a(n)`, while
  circuit descriptions of a size-bounded family have varying lengths. The description is
  therefore followed by a `1` and then `0`s up to the exact length
  `(12a² + 1)(n + 1)^(2k)` (`BoolCircuit.DAGCircuit.length_encode_le_of_isFaninTwo`
  bounds `|C_n.encode| ≤ 12 |C_n|²`); [AB09] takes the description as the advice and
  leaves its length implicit.
* The time and advice bounds have the shapes of `Complexity.PAdvicePoly`
  (`n^c + 1`, `C · (n + 1)^d`); see `TCSlib.Complexity.CircuitComplexity.Advice`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§6.3, Theorem 6.18 and its proof, p. 113.)
-/

namespace Complexity

open Turing BoolCircuit

/-- Stripping at the last `1`: `u ++ 1 0^m ↦ u`. -/
private lemma splitAtLastTrue_pad (u : List Bool) (m : ℕ) :
    splitAtLastTrue (u ++ true :: List.replicate m false) = some u := by
  have h : ∀ m : ℕ, (List.replicate m false ++ true :: u.reverse).dropWhile (fun b => !b) =
      true :: u.reverse := by
    intro m
    induction m with
    | zero => simp
    | succ m ih => simp [List.replicate_succ, ih]
  rw [splitAtLastTrue, List.reverse_append, List.reverse_cons, List.reverse_replicate]
  simp only [List.append_assoc, List.singleton_append]
  rw [h m]
  simp

/-- The padded advice: the description of the length-`n` circuit, then a `1`, then `0`s
up to total length `A n`. -/
private def padAdvice (C : DAGCircuitFamily) (A : ℕ → ℕ) (n : ℕ) : List Bool :=
  (C.circuit n).encode ++ true :: List.replicate (A n - (C.circuit n).encode.length - 1) false

/-- The padded advice has length exactly `A n` once the description fits. -/
private lemma length_padAdvice (C : DAGCircuitFamily) (A : ℕ → ℕ) (n : ℕ)
    (h : (C.circuit n).encode.length + 1 ≤ A n) : (padAdvice C A n).length = A n := by
  simp only [padAdvice, List.length_append, List.length_cons, List.length_replicate]
  omega

/-- The verdict of the circuit-value algorithm (exact mode) on `⟨C.encode, x⟩`, for a
fan-in-two circuit `C` on `|x|` inputs, is the circuit's output on `x`.

**Proof sketch.** If `C` outputs `1`, `verdict_pairEncode` applies with `C` itself as the
witness. If `C` outputs `0` but the verdict were `1`, the witnessed circuit has the same
code as `C`, so by injectivity of the encoding it is `C`, a contradiction. -/
private lemma verdict_encode {m : ℕ} (C : DAGCircuit m) (hC : C.IsFaninTwo) (x : List Bool)
    (hx : x.length = m) :
    CircuitEval.verdict true (pairEncode C.encode x) = C.eval (fun i => x.getD i false) := by
  cases hv : C.eval (fun i => x.getD i false)
  · cases h : CircuitEval.verdict true (pairEncode C.encode x)
    · rfl
    · obtain ⟨n', C', _, henc, -, hex, hev⟩ := (CircuitEval.verdict_pairEncode true _ _).mp h
      obtain ⟨hn, -⟩ := DAGCircuit.eq_of_encode_eq henc
      subst hn
      obtain rfl := DAGCircuit.encode_injective _ henc
      rw [hv] at hev
      exact absurd hev (by simp)
  · exact (CircuitEval.verdict_pairEncode true _ _).mpr
      ⟨m, C, hC, rfl, hx.ge, fun _ => hx.symm, hv⟩

/-- `C · (n + 1)^d` is at most `C · (n + 1)^(d + 1)`. -/
private lemma mul_pow_le_mul_pow_succ (C n d : ℕ) : C * (n + 1) ^ d ≤ C * (n + 1) ^ (d + 1) :=
  Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))

/-- The circuit-value verdict on `⟨Cₙ.encode, x⟩` (with `n = |x|`) is the indicator of
membership of `x` in the family's language. -/
private lemma verdict_encode_family (C : DAGCircuitFamily) (hfan : C.HasFaninTwo)
    (x : List Bool) :
    [CircuitEval.verdict true (pairEncode (C.circuit x.length).encode x)] =
      [MultiTapeTM.indicator (C.language : Set (List Bool)) x] := by
  have hmem : x ∈ (C.language : Set (List Bool)) ↔ (C.circuit x.length).eval x.get = true :=
    Iff.rfl
  have hget : (fun i : Fin x.length => x.getD i false) = x.get := by
    funext i
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem i.isLt]
    rfl
  rw [verdict_encode _ (hfan _) x rfl, hget]
  cases hv : (C.circuit x.length).eval x.get <;> simp [MultiTapeTM.indicator, hmem, hv]

/-- The running-time arithmetic shared by the advice machines: if the input length `m`
satisfies `m + 1 ≤ B (n + 1)^D`, then a polynomial budget `K (m + 1)^e` is at most
`K B^e 2^(De) (n^(De) + 1)`. -/
private lemma time_le_of_length_le {K e B D n m : ℕ} (h : m + 1 ≤ B * (n + 1) ^ D) :
    K * (m + 1) ^ e ≤ K * B ^ e * 2 ^ (D * e) * (n ^ (D * e) + 1) := by
  calc K * (m + 1) ^ e ≤ K * (B * (n + 1) ^ D) ^ e :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h e)
    _ = K * B ^ e * (n + 1) ^ (D * e) := by rw [mul_pow, ← pow_mul]; ring
    _ ≤ K * B ^ e * (2 ^ (D * e) * (n ^ (D * e) + 1)) :=
        Nat.mul_le_mul_left _ (succ_pow_le n _)
    _ = _ := by ring

/-- **Circuits as advice** [AB09, Thm 6.18, `⊆`, proof on p. 113]: a language decided by
fan-in-two circuits of size at most `a · (n + 1)^k` is decided in time `O(n^c + 1)`, for
some `c`, with advice of length exactly `(12a² + 1) · (n + 1)^(2k)`.

**Proof sketch.** The advice for length `n` is the description of `C_n` followed by a
`1` and `0`s up to the exact length; the description fits, as
`|C_n.encode| ≤ 12 |C_n|² ≤ 12a² (n + 1)^(2k)`. The machine strips the advice at its
last `1`, rebuilds the pair as ⟨description, input⟩ (the description is the second
component of the stripped pair, the input its first), and runs the circuit-value
machine, whose verdict on that pair is `C_n(x)`. All three stages are polynomial-time
transformers, so their composite runs within `K (m + 1)^e` steps on inputs of length
`m = 2n + 2 + (12a² + 1)(n + 1)^(2k)`; this is at most a constant times
`n^((2k + 1)e) + 1`. -/
theorem mem_DTIMEAdvice_of_inSIZE {L : Language Bool} {a k : ℕ}
    (hL : L.InSIZE fun n => a * (n + 1) ^ k) :
    ∃ c, L ∈ DTIMEAdvice (fun n => n ^ c + 1) fun n => (12 * a ^ 2 + 1) * (n + 1) ^ (2 * k) := by
  obtain ⟨C, hfan, hsize, rfl⟩ := hL
  set A : ℕ → ℕ := fun n => (12 * a ^ 2 + 1) * (n + 1) ^ (2 * k) with hA
  -- the description fits in the advice
  have hfit : ∀ n, (C.circuit n).encode.length + 1 ≤ A n := by
    intro n
    have h1 := DAGCircuit.length_encode_le_of_isFaninTwo _ (hfan n)
    have h2 : (C.circuit n).size ^ 2 ≤ (a * (n + 1) ^ k) ^ 2 := Nat.pow_le_pow_left (hsize n) 2
    have h3 : 1 ≤ (n + 1) ^ (2 * k) := Nat.one_le_pow _ _ (by omega)
    have h4 : (a * (n + 1) ^ k) ^ 2 = a ^ 2 * (n + 1) ^ (2 * k) := by ring
    simp only [hA]
    nlinarith
  -- the three stages
  obtain ⟨MS, cS, hMS⟩ := FinTM.computesFunInTime_stripLast
  have hS := (⟨MS, cS, 2, hMS⟩ : PolyTimeComputable _)
  have hsnd := polyTimeComputable_of_linear FinTM.computesFunInTime_pairSnd
  have hfst := polyTimeComputable_of_linear FinTM.computesFunInTime_pairFst
  have hP := PolyTimeComputable.pairEncode (hsnd.comp hS) hfst
  have hE : PolyTimeComputable fun z => [CircuitEval.verdict true z] :=
    ⟨CircuitEval.evalTM true, 12, 2, CircuitEval.evalTM_computes true⟩
  obtain ⟨M, K, e, hM⟩ := hE.comp hP
  refine ⟨(2 * k + 1) * e, K * (12 * a ^ 2 + 4) ^ e * 2 ^ ((2 * k + 1) * e),
    padAdvice C A, M, fun n => length_padAdvice C A n (hfit n), fun x => ?_⟩
  set n := x.length with hn
  set w := pairEncode x (padAdvice C A n) with hw
  have h := hM w
  -- the output is the circuit's verdict
  have h2 : M.ComputesInTime w [MultiTapeTM.indicator (C.language : Set (List Bool)) x]
      (K * (w.length + 1) ^ e) := by
    convert h using 1
    simp only [Function.comp_apply, hw, pairDecode_pairEncode, padAdvice,
      splitAtLastTrue_pad, Option.map_some, Option.getD_some]
    exact (verdict_encode_family C hfan x).symm
  refine h2.mono ?_
  dsimp only
  -- the time bound
  have hlen : w.length = 2 * n + 2 + A n := by
    simp only [hw, pairEncode, List.length_append, List.length_flatMap, List.length_cons,
      List.length_nil, length_padAdvice C A n (hfit n)]
    simp [List.sum_replicate, hn]
    ring
  have hP1 : 1 ≤ (n + 1) ^ (2 * k) := Nat.one_le_pow _ _ (by omega)
  have hP2 : n + 1 ≤ (n + 1) ^ (2 * k + 1) := Nat.le_self_pow (by omega) _
  have hwb : w.length + 1 ≤ (12 * a ^ 2 + 4) * (n + 1) ^ (2 * k + 1) := by
    rw [hlen]
    have := mul_pow_le_mul_pow_succ (12 * a ^ 2 + 1) n (2 * k)
    simp only [hA]
    nlinarith
  exact time_le_of_length_le hwb

/-- **`P/poly ⊆ ⋃_{c,d} DTIME(n^c)/n^d`** [AB09, Thm 6.18, direction `⊆`]: every language
with polynomial-size fan-in-two circuits is decided by a polynomial-time machine with
polynomial advice (the class `Complexity.PAdvicePoly`, i.e.
`⋃ DTIME(n^c + 1)/(C · (n + 1)^d)`).

The converse `PAdvicePoly ⊆ P/poly`, the other half of [AB09, Thm 6.18], is
`Complexity.PAdvicePoly_subset_PPoly` (`CircuitComplexity/PAdviceSubsetPPoly.lean`).

**Proof sketch.** `Complexity.mem_DTIMEAdvice_of_inSIZE`: with circuits of size
`a (n + 1)^k`, the padded descriptions are advice of length `(12a² + 1)(n + 1)^(2k)`
and the strip–rearrange–evaluate machine runs in polynomial time. -/
theorem PPoly_subset_PAdvicePoly : {L : Language Bool | L.InPPoly} ⊆ PAdvicePoly := by
  rintro L ⟨a, k, hL⟩
  obtain ⟨c, hc⟩ := mem_DTIMEAdvice_of_inSIZE hL
  exact DTIMEAdvice_subset_PAdvicePoly c (12 * a ^ 2 + 1) (2 * k) hc

/-! ### Advice of length exactly `n^d` -/

/-- For `n ≥ 2`, a coefficient `m` is at most `n^m`. -/
private lemma le_pow_self_of_two_le (m n : ℕ) (hn : 2 ≤ n) : m ≤ n ^ m :=
  (Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_left hn m)

/-- For `n ≥ 2`, `(m + 1)(n + 1)^(2k) ≤ n^(m + 1 + 4k)`: the polynomial
`(m + 1)(n + 1)^(2k)` is dominated by a pure power of `n` once `n ≥ 2`. -/
private lemma mul_succ_pow_le_pow (m k n : ℕ) (hn : 2 ≤ n) :
    (m + 1) * (n + 1) ^ (2 * k) ≤ n ^ (m + 1 + 4 * k) := by
  have h1 : n + 1 ≤ n ^ 2 := by nlinarith
  have h2 : (n + 1) ^ (2 * k) ≤ n ^ (4 * k) := by
    calc (n + 1) ^ (2 * k) ≤ (n ^ 2) ^ (2 * k) := Nat.pow_le_pow_left h1 _
      _ = n ^ (4 * k) := by rw [← pow_mul]; ring_nf
  calc (m + 1) * (n + 1) ^ (2 * k) ≤ n ^ (m + 1) * n ^ (4 * k) :=
        Nat.mul_le_mul (le_pow_self_of_two_le (m + 1) n hn) h2
    _ = n ^ (m + 1 + 4 * k) := (pow_add n (m + 1) (4 * k)).symm

/-- The length test `|fst z| ≤ m` on pairs is polynomial-time (the threaded length test
`Complexity.polyTimeComputable_lenLe` against the constant `1^m`). -/
private lemma polyTimeComputable_lenFstLe (m : ℕ) :
    PolyTimeComputable fun z => [decide ((pairFstD z).length ≤ m)] := by
  have h := polyTimeComputable_lenLe.comp
    ((polyTimeComputable_const (List.replicate m true)).pairEncode polyTimeComputable_pairFstD)
  convert h using 1
  funext z
  simp

/-- **Circuits as advice of length exactly `n^d`** [AB09, Thm 6.18, `⊆`, with the book's
advice length `n^d` literally]: a language decided by fan-in-two circuits of size at
most `a · (n + 1)^k` lies in `DTIME(n^c + 1)/n^d` for some `c` and `d`.

Divergence from `Complexity.mem_DTIMEAdvice_of_inSIZE`: there the advice length
`(12a² + 1)(n + 1)^(2k)` is chosen to fit the circuit description at every `n`.  An
advice length `n^d` is `0` at `n = 0` and `1` at `n = 1`, too short for any description;
so the machine hard-codes the two circuits `C₀` and `C₁` (finitely much information,
part of the machine's finite control), and only for `n ≥ 2` reads the description from
the advice.  The advice at `n ≤ 1` is all zeros and is ignored.

**Proof sketch.** Take `d = 12a² + 2 + 4k`, so that for `n ≥ 2` the padded description
fits: `|C_n.encode| + 1 ≤ (12a² + 1)(n + 1)^(2k) ≤ n^d`.  The machine computes
`G(z)` = `C₀.encode` if `|fst z| ≤ 0`, `C₁.encode` if `|fst z| ≤ 1`, and otherwise the
second component of `z` stripped at its last `1`; it then runs the circuit-value machine
on `⟨G(z), fst z⟩`.  The two length tests are threaded length checks against constants,
and polynomial-time branching (`Complexity.polyTimeComputable_ite`) assembles the
pieces.  On `⟨x, αₙ⟩` the description `G` is `Cₙ.encode` in all three cases, so the
verdict is `Cₙ(x)`.  The input has length `2n + 2 + n^d ≤ 4(n + 1)^d`, so the running
time `K (|w| + 1)^e` is a constant times `n^(de) + 1`. -/
theorem mem_DTIMEAdvice_pow_of_inSIZE {L : Language Bool} {a k : ℕ}
    (hL : L.InSIZE fun n => a * (n + 1) ^ k) :
    ∃ c d, L ∈ DTIMEAdvice (fun n => n ^ c + 1) fun n => n ^ d := by
  obtain ⟨C, hfan, hsize, rfl⟩ := hL
  set d := 12 * a ^ 2 + 1 + 1 + 4 * k with hd
  set A : ℕ → ℕ := fun n => n ^ d with hA
  -- the description fits in the advice once `n ≥ 2`
  have hfit : ∀ n, 2 ≤ n → (C.circuit n).encode.length + 1 ≤ A n := by
    intro n hn
    have h1 := DAGCircuit.length_encode_le_of_isFaninTwo _ (hfan n)
    have h2 : (C.circuit n).size ^ 2 ≤ (a * (n + 1) ^ k) ^ 2 := Nat.pow_le_pow_left (hsize n) 2
    have h3 : 1 ≤ (n + 1) ^ (2 * k) := Nat.one_le_pow _ _ (by omega)
    have h4 : (a * (n + 1) ^ k) ^ 2 = a ^ 2 * (n + 1) ^ (2 * k) := by ring
    have h5 := mul_succ_pow_le_pow (12 * a ^ 2 + 1) k n hn
    simp only [hA, hd]
    nlinarith
  let α : ℕ → List Bool := fun n =>
    if n ≤ 1 then List.replicate (n ^ d) false else padAdvice C A n
  have hαlen : ∀ n, (α n).length = n ^ d := by
    intro n
    by_cases hn : n ≤ 1
    · simp [α, hn]
    · simp only [α, if_neg hn]
      exact length_padAdvice C A n (hfit n (by omega))
  -- the machine
  let strip : List Bool → List Bool := fun x => match pairDecode x with
    | some (a, v) =>
      match splitAtLastTrue v with
      | some u => pairEncode a u
      | none => []
    | none => []
  obtain ⟨MS, cS, hMS⟩ := FinTM.computesFunInTime_stripLast
  have hS : PolyTimeComputable strip := ⟨MS, cS, 2, hMS⟩
  let G : List Bool → List Bool := fun z =>
    if decide ((pairFstD z).length ≤ 0) then (C.circuit 0).encode
    else if decide ((pairFstD z).length ≤ 1) then (C.circuit 1).encode
    else pairSndD (strip z)
  have hG : PolyTimeComputable G :=
    polyTimeComputable_ite (polyTimeComputable_lenFstLe 0) (polyTimeComputable_const _)
      (polyTimeComputable_ite (polyTimeComputable_lenFstLe 1) (polyTimeComputable_const _)
        (polyTimeComputable_pairSndD.comp hS))
  have hP := hG.pairEncode polyTimeComputable_pairFstD
  have hE : PolyTimeComputable fun z => [CircuitEval.verdict true z] :=
    ⟨CircuitEval.evalTM true, 12, 2, CircuitEval.evalTM_computes true⟩
  obtain ⟨M, K, e, hM⟩ := hE.comp hP
  refine ⟨d * e, d, K * 4 ^ e * 2 ^ (d * e), α, M, hαlen, fun x => ?_⟩
  set n := x.length with hn
  set w := pairEncode x (α n) with hw
  have h := hM w
  -- the description handed to the evaluator is that of `Cₙ`
  have hGw : G w = (C.circuit n).encode := by
    have hfw : pairFstD w = x := by simp [hw]
    rcases Nat.lt_or_ge n 2 with hn2 | hn2
    · rcases (show n = 0 ∨ n = 1 by omega) with hn0 | hn0
      · simp only [G, hfw, ← hn, hn0]
        simpa using congrArg (fun m => (C.circuit m).encode) hn0.symm
      · simp only [G, hfw, ← hn, hn0]
        simpa using congrArg (fun m => (C.circuit m).encode) hn0.symm
    · have hn1 : ¬ n ≤ 1 := by omega
      have hstrip : strip w = pairEncode x (C.circuit n).encode := by
        simp only [strip, hw, pairDecode_pairEncode, α, if_neg hn1, padAdvice,
          splitAtLastTrue_pad]
      simp only [G, hfw, ← hn, hstrip, pairSndD_pairEncode]
      rw [if_neg (by simp; omega), if_neg (by simp; omega)]
  have h2 : M.ComputesInTime w [MultiTapeTM.indicator (C.language : Set (List Bool)) x]
      (K * (w.length + 1) ^ e) := by
    convert h using 1
    simp only [Function.comp_apply, pairFstD_pairEncode, hw]
    rw [← hw, hGw]
    exact (verdict_encode_family C hfan x).symm
  refine h2.mono ?_
  dsimp only
  -- the time bound
  have hlen : w.length = 2 * n + 2 + n ^ d := by
    simp only [hw, pairEncode, List.length_append, List.length_flatMap, List.length_cons,
      List.length_nil, hαlen]
    simp [List.sum_replicate, hn]
    ring
  have hd1 : 1 ≤ d := by omega
  have hP1 : n + 1 ≤ (n + 1) ^ d := Nat.le_self_pow (by omega) _
  have hP2 : n ^ d ≤ (n + 1) ^ d := Nat.pow_le_pow_left (by omega) _
  have hwb : w.length + 1 ≤ 4 * (n + 1) ^ d := by rw [hlen]; omega
  exact time_le_of_length_le hwb

/-- `BoolCircuit.PPoly ⊆ Complexity.PAdvicePoly`, the set form of
`Complexity.PPoly_subset_PAdvicePoly`. [AB09, Thm 6.18, `⊆`] -/
theorem PPoly_subset_PAdvicePoly' : BoolCircuit.PPoly ⊆ PAdvicePoly :=
  PPoly_subset_PAdvicePoly

end Complexity
