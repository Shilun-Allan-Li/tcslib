/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.TuringMachine.Universal
import TCSlib.Complexity.TuringMachine.Encoding
import TCSlib.Cryptography.Asymptotic.OneWay
import TCSlib.Cryptography.Asymptotic.CollectionsLemmas
import TCSlib.Cryptography.Asymptotic.UniversalLemmas
import TCSlib.Cryptography.Asymptotic.UniversalPadding
import TCSlib.Cryptography.OneWayFunctions.OutputLength
import Mathlib.Data.Nat.Log

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Levin's universal one-way function

The universal one-way function of [PS10, §2.13]: `f_universal` interprets its input `y` as a
machine–input pair `⟨M, x⟩` with `|M| = ⌊log₂ |y|⌋`, runs `M` on `x` for a cubic number of
steps through the clocked universal machine `Turing.timed_universal_concrete`, and outputs
`⟨M, M(x)⟩` (or `⟨M, ⊥⟩` on timeout). [PS10, Theorem 63.1] says that `f_universal` is one-way
as soon as *some* one-way function exists; the proof shows weak one-wayness with `q(n) = n³`
through [PS10, Lemma 64.3] (a strong one-way function computable in quadratic time, by
padding) and the two counting claims of [PS10, p. 65] (`PickG`, the union bound), then applies
Yao's amplification [PS10, Theorem 35.1] (`weak_to_strong`).

**Deviation (source error, DESIGN §7, error 1):** [PS10, Algorithm 64.2] outputs `M(x)` only;
an inverter may then answer `⟨M', x'⟩` with `M' ≠ M_g`, which yields no preimage under `M_g`,
and the proof of Theorem 63.1 is invalid. The corrected function outputs `⟨M, M(x)⟩` (Levin's
definition). The budget `|y|³` becomes `(|y| + 1)³` (error 19); the timeout symbol `⊥` is
`[false]`, distinct from every successful answer `true :: M(x)` (`Turing.timed_universal`).

**Deviation (encoding of machines):** the text "assumes a standard way to encode Turing
machines with appropriate padding"; here the encoding is an arbitrary effective scheme
`c : Turing.EffectiveMachineCode` ([AB09, §1.4], `decode_encode_pad`), and the clocked
simulation costs the code-dependent coefficient of `Turing.timed_universal_concrete`, which
includes `c.canonizerTime |M|`. The theorems assume a canonizer at most exponential in the code
length (`CanonizerExp c`), so that the coefficient is polynomial in `n` for codes of length
`⌊log₂ n⌋`; no bound on the canonizer of `Turing.exists_effectiveMachineCode` is available,
so the headlines `fUniversal_easy`, `fUniversal_hard`, `fUniversal_weakOneWay` and
`theorem_63_1` are **conditional** on this hypothesis — ratified by the run-3 audit (P3-4) as
an explicit hypothesis in the manner of the arithmetic bundle `Candidates.ArithmeticFP`
(plan D11); the open problem of exhibiting a scheme with such a canonizer is the sorried
`exists_canonizerExp`.

**Deviation (typed domains, D5):** `fUniversal c` is `FunFamily.ofString` of the string
function with the output-length polynomial `univOutLen` (outputs padded with `false`, never
truncated by `length_fUniversalStr_le`); the `g'` of Lemma 64.3 is a family with `inLen = var`
computable by a coded machine on the bare input (`FunFamily.QuadraticCode`).

## Main definitions

* `TCSlib.Cryptography.clockedAnswer`, `TCSlib.Cryptography.univCoeff` — the answer and the
  coefficient of the clocked universal simulation.
* `TCSlib.Cryptography.univCode`, `TCSlib.Cryptography.univArg`,
  `TCSlib.Cryptography.fUniversalStr`, `TCSlib.Cryptography.univOutLen`,
  `TCSlib.Cryptography.fUniversal` — `f_universal` [PS10, Algorithm 64.2], corrected.
* `TCSlib.Cryptography.CanonizerExp` — the hypothesis on the encoding scheme;
  `TCSlib.Cryptography.FunFamily.QuadraticCode` — computable by a coded machine in time
  `c₀ (|x| + 1)²` [PS10, Lemma 64.3].

## Main results

* `TCSlib.Cryptography.exists_univ_computes` — the clocked universal machine computes
  `clockedAnswer` (repackaging of `Turing.timed_universal_concrete`); the serialization-length
  facts it needs live in `TCSlib.Cryptography.Asymptotic.UniversalLemmas`;
  `TCSlib.Cryptography.exists_univCoeff_le` — its coefficient is polynomial on codes of
  length `⌊log₂ n⌋` under `CanonizerExp`; `TCSlib.Cryptography.exists_canonizerExp` — the
  open problem that some scheme satisfies `CanonizerExp` (sorried, run-3 audit P3-4).
* `TCSlib.Cryptography.fUniversal_easy` — `f_universal` is polynomial-time computable
  [PS10, Algorithm 64.2, "computable in time `O(|y|³)`"] (proved; the evaluator is assembled
  from `polyTimeComputable_univCode`, `polyTimeComputable_univArg`,
  `polyTimeComputable_clockedAnswer` and `polyTimeComputable_fUniversalStr`, with the generic
  padding and splitting lemmas of `TCSlib.Cryptography.Asymptotic.CollectionsLemmas` and
  `TCSlib.Cryptography.Asymptotic.UniversalLemmas`).
* `TCSlib.Cryptography.lemma_64_3` — a strong one-way function computable in quadratic time
  [PS10, Lemma 64.3] (from `PadQuad.exists_family` of
  `TCSlib.Cryptography.Asymptotic.UniversalPadding`; one machine admission remains, see the
  fill note).
* `TCSlib.Cryptography.claim_65_1`, `claim_65_2`, `claim_65_2_cond` — `PickG` and the union
  bound [PS10, p. 65].
* `TCSlib.Cryptography.fUniversal_hard`, `TCSlib.Cryptography.fUniversal_weakOneWay`,
  `TCSlib.Cryptography.theorem_63_1` — `f_universal` is weakly one-way with `q(n) = n³`, hence
  (after amplification) strongly one-way [PS10, Theorem 63.1] (`fUniversal_hard` and
  `fUniversal_weakOneWay` are proved from the hypothesis of `lemma_64_3`; `theorem_63_1`
  depends on `lemma_64_3`, which is sorried, see its fill note).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§2.13: Theorem 63.1, Algorithm 64.2, Lemma 64.3.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §2.4 (Lemma 2.3, padding) and Exercise 2.4.
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§1.4: encodings of machines, universal simulation.)
-/

namespace TCSlib.Cryptography

open Complexity Turing Finset

/-! ## The clocked universal simulation -/

/-- The answer of the clocked simulation of the coded machine `c.decode α` on the input `x`
with the budget `t`: `true :: output` if the machine has halted within `t` steps (deadline
included), `[false]` (the `⊥` of [PS10, Algorithm 64.2]) otherwise — the output convention of
`Turing.timed_universal`. -/
def clockedAnswer (c : EffectiveMachineCode) (α x : List Bool) (t : ℕ) : List Bool :=
  if ((c.decode α).tm.runFrom ((c.decode α).tm.initCfg x) t).state = none then
    true :: ((c.decode α).tm.runFrom ((c.decode α).tm.initCfg x) t).output
  else [false]

/-- The code-dependent coefficient of the quadratic time bound of the clocked universal
simulation, as displayed in `Turing.timed_universal_concrete` (startup part
`3|α| + canonizerTime |α| + |serialize| + 2|bits numStates| + 2 q₀ + 16`, then
`Turing.universalBlockBound c α + 14`). -/
def univCoeff (c : EffectiveMachineCode) (α : List Bool) : ℕ :=
  3 * α.length + c.canonizerTime α.length + (c.decode α).serialize.length +
    2 * (Nat.bits (c.decode α).numStates).length + 2 * (c.decode α).tm.q₀.val + 16 +
    universalBlockBound c α + 14

/-- If the coded machine computes `out` from `x` within `t` steps, the clocked answer is
`true :: out`. -/
theorem clockedAnswer_eq_cons_of_computesInTime (c : EffectiveMachineCode) {α x out : List Bool}
    {t : ℕ} (h : (c.decode α).toFinTM.ComputesInTime x out t) :
    clockedAnswer c α x t = true :: out := by
  obtain ⟨hs, ho⟩ := (FinTM.computesInTime_iff _ _ _ _).mp h
  have hs' : ((c.decode α).tm.runFrom ((c.decode α).tm.initCfg x) t).state = none := hs
  have ho' : ((c.decode α).tm.runFrom ((c.decode α).tm.initCfg x) t).output = out := ho
  unfold clockedAnswer
  rw [if_pos hs', ho']

/-- If the coded machine does not halt on `x` within `t` steps, the clocked answer is the
timeout symbol `[false]`. -/
theorem clockedAnswer_eq_false_of_not_computesInTime (c : EffectiveMachineCode)
    {α x : List Bool} {t : ℕ} (h : ∀ out, ¬ (c.decode α).toFinTM.ComputesInTime x out t) :
    clockedAnswer c α x t = [false] := by
  have hs : ((c.decode α).tm.runFrom ((c.decode α).tm.initCfg x) t).state ≠ none := by
    intro hs
    exact h _ ((FinTM.computesInTime_iff (c.decode α).toFinTM _ _ _).mpr ⟨hs, rfl⟩)
  unfold clockedAnswer
  rw [if_neg hs]

/-- The clocked answer has at most `t + 1` bits (a machine emits at most one symbol per step,
`Turing.MultiTapeTM.output_length_le`). -/
theorem length_clockedAnswer_le (c : EffectiveMachineCode) (α x : List Bool) (t : ℕ) :
    (clockedAnswer c α x t).length ≤ t + 1 := by
  unfold clockedAnswer
  split_ifs
  · simp only [List.length_cons]
    exact Nat.add_le_add_right ((c.decode α).tm.output_length_le x t) 1
  · simp

/-- **The clocked universal machine** [AB09, §1.4.1; `Turing.timed_universal_concrete`]: one
machine `U` which, on `⟨⟨bits t, α⟩, x⟩`, outputs `clockedAnswer c α x t` within
`univCoeff c α · (t + 1)²` steps, for every code `α`, input `x` and budget `t`.

**Proof sketch.** The simulator of `Turing.timed_universal_concrete c`: success clause with
`clockedAnswer_eq_cons_of_computesInTime`, or timeout clause with
`clockedAnswer_eq_false_of_not_computesInTime`. -/
theorem exists_univ_computes (c : EffectiveMachineCode) :
    ∃ U : FinTM Bool, ∀ (α x : List Bool) (t : ℕ),
      U.ComputesInTime (pairEncode (pairEncode (Nat.bits t) α) x) (clockedAnswer c α x t)
        (univCoeff c α * (t + 1) ^ 2) := by
  obtain ⟨U, hU⟩ := timed_universal_concrete c
  refine ⟨U, fun α x t => ?_⟩
  by_cases h : ∃ out, (c.decode α).toFinTM.ComputesInTime x out t
  · obtain ⟨out, hout⟩ := h
    rw [clockedAnswer_eq_cons_of_computesInTime c hout]
    exact (hU α x t).1 out hout
  · push_neg at h
    rw [clockedAnswer_eq_false_of_not_computesInTime c h]
    exact (hU α x t).2 h

/-! ## Algorithm 64.2: the universal function -/

/-- The code field of `y`: its first `⌊log₂ |y|⌋` bits ("interpret `y` as `⟨M, x⟩` where
`|M| = log |y|`", [PS10, Algorithm 64.2]). -/
def univCode (y : List Bool) : List Bool := y.take (Nat.log 2 y.length)

/-- The argument field of `y`: the bits after the first `⌊log₂ |y|⌋` [PS10, Algorithm 64.2]. -/
def univArg (y : List Bool) : List Bool := y.drop (Nat.log 2 y.length)

/-- The code field has exactly `⌊log₂ |y|⌋` bits. -/
@[simp] theorem length_univCode (y : List Bool) : (univCode y).length = Nat.log 2 y.length := by
  simp [univCode, Nat.log_le_self]

/-- The argument field has `|y| - ⌊log₂ |y|⌋` bits. -/
@[simp] theorem length_univArg (y : List Bool) : (univArg y).length = y.length - Nat.log 2 y.length := by
  simp [univArg]

/-- The code field of `α ++ x` is `α` when `|α| = ⌊log₂ (|α| + |x|)⌋`. -/
theorem univCode_append {α x : List Bool} (hα : α.length = Nat.log 2 (α.length + x.length)) :
    univCode (α ++ x) = α := by
  simp only [univCode, List.length_append, ← hα]
  exact List.take_left

/-- The argument field of `α ++ x` is `x` when `|α| = ⌊log₂ (|α| + |x|)⌋`. -/
theorem univArg_append {α x : List Bool} (hα : α.length = Nat.log 2 (α.length + x.length)) :
    univArg (α ++ x) = x := by
  simp only [univArg, List.length_append, ← hα]
  exact List.drop_left

/-- **`f_universal` as a string function** [PS10, Algorithm 64.2, corrected]: interpret `y` as
`⟨M, x⟩` with `|M| = ⌊log₂ |y|⌋`, run `M` on `x` for `(|y| + 1)³` steps, and output `⟨M, M(x)⟩`
(`M(x)` prefixed by `true`) if `M` halts, `⟨M, ⊥⟩` (`⊥ = [false]`) otherwise.

**Deviation:** the output carries the code `M` (DESIGN §7, error 1); budget `(|y| + 1)³`
(error 19); machines are decoded by the effective scheme `c`. -/
def fUniversalStr (c : EffectiveMachineCode) (y : List Bool) : List Bool :=
  pairEncode (univCode y) (clockedAnswer c (univCode y) (univArg y) ((y.length + 1) ^ 3))

/-- The output-length polynomial of `f_universal`: `2n + 3 + (n + 1)³`, a bound on
`|⟨M, answer⟩| = 2|M| + 2 + |answer| ≤ 2⌊log₂ n⌋ + 2 + (n + 1)³ + 1`. -/
def univOutLen : PolyExpr :=
  .add (.add (.mul (.const 2) .var) (.const 3)) (.pow (.add .var (.const 1)) 3)

/-- `univOutLen` evaluates to `2n + 3 + (n + 1)³`. -/
@[simp] theorem eval_univOutLen (n : ℕ) : univOutLen.eval n = 2 * n + 3 + (n + 1) ^ 3 := rfl

/-- The output of `f_universal` on `y` has at most `univOutLen |y|` bits (so the family
`fUniversal` pads and never truncates). -/
theorem length_fUniversalStr_le (c : EffectiveMachineCode) (y : List Bool) :
    (fUniversalStr c y).length ≤ univOutLen.eval y.length := by
  simp only [fUniversalStr, length_pairEncode, length_univCode, eval_univOutLen]
  have h₁ := length_clockedAnswer_le c (univCode y) (univArg y) ((y.length + 1) ^ 3)
  have h₂ := Nat.log_le_self 2 y.length
  omega

/-- On a well-formed `y = α ++ x` (`|α| = ⌊log₂ |y|⌋`) whose coded machine computes `out`
from `x` within the budget, `f_universal (y) = ⟨α, true :: out⟩`: the evaluation step
"`f_universal (⟨M_g, x⟩) = ⟨M_g, g(x)⟩`" of the proof of [PS10, Theorem 63.1]. -/
theorem fUniversalStr_append_of_computesInTime (c : EffectiveMachineCode) {α x out : List Bool}
    {t : ℕ} (hα : α.length = Nat.log 2 (α.length + x.length))
    (h : (c.decode α).toFinTM.ComputesInTime x out t) (ht : t ≤ (α.length + x.length + 1) ^ 3) :
    fUniversalStr c (α ++ x) = pairEncode α (true :: out) := by
  simp only [fUniversalStr, univCode_append hα, univArg_append hα, List.length_append]
  rw [clockedAnswer_eq_cons_of_computesInTime c (h.mono ht)]

/-- **`f_universal` as a function family** [PS10, Algorithm 64.2]: parameter = input length,
output length `univOutLen` (the string output padded with `false`, never truncated by
`length_fUniversalStr_le`). -/
def fUniversal (c : EffectiveMachineCode) : FunFamily :=
  FunFamily.ofString (fUniversalStr c) univOutLen

/-- The padded reading of a string: `List.ofFn (fun i : Fin p => w.getD i false)` is
`(w ++ 0^p).take p` (the encoding of `FunFamily.ofString`'s output). -/
theorem ofFn_getD_eq_take (w : List Bool) (p : ℕ) :
    List.ofFn (fun i : Fin p => w.getD i false) = (w ++ List.replicate p false).take p :=
  ofFn_padFin_eq_take p w

/-- The encoding of `fUniversal c` at parameter `n` is the string output padded with `false`
to `univOutLen n` bits. -/
theorem ofFn_fUniversal_f (c : EffectiveMachineCode) (n : ℕ) (x : Fin n → Bool) :
    List.ofFn ((fUniversal c).f n x) =
      (fUniversalStr c (List.ofFn x) ++ List.replicate (univOutLen.eval n) false).take
        (univOutLen.eval n) :=
  ofFn_getD_eq_take _ _

/-! ## The encoding hypothesis and the polynomial coefficient -/

/-- The canonizer of the encoding scheme `c` runs in time at most exponential in the code
length: `canonizerTime k ≤ A · 2^{B k}`. For codes of length `⌊log₂ n⌋` the coefficient
`univCoeff` of the clocked simulation is then polynomial in `n` (`exists_univCoeff_le`), which
is what makes `f_universal` polynomial-time computable.

**Deviation:** [PS10] assumes a standard encoding with an implicit efficient universal
simulation; here the simulation cost of the arbitrary effective scheme `c` is made explicit
through this hypothesis (no bound is known for `Turing.exists_effectiveMachineCode`). -/
def CanonizerExp (c : EffectiveMachineCode) : Prop :=
  ∃ A B : ℕ, ∀ k, c.canonizerTime k ≤ A * 2 ^ (B * k)

/-- **Open problem (run-3 audit P3-4): some effective encoding scheme has a canonizer at most
exponential in the code length.** The standard encodings have polynomial canonizers (parse and
re-serialize), so the hypothesis `CanonizerExp c` of `theorem_63_1` is mathematically harmless
and is accepted as an explicit hypothesis (plan D11, like `Candidates.ArithmeticFP`); but the
only scheme in the library, `Turing.exists_effectiveMachineCode`, carries a `canonizerTime`
defined as a finite maximum of halting times with no bound, so no instance is available and the
headlines of this file are conditional. This statement records the gap.

**Proof sketch.** Build a scheme in the `Build/` style: keep the serialization
`Turing.CodeTM.serialize` and the parser `Turing.codeDecode` of
`TCSlib.Complexity.TuringMachine.MathlibBridge`, and implement the canonizer as an explicit
finite machine performing the parse of the `9 · (numStates + 1)` fixed-format records (with the
up-front minimum-length guard) followed by re-serialization — the superseded composition route
described in `MathlibBridge` — through the combinators of
`TCSlib.Complexity.TuringMachine.Composition` and the primitives of
`TCSlib.Complexity.TuringMachine.Build`; its running time is polynomial in the code length,
in particular `≤ A · 2^{B k}`. -/
theorem exists_canonizerExp : ∃ c : EffectiveMachineCode, CanonizerExp c := by
  sorry

/-- **The coefficient is polynomial on codes of logarithmic length.** If `c` has an
exponential canonizer, there is a syntactic polynomial `p` with
`univCoeff c α ≤ p(n)` for every `n` and every code `α` of length `⌊log₂ n⌋`.

**Proof sketch.** With `A, B` from `CanonizerExp c` and `k = |α| = ⌊log₂ n⌋`:
`canonizerTime k ≤ A · 2^{Bk} = A (2^k)^B ≤ A (n + 1)^B` (`Nat.pow_log_le_self`, `pow_mul`);
`|serialize| ≤ canonizerTime k` (`length_serialize_decode_le`); `numStates + 1 ≤ |serialize|`
(`numStates_add_one_le_length_serialize`), so `|bits numStates| ≤ numStates`
(`Turing.length_bits_le_self`) and `q₀.val ≤ numStates` are below `|serialize|`;
`Turing.universalBlockBound c α = 3|serialize| + 5(numStates + 1) + 20`; and `3k ≤ 3n`
(`Nat.log_le_self`). Collecting, `univCoeff c α ≤ 3n + 14 A (n + 1)^B + 60`. -/
theorem exists_univCoeff_le (c : EffectiveMachineCode) (hc : CanonizerExp c) :
    ∃ p : PolyExpr, ∀ (n : ℕ) (α : List Bool), α.length = Nat.log 2 n →
      univCoeff c α ≤ p.eval n := by
  obtain ⟨A, B, hAB⟩ := hc
  refine ⟨.add (.add (.mul (.const 3) .var)
    (.mul (.const 14) (.mul (.const A) (.pow (.add .var (.const 1)) B)))) (.const 60),
    fun n α hα => ?_⟩
  simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var,
    PolyExpr.eval_pow]
  have h2k : 2 ^ Nat.log 2 n ≤ n + 1 := by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · exact (Nat.pow_log_le_self 2 hn.ne').trans (Nat.le_succ n)
  have hT : c.canonizerTime α.length ≤ A * (n + 1) ^ B := by
    calc c.canonizerTime α.length ≤ A * 2 ^ (B * α.length) := hAB _
      _ = A * (2 ^ Nat.log 2 n) ^ B := by rw [hα, mul_comm B, pow_mul]
      _ ≤ A * (n + 1) ^ B := Nat.mul_le_mul_left A (Nat.pow_le_pow_left h2k B)
  have hS := length_serialize_decode_le c α
  have hN := numStates_add_one_le_length_serialize (c.decode α)
  have hb := length_bits_le_self (c.decode α).numStates
  have hq := (c.decode α).tm.q₀.isLt
  have hk : α.length ≤ n := hα ▸ Nat.log_le_self 2 n
  simp only [univCoeff, universalBlockBound]
  omega

/-! ## The evaluator machine of `f_universal` -/

/-- Composition of polynomial-time functions, in applied form (private copy of the helper
of `TCSlib.Complexity.Randomized.Closure`). -/
private theorem ptc_comp {g f : List Bool → List Bool} (hg : PolyTimeComputable g)
    (hf : PolyTimeComputable f) : PolyTimeComputable fun z => g (f z) :=
  hg.comp hf

/-- **The code field is polynomial-time**: the typed cut `polyTimeComputable_pairTakePoly var`
on `⟨(bits |y|).tail, y⟩` keeps the first `⌊log₂ |y|⌋` bits (`length_tail_bits`). -/
theorem polyTimeComputable_univCode : PolyTimeComputable univCode := by
  have h := ptc_comp (polyTimeComputable_pairTakePoly .var)
    (polyTimeComputable_logMarker.pairEncode polyTimeComputable_id)
  convert h using 1
  funext y
  simp only [univCode, pairFstD_pairEncode, pairSndD_pairEncode, PolyExpr.eval_var, id_eq,
    length_tail_bits]

/-- **The argument field is polynomial-time**: the typed cut `polyTimeComputable_pairDropPoly var`
on `⟨(bits |y|).tail, y⟩` drops the first `⌊log₂ |y|⌋` bits (`length_tail_bits`). -/
theorem polyTimeComputable_univArg : PolyTimeComputable univArg := by
  have h := ptc_comp (polyTimeComputable_pairDropPoly .var)
    (polyTimeComputable_logMarker.pairEncode polyTimeComputable_id)
  convert h using 1
  funext y
  simp only [univArg, pairFstD_pairEncode, pairSndD_pairEncode, PolyExpr.eval_var, id_eq,
    length_tail_bits]

/-- The input `⟨⟨bits ((|y| + 1)³), univCode y⟩, univArg y⟩` of the clocked universal machine
is polynomial-time in `y`. -/
theorem polyTimeComputable_univInput :
    PolyTimeComputable fun y : List Bool =>
      pairEncode (pairEncode (Nat.bits ((y.length + 1) ^ 3)) (univCode y)) (univArg y) :=
  (polyTimeComputable_univBudget.pairEncode polyTimeComputable_univCode).pairEncode
    polyTimeComputable_univArg

/-- **The clocked simulation is polynomial-time** for a scheme with an exponential
canonizer: `y ↦ clockedAnswer c (univCode y) (univArg y) ((|y| + 1)³)`.

**Proof sketch.** `Turing.FinTM.exists_comp_on_image` with the machine of
`polyTimeComputable_univInput` (time `C (n + 1)^d`) and the universal machine `U` of
`exists_univ_computes c`, which on the image maps `⟨⟨bits t, univCode y⟩, univArg y⟩` to the
clocked answer within `univCoeff c (univCode y) · (t + 1)² ≤ p(|y|) · ((|y| + 1)³ + 1)²`
(`exists_univCoeff_le` at `n := |y|`, `length_univCode`, `ComputesInTime.mono`); the total
`2 C (n + 1)^d + p(n)((n + 1)³ + 1)² + 2` is a syntactic polynomial, majorised in normal form
by `PolyExpr.eval_le`. -/
theorem polyTimeComputable_clockedAnswer (c : EffectiveMachineCode) (hc : CanonizerExp c) :
    PolyTimeComputable fun y : List Bool =>
      clockedAnswer c (univCode y) (univArg y) ((y.length + 1) ^ 3) := by
  obtain ⟨M, C, d, hM⟩ := polyTimeComputable_univInput
  obtain ⟨U, hU⟩ := exists_univ_computes c
  obtain ⟨p, hp⟩ := exists_univCoeff_le c hc
  have hU' : ∀ y : List Bool, U.ComputesInTime
      (pairEncode (pairEncode (Nat.bits ((y.length + 1) ^ 3)) (univCode y)) (univArg y))
      (clockedAnswer c (univCode y) (univArg y) ((y.length + 1) ^ 3))
      (p.eval y.length * ((y.length + 1) ^ 3 + 1) ^ 2) := fun y =>
    (hU _ _ _).mono (Nat.mul_le_mul_right _ (hp y.length _ (length_univCode y)))
  obtain ⟨N, hN⟩ := FinTM.exists_comp_on_image M U _ _ (fun n => C * (n + 1) ^ d)
    (fun n => p.eval n * ((n + 1) ^ 3 + 1) ^ 2) hM hU'
  obtain ⟨C', c', hC'⟩ := PolyExpr.eval_le (.add (.add (.mul (.const 2) (.normal C d))
    (.mul p (.pow (.add (.pow (.add .var (.const 1)) 3) (.const 1)) 2))) (.const 2))
  refine ⟨N, C', c', fun y => (hN y).mono ?_⟩
  have h := hC' y.length
  simpa [PolyExpr.eval_normal] using h

/-- **`f_universal` as a string function is polynomial-time** for a scheme with an
exponential canonizer: `⟨univCode y, clockedAnswer …⟩` by `PolyTimeComputable.pairEncode`. -/
theorem polyTimeComputable_fUniversalStr (c : EffectiveMachineCode) (hc : CanonizerExp c) :
    PolyTimeComputable (fUniversalStr c) :=
  polyTimeComputable_univCode.pairEncode (polyTimeComputable_clockedAnswer c hc)

/-- **`f_universal` is easy to compute** [PS10, Algorithm 64.2: "clearly `f_universal` is
computable in time `O(|y|³)`"]: for a scheme with an exponential canonizer, `fUniversal c` is
`Easy`.

**Deviation:** the evaluator is a deterministic polynomial-time machine on `⟨1^n, y⟩` (D3); the
time is `p(n) · ((n+1)³ + 1)²` with the coefficient polynomial `p` of `exists_univCoeff_le`,
not the text's `O(|y|³)` (the simulation overhead of `Turing.timed_universal_concrete` is
quadratic in the budget).

**Proof sketch.** The evaluator on `z = ⟨1^n, y⟩` (`y := pairSndD z`) is built in the FP
calculus of `ClassNP/PolyTimePairing.lean` plus one timed composition: (1) *the split at
`⌊log₂ |y|⌋`:* `Nat.bits |y|` (`Turing.FinTM.computesFunInTime_lengthBits`) has
`⌊log₂ |y|⌋ + 1` bits; its tail (`List.drop 1`, linear) paired with `y` and split by
`Turing.FinTM.computesFunInTime_pairSplitAt` gives `⟨univCode y, univArg y⟩`; (2) *the budget*
`Nat.bits ((|y| + 1)³)` by `Turing.FinTM.computesFunInTime_polyBits 1 3`; (3) *the universal
input* `g y := ⟨⟨bits t, univCode y⟩, univArg y⟩` by `PolyTimeComputable.pairEncode`; (4) *the
simulation:* `Turing.FinTM.exists_comp_on_image` with `M` computing `g` in time `T₁` and `U`
from `exists_univ_computes c` computing `clockedAnswer c (univCode y) (univArg y) t` on the image
within `T₂ |z| := p(|z|) · ((|z| + 1)³ + 1)²`, where `univCoeff c (univCode y) ≤ p(|y|) ≤ p(|z|)`
by `exists_univCoeff_le` (at `n := |y|`, `length_univCode`) and `PolyExpr.eval_mono`; (5) *the
output* `pairEncode (univCode y) answer` by `PolyTimeComputable.pairEncode`, which is
`fUniversalStr c y`; (6) *the padding* `(w ++ 0^{p(n)}).take (p(n))` with
`0^{p(n)} = zipWith xor 1^{p(n)} 1^{p(n)}` (`Complexity.polyTimeComputable_unaryPoly univOutLen`
on `1^n = pairFstD z`, `Complexity.polyTimeComputable_pairXor`), `PolyTimeComputable.append`,
`Complexity.polyTimeComputable_pairTakePoly univOutLen` on `⟨1^n, w ++ 0^{p(n)}⟩`. Correctness
on `advInput n (List.ofFn x)` is `ofFn_fUniversal_f` with `List.length_ofFn`,
`Turing.pairDecode_pairEncode` and `List.length_replicate`. -/
theorem fUniversal_easy (c : EffectiveMachineCode) (hc : CanonizerExp c) :
    (fUniversal c).Easy := by
  have hF : PolyTimeComputable fun z =>
      padStr univOutLen (pairFstD z) (fUniversalStr c (pairSndD z)) := by
    have h := ptc_comp (polyTimeComputable_padStr univOutLen)
      (polyTimeComputable_pairFstD.pairEncode
        (ptc_comp (polyTimeComputable_fUniversalStr c hc) polyTimeComputable_pairSndD))
    convert h using 1
    funext z
    simp
  refine ⟨_, hF, fun n x => ?_⟩
  simp only [NUPPT.advInput, pairFstD_pairEncode, pairSndD_pairEncode]
  rw [ofFn_fUniversal_f]
  simp [padStr]

/-! ## Lemma 64.3: a strong one-way function computable in quadratic time -/

/-- `𝓕` is *computable in quadratic time by a coded machine*: some `Turing.CodeTM` (one work
tape, binary alphabet — the machines the universal machine interprets) computes
`f n x` from the bare input `x` within `c₀ (|x| + 1)²` steps. This is "`g'` is computable in
time `O(n²)`" of [PS10, Lemma 64.3], at the level of the coded machines of
[PS10, Algorithm 64.2]. -/
def FunFamily.QuadraticCode (𝓕 : FunFamily) : Prop :=
  ∃ (M : CodeTM) (c₀ : ℕ), ∀ n (x : Fin (𝓕.inLen.eval n) → Bool),
    M.toFinTM.ComputesInTime (List.ofFn x) (List.ofFn (𝓕.f n x))
      (c₀ * (𝓕.inLen.eval n + 1) ^ 2)

/-- **Strong one-way functions computable in quadratic time** [PS10, Lemma 64.3]: if there is
a strong one-way function, there is a strong one-way function `g'` with parameter = input
length (`inLen = var`) computable by a coded machine in time `c₀ (n + 1)²` on the bare input.

**Deviation:** the text defines `g'(⟨a, b⟩) = ⟨a, g(b)⟩` on lengths `m = n^c` only and
leaves the recovery of `n` from `m` implicit; the formal `g'` is defined at every length `m`
with the parameter `ν(m) := max {n : P(n) ≤ m}` recovered from the input length, and the
output `a ++ g_{ν m}(b)` is padded with `false` to the syntactic length `2·var` (which it never
exceeds from `P(0)` on; truncated at the finitely many smaller `m`).

Repair (run-3 audit P3-3): the sketch's family is `𝓖 := ⟨var, mul (const 2) var, g'⟩`, not
`⟨var, add var outLen, g'⟩` — padding to `m + outLen(m)` bits is not computable within the
quadratic one-tape budget when `deg outLen ≥ 2`; the raw output has at most `2m` bits. The
"non-constant input length" sub-lemma is unnecessary (`P` is strictly increasing because of its
summand `n`). Statement unchanged.

**Proof sketch.** Let `𝓕` be strong one-way with input length `ℓ := 𝓕.inLen`, evaluator `F`
(`h.easy`) within `C(k + 1)^c`, and `T_F(n) := C(2n + 3 + ℓ(n))^c` its time on `⟨1^n, x⟩`.
*Padding:* `P(n) := ℓ(n) + T_F(n) + n`, strictly increasing (its summand `n`), so
`ν(m) := max {n : P(n) ≤ m}` (`0` below `P(0)`) is well defined, `P(ν m) ≤ m < P(ν m + 1)` for
`m ≥ P(0)`, and `ν` is unbounded; `g'_m(y) := y.take (m - ℓ(ν m)) ++ F ⟨1^{ν m}, y.drop (m - ℓ(ν m))⟩`
padded with `false` to `2m` bits (`𝓖 := ⟨var, mul (const 2) var, g'⟩`): for `m ≥ P(0)` the raw
output has `(m − ℓ(ν m)) + |F ⟨1^{ν m}, b⟩| ≤ m + T_F(ν m) ≤ m + P(ν m) ≤ 2m` bits, an
evaluator's output being no longer than its running time (`PolyTimeComputable.output_length_le`,
as in `Collection.exists_outLenBound`), so the padding is lossless (`ofFn_padFin_of_le`).
*Hardness:* an inverter `A'` of `𝓖` with `1/m^d ≤ invProbAt A' m` infinitely often
(`not_negligible_iff`) gives an inverter of `𝓕` at `n := ν(m)` by `OneWay.invProb_pad_le`
[Gar26, Lemma 2.3] (`OneWay.pad`, `OneWay.padInverter`): sample the padding `a` from the
coins (`NUPPT.exists_split`), call `A'` at the length `m < P(n + 1)` hard-wired as advice
(`NUPPT.exists_reparam_advice` with the majorant `P.subst (add var (const 1))`), project the
`b`-part (`NUPPT.exists_comp`). Two inputs `a ++ b`, `a' ++ b'` of length `m` with equal padded
outputs have equal raw outputs (both raw outputs have length `(m − ℓ(n)) + outLen(n)`, so the
zero-padding to `2m` bits is injective on them, `List.append` of equal-length prefixes), hence
`a' = a` and `f_n(b') = f_n(b)`; `1/m^d ≥ 1/P(n+1)^d` and `not_negligible_iff` contradict
`h.hard`. *Quadratic time:* a multi-tape machine computing `g'` in linear time `O(m)` — the
parameter `1^{ν m}` by incremental unary counting (the powers `(n+1)^j`, `j ≤ deg P`, kept on
`deg P` tapes and updated by the binomial identity, total cost
`∑_{n ≤ ν m} O((n+1)^{deg P - 1}) = O(m)`), then `1^{ℓ(ν m)}`
(`Turing.FinTM.computesFunInTime_polyUnary`, cost `O(P(ν m)) = O(m)`), the split and the copy
(`pairSplitAt`, `pairConcat`), the call of `F` (cost `T_F(ν m) ≤ m`), the padding to `2m` bits
(`O(m)` steps); then `Turing.FinTM.one_work_tape_binary` gives a one-work-tape binary machine
within `c (O(m) + 1)² = O(m²)` and `Turing.exists_codeTM` a `CodeTM` with the same runs.
Sub-obligations: the identification of `g'` with `OneWay.pad`, and the linear-time
parameter-recovery machine (the only new machine; `Turing.FinTM.computesFunInTime_splitSolve`
solves the same length equation in time `(m+1)^{e+2}`, too slow for a quadratic one-tape
bound).

**Fill note (run 4).** Proved in `TCSlib.Cryptography.Asymptotic.UniversalPadding`
(`PadQuad.exists_family`: the padded family `PadQuad.family` with `ν m = max {n : n^d ≤ m}`,
its one-wayness `PadQuad.strongOneWay` and `PadQuad.quadraticCode_of_linear`) **modulo one
machine admission**, `PadQuad.exists_linearTime_gStr`: a *linear-time multitape* evaluator of
the padded function (`one_work_tape_binary` squares the time, so quadratic one-tape time needs
linear multitape time). No assembly of the timed catalogue is output-linear for the parameter
recovery `1^m ↦ 1^{ν m}`: `computesFunInTime_polyUnary C e` costs `(n+1)^{e+1}` for an output of
length `C(n+1)^e`, `computesFunInTime_comp` evaluates the second bound at the *time* of the
first stage (only `exists_comp_on_image` avoids this), `pairMapSnd` charges the whole pair, and
the loop combinators charge rounds × maximal round cost; the missing primitive is a bespoke
linear-time unary root (or an output-linear binary-to-unary converter), see the construction
sketch of `PadQuad.exists_linearTime_gStr`. -/
theorem lemma_64_3 (h : ∃ 𝓕 : FunFamily, 𝓕.StrongOneWay) :
    ∃ 𝓖 : FunFamily, 𝓖.inLen = .var ∧ 𝓖.StrongOneWay ∧ 𝓖.QuadraticCode :=
  PadQuad.exists_family h

/-! ## Claims 65.1 and 65.2: the counting steps -/

/-- **`PickG`** [PS10, p. 65, Claim 65.1 of the inventory]: for a uniform `y ∈ {0,1}^n` and any
fixed code `code` of `⌊log₂ n⌋` bits (the description of `M_g` padded to that length), the
first `⌊log₂ n⌋` bits of `y` equal `code` with probability `2^{-⌊log₂ n⌋} ≥ 1/n`.

**Proof sketch.** Split `y` as `(prefix, rest)` by `Fin.appendEquiv` (`uprob_comp_equiv`); the
event is a point event on the first component (`uprob_fst`, `OneWay.uprob_eq_one_div_card`),
of probability `1/2^k`, and `2^k ≤ n` (`Nat.pow_log_le_self`). -/
theorem claim_65_1 (n : ℕ) (hn : n ≠ 0) (code : Fin (Nat.log 2 n) → Bool) :
    1 / (n : ℝ) ≤ uprob fun y : Fin n → Bool =>
      (List.ofFn y).take (Nat.log 2 n) = List.ofFn code := by
  have hkn : Nat.log 2 n ≤ n := Nat.log_le_self 2 n
  have hcast : Nat.log 2 n + (n - Nat.log 2 n) = n := by omega
  let e : (Fin (Nat.log 2 n) → Bool) × (Fin (n - Nat.log 2 n) → Bool) ≃ (Fin n → Bool) :=
    (Fin.appendEquiv (Nat.log 2 n) (n - Nat.log 2 n)).trans
      (Equiv.arrowCongr (finCongr hcast) (Equiv.refl Bool))
  rw [← uprob_comp_equiv e]
  have hP : (fun z : (Fin (Nat.log 2 n) → Bool) × (Fin (n - Nat.log 2 n) → Bool) =>
      (List.ofFn (e z)).take (Nat.log 2 n) = List.ofFn code) = fun z => z.1 = code := by
    funext z
    have h1 : List.ofFn (e z) = List.ofFn z.1 ++ List.ofFn z.2 := by
      rw [← List.ofFn_fin_append]
      exact (List.ofFn_congr hcast (Fin.append z.1 z.2)).symm
    rw [h1, List.take_left' (List.length_ofFn (f := z.1)), List.ofFn_inj]
  rw [hP, uprob_fst (fun a : Fin (Nat.log 2 n) → Bool => a = code), OneWay.uprob_eq_one_div_card]
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin]
  have h2 : ((2 ^ Nat.log 2 n : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.pow_log_le_self 2 hn
  have hpos : (0 : ℝ) < ((2 ^ Nat.log 2 n : ℕ) : ℝ) := by positivity
  exact one_div_le_one_div_of_le hpos h2

/-- **The union bound** [PS10, p. 65, the displayed inequalities]: if `A` inverts with
probability more than `1 - 1/n³` (`Invert`) and the code field is `M_g` with probability at
least `1/n` (`PickG`), then `Pr[¬Invert ∨ ¬PickG] ≤ 1/n³ + (1 - 1/n)`, i.e.
`Pr[Invert ∧ PickG] ≥ 1/n - 1/n³` (which is `≥ 1/n³` for `n ≥ 2`, the text's bound).

**Proof sketch.** `uprob_or_le` on the complements and `uprob_not`. -/
theorem claim_65_2 {Ω : Type*} [Fintype Ω] [Nonempty Ω] (Invert PickG : Ω → Prop) (n : ℕ)
    (hI : 1 - 1 / (n : ℝ) ^ 3 < uprob Invert) (hP : 1 / (n : ℝ) ≤ uprob PickG) :
    1 / (n : ℝ) - 1 / (n : ℝ) ^ 3 ≤ uprob fun w => Invert w ∧ PickG w := by
  have h1 : uprob (fun w => ¬ (Invert w ∧ PickG w)) ≤
      uprob (fun w => ¬ Invert w) + uprob (fun w => ¬ PickG w) := by
    calc uprob (fun w => ¬ (Invert w ∧ PickG w))
        = uprob (fun w => ¬ Invert w ∨ ¬ PickG w) := by
          congr 1
          funext w
          exact propext not_and_or
      _ ≤ _ := uprob_or_le _ _
  rw [uprob_not, uprob_not, uprob_not] at h1
  linarith

/-- The probability of an event on the fibre over a fixed first coordinate is at most
`|α|` times its probability on the product: `Pr_b[E(a, b)] ≤ |α| · Pr_{(a', b)}[E]`
(Fubini, `uprob_prod`, one term of the average). -/
theorem uprob_fiber_le_card_mul {α β : Type*} [Fintype α] [Fintype β] (E : α × β → Prop)
    (a : α) : uprob (fun b => E (a, b)) ≤ Fintype.card α * uprob E := by
  haveI : Nonempty α := ⟨a⟩
  rw [uprob_prod, uexp]
  have hcard : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [mul_div_cancel₀ _ hcard]
  exact Finset.single_le_sum (f := fun a' => uprob fun b => E (a', b))
    (fun a' _ => uprob_nonneg _) (Finset.mem_univ a)

/-- **The conditional form of the union bound** (the form the reduction of
[PS10, Theorem 63.1] uses): if `Invert` has probability at least `1 - 1/n³` on the product
`α × β` with `|α| ≤ n` (the code field, `|α| = 2^{⌊log₂ n⌋}`), then conditioned on the code
field being `a` — i.e. on the fibre — `Invert` has probability at least `1 - 1/n²`.

**Proof sketch.** `uprob_fiber_le_card_mul` for the complement: `Pr_b[¬Invert(a, b)] ≤ |α| ·
Pr[¬Invert] ≤ n · (1/n³) = 1/n²`, then `uprob_not`. -/
theorem claim_65_2_cond {α β : Type*} [Fintype α] [Fintype β] [Nonempty β]
    (Invert : α × β → Prop) (a : α) (n : ℕ) (hn : 0 < n) (hα : Fintype.card α ≤ n)
    (hI : 1 - 1 / (n : ℝ) ^ 3 ≤ uprob Invert) :
    1 - 1 / (n : ℝ) ^ 2 ≤ uprob fun b => Invert (a, b) := by
  haveI : Nonempty α := ⟨a⟩
  have h1 := uprob_fiber_le_card_mul (fun z => ¬ Invert z) a
  rw [uprob_not, uprob_not] at h1
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hcard : (Fintype.card α : ℝ) ≤ n := by exact_mod_cast hα
  have h2 : (Fintype.card α : ℝ) * (1 - uprob Invert) ≤ n * (1 / (n : ℝ) ^ 3) :=
    mul_le_mul hcard (by linarith) (by linarith [uprob_le_one Invert]) (by positivity)
  have h3 : (n : ℝ) * (1 / (n : ℝ) ^ 3) = 1 / (n : ℝ) ^ 2 := by
    field_simp
  linarith

/-! ## Theorem 63.1: the universal one-way function -/

/-! ### The reduction of Theorem 63.1 -/

/-- **Evaluation on the fibre of the code field** [PS10, Theorem 63.1,
"`f_universal(⟨M_g, x⟩) = ⟨M_g, g(x)⟩`"]: for a code of `⌊log₂ n⌋` bits decoding to the
quadratic machine `M_g` of `g` and an argument `x` of `n − ⌊log₂ n⌋` bits,
`fUniversalStr c (code ++ x) = ⟨code, true :: g(x)⟩`.

**Proof sketch.** `fUniversalStr_append_of_computesInTime` with `|code| + |x| = n`: the code
field is `code` (its length is `⌊log₂ n⌋`), the decoded machine is `M_g` (`hdec`), which
computes `g(x)` within `c₀ (|x| + 1)² ≤ (n + 1)³` (`quadratic_le_cubic`). -/
private theorem fUniversalStr_ofFn_eq (c : EffectiveMachineCode) {L : PolyExpr}
    (g : ∀ m, (Fin m → Bool) → Fin (L.eval m) → Bool) (Mg : CodeTM) (c₀ : ℕ)
    (hMg : ∀ m (x : Fin m → Bool),
      Mg.toFinTM.ComputesInTime (List.ofFn x) (List.ofFn (g m x)) (c₀ * (m + 1) ^ 2))
    {n : ℕ} {code : List Bool} (hcode : code.length = Nat.log 2 n) (hdec : c.decode code = Mg)
    (hc₀ : c₀ ≤ n + 1) (x : Fin (n - Nat.log 2 n) → Bool) (y : Fin n → Bool)
    (hy : List.ofFn y = code ++ List.ofFn x) :
    fUniversalStr c (List.ofFn y) = pairEncode code (true :: List.ofFn (g _ x)) := by
  have hkn : Nat.log 2 n ≤ n := Nat.log_le_self 2 n
  have hsum : code.length + (List.ofFn x).length = n := by
    rw [hcode, List.length_ofFn]
    omega
  have hα : code.length = Nat.log 2 (code.length + (List.ofFn x).length) := by
    rw [hsum, hcode]
  have hM : (c.decode code).toFinTM.ComputesInTime (List.ofFn x) (List.ofFn (g _ x))
      (c₀ * ((n - Nat.log 2 n) + 1) ^ 2) := by
    rw [hdec]
    exact hMg _ x
  rw [hy]
  exact fUniversalStr_append_of_computesInTime c hα hM
    (by rw [hsum]; exact quadratic_le_cubic (by omega) hc₀)

/-- The padded encoding of `f_universal (code ++ x)` is the padding evaluator on
`⟨code, true :: g(x)⟩`: the pre-processing of the reduction produces exactly the challenge
`A` expects (`ofFn_fUniversal_f`, `fUniversalStr_ofFn_eq`). -/
private theorem padStr_eq_ofFn_fUniversal_f (c : EffectiveMachineCode) {L : PolyExpr}
    (g : ∀ m, (Fin m → Bool) → Fin (L.eval m) → Bool) (Mg : CodeTM) (c₀ : ℕ)
    (hMg : ∀ m (x : Fin m → Bool),
      Mg.toFinTM.ComputesInTime (List.ofFn x) (List.ofFn (g m x)) (c₀ * (m + 1) ^ 2))
    {n : ℕ} {code : List Bool} (hcode : code.length = Nat.log 2 n) (hdec : c.decode code = Mg)
    (hc₀ : c₀ ≤ n + 1) (x : Fin (n - Nat.log 2 n) → Bool) (y : Fin n → Bool)
    (hy : List.ofFn y = code ++ List.ofFn x) :
    padStr univOutLen (List.replicate n true) (pairEncode code (true :: List.ofFn (g _ x))) =
      List.ofFn ((fUniversal c).f n y) := by
  rw [ofFn_fUniversal_f, fUniversalStr_ofFn_eq c g Mg c₀ hMg hcode hdec hc₀ x y hy, padStr,
    List.length_replicate]

/-- **Inverses on the fibre** [PS10, Theorem 63.1, "`A` outputs `⟨M_g, x'⟩` with
`g(x') = g(x)`"]: if `y'` has the same `f_universal`-value as `y = code ++ x` (code of
`⌊log₂ n⌋` bits decoding to `M_g`), then the argument field of `y'` is some `x'` with
`g(x') = g(x)`.

**Proof sketch.** Both padded outputs are `⟨·, ·⟩ ++ 0^*` with first components of
`⌊log₂ n⌋` bits (`length_univCode`), so `pairEncode_append_eq` gives `univCode y' = code` and
equal padded answers; the answer on `y'` is `clockedAnswer c code x' ((n+1)³) = true :: g(x')`
(`clockedAnswer_eq_cons_of_computesInTime`, budget `quadratic_le_cubic`), and the two
`g`-values have the same length, so they agree (`List.append_inj_left`, `List.ofFn_injective`). -/
private theorem exists_preimage_of_fUniversal_eq (c : EffectiveMachineCode) {L : PolyExpr}
    (g : ∀ m, (Fin m → Bool) → Fin (L.eval m) → Bool) (Mg : CodeTM) (c₀ : ℕ)
    (hMg : ∀ m (x : Fin m → Bool),
      Mg.toFinTM.ComputesInTime (List.ofFn x) (List.ofFn (g m x)) (c₀ * (m + 1) ^ 2))
    {n : ℕ} {code : List Bool} (hcode : code.length = Nat.log 2 n) (hdec : c.decode code = Mg)
    (hc₀ : c₀ ≤ n + 1) (x : Fin (n - Nat.log 2 n) → Bool) (y y' : Fin n → Bool)
    (hy : List.ofFn y = code ++ List.ofFn x) (h : (fUniversal c).f n y' = (fUniversal c).f n y) :
    ∃ x' : Fin (n - Nat.log 2 n) → Bool, List.ofFn x' = univArg (List.ofFn y') ∧ g _ x' = g _ x := by
  have hkn : Nat.log 2 n ≤ n := Nat.log_le_self 2 n
  obtain ⟨x', hx'⟩ := exists_ofFn_eq_of_length (m := n - Nat.log 2 n)
    (w := univArg (List.ofFn y')) (by simp)
  refine ⟨x', hx', ?_⟩
  have h1 := congrArg List.ofFn h
  rw [ofFn_fUniversal_f, ofFn_fUniversal_f,
    take_append_replicate_of_le (by simpa using length_fUniversalStr_le c (List.ofFn y')),
    take_append_replicate_of_le (by simpa using length_fUniversalStr_le c (List.ofFn y)),
    fUniversalStr_ofFn_eq c g Mg c₀ hMg hcode hdec hc₀ x y hy] at h1
  unfold fUniversalStr at h1
  simp only [List.length_ofFn] at h1
  obtain ⟨hcd, hans⟩ := pairEncode_append_eq (by simp [hcode]) h1
  rw [hcd, ← hx'] at hans
  have hM : (c.decode code).toFinTM.ComputesInTime (List.ofFn x') (List.ofFn (g _ x'))
      ((n + 1) ^ 3) := by
    rw [hdec]
    exact (hMg _ x').mono (quadratic_le_cubic (by omega) hc₀)
  rw [clockedAnswer_eq_cons_of_computesInTime c hM, List.cons_append, List.cons_append] at hans
  exact List.ofFn_injective (List.append_inj_left (List.tail_eq_of_cons_eq hans) (by simp))

/-- **The reduction wins on the fibre** [PS10, Theorem 63.1, the displayed bound
`Pr[Invert ∧ PickG]`]: if `A` inverts `f_universal` at parameter `n` with probability more
than `1 − 1/n³`, and `B` at parameter `m = n − ⌊log₂ n⌋` runs `A` on the padded
`⟨code, true :: y⟩` and returns the argument field of its answer, then `B` inverts `g` at `m`
with probability at least `1 − 1/n²`.

**Proof sketch.** Split `{0,1}^n ≃ {0,1}^{⌊log₂ n⌋} × {0,1}^m` (`Fin.appendEquiv`); the
inversion event of `A` on the product has probability `invProbAt A n`
(`invProbAt_eq_uprob`, `uprob_comp_equiv`), so `claim_65_2_cond` with
`2^{⌊log₂ n⌋} ≤ n` (`OneWay.card_log_bits_le`) gives probability `≥ 1 − 1/n²` on the fibre of
the code. On that fibre `B`'s challenge is `A`'s (`padStr_eq_ofFn_fUniversal_f`), `B`'s coins
are `A`'s followed by unread coins (`uprob_comp_equiv`, `uprob_fst`), and `A`'s success gives
`B`'s by `exists_preimage_of_fUniversal_eq` (`uprob_mono`). -/
private theorem invProbAt_reduction_ge (c : EffectiveMachineCode) {L : PolyExpr}
    (g : ∀ m, (Fin m → Bool) → Fin (L.eval m) → Bool) (Mg : CodeTM) (c₀ : ℕ)
    (hMg : ∀ m (x : Fin m → Bool),
      Mg.toFinTM.ComputesInTime (List.ofFn x) (List.ofFn (g m x)) (c₀ * (m + 1) ^ 2))
    (A B : NUPPT) {n : ℕ} (hn : 2 ≤ n) {code : List Bool} (hcode : code.length = Nat.log 2 n)
    (hdec : c.decode code = Mg) (hc₀ : c₀ ≤ n + 1)
    (hBc : A.coinLen n ≤ B.coinLen (n - Nat.log 2 n))
    (hB : ∀ y (r : List Bool), B.runAtL (n - Nat.log 2 n) y r =
      univArg (A.runAtL n (padStr univOutLen (List.replicate n true) (pairEncode code (true :: y)))
        (r.take (A.coinLen n))))
    (hA : 1 - 1 / (n : ℝ) ^ 3 < (fUniversal c).invProbAt A n) :
    1 - 1 / (n : ℝ) ^ 2 ≤ (⟨.var, L, g⟩ : FunFamily).invProbAt B (n - Nat.log 2 n) := by
  have hkn : Nat.log 2 n ≤ n := Nat.log_le_self 2 n
  have hcast : Nat.log 2 n + (n - Nat.log 2 n) = n := by omega
  let e : (Fin (Nat.log 2 n) → Bool) × (Fin (n - Nat.log 2 n) → Bool) ≃ (Fin n → Bool) :=
    (Fin.appendEquiv (Nat.log 2 n) (n - Nat.log 2 n)).trans
      (Equiv.arrowCongr (finCongr hcast) (Equiv.refl Bool))
  have hofn : ∀ z : (Fin (Nat.log 2 n) → Bool) × (Fin (n - Nat.log 2 n) → Bool),
      List.ofFn (e z) = List.ofFn z.1 ++ List.ofFn z.2 := by
    intro z
    rw [← List.ofFn_fin_append]
    exact (List.ofFn_congr hcast (Fin.append z.1 z.2)).symm
  obtain ⟨cf, hcf⟩ := exists_ofFn_eq_of_length (m := Nat.log 2 n) hcode
  let Invert : (Fin (Nat.log 2 n) → Bool) × ((Fin (n - Nat.log 2 n) → Bool) × A.Coins n) → Prop :=
    fun w => ∃ y', A.runAt n (List.ofFn ((fUniversal c).f n (e (w.1, w.2.1)))) w.2.2 = List.ofFn y' ∧
      (fUniversal c).f n y' = (fUniversal c).f n (e (w.1, w.2.1))
  have hInv : uprob Invert = (fUniversal c).invProbAt A n := by
    rw [FunFamily.invProbAt_eq_uprob]
    let e' : (Fin (Nat.log 2 n) → Bool) × ((Fin (n - Nat.log 2 n) → Bool) × A.Coins n) ≃
        (Fin ((fUniversal c).inLen.eval n) → Bool) × A.Coins n :=
      (Equiv.prodAssoc _ _ _).symm.trans (Equiv.prodCongr e (Equiv.refl _))
    rw [← uprob_comp_equiv e']
    exact OneWay.uprob_congr fun w => Iff.rfl
  have hfib := claim_65_2_cond Invert cf n (by omega) (OneWay.card_log_bits_le (by omega))
    (by rw [hInv]; exact hA.le)
  rw [FunFamily.invProbAt_eq_uprob]
  have hlen : B.coinLen (n - Nat.log 2 n) =
      A.coinLen n + (B.coinLen (n - Nat.log 2 n) - A.coinLen n) := by omega
  let e₂ : ((Fin (n - Nat.log 2 n) → Bool) × A.Coins n) ×
      (Fin (B.coinLen (n - Nat.log 2 n) - A.coinLen n) → Bool) ≃
      (Fin (n - Nat.log 2 n) → Bool) × B.Coins (n - Nat.log 2 n) :=
    (Equiv.prodAssoc _ _ _).trans (Equiv.prodCongr (Equiv.refl _)
      ((Fin.appendEquiv _ _).trans (Equiv.arrowCongr (finCongr hlen.symm) (Equiv.refl Bool))))
  rw [← uprob_comp_equiv e₂]
  refine hfib.trans ?_
  rw [← uprob_fst (β := Fin (B.coinLen (n - Nat.log 2 n) - A.coinLen n) → Bool)
    (fun b : (Fin (n - Nat.log 2 n) → Bool) × A.Coins n => Invert (cf, b))]
  refine uprob_mono fun w hw => ?_
  obtain ⟨y', hy', hfy'⟩ := hw
  have hcoins : List.ofFn (e₂ w).2 = List.ofFn w.1.2 ++ List.ofFn w.2 := by
    show List.ofFn ((Equiv.arrowCongr (finCongr hlen.symm) (Equiv.refl Bool))
      (Fin.appendEquiv _ _ (w.1.2, w.2))) = _
    rw [← List.ofFn_fin_append]
    exact (List.ofFn_congr hlen.symm (Fin.append w.1.2 w.2)).symm
  have hy : List.ofFn (e (cf, w.1.1)) = code ++ List.ofFn w.1.1 := by rw [hofn, hcf]
  show ∃ x', B.runAt (n - Nat.log 2 n) (List.ofFn (g _ w.1.1)) (e₂ w).2 = List.ofFn x' ∧
    g _ x' = g _ w.1.1
  have hBrun : B.runAt (n - Nat.log 2 n) (List.ofFn (g _ w.1.1)) (e₂ w).2 =
      univArg (List.ofFn y') := by
    rw [NUPPT.runAt_eq, hB, hcoins, List.take_left' (List.length_ofFn (f := w.1.2)), ← NUPPT.runAt_eq,
      padStr_eq_ofFn_fUniversal_f c g Mg c₀ hMg hcode hdec hc₀ w.1.1 (e (cf, w.1.1)) hy, hy']
  obtain ⟨x', hx', hgx'⟩ :=
    exists_preimage_of_fUniversal_eq c g Mg c₀ hMg hcode hdec hc₀ w.1.1 (e (cf, w.1.1)) y' hy hfy'
  exact ⟨x', by rw [hBrun, hx'], hgx'⟩

/-- **`f_universal` is hard to invert with `q(n) = n³`** [PS10, Theorem 63.1, proof of weak
one-wayness]: for a scheme `c` with an exponential canonizer, if some strong one-way function
`𝓖` with `inLen = var` is computable in quadratic time by a coded machine (the output of
`lemma_64_3`), every non-uniform PPT inverts `fUniversal c` with probability at most
`1 - 1/n³` for all large `n`.

**Deviation:** the hypothesis is the conclusion of Lemma 64.3 (`theorem_63_1` composes the
two); `q(n) = n³` is literal; `Invert` is `invProbAt_eq_uprob`'s event with the inverse
decoded as an `n`-bit string (D5).

**Proof sketch.** Let `M_g, c₀` be the coded machine of `hG.2.2`, `α₀ := c.encode M_g`, and
suppose `A` inverts with probability `> 1 - 1/n³` for infinitely many `n`. Fix such an
`n ≥ max c₀ 2^{|α₀|+1}`, `k := ⌊log₂ n⌋ ≥ |α₀|`, `m := n - k`, `code := α₀ ++ 1^{k - |α₀|}`
(`c.decode code = M_g` by `Turing.MachineCode.decode_encode_pad`). *Evaluation on `PickG`:*
for `y = code ++ x`, `|x| = m`, `fUniversalStr_append_of_computesInTime` with `hG.2.2` at `m`
and `c₀ (m + 1)² ≤ (n + 1)³` gives `fUniversalStr c y = pairEncode code (true :: ofFn (g m x))`,
`ofFn_fUniversal_f` the padded encoding. *Conditioning:* split `{0,1}^n ≃ {0,1}^k × {0,1}^m`
(`Fin.appendEquiv`, `uprob_comp_equiv`, as in `claim_65_1`); `claim_65_2_cond` with
`2^k ≤ n` (`OneWay.card_log_bits_le`) gives `Pr_{x, r}[Invert(code ++ x, r)] ≥ 1 - 1/n²`.
*Inverses on the fibre:* an answer `y' = code' ++ x'` with equal padded outputs has
`code' = code` (the first `2k + 2` bits are the doubled code and the separator,
`Turing.pairEncode`, `List.take` of `ofFn_fUniversal_f`), then
`ofFn (g m x') = ofFn (g m x)` (equal lengths `1 + outLen m`), so `g m x' = g m x`
(`List.ofFn_injective`). *The reduction `B`* for `𝓖` at parameter `m`: advice `⟨1^n, code⟩`
with `n ≤ 2(m + 1)` (`2⌊log₂ n⌋ ≤ n + 2`), by `NUPPT.exists_reparam_advice A φ
(mul (const 2) (add var (const 1)))` with `φ m := n` on the infinitely many `m = n - ⌊log₂ n⌋`
with `n` good (`0` elsewhere; fibres of `n ↦ n - ⌊log₂ n⌋` have at most two elements),
composed (`NUPPT.exists_comp`, `NUPPT.exists_withAdvice`) with the pre-processing
`z ↦ (pairEncode code (true :: z) ++ 0^{univOutLen n}).take (univOutLen n)` and the
post-processing `univArg` (the split of `fUniversal_easy` (1)); extra coins unread
(`List.take`, `uprob_fst` on `Fin.appendEquiv`). *Functional identity:*
`B.inverter m _ _ (g m x) r = some x'` iff `A.runAt n (ofFn ((fUniversal c).f n (code ++ x))) r'
= ofFn (code ++ x')` (`NUPPT.inverter_eq_some_iff`, `decodeFin_ofFn`, `univArg_append`), so
`𝓖.invProbAt B m ≥ 1 - 1/n² ≥ 1/2` (`invProbAt_eq_uprob`, `uprob_mono`). *Conclusion:* for
infinitely many `m` (unbounded, `m ≥ n/2`), so `fun m => 𝓖.invProbAt B m` is not negligible
(`not_negligible_iff` with `c = 1`), contradicting `hG.2.1.hard B`. -/
theorem fUniversal_hard (c : EffectiveMachineCode) (hc : CanonizerExp c)
    (hG : ∃ 𝓖 : FunFamily, 𝓖.inLen = .var ∧ 𝓖.StrongOneWay ∧ 𝓖.QuadraticCode) (A : NUPPT) :
    ∃ n₀, ∀ n ≥ n₀, (fUniversal c).invProbAt A n ≤ 1 - 1 / (n : ℝ) ^ 3 := by
  classical
  obtain ⟨⟨ℓ, L, g⟩, hℓ, hsow, Mg, c₀, hMg⟩ := hG
  dsimp only at hℓ
  subst hℓ
  by_contra hcon
  push_neg at hcon
  -- the good parameters, the code of `M_g` padded to `⌊log₂ n⌋` bits, the parameter change
  set α₀ := c.encode Mg with hα₀
  obtain ⟨K, hK⟩ : ∃ K, 2 ^ α₀.length = K := ⟨_, rfl⟩
  set N₀ := K + c₀ + 4 with hN₀
  let good : ℕ → Prop := fun n => N₀ ≤ n ∧ 1 - 1 / (n : ℝ) ^ 3 < (fUniversal c).invProbAt A n
  let φ : ℕ → ℕ := fun m => if h : ∃ n, good n ∧ n - Nat.log 2 n = m then h.choose else 0
  have hφ : ∀ m, φ m ≤ (PolyExpr.mul (.const 2) .var).eval m := by
    intro m
    simp only [φ, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
    split_ifs with h
    · have h1 := h.choose_spec.2
      have h2 := two_mul_log_two_le h.choose
      omega
    · exact Nat.zero_le _
  have hφ_spec : ∀ m, (∃ n, good n ∧ n - Nat.log 2 n = m) →
      good (φ m) ∧ φ m - Nat.log 2 (φ m) = m := by
    intro m h
    simp only [φ, dif_pos h]
    exact h.choose_spec
  let code : ℕ → List Bool := fun n => α₀ ++ List.replicate (Nat.log 2 n - α₀.length) true
  have hcode_len : ∀ n, N₀ ≤ n → (code n).length = Nat.log 2 n := by
    intro n hn
    have : α₀.length ≤ Nat.log 2 n := Nat.le_log_of_pow_le (by norm_num) (by rw [hK]; omega)
    simp only [code, List.length_append, List.length_replicate]
    omega
  have hcode_dec : ∀ n, c.decode (code n) = Mg := fun n => c.decode_encode_pad Mg _
  have hcode_le : ∀ n, (code n).length ≤ α₀.length + n := by
    intro n
    have := Nat.log_le_self 2 n
    simp only [code, List.length_append, List.length_replicate]
    omega
  -- the reduction `B`
  let β : ℕ → List Bool := fun m => pairEncode (List.replicate (φ m) true) (code (φ m))
  have hβ : ∀ m, (β m).length ≤
      (PolyExpr.add (.add (.mul (.const 6) .var) (.const 2)) (.const α₀.length)).eval m := by
    intro m
    have h1 := hφ m
    have h2 := hcode_le (φ m)
    simp only [PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var] at h1
    simp only [β, length_pairEncode, List.length_replicate, PolyExpr.eval_add, PolyExpr.eval_mul,
      PolyExpr.eval_const, PolyExpr.eval_var]
    omega
  have hpre : PolyTimeComputable fun w => padStr univOutLen (pairFstD (pairFstD w))
      (pairEncode (pairSndD (pairFstD w)) (true :: pairSndD w)) := by
    have h := ptc_comp (polyTimeComputable_padStr univOutLen)
      ((ptc_comp polyTimeComputable_pairFstD polyTimeComputable_pairFstD).pairEncode
        ((ptc_comp polyTimeComputable_pairSndD polyTimeComputable_pairFstD).pairEncode
          (ptc_comp (StateLoop.cons_poly true) polyTimeComputable_pairSndD)))
    convert h using 1
    funext w
    simp
  obtain ⟨B, hBc, hB⟩ := A.exists_reparam_pre_post φ _ hφ β _ hβ hpre polyTimeComputable_univArg
  have hB' : ∀ m y r, B.runAtL m y r = univArg (A.runAtL (φ m)
      (padStr univOutLen (List.replicate (φ m) true) (pairEncode (code (φ m)) (true :: y)))
      (r.take (A.coinLen (φ m)))) := by
    intro m y r
    rw [hB]
    simp [β]
  -- `B` inverts `g` with probability `≥ 1/2` infinitely often, contradicting its one-wayness
  refine (not_negligible_iff.mpr ⟨1, fun m₀ => ?_⟩) (hsow.hard B)
  obtain ⟨n, hn, hgood⟩ := hcon (max (2 * m₀) N₀)
  have hNn : N₀ ≤ n := le_of_max_le_right hn
  have hmn : 2 * m₀ ≤ n := le_of_max_le_left hn
  have hgoodn : good n := ⟨hNn, hgood⟩
  obtain ⟨hgood', hφm⟩ := hφ_spec (n - Nat.log 2 n) ⟨n, hgoodn, rfl⟩
  have hlog := two_mul_log_two_le n
  have hm₀ : m₀ ≤ n - Nat.log 2 n := by omega
  refine ⟨n - Nat.log 2 n, hm₀, ?_⟩
  have hn'N : N₀ ≤ φ (n - Nat.log 2 n) := hgood'.1
  have hcoins : A.coinLen (φ (n - Nat.log 2 n)) ≤
      B.coinLen (φ (n - Nat.log 2 n) - Nat.log 2 (φ (n - Nat.log 2 n))) := by
    rw [hφm]
    simp only [NUPPT.coinLen, hBc, PolyExpr.eval_subst]
    exact A.coins.eval_mono (hφ _)
  have hrun : ∀ y (r : List Bool),
      B.runAtL (φ (n - Nat.log 2 n) - Nat.log 2 (φ (n - Nat.log 2 n))) y r =
      univArg (A.runAtL (φ (n - Nat.log 2 n)) (padStr univOutLen
        (List.replicate (φ (n - Nat.log 2 n)) true)
        (pairEncode (code (φ (n - Nat.log 2 n))) (true :: y)))
        (r.take (A.coinLen (φ (n - Nat.log 2 n))))) := by
    intro y r
    rw [hφm]
    exact hB' _ y r
  have hkey := invProbAt_reduction_ge c g Mg c₀ hMg A B (n := φ (n - Nat.log 2 n)) (by omega)
    (hcode_len _ hn'N) (hcode_dec _) (by omega) hcoins hrun hgood'.2
  rw [hφm] at hkey
  rw [abs_of_nonneg (FunFamily.invProbAt_nonneg _ _ _)]
  refine le_trans ?_ hkey
  have hm2 : (2 : ℝ) ≤ ((n - Nat.log 2 n : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ n - Nat.log 2 n by omega)
  have hn2 : (2 : ℝ) ≤ ((φ (n - Nat.log 2 n) : ℕ) : ℝ) := by exact_mod_cast (show 2 ≤ φ (n - Nat.log 2 n) by omega)
  have h1 : 1 / ((n - Nat.log 2 n : ℕ) : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hm2
  have h2 : 1 / ((φ (n - Nat.log 2 n) : ℕ) : ℝ) ^ 2 ≤ 1 / 2 := by
    refine one_div_le_one_div_of_le (by norm_num) ?_
    nlinarith
  simp only [pow_one]
  linarith

/-- **`f_universal` is weakly one-way** [PS10, Theorem 63.1, "we claim that this function is
weakly one-way"] with the polynomial `q(n) = (n + 1)³`, for a scheme with an exponential
canonizer, given a quadratic-time strong one-way function (`lemma_64_3`).

**Deviation:** `WeakOneWay` requires `0 < q(n)` at every `n`, so the text's `q(n) = n³` is
replaced by `(n + 1)³ ≥ n³` (the bound `1 - 1/n³ ≤ 1 - 1/(n+1)³` of `fUniversal_hard` is the
stronger one).

**Proof sketch.** `fUniversal_easy` and `fUniversal_hard`; `1/(n+1)³ ≤ 1/n³` for `n ≥ 1`
(`one_div_le_one_div_of_le`), and at `n = 0` the bound `1 - 1/1 = 0` is only needed for
`n ≥ max n₀ 1`. -/
theorem fUniversal_weakOneWay (c : EffectiveMachineCode) (hc : CanonizerExp c)
    (hG : ∃ 𝓖 : FunFamily, 𝓖.inLen = .var ∧ 𝓖.StrongOneWay ∧ 𝓖.QuadraticCode) :
    (fUniversal c).WeakOneWay := by
  refine ⟨fUniversal_easy c hc, PolyExpr.normal 1 3, fun n => by simp [PolyExpr.eval_normal],
    fun A => ?_⟩
  obtain ⟨n₀, hn₀⟩ := fUniversal_hard c hc hG A
  refine ⟨max n₀ 1, fun n hn => ?_⟩
  have h1 := hn₀ n (le_of_max_le_left hn)
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast le_of_max_le_right hn
  have h2 : 1 / ((n : ℝ) + 1) ^ 3 ≤ 1 / (n : ℝ) ^ 3 :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ (by linarith) (by linarith) 3)
  simp only [PolyExpr.eval_normal, Nat.cast_one, Nat.cast_pow, Nat.cast_add, one_mul]
  linarith

/-- **The universal one-way function** [PS10, Theorem 63.1]: if there exists a (strong)
one-way function, then `f_universal` (for a scheme with an exponential canonizer) is weakly
one-way, and its direct product `(fUniversal c).prod q` is strongly one-way for some
polynomial `q` (hardness amplification, [PS10, Theorem 35.1], `weak_to_strong`).

**Deviation:** the output of `f_universal` carries the machine description (DESIGN §7,
error 1); "hardness amplification from §2.3" of the text is §2.4 (error 19); the scheme
hypothesis `CanonizerExp c`; the strong one-way function is the amplified product.

**Proof sketch.** `lemma_64_3`, `fUniversal_weakOneWay`, `weak_to_strong`. -/
theorem theorem_63_1 (c : EffectiveMachineCode) (hc : CanonizerExp c)
    (h : ∃ 𝓕 : FunFamily, 𝓕.StrongOneWay) :
    (fUniversal c).WeakOneWay ∧ ∃ q : PolyExpr, FunFamily.StrongOneWay ((fUniversal c).prod q) :=
  have hw := fUniversal_weakOneWay c hc (lemma_64_3 h)
  ⟨hw, weak_to_strong hw⟩

end TCSlib.Cryptography
