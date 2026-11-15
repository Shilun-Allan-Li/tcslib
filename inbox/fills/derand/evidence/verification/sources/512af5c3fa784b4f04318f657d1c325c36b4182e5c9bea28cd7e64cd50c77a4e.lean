/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.ClassP.P
import TCSlib.Complexity.TuringMachine.Build.Primitives
import TCSlib.Complexity.CircuitComplexity.SizeClasses

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Turing machines that take advice

The machine-side characterization of `P/poly` from [AB09, §6.3]: a machine that, on
inputs of length `n`, also receives a fixed *advice string* `αₙ` depending only on `n`.
`DTIME(T(n))/a(n)` is the class of languages decided in time `O(T(n))` with `a(n)` bits of
advice [AB09, Def 6.16], and `⋃_{c,d} DTIME(n^c)/n^d` is the right-hand side of
[AB09, Thm 6.18].

The file lives in `CircuitComplexity/` rather than `ClassP/` because advice classes are
introduced in the circuit chapter ([AB09, §6.3]) as the machine counterpart of `P/poly`,
and the unary example (Ex 6.17) uses the circuit-side `Language.allOnes`.

## Main definitions

* `Turing.FinTM.DecidesWithAdviceInTime` — `M`, given the advice sequence `α`, decides `L`
  within time `T`: on every `x` it halts on the pair `Turing.pairEncode x (α |x|)` within
  `T |x|` steps with output `[true]` iff `x ∈ L`.
* `Complexity.DTIMEAdvice T a` — the class `DTIME(T(n))/a(n)`. [AB09, Def 6.16]
* `Complexity.PAdvicePoly` — polynomial time with polynomial advice, the class on the
  right of [AB09, Thm 6.18].

## Main results

* `Complexity.DTIMEAdvice.mono`, `Complexity.DTIMEAdvice.mono_const` — monotonicity in
  the time bound, up to constant factors.
* `Complexity.DTIMEAdvice_eq_empty_of_eq_zero`, `Complexity.DTIMEAdvice_pow_eq_empty`,
  `Complexity.iUnion_DTIMEAdvice_pow_eq` — a time bound vanishing at `n = 0` empties
  `DTIME(T)/a`; so the literal `DTIME(n^c)/a` is empty for `c ≥ 1`, and the literal union
  `⋃_{c,d} DTIME(n^c)/n^d` is only `⋃_d DTIME(1)/n^d`.
* `Complexity.DTIMEAdvice_zero_eq_DTIME` — `DTIME(T)/0 = DTIME(T)` whenever
  `T(n) ≥ n + 1`; `Complexity.iUnion_DTIMEAdvice_zero_eq_P` — `⋃_c DTIME(n^c + 1)/0 = P`.
* `Complexity.P_subset_PAdvicePoly` — `P ⊆ PAdvicePoly` (the zero-advice component).
* `Complexity.mem_DTIMEAdvice_one_of_le_allOnes` — every unary language is decidable in
  linear time with one bit of advice. [AB09, Ex 6.17]
* `Complexity.mem_PAdvicePoly_of_le_allOnes` — hence every unary language (in particular
  an undecidable one) lies in `PAdvicePoly`. [AB09, Ex 6.17]

## [AB09, Thm 6.18]: status

[AB09, Thm 6.18] states `P/poly = ⋃_{c,d} DTIME(n^c)/n^d`, i.e. (in this library)
`{L | L.InPPoly} = Complexity.PAdvicePoly`. The inclusion `⊆` is
`Complexity.PPoly_subset_PAdvicePoly` in `CircuitComplexity.PPolyAdvice` (the advice is the
padded description of `Cₙ`, evaluated by the circuit-evaluating machine of
`CircuitComplexity.CircuitEval`). The inclusion `⊇` is
`Complexity.PAdvicePoly_subset_PPoly`, and the equality `Complexity.PPoly_eq_PAdvicePoly`,
in `CircuitComplexity.PAdviceSubsetPPoly` (a tableau circuit for the advice machine on
the pair, with the advice hard-wired by `CircuitComplexity.HardWire`).  The form with the
book's advice length `n^d` exactly, `Complexity.PPoly_eq_iUnion_DTIMEAdvice_pow`, is in
the same file; the time bound there is `n^c + 1`, because the
literal `n^c` is degenerate at `n = 0` (see the divergences below).

## Divergences from [AB09, Def 6.16 and Thm 6.18]

* **Pairing.** [AB09] runs `M` on the pair `(x, αₙ)`; we use the library's
  self-delimiting pairing `Turing.pairEncode x αₙ` (the bits of `x` doubled, the
  separator `01`, then `αₙ` verbatim; the advice starts at cell `2|x| + 2`). Plain
  concatenation `x ++ αₙ` would be unfaithful: when `n ↦ n + a n` is not injective,
  different `(x, αₙ)` collide, and in any case it hides the boundary between `x` and
  the advice (finding it costs a scan of `n + a n` cells).
* **The time bound is in `|x|`, not in the input length `2|x| + 2 + a(|x|)`**, exactly
  as in [AB09] ("on input `(x, αₙ)` the machine `M` runs for at most `O(T(n))` steps",
  with `n = |x|`). In particular a machine may be unable to read all its advice, and for
  `T(n) < 2n + 2` not even all of `x`; the book has the same phenomenon up to the
  constant factor of its pair encoding, which the free constant `c` absorbs.
* **Correctness is only demanded on the pairs `⟨x, α |x|⟩`**, as in [AB09]: on other
  inputs `M` may do anything (including not halting).
* **`O(T(n))` is `c · T(n)`** for some constant `c`, as in `Complexity.DTIME`.
* **`DTIME(T) = DTIME(T)/0` needs `T(n) ≥ n + 1`.** With the pairing, the zero-advice
  machine reads `⟨x, []⟩` (length `2|x| + 2`) rather than `x`.
  `Complexity.DTIMEAdvice_zero_eq_DTIME` translates in both directions by composing with
  a linear-time pair extractor or pair encoder, which costs `O(|x|)` steps; the bound
  `T(n) ≥ n + 1` absorbs that cost, and holds for every bound used in the book
  (`Complexity.iUnion_DTIMEAdvice_zero_eq_P` is the polynomial-time case).  For
  sublinear `T` the identity is not stated: the translation could not even read `x`.
* **Advice length in `PAdvicePoly` is `C · (n + 1)^d`, not `n^d`.** This is the explicit
  polynomial formula of `Complexity.NP` (certificate lengths); the coefficient `C = 0`
  (empty advice) makes `P ⊆ PAdvicePoly` immediate.  The book's literal advice length
  `n^d` gives the same class: `Complexity.PPoly_eq_iUnion_DTIMEAdvice_pow`
  (`CircuitComplexity/PAdviceSubsetPPoly.lean`) proves
  `P/poly = ⋃_{c,d} DTIME(n^c + 1)/n^d`, so both unions equal `P/poly`.
* **Time `n^c + 1`, not `n^c`, and this is forced.** The literal `DTIME(n^c)/a` is
  empty for every `c ≥ 1` (`Complexity.DTIMEAdvice_pow_eq_empty`): on the empty input the
  machine gets `c' · 0^c = 0` steps and cannot halt.  The literal union
  `⋃_{c,d} DTIME(n^c)/n^d` therefore collapses to the constant-time classes
  `⋃_d DTIME(1)/n^d` (`Complexity.iUnion_DTIMEAdvice_pow_eq`), and the `+ 1` is the
  same empty-input repair as in `Complexity.P`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§6.3; Definition 6.16, Example 6.17,
  Theorem 6.18.)
-/

namespace Turing.FinTM

/-- The machine `M`, given the advice sequence `α` (one string per input length), decides
the language `L` within time `T`: on every input `x` the machine, run on the
self-delimiting pair `Turing.pairEncode x (α |x|)` (the bits of `x` doubled, the
separator `01`, then the advice verbatim), halts within `T |x|` steps with output
`[true]` if `x ∈ L` and `[false]` otherwise. [AB09, Def 6.16] (the pair `(x, αₙ)`
rendered by the library's pairing, and the time bound measured in `|x|`, as in the
book). -/
def DecidesWithAdviceInTime (M : FinTM Bool) (L : Language Bool) (α : ℕ → List Bool)
    (T : ℕ → ℕ) : Prop :=
  ∀ x : List Bool,
    M.ComputesInTime (pairEncode x (α x.length))
      [MultiTapeTM.indicator (L : Set (List Bool)) x] (T x.length)

end Turing.FinTM

namespace Complexity

open Turing

/-- **`DTIME(T(n))/a(n)`** [AB09, Def 6.16]: the languages `L` for which there are a
constant `c`, an advice sequence `α` with `|α n| = a n` for every `n`, and a finite
binary machine `M` that, on the pair `Turing.pairEncode x (α |x|)`, halts within
`c · T |x|` steps with output `[true]` iff `x ∈ L`. -/
def DTIMEAdvice (T a : ℕ → ℕ) : Set (Language Bool) :=
  {L | ∃ (c : ℕ) (α : ℕ → List Bool) (M : FinTM Bool),
    (∀ n, (α n).length = a n) ∧ M.DecidesWithAdviceInTime L α fun n => c * T n}

/-- `DTIME(T)/a` is monotone in the time bound `T`.

**Proof sketch.** The same advice and machine work; halting is absorbing, so a run
finishing within `c · T₁ n` steps also finishes within `c · T₂ n`
(`Turing.FinTM.ComputesInTime.mono`). -/
theorem DTIMEAdvice.mono {T₁ T₂ : ℕ → ℕ} {a : ℕ → ℕ} (h : ∀ n, T₁ n ≤ T₂ n) :
    DTIMEAdvice T₁ a ⊆ DTIMEAdvice T₂ a := by
  rintro L ⟨c, α, M, hα, hM⟩
  exact ⟨c, α, M, hα, fun x => (hM x).mono (Nat.mul_le_mul (le_refl c) (h x.length))⟩

/-- **Polynomial time with polynomial advice**, the class `⋃_{c,d} DTIME(n^c)/n^d` on the
right-hand side of [AB09, Thm 6.18]: the union over `c`, `C`, `d` of
`DTIME(n^c + 1) / (C · (n + 1)^d)`. The `+ 1` in the time bound is the convention of
`Complexity.P`; the advice length is the explicit polynomial formula of `Complexity.NP`
(see the module docstring for both divergences). The variant with the book's advice
length `n^d` is the same class, as both equal `P/poly`
(`Complexity.PPoly_eq_iUnion_DTIMEAdvice_pow`); the book's literal time bound `n^c` would
empty every component with `c ≥ 1` (`Complexity.DTIMEAdvice_pow_eq_empty`).

[AB09, Thm 6.18] asserts that this class is `P/poly`; `P/poly ⊆` it is
`Complexity.PPoly_subset_PAdvicePoly`, the converse is `Complexity.PAdvicePoly_subset_PPoly`
(`CircuitComplexity.PAdviceSubsetPPoly`). -/
def PAdvicePoly : Set (Language Bool) :=
  ⋃ (c : ℕ) (C : ℕ) (d : ℕ), DTIMEAdvice (fun n => n ^ c + 1) fun n => C * (n + 1) ^ d

/-- Each component `DTIME(n^c + 1)/(C · (n + 1)^d)` is contained in `PAdvicePoly`. -/
theorem DTIMEAdvice_subset_PAdvicePoly (c C d : ℕ) :
    DTIMEAdvice (fun n => n ^ c + 1) (fun n => C * (n + 1) ^ d) ⊆ PAdvicePoly := by
  intro L hL
  simp only [PAdvicePoly, Set.mem_iUnion]
  exact ⟨c, C, d, hL⟩

/-- The doubled-bit prefix of `Turing.pairEncode` has twice the length. -/
private lemma length_doubled (x : List Bool) :
    (x.flatMap fun b => [b, b]).length = 2 * x.length := by
  induction x with
  | nil => rfl
  | cons b x ih => simp only [List.flatMap_cons, List.length_append, ih]; simp; ring

/-- `DTIME(T)/a` absorbs constant factors in the time bound: if `T₁ ≤ a · T₂` pointwise,
then `DTIME(T₁)/A ⊆ DTIME(T₂)/A`. -/
theorem DTIMEAdvice.mono_const {T₁ T₂ : ℕ → ℕ} {A : ℕ → ℕ} (a : ℕ) (h : ∀ n, T₁ n ≤ a * T₂ n) :
    DTIMEAdvice T₁ A ⊆ DTIMEAdvice T₂ A := by
  rintro L ⟨c, α, M, hα, hM⟩
  refine ⟨c * a, α, M, hα, fun x => (hM x).mono ?_⟩
  calc c * T₁ x.length ≤ c * (a * T₂ x.length) := Nat.mul_le_mul_left _ (h x.length)
    _ = c * a * T₂ x.length := by ring

/-- **A time bound vanishing at length `0` makes `DTIME(T)/a` empty.**  If `T 0 = 0`, no
language lies in `DTIME(T)/a`, whatever the advice length `a`. [AB09, Def 6.16] (the
degenerate case of the definition at `n = 0`)

This is why the literal right-hand side `⋃_{c,d} DTIME(n^c)/n^d` of [AB09, Thm 6.18]
cannot be taken verbatim: see `Complexity.DTIMEAdvice_pow_eq_empty`.

**Proof sketch.** On the empty input `x = []` the machine must halt within
`c · T 0 = 0` steps, but after `0` steps it is still in its initial configuration, whose
state is the start state, not the halting state `none`. -/
theorem DTIMEAdvice_eq_empty_of_eq_zero {T : ℕ → ℕ} (hT : T 0 = 0) (a : ℕ → ℕ) :
    DTIMEAdvice T a = ∅ := by
  ext L
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨c, α, M, -, hM⟩
  have h := ((FinTM.computesInTime_iff _ _ _ _).mp (hM [])).1
  simp [hT, MultiTapeTM.runFrom, MultiTapeTM.initCfg] at h

/-- **The literal `DTIME(n^c)/a` is empty for `c ≥ 1`.**  With the time bound `n^c`
taken literally, the machine gets `c' · 0^c = 0` steps on the empty input, so no
language (not even `∅`, which still needs the answer `0` on `[]`) is decided.  This is
the advice analogue of the `n = 0` repair recorded on `Complexity.P`, and it forces the
`+ 1` in the time bound `n^c + 1` of `Complexity.PAdvicePoly` and of
`Complexity.PPoly_eq_iUnion_DTIMEAdvice_pow`. [AB09, Def 6.16, Thm 6.18] -/
theorem DTIMEAdvice_pow_eq_empty {c : ℕ} (hc : c ≠ 0) (a : ℕ → ℕ) :
    DTIMEAdvice (fun n => n ^ c) a = ∅ :=
  DTIMEAdvice_eq_empty_of_eq_zero (by simp [hc]) a

/-- **The literal union `⋃_{c,d} DTIME(n^c)/n^d` collapses to constant time.**  Only the
`c = 0` components (time `n^0 = 1`, i.e. a constant number of steps) are nonempty, so
the book's literal right-hand side of [AB09, Thm 6.18] is
`⋃_d DTIME(1)/n^d` — machines that read only a constant-length prefix of their input.
The faithful reading, with time `n^c + 1`, is
`Complexity.PPoly_eq_iUnion_DTIMEAdvice_pow`.

**Proof sketch.** `Complexity.DTIMEAdvice_pow_eq_empty` for `c ≠ 0`; the `c = 0`
component is `DTIME(1)/n^d` since `n^0 = 1`. -/
theorem iUnion_DTIMEAdvice_pow_eq :
    (⋃ (c : ℕ) (d : ℕ), DTIMEAdvice (fun n => n ^ c) fun n => n ^ d) =
      ⋃ d : ℕ, DTIMEAdvice (fun _ => 1) fun n => n ^ d := by
  ext L
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨c, d, hL⟩
    rcases Nat.eq_zero_or_pos c with rfl | hc
    · exact ⟨d, by simpa using hL⟩
    · rw [DTIMEAdvice_pow_eq_empty hc.ne'] at hL
      exact hL.elim
  · rintro ⟨d, hL⟩
    exact ⟨0, d, by simpa using hL⟩

/-- **Zero advice is no advice**: `DTIME(T)/0 = DTIME(T)` for every time bound with
`T(n) ≥ n + 1`.  [AB09, §6.3] (implicit in Def 6.16: `DTIME(T)/0` is `DTIME(T)`)

The hypothesis `T(n) ≥ n + 1` is the room needed to translate between the input `x` and
the pair `⟨x, []⟩` of length `2|x| + 2`; every time bound of interest (in particular
`n ^ c + 1` for `c ≥ 1`) satisfies it.

**Proof sketch.** `⊇`: run the linear-time first-component extractor
(`Turing.FinTM.computesFunInTime_pairFst`) on `⟨x, []⟩`, which outputs `x`, then the
decider for `L`; the buffered composition (`Turing.FinTM.bufferedCompTM_computesInTime`)
costs `O(|x|) + c · T(|x|) = O(T(|x|))`.  `⊆`: the advice strings all have length `0`,
so the advice machine `M` decides `L` on the pairs `⟨x, []⟩`; precompose the
linear-time encoder `x ↦ ⟨x, x⟩ ↦ ⟨x, []⟩` (`computesFunInTime_pairDup`, then
`computesFunInTime_pairMapSnd` with the constant `[]`).  Only the pointwise composition
is used, so `M` need not behave on inputs that are not pairs. -/
theorem DTIMEAdvice_zero_eq_DTIME {T : ℕ → ℕ} (hT : ∀ n, n + 1 ≤ T n) :
    DTIMEAdvice T (fun _ => 0) = DTIME T := by
  ext L
  constructor
  · -- `⊆`: encode `x` as the pair `⟨x, []⟩`, then run the advice machine
    rintro ⟨k, α, M, hα, hM⟩
    obtain ⟨D, d, hD⟩ := FinTM.computesFunInTime_pairDup
    obtain ⟨Z, z, hZ⟩ := FinTM.computesFunInTime_const []
    have hZmono : Monotone fun n : ℕ => z * (n + 1) := fun a b h =>
      Nat.mul_le_mul_left _ (by omega)
    obtain ⟨P, p, hP⟩ := FinTM.computesFunInTime_pairMapSnd hZ hZmono
    refine ⟨d + 8 + 3 * p * (1 + z) + k, FinTM.bufferedCompTM (FinTM.bufferedCompTM D P) M,
      fun x => ?_⟩
    set n := x.length
    have hαx : α n = [] := List.eq_nil_of_length_eq_zero (hα n)
    have h1 := hD x
    have h2 := hP (pairEncode x x)
    simp only [pairDecode_pairEncode, length_pairEncode] at h2
    have h3 := hM x
    rw [hαx] at h3
    have h12 := FinTM.bufferedCompTM_computesInTime D P h1 h2
    have h := FinTM.bufferedCompTM_computesInTime _ M h12 h3
    refine h.mono ?_
    simp only [length_pairEncode, List.length_nil, add_zero]
    have hn := hT n
    have hlin : d * (n + 1) + (2 * n + 2 + n) + 2 +
        p * (2 * n + 2 + n + 1 + z * (2 * n + 2 + n + 1)) + (2 * n + 2) + 2 ≤
        (d + 8 + 3 * p * (1 + z)) * (n + 1) := by
      have : p * (2 * n + 2 + n + 1 + z * (2 * n + 2 + n + 1)) = 3 * p * (1 + z) * (n + 1) := by
        ring
      rw [this]; nlinarith
    have hmul : (d + 8 + 3 * p * (1 + z)) * (n + 1) ≤ (d + 8 + 3 * p * (1 + z)) * T n :=
      Nat.mul_le_mul_left _ hn
    nlinarith
  · -- `⊇`: extract `x` from the pair `⟨x, []⟩`, then run the decider
    rintro ⟨c, M, hM⟩
    obtain ⟨E, e, hE⟩ := FinTM.computesFunInTime_pairFst
    refine ⟨3 * e + 2 + c, fun _ => [], FinTM.bufferedCompTM E M, fun _ => rfl, fun x => ?_⟩
    have h1 := hE (pairEncode x [])
    simp only [pairDecode_pairEncode, Option.map_some, Option.getD_some] at h1
    have h := FinTM.bufferedCompTM_computesInTime E M h1 (hM x)
    refine h.mono ?_
    simp only [length_pairEncode, List.length_nil, add_zero]
    have hn := hT x.length
    nlinarith

/-- **`P` with zero advice is `P`**: `⋃_c DTIME(n^c + 1)/0 = P`.  [AB09, §6.3] (the
polynomial-time case of `DTIME(T)/0 = DTIME(T)`)

**Proof sketch.** Each component `DTIME(n^c + 1)/0` lies in `DTIME(n^(c+1) + 1)/0`
(`n^c + 1 ≤ 2 (n^(c+1) + 1)`, absorbed into the constant), which is
`DTIME(n^(c+1) + 1) ⊆ P` by `DTIMEAdvice_zero_eq_DTIME` (as `n + 1 ≤ n^(c+1) + 1`).
Conversely a language of `P` is in some `DTIME(n^c + 1) ⊆ DTIME(n^(c+1) + 1)`, which is
`DTIME(n^(c+1) + 1)/0` by the same theorem. -/
theorem iUnion_DTIMEAdvice_zero_eq_P :
    (⋃ c : ℕ, DTIMEAdvice (fun n => n ^ c + 1) (fun _ => 0)) = P := by
  have hstep : ∀ c n : ℕ, n ^ c + 1 ≤ 2 * (n ^ (c + 1) + 1) := by
    intro c n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rcases Nat.eq_zero_or_pos c with rfl | hc <;> simp [*]
    · have : n ^ c ≤ n ^ (c + 1) := Nat.pow_le_pow_right hn (by omega)
      omega
  have hge : ∀ c n : ℕ, n + 1 ≤ n ^ (c + 1) + 1 := fun c n => by
    have : n ≤ n ^ (c + 1) := by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · exact Nat.le_self_pow (by omega) n
    omega
  ext L
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨c, hL⟩
    have hL' := DTIMEAdvice.mono_const 2 (hstep c) hL
    rw [DTIMEAdvice_zero_eq_DTIME (hge c)] at hL'
    exact dtime_poly_subset_P (c + 1) hL'
  · intro hL
    obtain ⟨c, a, M, hM⟩ := Set.mem_iUnion.mp hL
    refine ⟨c + 1, ?_⟩
    rw [DTIMEAdvice_zero_eq_DTIME (hge c)]
    refine ⟨a * 2, M, fun x => (hM x).mono ?_⟩
    calc a * (x.length ^ c + 1) ≤ a * (2 * (x.length ^ (c + 1) + 1)) :=
          Nat.mul_le_mul_left _ (hstep c x.length)
      _ = a * 2 * (x.length ^ (c + 1) + 1) := by ring

/-- `P ⊆ PAdvicePoly`: polynomial-time languages need no advice.

**Proof sketch.** By `iUnion_DTIMEAdvice_zero_eq_P` a language of `P` lies in some
`DTIME(n^c + 1)/0`, which is the component of `PAdvicePoly` with advice coefficient
`C = 0` (empty advice). -/
theorem P_subset_PAdvicePoly : P ⊆ PAdvicePoly := by
  intro L hL
  rw [← iUnion_DTIMEAdvice_zero_eq_P, Set.mem_iUnion] at hL
  obtain ⟨c, k, α, M, hα, hM⟩ := hL
  exact DTIMEAdvice_subset_PAdvicePoly c 0 0 ⟨k, α, M, fun n => by simp [hα n], hM⟩

/-! ## [AB09, Ex 6.17]: unary languages with one bit of advice -/

/-- A right move into state `q'`. -/
private def aoMove (q' : Fin 4) : Action 0 Bool (Fin 4) := ⟨.pos, fun i => i.elim0, none, some q'⟩

/-- Halt emitting `b`. -/
private def aoHalt (b : Bool) : Action 0 Bool (Fin 4) := ⟨.zero, fun i => i.elim0, some b, none⟩

/-- The transition table of the advice scanner on `⟨x, [b]⟩`. State `0`: at an aligned
block, a `1` starts a data block (go to `1`), a `0` starts the separator or a `00`
block (go to `2`). State `1`: skip the second copy of a `1`. State `2`: a `1` completes
the separator `01` (go to `3`), anything else means `x` had a `0` — reject. State `3`:
output the advice bit. Blanks reject. -/
private def aoTr (q : Fin 4) (inp : Option Bool) : Action 0 Bool (Fin 4) :=
  if q = 0 then
    match inp with
    | some true => aoMove 1
    | some false => aoMove 2
    | none => aoHalt false
  else if q = 1 then
    match inp with
    | some _ => aoMove 0
    | none => aoHalt false
  else if q = 2 then
    match inp with
    | some true => aoMove 3
    | _ => aoHalt false
  else
    match inp with
    | some b => aoHalt b
    | none => aoHalt false

/-- The advice scanner: accepts `⟨x, [b]⟩` iff `x` is all ones and `b = 1`, in
`2|x| + 3` steps, with no work tapes. -/
private def adviceOnesTM : FinTM Bool where
  k := 0
  State := Fin 4
  tm := { q₀ := 0, tr := fun q inp _ => aoTr q inp }

/-- The live configuration in state `q` with the input head at native position `p`
(clamped to the right boundary). -/
private def aoCfg (w : List Bool) (q : Fin 4) (p : ℕ) : Cfg 0 Bool (Fin 4) w :=
  ⟨some q, ⟨min p (w.length + 1), by omega⟩, fun i => i.elim0, fun i => i.elim0, []⟩

/-- One step at an input letter applies the table to that letter. -/
private lemma ao_step (w : List Bool) (q : Fin 4) (i : ℕ) (hi : i < w.length) :
    adviceOnesTM.tm.step (aoCfg w q (i + 1)) = (aoTr q (some w[i])).apply (aoCfg w q (i + 1)) := by
  have hs : (aoCfg w q (i + 1)).inputSymbol = some w[i] :=
    inputSymbolInner i (by simp only [aoCfg]; omega) hi
  simp only [MultiTapeTM.step, aoCfg] at hs ⊢
  rw [hs]
  rfl

/-- A right-move transition advances the head by one cell. -/
private lemma ao_move (w : List Bool) (q q' : Fin 4) (i : ℕ) (hi : i < w.length) (v : Bool)
    (hv : w[i] = v) (h : aoTr q (some v) = aoMove q') :
    adviceOnesTM.tm.step (aoCfg w q (i + 1)) = aoCfg w q' (i + 1 + 1) := by
  rw [ao_step w q i hi, hv, h]
  apply Cfg.ext_zero_tapes
  · rfl
  · apply Fin.ext
    change (moveInputPos (⟨min (i + 1) (w.length + 1), by omega⟩ : Fin (w.length + 2))
      .pos).val = min (i + 1 + 1) (w.length + 1)
    rw [moveInputPos_pos_of_ne_right _ (by simp only; omega)]
    simp only
    omega
  · rfl

/-- A halting transition halts with its emitted bit. -/
private lemma ao_halt (w : List Bool) (q : Fin 4) (i : ℕ) (hi : i < w.length) (v b : Bool)
    (hv : w[i] = v) (h : aoTr q (some v) = aoHalt b) :
    (adviceOnesTM.tm.step (aoCfg w q (i + 1))).state = none ∧
      (adviceOnesTM.tm.step (aoCfg w q (i + 1))).output = [b] := by
  rw [ao_step w q i hi, hv, h]
  exact ⟨rfl, rfl⟩

/-- Even positions of the doubled prefix carry the bits of `x`, and so do odd ones. -/
private lemma doubled_getElem? (x : List Bool) (p : ℕ) :
    (x.flatMap fun b => [b, b])[2 * p]? = x[p]? ∧
      (x.flatMap fun b => [b, b])[2 * p + 1]? = x[p]? := by
  induction x generalizing p with
  | nil => simp
  | cons a x ih =>
    cases p with
    | zero => simp
    | succ p =>
      have e1 : 2 * (p + 1) = 2 * p + 1 + 1 := by ring
      rw [e1]
      simpa [List.flatMap_cons] using ih p

/-- The letters of `⟨x, α⟩`: the doubled bits, the separator `01`, then `α`.

**Proof sketch.** The pair encoding is the doubled prefix (of length `2|x|`), then the
separator `0 1`, then `α`. Positions below `2|x|` fall in the doubled prefix, where the
doubling lemma reads off the bit `x_p` at both `2p` and `2p+1`; positions `2|x|` and
`2|x|+1` fall on the separator; and position `2|x|+2+i` lies `i+2` past the prefix, i.e.
at letter `i` of `α`. Each case is one append-indexing rewrite plus arithmetic. -/
private lemma pairEncode_getElem? (x α : List Bool) :
    (∀ p, p < x.length → (pairEncode x α)[2 * p]? = x[p]? ∧
        (pairEncode x α)[2 * p + 1]? = x[p]?) ∧
      (pairEncode x α)[2 * x.length]? = some false ∧
      (pairEncode x α)[2 * x.length + 1]? = some true ∧
      ∀ i, (pairEncode x α)[2 * x.length + 2 + i]? = α[i]? := by
  have hd := length_doubled x
  refine ⟨fun p hp => ?_, ?_, ?_, fun i => ?_⟩
  · simp only [pairEncode, List.append_assoc]
    rw [List.getElem?_append_left (by omega), List.getElem?_append_left (by omega)]
    exact doubled_getElem? x p
  · simp only [pairEncode, List.append_assoc]
    rw [List.getElem?_append_right (by omega), hd]
    simp
  · simp only [pairEncode, List.append_assoc]
    rw [List.getElem?_append_right (by omega), hd]
    simp [show 2 * x.length + 1 - 2 * x.length = 1 by omega]
  · simp only [pairEncode, List.append_assoc]
    rw [List.getElem?_append_right (by omega), hd]
    rw [show 2 * x.length + 2 + i - 2 * x.length = i + 2 by omega]
    simp

/-- Turn a `getElem?` fact into an index bound and a `getElem` fact. -/
private lemma getElem_of_getElem?_eq {w : List Bool} {i : ℕ} {v : Bool} (h : w[i]? = some v) :
    ∃ hi : i < w.length, w[i] = v :=
  List.getElem?_eq_some_iff.mp h

/-- All letters of `x` at positions `≥ p` are `1`. -/
private def onesFrom (x : List Bool) (p : ℕ) : Prop :=
  ∀ j (hj : j < x.length), p ≤ j → x[j] = true

open Classical in
/-- From the aligned block of `x[p]` in state `0`, with `r = |x| - p` blocks left, the
scanner halts on `⟨x, [b]⟩` within `2r + 3` steps and reports whether the remaining bits
of `x` are all `1` and `b = 1`.

**Proof sketch.** Induct on `r`. With no blocks left the head reads the separator `0`,
then `1`, then the advice bit, which it outputs. Otherwise it reads the first copy of
`x[p]`: a `1` is skipped together with its copy (two steps) and the induction
hypothesis applies one block later; a `0` sends the machine to state `2`, which reads
the second `0` and rejects, after which the run is stationary. -/
private lemma ao_scan (x : List Bool) (b : Bool) : ∀ r p, x.length = p + r →
    let c := adviceOnesTM.tm.runFrom (aoCfg (pairEncode x [b]) 0 (2 * p + 1)) (2 * r + 3)
    c.state = none ∧ c.output = [if onesFrom x p ∧ b = true then true else false] := by
  obtain ⟨hdata, hsep0, hsep1, hadv⟩ := pairEncode_getElem? x [b]
  have hlen := length_pairEncode x [b]
  intro r
  induction r with
  | zero =>
    intro p hr
    have hp : p = x.length := by omega
    subst hp
    have hm : onesFrom x x.length := fun j hj hpj => by omega
    obtain ⟨h0, e0⟩ := getElem_of_getElem?_eq hsep0
    obtain ⟨h1, e1⟩ := getElem_of_getElem?_eq hsep1
    obtain ⟨h2, e2⟩ := getElem_of_getElem?_eq (by simpa using hadv 0)
    rw [show 2 * 0 + 3 = 0 + 1 + 1 + 1 by rfl, MultiTapeTM.runFrom_succ_eq_step,
      ao_move _ 0 2 _ h0 false e0 rfl, MultiTapeTM.runFrom_succ_eq_step,
      ao_move _ 2 3 _ h1 true e1 rfl, MultiTapeTM.runFrom_succ_eq_step]
    have hh := ao_halt _ 3 (2 * x.length + 1 + 1) (by omega) b b (by simpa using e2) rfl
    rw [MultiTapeTM.runFrom_of_halt _ hh.1]
    refine ⟨hh.1, ?_⟩
    rw [hh.2]
    cases b <;> simp [hm]
  | succ r ih =>
    intro p hr
    have hp : p < x.length := by omega
    obtain ⟨hd0, hd1⟩ := hdata p hp
    obtain ⟨i0, e0⟩ := getElem_of_getElem?_eq (hd0.trans (List.getElem?_eq_getElem hp))
    obtain ⟨i1, e1⟩ := getElem_of_getElem?_eq (hd1.trans (List.getElem?_eq_getElem hp))
    rw [show 2 * (r + 1) + 3 = 2 * r + 3 + 1 + 1 by ring, MultiTapeTM.runFrom_succ_eq_step]
    cases hx : x[p] with
    | true =>
      rw [hx] at e0 e1
      rw [ao_move _ 0 1 _ i0 true e0 rfl, MultiTapeTM.runFrom_succ_eq_step,
        ao_move _ 1 0 _ i1 true e1 rfl,
        show 2 * p + 1 + 1 + 1 = 2 * (p + 1) + 1 by ring]
      have hiff : onesFrom x p ↔ onesFrom x (p + 1) := by
        constructor
        · intro h j hj hpj; exact h j hj (by omega)
        · intro h j hj hpj
          by_cases hjp : j = p
          · subst j; exact hx
          · exact h j hj (by omega)
      simpa only [hiff] using ih (p + 1) (by omega)
    | false =>
      rw [hx] at e0 e1
      rw [ao_move _ 0 2 _ i0 false e0 rfl, MultiTapeTM.runFrom_succ_eq_step]
      have hm : ¬(onesFrom x p ∧ b = true) := fun h => by simpa [hx] using h.1 p hp le_rfl
      have hh := ao_halt _ 2 (2 * p + 1) i1 false false e1 rfl
      rw [MultiTapeTM.runFrom_of_halt _ hh.1]
      simpa only [if_neg hm] using hh

open Classical in
/-- **Unary languages need one bit of advice** [AB09, Ex 6.17]: every unary language
`L ≤ Language.allOnes` lies in `DTIME(n + 1)/1`. The advice bit for length `n` records
whether `1ⁿ ∈ L`. [AB09] states "polynomial time"; the machine here is linear.

**Proof sketch.** Take the advice `αₙ = [1ⁿ ∈ L]` and a four-state scanner of the pair
`⟨x, [αₙ]⟩ = x₁x₁ … xₙxₙ 0 1 αₙ`: it skips aligned `11` blocks, rejects at an aligned
`00` block, and after the separator `01` outputs the advice bit. It halts within
`2n + 3 ≤ 3 (n + 1)` steps and accepts iff `x` is all ones and `αₙ = 1`, i.e. iff
`x = 1ⁿ ∈ L`; and since `L` is unary, `x ∈ L` forces `x = 1ⁿ`. -/
theorem mem_DTIMEAdvice_one_of_le_allOnes {L : Language Bool} (hL : L ≤ Language.allOnes) :
    L ∈ DTIMEAdvice (fun n => n + 1) (fun _ => 1) := by
  refine ⟨3, fun n => [decide (List.replicate n true ∈ L)], adviceOnesTM, fun _ => rfl,
    fun x => ?_⟩
  set b := decide (List.replicate x.length true ∈ L)
  have hinit : adviceOnesTM.tm.initCfg (pairEncode x [b]) =
      aoCfg (pairEncode x [b]) 0 (2 * 0 + 1) := by
    refine Cfg.ext_zero_tapes rfl ?_ rfl
    apply Fin.ext
    simp only [MultiTapeTM.initCfg, Cfg.init, aoCfg]
    change 1 = min (2 * 0 + 1) _
    omega
  have hm : (onesFrom x 0 ∧ b = true) ↔ x ∈ L := by
    have hrep : x ∈ Language.allOnes → x = List.replicate x.length true :=
      (Language.mem_allOnes_iff x).mp
    have hones : onesFrom x 0 ↔ x ∈ Language.allOnes := by
      constructor
      · intro h c hc
        obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hc
        exact h j hj (Nat.zero_le j)
      · intro h j hj _
        exact h _ (List.getElem_mem hj)
    rw [hones]
    constructor
    · rintro ⟨hx, hb⟩
      rw [hrep hx]
      exact of_decide_eq_true hb
    · intro h
      refine ⟨hL h, ?_⟩
      show decide (List.replicate x.length true ∈ L) = true
      rw [← hrep (hL h)]
      exact decide_eq_true h
  have h := ao_scan x b x.length 0 (by omega)
  rw [← hinit] at h
  refine ((FinTM.computesInTime_iff _ _ _ _).mpr ⟨h.1, ?_⟩).mono (by dsimp only; omega)
  rw [h.2]
  simp only [MultiTapeTM.indicator, hm]

/-- Every unary language — in particular an undecidable one such as `UHALT` — lies in
`PAdvicePoly`. [AB09, Ex 6.17]

**Proof sketch.** `Complexity.mem_DTIMEAdvice_one_of_le_allOnes` is the component with
`c = 1`, `C = 1`, `d = 0`: the time bound `n + 1` is `n ^ 1 + 1` and the advice length
`1` is `1 · (n + 1)^0`. -/
theorem mem_PAdvicePoly_of_le_allOnes {L : Language Bool} (hL : L ≤ Language.allOnes) :
    L ∈ PAdvicePoly := by
  obtain ⟨k, α, M, hα, hM⟩ := mem_DTIMEAdvice_one_of_le_allOnes hL
  exact DTIMEAdvice_subset_PAdvicePoly 1 1 0
    ⟨k, α, M, fun n => by simp [hα n], fun x => by simpa using hM x⟩

end Complexity
