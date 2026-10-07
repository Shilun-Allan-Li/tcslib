/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.CircuitComplexity.PSubsetPPolyConfigCircuit
import TCSlib.Complexity.CircuitComplexity.PPolyAdvice
import TCSlib.Complexity.CircuitComplexity.HardWire
import TCSlib.Complexity.CircuitComplexity.UHaltMachine

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Polynomial time with advice is contained in `P/poly`

The direction `⊇` of [AB09, Thm 6.18] (p. 113): if `L` is decided in polynomial time by a
machine `M` given polynomial advice `αₙ`, then `L ∈ P/poly`.  Following the book: for
each `n` build a circuit `Dₙ(x, y)` that simulates `M` on the pair `⟨x, y⟩` for
`|x| = n`, `|y| = a(n)`, then hard-wire `y := αₙ` (`Language.InPPoly.of_hardwire`,
`CircuitComplexity/HardWire.lean`).  With the inclusion `⊆`
(`Complexity.PPoly_subset_PAdvicePoly`) this gives the theorem's equality.

## Main definitions

* `Complexity.pairLayout n a` — the virtual input `Turing.pairEncode x y` (`x` doubled, the
  separator `01`, then `y`) as a layout of the `n + a` circuit inputs: pure wiring and two
  constants.

## Main results

* `Complexity.PAdvicePoly_subset_PPoly` — `⋃_{c,d} DTIME(n^c)/n^d ⊆ P/poly`.
  [AB09, Thm 6.18, `⊇`]
* `Complexity.mem_PPoly_of_mem_DTIMEAdvice` — `DTIME(n^c + 1)/a ⊆ P/poly` for every advice
  length `a(n) ≤ C(n + 1)^d` (e.g. the book's `n^d`).  [AB09, Thm 6.18, `⊇`]
* `Complexity.PPoly_eq_PAdvicePoly` — `P/poly = ⋃_{c,d} DTIME(n^c)/n^d`.  [AB09, Thm 6.18]
* `Complexity.PPoly_eq_iUnion_DTIMEAdvice_pow` (and the set form `…_pow'`) —
  `{L | L.InPPoly} = ⋃_{c,d} DTIME(n^c + 1)/n^d`, with the book's advice length `n^d`
  exactly.  [AB09, Thm 6.18]
* `Complexity.UHALT_mem_DTIMEAdvice_one`, `Complexity.UHALT_mem_PAdvicePoly` — the
  undecidable unary language `UHALT` is decidable in linear time with one bit of advice.
  [AB09, Ex 6.17]

## Divergences from [AB09, Thm 6.18]

* **The simulating circuit is the non-oblivious configuration tableau**
  (`Complexity.cfgCircuit`, size `O(T(T + n + a(n)))`), not the oblivious tableau of
  [AB09, Thm 6.6].  An advice machine (`Turing.FinTM.DecidesWithAdviceInTime`) is only
  required to halt on the pairs `⟨x, αₙ⟩`; it need not decide any language on all inputs,
  so the library's oblivious simulation (`Complexity.oblivious_of_mem_DTIME`, which
  takes a decider) does not apply to it.  The book uses "the construction of Theorem 6.6
  to construct for every `n` a polynomial-sized circuit `Dₙ` such that on every
  `x ∈ {0,1}ⁿ`, `α ∈ {0,1}^a(n)`, `Dₙ(x, α) = M(x, α)`", tacitly assuming `M` can be
  clocked on all pairs; the configuration tableau needs no such
  assumption, since it simply runs `T(n)` steps.
* The classes are the library's: `PAdvicePoly` is `⋃ DTIME(n^c + 1)/(C(n + 1)^d)` and
  `P/poly` uses size bounds `a(n + 1)^k` (see `Complexity.PAdvicePoly`,
  `Language.InPPoly`).
* **Time `n^c + 1`, not `n^c`, and this is forced.**  Taken literally, `DTIME(n^c)/a`
  gives the machine `c' · 0^c = 0` steps on the empty input, so it is empty for every
  `c ≥ 1` (`Complexity.DTIMEAdvice_pow_eq_empty`), and the literal union collapses to the
  constant-time classes `⋃_d DTIME(1)/n^d` (`Complexity.iUnion_DTIMEAdvice_pow_eq`).  The
  `+ 1` is the same `n = 0` repair as in `Complexity.P`.  The advice length `n^d` of
  `Complexity.PPoly_eq_iUnion_DTIMEAdvice_pow` is the book's, taken literally.
* **Small lengths are hard-coded.**  The advice `n^d` has length `0` at `n = 0` and `1`
  at `n = 1`, too short for a circuit description; the machine of
  `Complexity.mem_DTIMEAdvice_pow_of_inSIZE` carries the circuits for these two lengths
  in its finite control.  The book's proof (use "the description of `Cₙ` as an advice
  string on inputs of size `n`") silently assumes the description fits.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.  (§6.3, Example 6.17, Theorem 6.18, p. 113.)
-/

namespace Complexity

open Turing BoolCircuit CfgTableau

/-- The layout of `Turing.pairEncode x y` over the circuit inputs `x₀, …, x_{n−1},
y₀, …, y_{a−1}` (vertices `0, …, n + a − 1`): each `xᵢ` twice, the constants `0, 1`, then
`y`. -/
def pairLayout (n a : ℕ) : List BitSrc :=
  (List.range n).flatMap (fun i => [.input i, .input i]) ++ [.const false, .const true] ++
    (List.range a).map (fun j => .input (n + j))

/-- The pair layout has `2n + 2 + a` entries, the length of `pairEncode x y`. -/
@[simp] theorem length_pairLayout (n a : ℕ) : (pairLayout n a).length = 2 * n + 2 + a := by
  rw [pairLayout, List.length_append, List.length_append,
    length_flatMap_const _ _ (c := 2) (fun _ => by simp)]
  simp; ring

/-- Every source of the pair layout is a circuit input or a constant. -/
theorem pairLayout_valid (n a w : ℕ) : ∀ s ∈ pairLayout n a, s.Valid (n + a) w 0 := by
  intro s hs
  simp only [pairLayout, List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons,
    List.not_mem_nil, or_false, List.mem_map] at hs
  rcases hs with (⟨i, hi, rfl | rfl⟩ | rfl | rfl) | ⟨j, hj, rfl⟩
  · show i < n + a; omega
  · show i < n + a; omega
  · trivial
  · trivial
  · show n + j < n + a; omega

private theorem range_map_getD (z : List Bool) {n : ℕ} (hn : n ≤ z.length) :
    (List.range n).map (fun i => z.getD i false) = z.take n := by
  apply List.ext_getElem (by simp; omega)
  intro i h1 h2
  simp only [List.getElem_map, List.getElem_range, List.getElem_take]
  rw [List.getD_eq_getElem _ _ (by simp at h1; omega)]

/-- The pair layout evaluates to the pair: on the circuit input `(x, y)` the virtual input
is `Turing.pairEncode x y`. -/
theorem pairLayout_eval {n a : ℕ} (x : Fin n → Bool) (y : Fin a → Bool) :
    (pairLayout n a).map (BitSrc.eval (List.ofFn (Fin.append x y)) []) =
      pairEncode (List.ofFn x) (List.ofFn y) := by
  set z := List.ofFn (Fin.append x y) with hz
  have hz' : z = List.ofFn x ++ List.ofFn y := by rw [hz, List.ofFn_fin_append]
  have hzl : z.length = n + a := by simp [hz]
  have hx : (List.range n).map (fun i => z.getD i false) = List.ofFn x := by
    rw [range_map_getD z (by omega), hz', List.take_left' (by simp)]
  have hy : (List.range a).map (fun j => z.getD (n + j) false) = List.ofFn y := by
    have : (List.range a).map (fun j => z.getD (n + j) false) =
        (List.range a).map (fun j => (z.drop n).getD j false) := by
      apply List.map_congr_left; intro j _
      simp [List.getD_eq_getElem?_getD, List.getElem?_drop]
    rw [this, range_map_getD _ (by simp; omega), hz', List.drop_left' (by simp),
      List.take_of_length_le (by simp)]
  simp only [pairLayout, List.map_append, List.map_flatMap, List.map_cons, List.map_nil,
    List.map_map, Function.comp_def, BitSrc.eval, pairEncode]
  rw [← hx, ← hy, List.flatMap_map]

private theorem ofFn_getD {a : ℕ} (l : List Bool) (hl : l.length = a) :
    List.ofFn (fun j : Fin a => l.getD j false) = l := by
  subst hl
  apply List.ext_getElem (by simp)
  intro i h1 h2
  simp

/-- The size arithmetic of [AB09, Thm 6.18, `⊇`]: for a configuration tableau with
per-instruction cost `K`, `k` work tapes, `T(n) = c₀(n^c + 1)` steps and advice length
`a(n) = C(n + 1)^d`, the size bound `n + a(n) + 2 + (T + 1)(k(2T + 1) + 2n + 2 + a(n) + 3) K`
is at most `A · (n + 1)^(2(c + d + 1))` for an explicit `A`.

**Proof sketch.** With `R = (n + 1)^(c + d + 1)` bound each ingredient by a multiple of
`R`: `T + 1 ≤ (2c₀ + 1) R`, the block count `k(2T + 1) + N + 3 ≤ (k(4c₀ + 1) + C + 7) R`,
and `n + a(n) + 2 ≤ (C + 3) R`.  Multiply, and use `R ≤ R²` with
`(n + 1)^(2(c + d + 1)) = R²`. -/
private theorem advice_size_le (k K c c₀ C d n : ℕ) :
    n + C * (n + 1) ^ d + 2 +
      (c₀ * (n ^ c + 1) + 1) *
        (k * (2 * (c₀ * (n ^ c + 1)) + 1) + (2 * n + 2 + C * (n + 1) ^ d) + 3) * K ≤
    (C + 3 + (2 * c₀ + 1) * (k * (4 * c₀ + 1) + C + 7) * K) *
      (n + 1) ^ (2 * (c + d + 1)) := by
  set R := (n + 1) ^ (c + d + 1) with hR
  have hR1 : 1 ≤ R := Nat.one_le_pow _ _ (Nat.succ_pos n)
  have hnR : n + 1 ≤ R := Nat.le_self_pow (by omega) (n + 1)
  have hcR : n ^ c ≤ R := (Nat.pow_le_pow_left (Nat.le_succ n) c).trans
    (Nat.pow_le_pow_right (Nat.succ_pos n) (by omega))
  have hdR : (n + 1) ^ d ≤ R := Nat.pow_le_pow_right (Nat.succ_pos n) (by omega)
  have hRR : R ≤ R ^ 2 := by nlinarith
  have hpow : (n + 1) ^ (2 * (c + d + 1)) = R ^ 2 := by rw [hR, ← pow_mul, Nat.mul_comm]
  rw [hpow]
  have hT : c₀ * (n ^ c + 1) ≤ 2 * c₀ * R := by nlinarith
  have hT1 : c₀ * (n ^ c + 1) + 1 ≤ (2 * c₀ + 1) * R := by nlinarith
  have ha : C * (n + 1) ^ d ≤ C * R := Nat.mul_le_mul_left C hdR
  have hN : k * (2 * (c₀ * (n ^ c + 1)) + 1) + (2 * n + 2 + C * (n + 1) ^ d) + 3 ≤
      (k * (4 * c₀ + 1) + C + 7) * R := by
    have : k * (2 * (c₀ * (n ^ c + 1)) + 1) ≤ k * ((4 * c₀ + 1) * R) :=
      Nat.mul_le_mul_left k (by nlinarith)
    nlinarith
  have hprod : (c₀ * (n ^ c + 1) + 1) *
      (k * (2 * (c₀ * (n ^ c + 1)) + 1) + (2 * n + 2 + C * (n + 1) ^ d) + 3) * K ≤
      (2 * c₀ + 1) * (k * (4 * c₀ + 1) + C + 7) * K * R ^ 2 := by
    have := Nat.mul_le_mul hT1 hN
    have := Nat.mul_le_mul_right K this
    calc _ ≤ (2 * c₀ + 1) * R * ((k * (4 * c₀ + 1) + C + 7) * R) * K := this
      _ = _ := by ring
  have hfirst : n + C * (n + 1) ^ d + 2 ≤ (C + 3) * R ^ 2 := by nlinarith
  nlinarith

/-- **Polynomial time with any polynomially bounded advice length is in `P/poly`**
[AB09, Thm 6.18, direction `⊇`, for an arbitrary advice-length function]: if
`a(n) ≤ C(n + 1)^d` for all `n`, then `DTIME(n^c + 1)/a(n) ⊆ P/poly`.  The advice length
`a` need not have the `C(n + 1)^d` shape of `Complexity.PAdvicePoly`; in particular the
book's literal `a(n) = n^d` is covered.

**Proof sketch.** As for `Complexity.PAdvicePoly_subset_PPoly`: the configuration-tableau
circuit of the advice machine on the virtual pair `⟨x, y⟩` with `|y| = a(n)`, then
`y := αₙ` hard-wired.  Its size bound is monotone in `a(n)`, so the estimate
`advice_size_le` at the majorant `C(n + 1)^d` still applies. -/
theorem mem_PPoly_of_mem_DTIMEAdvice {L : Language Bool} {c C d : ℕ} {a : ℕ → ℕ}
    (ha : ∀ n, a n ≤ C * (n + 1) ^ d) (hL : L ∈ DTIMEAdvice (fun n => n ^ c + 1) a) :
    L ∈ BoolCircuit.PPoly := by
  obtain ⟨c₀, α, M, hα, hM⟩ := hL
  set T : ℕ → ℕ := fun n => c₀ * (n ^ c + 1) with hT
  let D : (n : ℕ) → DAGCircuit (n + a n) := fun n =>
    cfgCircuit M (n + a n) (pairLayout n (a n)) (T n)
  let αf : (n : ℕ) → Fin (a n) → Bool := fun n j => (α n).getD j false
  have hlang : {w : List Bool | (D w.length).eval (Fin.append w.get (αf w.length)) = true} =
      L := by
    ext w
    simp only [Set.mem_setOf_eq, D]
    rw [cfgCircuit_eval (pairLayout_valid _ _ _), pairLayout_eval, List.ofFn_get,
      ofFn_getD (α w.length) (hα w.length),
      decide_emits_eq_of_computesInTime (hM w)]
    unfold MultiTapeTM.indicator
    by_cases h : w ∈ L
    · simp [h]
    · simp [h]
  rw [← hlang]
  refine Language.InPPoly.of_hardwire D αf (fun n => cfgCircuit_isFaninTwo _) (c := C + 3 +
    (2 * c₀ + 1) * (M.k * (4 * c₀ + 1) + C + 7) * cfgConst M) (k := 2 * (c + d + 1)) ?_
  intro n
  refine (cfgCircuit_size_le (M := M) (ℓ := pairLayout n (a n)) (T := T n) _).trans ?_
  rw [length_pairLayout]
  refine le_trans ?_ (advice_size_le M.k (cfgConst M) c c₀ C d n)
  have := ha n
  simp only [hT]
  gcongr

/-- **`⋃_{c,d} DTIME(n^c)/n^d ⊆ P/poly`** [AB09, Thm 6.18, direction `⊇`]: a language
decided in polynomial time with polynomial advice has polynomial-size fan-in-two
circuits.

**Proof sketch.** Let `M` decide `L` with advice `αₙ` of length `a(n) = C(n + 1)^d` within
`T(n) = c₀(n^c + 1)` steps, on the pairs `⟨x, αₙ⟩`.  For each `n` let `Dₙ` be the
configuration-tableau circuit (`Complexity.cfgCircuit`) of `M` for `T(n)` steps on `n + a(n)`
inputs `(x, y)`, reading the virtual input `⟨x, y⟩` through `Complexity.pairLayout` —
wiring and two constants.  It outputs `1` iff some step before `T(n)` of `M` on `⟨x, y⟩`
emits `1`, which for `y = αₙ` is `x ∈ L` (the output at the deadline is the answer bit).
Its size is `O(T(n)(T(n) + n + a(n)))`, a polynomial.  Hard-wiring `αₙ`
(`Language.InPPoly.of_hardwire`) gives the family.  This is the instance
`a(n) = C(n + 1)^d` of `Complexity.mem_PPoly_of_mem_DTIMEAdvice`. -/
theorem PAdvicePoly_subset_PPoly : PAdvicePoly ⊆ BoolCircuit.PPoly := by
  intro L hL
  simp only [PAdvicePoly, Set.mem_iUnion] at hL
  obtain ⟨c, C, d, hL⟩ := hL
  exact mem_PPoly_of_mem_DTIMEAdvice (C := C) (d := d) (fun _ => le_rfl) hL

/-- **[AB09, Thm 6.18]**: `P/poly = ⋃_{c,d} DTIME(n^c)/n^d` — in this library,
`{L | L.InPPoly} = Complexity.PAdvicePoly`.  The two directions are
`Complexity.PPoly_subset_PAdvicePoly` (`CircuitComplexity/PPolyAdvice.lean`) and
`Complexity.PAdvicePoly_subset_PPoly`. -/
theorem PPoly_eq_PAdvicePoly : {L : Language Bool | L.InPPoly} = PAdvicePoly :=
  Set.Subset.antisymm PPoly_subset_PAdvicePoly PAdvicePoly_subset_PPoly

/-! ### [AB09, Thm 6.18] with advice length exactly `n^d`, and [AB09, Ex 6.17] for `UHALT` -/

/-- **[AB09, Thm 6.18] with the book's advice length**: `P/poly = ⋃_{c,d} DTIME(n^c)/n^d`,
with advice of length exactly `n^d` and time `n^c + 1` (the literal time `n^c` makes every
component with `c ≥ 1` empty: `Complexity.DTIMEAdvice_pow_eq_empty`).

**Proof sketch.** `⊆`: a language with fan-in-two circuits of size `a(n + 1)^k` lies in
some `DTIME(n^c + 1)/n^d` by `Complexity.mem_DTIMEAdvice_pow_of_inSIZE` (padded
descriptions as advice for `n ≥ 2`, the circuits for `n ≤ 1` hard-coded).  `⊇`: the
advice length `n^d` is at most `1 · (n + 1)^d`, so
`Complexity.mem_PPoly_of_mem_DTIMEAdvice` (configuration tableau with the advice
hard-wired) applies. -/
theorem PPoly_eq_iUnion_DTIMEAdvice_pow :
    {L : Language Bool | L.InPPoly} =
      ⋃ (c : ℕ) (d : ℕ), DTIMEAdvice (fun n => n ^ c + 1) fun n => n ^ d := by
  ext L
  simp only [Set.mem_setOf_eq, Set.mem_iUnion]
  constructor
  · rintro ⟨a, k, hL⟩
    exact mem_DTIMEAdvice_pow_of_inSIZE hL
  · rintro ⟨c, d, hL⟩
    exact mem_PPoly_of_mem_DTIMEAdvice (C := 1)
      (fun n => by simpa using Nat.pow_le_pow_left (Nat.le_succ n) d) hL

/-- `BoolCircuit.PPoly = ⋃_{c,d} DTIME(n^c + 1)/n^d`, the set form of
`Complexity.PPoly_eq_iUnion_DTIMEAdvice_pow`. [AB09, Thm 6.18] -/
theorem PPoly_eq_iUnion_DTIMEAdvice_pow' :
    BoolCircuit.PPoly = ⋃ (c : ℕ) (d : ℕ), DTIMEAdvice (fun n => n ^ c + 1) fun n => n ^ d :=
  PPoly_eq_iUnion_DTIMEAdvice_pow

/-- **`UHALT` with one bit of advice** [AB09, Ex 6.17]: the undecidable unary language
`UHALT` (for any representation scheme `c`) is decided in linear time `O(n + 1)` with a
single advice bit, namely whether `1ⁿ ∈ UHALT`.  Contrast `Complexity.UHALT_not_mem_P`.

**Proof sketch.** `UHALT` is unary (`Complexity.UHALT_le_allOnes`), so
`Complexity.mem_DTIMEAdvice_one_of_le_allOnes` applies. -/
theorem UHALT_mem_DTIMEAdvice_one (c : MachineCode) :
    UHALT c ∈ DTIMEAdvice (fun n => n + 1) (fun _ => 1) :=
  mem_DTIMEAdvice_one_of_le_allOnes (UHALT_le_allOnes c)

/-- **`UHALT` is in polynomial time with polynomial advice** [AB09, Ex 6.17]: `UHALT ∈
⋃_{c,d} DTIME(n^c)/n^d` (the class `Complexity.PAdvicePoly`), although `UHALT` is
undecidable (`Complexity.not_decidesInTime_UHALT`).

**Proof sketch.** `Complexity.mem_PAdvicePoly_of_le_allOnes` with
`Complexity.UHALT_le_allOnes`. -/
theorem UHALT_mem_PAdvicePoly (c : MachineCode) : UHALT c ∈ PAdvicePoly :=
  mem_PAdvicePoly_of_le_allOnes (UHALT_le_allOnes c)

end Complexity
