/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.CircuitComplexity.KarpLiptonPrefix
import TCSlib.Complexity.CircuitComplexity.CircuitEval
import TCSlib.Complexity.CircuitComplexity.PPoly
import TCSlib.Complexity.CircuitComplexity.Uniform
import TCSlib.Complexity.PolyHierarchy.Collapse

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The Karp–Lipton theorem

[AB09, Thm 6.19] (Karp–Lipton): **if `NP ⊆ P/poly` then `PH = Σ₂ᵖ`.**

By [AB09, Thm 5.4] (`Complexity.PH_eq_SigmaP_of_PiP_subset_SigmaP`) it suffices to show
`Π₂ᵖ ⊆ Σ₂ᵖ`. Let `L ∈ Π₂ᵖ`, `x ∈ L ⟺ ∀ u ∃ v, ⟨⟨x, u⟩, v⟩ ∈ V` (blocks of length
`m = C (|x|+1)^c`, `V ∈ P`). The prefix language of `V` (`KarpLiptonPrefix.lean`) is in
`NP`, hence by hypothesis decided by a polynomial-size circuit family `D`. As in [AB09],
the circuit is *guessed* by the `∃` quantifier — as its description
`BoolCircuit.DAGCircuit.encode`, padded to an exact polynomial length, whose length is
polynomial by `BoolCircuit.DAGCircuit.length_encode_le_of_isFaninTwo` (the analogue, for
the guessed *decision* circuit `D`, of the book's "`C'_n` can be described using
`10 q(n)²` bits" for its search circuit `C'_n`) — and checked by the `∀` quantifier
with the polynomial-time circuit evaluator `BoolCircuit.CVAL_mem_P`.

## The verifier

Writing `D(y, e)` for "the guessed description `d` accepts `⟨y, e⟩`" (a `CVAL` query),
`y = ⟨x, u⟩`, and `1ᵏ 0 p` for the marker encoding of a partial witness `p`
(`k + |p| = m`), the `Σ₂ᵖ` formula is

`∃ d ∀ u j p :`
* (root) `D(y, 1ᵐ 0) = 1`;
* (leaf) if `|p| = m` and `D(y, 0 p) = 1` then `⟨y, p⟩ ∈ V`;
* (branch) if `|j| + |p| + 1 = m` and `D(y, 1^{|j|} 1 0 p) = 1` then
  `D(y, 1^{|j|} 0 p0) = 1` or `D(y, 1^{|j|} 0 p1) = 1`.

If `x ∈ L`, the true circuit passes all checks (`allGood_of_decides`). Conversely, if a
guessed `d` passes all checks, then for every `u` the root/branch checks let one walk
down a path of accepted prefixes `p` of every length — exactly the bit-by-bit
search of [AB09, Thm 2.18] ("thinking of this algorithm as a circuit") — and the leaf
check certifies the last one: `⟨y, p⟩ ∈ V` (`exists_witness_of_allGood`).

## Main definitions

* `Complexity.KarpLipton.Query` — one evaluation of the guessed circuit.
* `Complexity.KarpLipton.BadSpec` — a counterexample `(u, j, p)` to the checks.
* `Complexity.KarpLipton.badLang`, `Complexity.KarpLipton.innerLang` — the `P`
  counterexample language and the `coNP` inner language of the `Σ₂ᵖ` formula.

## Main results

* `Complexity.KarpLipton.badLang_mem_P`, `Complexity.KarpLipton.innerLang_mem_coNP`.
* `Complexity.KarpLipton.exists_witness_of_allGood` — soundness (the search walk).
* `Complexity.KarpLipton.allGood_of_decides` — completeness (the true circuit).
* `Complexity.KarpLipton.length_encode_le` — the description-length bound.
* `Complexity.PiP_two_subset_SigmaP_two_of_NP_subset_PPoly` — `Π₂ᵖ ⊆ Σ₂ᵖ`.
* `Complexity.PH_eq_SigmaP_two_of_NP_subset_PPoly` — **[AB09, Thm 6.19]**.

## Divergences from [AB09, proof of Thm 6.19]

* **No quantified-formula language.** The book shows that the `Π₂ᵖ`-complete language of
  true formulas `∀ u ∃ v ϕ(u, v)` (6.1) is in `Σ₂ᵖ`; its completeness rests on
  Cook–Levin. We instead work with an arbitrary `Π₂ᵖ` language and its own
  verifier `V`, applying `NP ⊆ P/poly` to the prefix language of `V`.
* **Self-consistency instead of an explicit search circuit.** The book guesses the
  multi-output search circuit `C'_n` and checks `ϕ(u, C'_n(ϕ, u)) = 1`. Evaluating a
  multi-output circuit, or running the `m`-step search, inside the `∀` verifier would need
  an iteration combinator for polynomial-time machines that the library does not have.
  We guess the *decision* circuit `D` and let the `∀` block check its local
  self-consistency (root, branch, leaf), which needs only four `CVAL` queries per
  instance; the search is carried out in the correctness proof. The search circuit itself
  is formalized separately (`KarpLiptonSearch.lean`, `BoolCircuit.searchCircuit`).
* **One circuit per `x`.** Partial witnesses are queried in the fixed-length marker
  encoding `1ᵏ 0 p`, so all queries made for one `x` have the same length and the single
  circuit `D_{N(|x|)}` answers them; the book uses the circuits for several lengths.
* **Description length.** The model's descriptions satisfy `|⌜D⌝| ≤ 12 · |D|²`
  (`BoolCircuit.DAGCircuit.length_encode_le_of_isFaninTwo`) rather than the book's
  `10 q(n)²`; the description is padded as `1ʳ 0 ⌜D⌝` to the exact block length.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§2.5, Theorem 2.18; §5.2, Theorem 5.4; §6.4,
  Theorem 6.19, pp. 113–114.)
-/

namespace Complexity.KarpLipton

open Turing Complexity.PolyHierarchy BoolCircuit

/-! ### The checks -/

/-- **One query to the guessed circuit**: the description `d` (of a circuit with
`|⟨y, e⟩|` inputs) accepts `⟨y, e⟩`, i.e. `⟨d, ⟨y, e⟩⟩ ∈ CVAL`. -/
def Query (d y e : List Bool) : Prop := pairEncode d (pairEncode y e) ∈ CVAL

/-- **A counterexample to the Karp–Lipton checks** for input `x`, padded description `U`,
universal block `u`, unary counter `j` and partial witness `p`: with `m = C (|x|+1)^c`,
`y = ⟨x, u⟩` and `d` the description stripped of its padding marker, the lengths are in
range (`|u| = m`, `|j|, |p| ≤ m`) and one of the checks fails: the root query rejects,
or a full-length accepted leaf `p` is rejected by `V`, or an accepted prefix
`1^{|j|} 1 0 p` has no accepted one-bit extension. -/
def BadSpec (C c : ℕ) (V : Language Bool) (x U u j p : List Bool) : Prop :=
  u.length = C * (x.length + 1) ^ c ∧ j.length ≤ C * (x.length + 1) ^ c ∧
    p.length ≤ C * (x.length + 1) ^ c ∧
    (¬ Query (dropMarker U) (pairEncode x u)
        (List.replicate (C * (x.length + 1) ^ c) true ++ [false]) ∨
      (p.length = C * (x.length + 1) ^ c ∧ Query (dropMarker U) (pairEncode x u) (false :: p) ∧
        pairEncode (pairEncode x u) p ∉ V) ∨
      (j.length + p.length + 1 = C * (x.length + 1) ^ c ∧
        Query (dropMarker U) (pairEncode x u) (List.replicate j.length true ++ true :: false :: p) ∧
        ¬ Query (dropMarker U) (pairEncode x u)
          (List.replicate j.length true ++ false :: (p ++ [false])) ∧
        ¬ Query (dropMarker U) (pairEncode x u)
          (List.replicate j.length true ++ false :: (p ++ [true]))))

/-! ### Coordinates of the verifier input `⟨⟨x, U⟩, ⟨⟨u, j⟩, p⟩⟩` -/

/-- The input `x` of the verifier input `⟨⟨x, U⟩, ⟨⟨u, j⟩, p⟩⟩`. -/
def gx (z : List Bool) : List Bool := pairFstD (pairFstD z)
/-- The padded description `U` of the verifier input. -/
def gU (z : List Bool) : List Bool := pairSndD (pairFstD z)
/-- The universal block `u` of the verifier input. -/
def gu (z : List Bool) : List Bool := pairFstD (pairFstD (pairSndD z))
/-- The unary counter `j` of the verifier input. -/
def gj (z : List Bool) : List Bool := pairSndD (pairFstD (pairSndD z))
/-- The partial witness `p` of the verifier input. -/
def gp (z : List Bool) : List Bool := pairSndD (pairSndD z)

section coords

variable (x U t u j p : List Bool)

/-- The `x` coordinate of a well-formed verifier input. -/
@[simp] theorem gx_pair : gx (pairEncode (pairEncode x U) t) = x := by simp [gx]
/-- The `U` coordinate of a well-formed verifier input. -/
@[simp] theorem gU_pair : gU (pairEncode (pairEncode x U) t) = U := by simp [gU]
/-- The `u` coordinate of a well-formed verifier input. -/
@[simp] theorem gu_pair : gu (pairEncode (pairEncode x U) (pairEncode (pairEncode u j) p)) = u := by
  simp [gu]
/-- The `j` coordinate of a well-formed verifier input. -/
@[simp] theorem gj_pair : gj (pairEncode (pairEncode x U) (pairEncode (pairEncode u j) p)) = j := by
  simp [gj]
/-- The `p` coordinate of a well-formed verifier input. -/
@[simp] theorem gp_pair : gp (pairEncode (pairEncode x U) (pairEncode (pairEncode u j) p)) = p := by
  simp [gp]

end coords

/-- The `x` coordinate is polynomial-time computable. -/
theorem polyTimeComputable_gx : PolyTimeComputable gx :=
  polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD
/-- The `U` coordinate is polynomial-time computable. -/
theorem polyTimeComputable_gU : PolyTimeComputable gU :=
  polyTimeComputable_pairSndD.comp polyTimeComputable_pairFstD
/-- The `u` coordinate is polynomial-time computable. -/
theorem polyTimeComputable_gu : PolyTimeComputable gu :=
  polyTimeComputable_pairFstD.comp (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD)
/-- The `j` coordinate is polynomial-time computable. -/
theorem polyTimeComputable_gj : PolyTimeComputable gj :=
  polyTimeComputable_pairSndD.comp (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD)
/-- The `p` coordinate is polynomial-time computable. -/
theorem polyTimeComputable_gp : PolyTimeComputable gp :=
  polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD

/-- **The counterexample language**: verifier inputs `⟨⟨x, U⟩, ⟨⟨u, j⟩, p⟩⟩` (read through
the total projections) that are counterexamples to the Karp–Lipton checks. -/
def badLang (C c : ℕ) (V : Language Bool) : Language Bool :=
  {z | BadSpec C c V (gx z) (gU z) (gu z) (gj z) (gp z)}

/-- Membership in the counterexample language, unfolded. -/
theorem mem_badLang {C c : ℕ} {V : Language Bool} {z : List Bool} :
    z ∈ badLang C c V ↔ BadSpec C c V (gx z) (gU z) (gu z) (gj z) (gp z) := Iff.rfl

/-! ### The counterexample language is in `P` -/

section closure

/-- Conjunction of predicates decidable in `P`. -/
private theorem pred_and {p q : List Bool → Prop} (hp : ({z | p z} : Language Bool) ∈ P)
    (hq : ({z | q z} : Language Bool) ∈ P) : ({z | p z ∧ q z} : Language Bool) ∈ P :=
  inter_mem_P hp hq

/-- Disjunction of predicates decidable in `P`. -/
private theorem pred_or {p q : List Bool → Prop} (hp : ({z | p z} : Language Bool) ∈ P)
    (hq : ({z | q z} : Language Bool) ∈ P) : ({z | p z ∨ q z} : Language Bool) ∈ P :=
  union_mem_P hp hq

/-- Negation of a predicate decidable in `P`. -/
private theorem pred_not {p : List Bool → Prop} (hp : ({z | p z} : Language Bool) ∈ P) :
    ({z | ¬ p z} : Language Bool) ∈ P :=
  compl_mem_P hp

/-- A query whose three arguments are polynomial-time computable is decidable in `P`. -/
private theorem pred_query {d y e : List Bool → List Bool} (hd : PolyTimeComputable d)
    (hy : PolyTimeComputable y) (he : PolyTimeComputable e) :
    ({z | Query (d z) (y z) (e z)} : Language Bool) ∈ P :=
  preimage_mem_P CVAL_mem_P (hd.pairEncode (hy.pairEncode he))

/-- A length comparison with the witness length `C (|x|+1)^c` is decidable in `P`. -/
private theorem pred_len_eq {C c : ℕ} {f : List Bool → List Bool} (hf : PolyTimeComputable f) :
    ({z | (f z).length = C * ((gx z).length + 1) ^ c} : Language Bool) ∈ P := by
  have h := lenEq_preimage_mem_P hf (unaryPT_poly C c polyTimeComputable_gx)
  convert h using 1
  ext z
  simp

/-- A length bound by the witness length `C (|x|+1)^c` is decidable in `P`. -/
private theorem pred_len_le {C c : ℕ} {f : List Bool → List Bool} (hf : PolyTimeComputable f) :
    ({z | (f z).length ≤ C * ((gx z).length + 1) ^ c} : Language Bool) ∈ P := by
  have h := lenLe_preimage_mem_P (unaryPT_poly C c polyTimeComputable_gx) hf
  convert h using 1
  ext z
  simp

end closure

/-- **The counterexample language is in `P`** (when `V` is).

**Proof sketch.** `BadSpec` is a Boolean combination of length comparisons with the
unary template `1^{C(|x|+1)^c}`, four `CVAL` queries and one `V` query, each applied to
strings computed in polynomial time from the coordinates (projections, the marker
transducer, concatenations with constants, unary templates). `P` is closed under these
Boolean combinations and under polynomial-time preimages. -/
theorem badLang_mem_P {C c : ℕ} {V : Language Bool} (hV : V ∈ P) : badLang C c V ∈ P := by
  have hx := polyTimeComputable_gx
  have hu := polyTimeComputable_gu
  have hj := polyTimeComputable_gj
  have hp := polyTimeComputable_gp
  have hd : PolyTimeComputable (fun z => dropMarker (gU z)) :=
    polyTimeComputable_dropMarker.comp polyTimeComputable_gU
  have hy : PolyTimeComputable (fun z => pairEncode (gx z) (gu z)) := hx.pairEncode hu
  have hM : PolyTimeComputable (fun z => List.replicate (C * ((gx z).length + 1) ^ c) true) :=
    unaryPT_poly C c hx
  have hR : PolyTimeComputable (fun z => List.replicate (gj z).length true) :=
    polyTimeComputable_unary.comp hj
  have hroot : PolyTimeComputable
      (fun z => List.replicate (C * ((gx z).length + 1) ^ c) true ++ [false]) :=
    PolyTimeComputable.append hM (polyTimeComputable_const _)
  have hleaf : PolyTimeComputable (fun z => false :: gp z) :=
    (polyTimeComputable_prepend [false]).comp hp
  have hpar : PolyTimeComputable
      (fun z => List.replicate (gj z).length true ++ true :: false :: gp z) :=
    PolyTimeComputable.append hR ((polyTimeComputable_prepend [true, false]).comp hp)
  have hchild : ∀ b : Bool, PolyTimeComputable
      (fun z => List.replicate (gj z).length true ++ false :: (gp z ++ [b])) := fun b =>
    PolyTimeComputable.append hR ((polyTimeComputable_prepend [false]).comp
      (PolyTimeComputable.append hp (polyTimeComputable_const [b])))
  have hjp : PolyTimeComputable (fun z => gj z ++ gp z ++ [true]) :=
    PolyTimeComputable.append (PolyTimeComputable.append hj hp) (polyTimeComputable_const _)
  have hbranchLen := pred_len_eq (C := C) (c := c) hjp
  simp only [List.length_append, List.length_singleton] at hbranchLen
  exact pred_and (pred_len_eq hu) (pred_and (pred_len_le hj) (pred_and (pred_len_le hp)
    (pred_or (pred_not (pred_query hd hy hroot))
      (pred_or (pred_and (pred_len_eq hp) (pred_and (pred_query hd hy hleaf)
          (pred_not (preimage_mem_P hV (hy.pairEncode hp)))))
        (pred_and hbranchLen (pred_and (pred_query hd hy hpar)
          (pred_and (pred_not (pred_query hd hy (hchild false)))
            (pred_not (pred_query hd hy (hchild true))))))))))

/-! ### The inner `coNP` language -/

/-- **The inner language of the `Σ₂ᵖ` formula**: the pairs `w = ⟨x, U⟩` admitting no
counterexample, i.e. for which the description padded in `U` passes all Karp–Lipton
checks. -/
def innerLang (C c : ℕ) (V : Language Bool) : Language Bool :=
  {w | ∀ t : List Bool, pairEncode w t ∉ badLang C c V}

/-- On a pair `⟨x, U⟩`, the inner language says that no `(u, j, p)` is a counterexample. -/
theorem mem_innerLang_pair {C c : ℕ} {V : Language Bool} (x U : List Bool) :
    pairEncode x U ∈ innerLang C c V ↔ ∀ u j p : List Bool, ¬ BadSpec C c V x U u j p := by
  constructor
  · intro h u j p hb
    refine h (pairEncode (pairEncode u j) p) ?_
    rw [mem_badLang]
    simpa using hb
  · intro h t ht
    rw [mem_badLang] at ht
    simp only [gx_pair, gU_pair] at ht
    exact h _ _ _ ht

/-- **The inner language is in `coNP`.**

**Proof sketch.** Its complement is `{w | ∃ t, ⟨w, t⟩ ∈ badLang}` with `badLang ∈ P`. A
counterexample can always be re-encoded as `t = ⟨⟨u, j⟩, p⟩` from its coordinates, and
then `|t| ≤ 7m + 6` with `m = C (|x|+1)^c ≤ C (|w|+1)^c`, since the checks bound
`|u|, |j|, |p| ≤ m`. This is the bounded-certificate form of `NP`. -/
theorem innerLang_mem_coNP {C c : ℕ} {V : Language Bool} (hV : V ∈ P) :
    innerLang C c V ∈ coNP := by
  show (innerLang C c V)ᶜ ∈ NP
  refine mem_NP_iff_exists_length_le.mpr ⟨7 * C + 6, c, badLang C c V, badLang_mem_P hV,
    fun w => ?_⟩
  constructor
  · intro hw
    have hw' : ¬ ∀ t : List Bool, pairEncode w t ∉ badLang C c V := hw
    push_neg at hw'
    obtain ⟨t, ht⟩ := hw'
    set z := pairEncode w t
    refine ⟨pairEncode (pairEncode (gu z) (gj z)) (gp z), ?_, ?_⟩
    · obtain ⟨h1, h2, h3, -⟩ := mem_badLang.mp ht
      have hx : (gx z).length ≤ w.length := by
        simpa [gx, z] using length_pairFstD_le w
      have hm : C * ((gx z).length + 1) ^ c ≤ C * (w.length + 1) ^ c :=
        Nat.mul_le_mul_left C (Nat.pow_le_pow_left (by omega) c)
      have hone : 1 ≤ (w.length + 1) ^ c := Nat.one_le_pow _ _ (by omega)
      simp only [length_pairEncode]
      nlinarith
    · rw [mem_badLang] at ht ⊢
      have e1 : gx (pairEncode w (pairEncode (pairEncode (gu z) (gj z)) (gp z))) = gx z := by
        simp [gx, z]
      have e2 : gU (pairEncode w (pairEncode (pairEncode (gu z) (gj z)) (gp z))) = gU z := by
        simp [gU, z]
      have e3 : gu (pairEncode w (pairEncode (pairEncode (gu z) (gj z)) (gp z))) = gu z := by
        simp [gu]
      have e4 : gj (pairEncode w (pairEncode (pairEncode (gu z) (gj z)) (gp z))) = gj z := by
        simp [gj]
      have e5 : gp (pairEncode w (pairEncode (pairEncode (gu z) (gj z)) (gp z))) = gp z := by
        simp [gp]
      rw [e1, e2, e3, e4, e5]
      exact ht
  · rintro ⟨t, -, ht⟩ hin
    exact hin t ht

/-! ### Soundness: walking down the accepted prefixes -/

/-- **Soundness of the checks (the search walk)** [AB09, Thm 2.18 idea, used in the proof
of Thm 6.19]: if no `(u, j, p)` is a counterexample for `x` and `U`, then for every `u` of
length `m = C (|x|+1)^c` there is a witness `v` of length `m` with `⟨⟨x, u⟩, v⟩ ∈ V`.
Note that nothing is assumed about the guessed description.

**Proof sketch.** Fix `u`. The root check says the guessed circuit accepts the empty
prefix `1ᵐ 0`. By induction on `i ≤ m`, some prefix `p` of length `i` is accepted in the
encoding `1^{m-i} 0 p`: the branch check (with `j = 1^{m-i-1}`) turns an accepted prefix
of length `i < m` into an accepted one-bit extension — this is the bit-by-bit search.
At `i = m` the leaf check gives `⟨y, p⟩ ∈ V`. -/
theorem exists_witness_of_allGood {C c : ℕ} {V : Language Bool} {x U : List Bool}
    (h : ∀ u j p : List Bool, ¬ BadSpec C c V x U u j p) (u : List Bool)
    (hu : u.length = C * (x.length + 1) ^ c) :
    ∃ v : List Bool, v.length = C * (x.length + 1) ^ c ∧ pairEncode (pairEncode x u) v ∈ V := by
  set m := C * (x.length + 1) ^ c with hm
  -- the root query is accepted
  have hroot : Query (dropMarker U) (pairEncode x u) (List.replicate m true ++ [false]) := by
    by_contra hq
    exact h u [] [] ⟨hu, by simp, by simp, Or.inl hq⟩
  -- the search walk: an accepted prefix of every length `i ≤ m`
  have walk : ∀ i, i ≤ m → ∃ p : List Bool, p.length = i ∧
      Query (dropMarker U) (pairEncode x u) (List.replicate (m - i) true ++ false :: p) := by
    intro i
    induction i with
    | zero => intro _; exact ⟨[], rfl, by simpa using hroot⟩
    | succ i ih =>
      intro hi
      obtain ⟨p, hp, hq⟩ := ih (by omega)
      have hrep : List.replicate (m - i) true = List.replicate (m - i - 1) true ++ [true] := by
        rw [← List.replicate_succ']
        congr 1
        omega
      have hk : m - (i + 1) = m - i - 1 := by omega
      by_contra hno
      push_neg at hno
      apply h u (List.replicate (m - i - 1) true) p
      refine ⟨hu, by simp; omega, by omega, Or.inr (Or.inr ⟨by simp; omega, ?_, ?_, ?_⟩)⟩
      · rw [hrep, List.append_assoc] at hq
        simpa using hq
      · intro hq0
        exact hno (p ++ [false]) (by simp [hp]) (by simpa [hk] using hq0)
      · intro hq1
        exact hno (p ++ [true]) (by simp [hp]) (by simpa [hk] using hq1)
  obtain ⟨p, hp, hq⟩ := walk m le_rfl
  refine ⟨p, hp, ?_⟩
  by_contra hv
  exact h u [] p ⟨hu, by simp, by omega, Or.inr (Or.inl ⟨hp, by simpa using hq, hv⟩)⟩

/-! ### Completeness: the true circuit passes the checks -/

/-- **A query to the description of a family circuit is a membership test**: for a
fan-in-two family `F`, the description of `F`'s circuit for length `|⟨y, e⟩|` accepts
`⟨y, e⟩` iff `⟨y, e⟩` is in the language of `F`. -/
theorem query_iff_mem_language {F : DAGCircuitFamily} (hF : F.HasFaninTwo) (y e : List Bool) :
    Query (F.circuit (pairEncode y e).length).encode y e ↔ pairEncode y e ∈ F.language := by
  set q := pairEncode y e with hq
  constructor
  · rintro ⟨x', C', -, hev, heq⟩
    obtain ⟨h1, h2⟩ := Prod.mk.inj (pairEncode_injective (a₁ := (_, _)) (a₂ := (_, _)) heq)
    subst h2
    have h3 := DAGCircuit.encode_injective _ h1
    rw [F.mem_language_iff, h3]
    exact hev
  · intro hmem
    exact ⟨q, F.circuit q.length, hF _, hmem, rfl⟩

/-- The common length `|⟨⟨x, u⟩, e⟩|` of all queries made for the input `x`
(`|u| = m`, `|e| = m + 1`, `m = C (|x|+1)^c`). -/
def qlen (C c : ℕ) (x : List Bool) : ℕ :=
  2 * (2 * x.length + 2 + C * (x.length + 1) ^ c) + 2 + (C * (x.length + 1) ^ c + 1)

/-- A query with `|u| = m` and `|e| = m + 1` has the common length `qlen`. -/
theorem length_query {C c : ℕ} {x u e : List Bool} (hu : u.length = C * (x.length + 1) ^ c)
    (he : e.length = C * (x.length + 1) ^ c + 1) :
    (pairEncode (pairEncode x u) e).length = qlen C c x := by
  simp [length_pairEncode, hu, he, qlen]

/-- **Completeness of the checks** [AB09, proof of Thm 6.19: "if (6.1) holds then (6.2)
is true"]: if the fan-in-two family `F` decides the prefix language of `V`, `U` pads the
description of `F`'s circuit for the query length of `x`, and `x ∈ L` (every `u` has a
witness), then no `(u, j, p)` is a counterexample.

**Proof sketch.** Every query has the common length `qlen`, so it is answered correctly
by the padded circuit (`query_iff_mem_language`): an accepted query is a prefix that
extends to a witness. The root `1ᵐ 0` (empty prefix) extends because `x ∈ L`; an
accepted full-length leaf `0 p` extends only by the empty word, so `⟨y, p⟩ ∈ V`; and an
accepted prefix `p` of length `< m` extends by some `b s`, so its extension `p b` is
accepted. -/
theorem allGood_of_decides {C c : ℕ} {V : Language Bool} {F : DAGCircuitFamily}
    (hF : F.HasFaninTwo) (hFL : F.language = prefixLang C c V) {x U : List Bool}
    (hU : dropMarker U = (F.circuit (qlen C c x)).encode)
    (hx : ∀ u : List Bool, u.length = C * (x.length + 1) ^ c →
      ∃ v : List Bool, v.length = C * (x.length + 1) ^ c ∧ pairEncode (pairEncode x u) v ∈ V) :
    ∀ u j p : List Bool, ¬ BadSpec C c V x U u j p := by
  set m := C * (x.length + 1) ^ c with hm
  intro u j p ⟨hu, hj, hp, hbad⟩
  -- every well-formed query is a prefix-language membership test
  have key : ∀ (k : ℕ) (q : List Bool), k + q.length = m →
      (Query (dropMarker U) (pairEncode x u) (List.replicate k true ++ false :: q) ↔
        ∃ s : List Bool, (q ++ s).length = m ∧ pairEncode (pairEncode x u) (q ++ s) ∈ V) := by
    intro k q hkq
    have hlen := length_query (C := C) (c := c) (x := x) (u := u)
      (e := List.replicate k true ++ false :: q) hu (by simp; omega)
    rw [hU, ← hlen, query_iff_mem_language hF, hFL, mem_prefixLang_iff, wLen_pairEncode]
  rcases hbad with hroot | ⟨hpm, hleaf, hv⟩ | ⟨hjp, hpar, hc0, hc1⟩
  · -- the root query is accepted, since `x ∈ L`
    apply hroot
    have := (key m [] (by simp)).mpr (by simpa using hx u hu)
    simpa using this
  · -- an accepted leaf is a witness
    obtain ⟨s, hs, hsv⟩ := (key 0 p (by simp; omega)).mp (by simpa using hleaf)
    have : s = [] := by
      rw [List.length_append] at hs
      exact List.eq_nil_of_length_eq_zero (by omega)
    subst this
    exact hv (by simpa using hsv)
  · -- an accepted proper prefix has an accepted one-bit extension
    have hpar' : Query (dropMarker U) (pairEncode x u)
        (List.replicate (j.length + 1) true ++ false :: p) := by
      rw [List.replicate_succ', List.append_assoc]
      simpa using hpar
    obtain ⟨s, hs, hsv⟩ := (key (j.length + 1) p (by omega)).mp hpar'
    obtain ⟨b, s', rfl⟩ : ∃ b s', s = b :: s' := by
      cases s with
      | nil => simp at hs; omega
      | cons b s' => exact ⟨b, s', rfl⟩
    have hext := (key j.length (p ++ [b]) (by simp; omega)).mpr
      ⟨s', by simpa using hs, by simpa using hsv⟩
    cases b
    · exact hc0 hext
    · exact hc1 hext

/-! ### The description length -/

/-- **The guessed description has polynomial length**: the analogue, for the guessed
*decision* circuit, of [AB09, p. 114: "`C'_n` can be described using `10 q(n)²` bits"]
(stated there for the search circuit `C'_n`, which our verifier does not guess). If the
fan-in-two family `F` has size at most
`a (n+1)^k`, then the description of its circuit for the query length of `x`, plus the
padding marker, fits in `(12 a² (8 + 3C)^{2k} + 1) (|x|+1)^{2(c+1)k}` bits.

**Proof sketch.** The query length is `4|x| + 7 + 3m ≤ (8 + 3C)(|x|+1)^{c+1} - 1` with
`m = C(|x|+1)^c`, so the circuit has size at most `a (8+3C)^k (|x|+1)^{(c+1)k}`, and a
fan-in-two circuit of size `S` has a description of length at most `12 S²`
(`BoolCircuit.DAGCircuit.length_encode_le_of_isFaninTwo`; the book's constant is `10`). -/
theorem length_encode_le {C c a k : ℕ} {F : DAGCircuitFamily} (hF : F.HasFaninTwo)
    (hS : ∀ n, (F.circuit n).size ≤ a * (n + 1) ^ k) (x : List Bool) :
    (F.circuit (qlen C c x)).encode.length + 1 ≤
      (12 * a ^ 2 * (8 + 3 * C) ^ (2 * k) + 1) * (x.length + 1) ^ (2 * (c + 1) * k) := by
  set n := x.length with hn
  set P := (n + 1) ^ (c + 1) with hP
  have hn1 : n + 1 ≤ P := by
    calc n + 1 = (n + 1) ^ 1 := (pow_one _).symm
      _ ≤ P := Nat.pow_le_pow_right (by omega) (by omega)
  have hc : (n + 1) ^ c ≤ P := Nat.pow_le_pow_right (by omega) (by omega)
  have hq : qlen C c x + 1 ≤ (8 + 3 * C) * P := by
    have : C * (n + 1) ^ c ≤ C * P := Nat.mul_le_mul_left C hc
    simp only [qlen, ← hn]
    nlinarith
  have hsize : (F.circuit (qlen C c x)).size ≤ a * (8 + 3 * C) ^ k * P ^ k := by
    calc _ ≤ a * (qlen C c x + 1) ^ k := hS _
      _ ≤ a * ((8 + 3 * C) * P) ^ k := Nat.mul_le_mul_left a (Nat.pow_le_pow_left hq k)
      _ = _ := by rw [mul_pow, mul_assoc]
  have henc := DAGCircuit.length_encode_le_of_isFaninTwo _ (hF (qlen C c x))
  have hPk : P ^ (2 * k) = (n + 1) ^ (2 * (c + 1) * k) := by
    rw [hP, ← pow_mul]
    ring_nf
  have hone : 1 ≤ (n + 1) ^ (2 * (c + 1) * k) := Nat.one_le_pow _ _ (by omega)
  have hsq := Nat.pow_le_pow_left hsize 2
  calc _ ≤ 12 * (a * (8 + 3 * C) ^ k * P ^ k) ^ 2 + 1 := by omega
    _ = 12 * a ^ 2 * (8 + 3 * C) ^ (2 * k) * (n + 1) ^ (2 * (c + 1) * k) + 1 := by
        rw [← hPk]
        ring
    _ ≤ _ := by nlinarith

end Complexity.KarpLipton

namespace Complexity

open Turing KarpLipton

/-- **`Π₂ᵖ ⊆ Σ₂ᵖ` under `NP ⊆ P/poly`** [AB09, proof of Thm 6.19]: if every `NP`
language has polynomial-size circuits, then every `Π₂ᵖ` language is in `Σ₂ᵖ`.

Deviation: the book shows the special case of the complete language (6.1) (relying on
completeness); we treat an arbitrary `Π₂ᵖ` language directly, and the `∀` block checks the
self-consistency of the guessed decision circuit instead of running the search circuit
(see the module docstring).

**Proof sketch.** Write `x ∈ L ⟺ ∀ u ∃ v, ⟨⟨x,u⟩,v⟩ ∈ V`. The prefix language of `V` is in
`NP`, so some fan-in-two family `F` of size `a(n+1)^k` decides it. Then
`x ∈ L ⟺ ∃ U (|U| = B(|x|+1)^b), ⟨x, U⟩ ∈ innerLang`, a `Σ₂ᵖ` formula since
`innerLang ∈ coNP`: (⇒) pad the description of `F`'s circuit for the query length of
`x` to `U = 1ʳ 0 ⌜F⌝` (it fits by `length_encode_le`) and use completeness
`allGood_of_decides`; (⇐) soundness `exists_witness_of_allGood`. -/
theorem PiP_two_subset_SigmaP_two_of_NP_subset_PPoly (h : NP ⊆ BoolCircuit.PPoly) :
    PiP 2 ⊆ SigmaP 2 := by
  intro L hL
  obtain ⟨C, c, V, hV, hLx⟩ := mem_PiP_two_iff_forall_exists.mp hL
  obtain ⟨a, k, F, hF, hS, hFL⟩ := h (prefixLang_mem_NP (C := C) (c := c) hV)
  refine mem_SigmaP_two_iff.mpr ⟨12 * a ^ 2 * (8 + 3 * C) ^ (2 * k) + 1, 2 * (c + 1) * k,
    innerLang C c V, innerLang_mem_coNP hV, fun x => ?_⟩
  rw [hLx x]
  constructor
  · intro hx
    have hlen := length_encode_le (C := C) (c := c) hF hS x
    set d := (F.circuit (qlen C c x)).encode with hd
    refine ⟨List.replicate ((12 * a ^ 2 * (8 + 3 * C) ^ (2 * k) + 1) *
        (x.length + 1) ^ (2 * (c + 1) * k) - d.length - 1) true ++ false :: d, ?_, ?_⟩
    · simp only [List.length_append, List.length_replicate, List.length_cons]
      omega
    · rw [mem_innerLang_pair]
      exact allGood_of_decides hF hFL (by simp [hd]) hx
  · rintro ⟨U, -, hU⟩
    rw [mem_innerLang_pair] at hU
    exact exists_witness_of_allGood hU

/-- **The Karp–Lipton theorem** [AB09, Thm 6.19]: if `NP ⊆ P/poly` then `PH = Σ₂ᵖ`.

Here `P/poly` is `BoolCircuit.PPoly` (polynomial-size fan-in-two families of the book's
circuit model, [AB09, Def 6.5]) and `PH`, `Σ₂ᵖ` are `Complexity.PH`,
`Complexity.SigmaP 2` ([AB09, Def 5.3]).

**Proof sketch.** By `Complexity.PiP_two_subset_SigmaP_two_of_NP_subset_PPoly`,
`Π₂ᵖ ⊆ Σ₂ᵖ`; by [AB09, Thm 5.4] (`Complexity.PH_eq_SigmaP_of_PiP_subset_SigmaP`) the
hierarchy collapses to its second level. -/
theorem PH_eq_SigmaP_two_of_NP_subset_PPoly (h : NP ⊆ BoolCircuit.PPoly) : PH = SigmaP 2 :=
  PH_eq_SigmaP_of_PiP_subset_SigmaP (by norm_num) (PiP_two_subset_SigmaP_two_of_NP_subset_PPoly h)

end Complexity
