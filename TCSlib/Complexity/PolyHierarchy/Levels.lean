/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.PolyHierarchy.Normalize

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The levels of the polynomial hierarchy

Structural facts about `Complexity.SigmaP` and `Complexity.PiP` [AB09, §5.2]:

* the first level is `NP` / `coNP` (with the campaign's own definitions);
* the inductive characterization `Σᵢ₊₁ᵖ = ∃·Πᵢᵖ` and `Πᵢ₊₁ᵖ = ∀·Σᵢᵖ` — the form in which
  Karp–Lipton and Meyer use `Σ₂ᵖ` and `Π₂ᵖ` [AB09, §6.4];
* merging an outer `∃` block into a `Σᵢᵖ` language (`i ≥ 1`), the quantifier-merging
  step of [AB09, proof of Theorem 5.4];
* closure under polynomial-time preimages;
* the containments `Σᵢᵖ ∪ Πᵢᵖ ⊆ Σᵢ₊₁ᵖ ∩ Πᵢ₊₁ᵖ` and `P ⊆ Σᵢᵖ` [AB09, §5.2].

## Main results

* `Complexity.SigmaP_one` — `Σ₁ᵖ = NP`; `Complexity.PiP_one` — `Π₁ᵖ = coNP`.
* `Complexity.mem_SigmaP_succ_iff` — `L ∈ Σᵢ₊₁ᵖ` iff `x ∈ L ⟺ ∃ u, ⟨x, u⟩ ∈ L'` for
  some `L' ∈ Πᵢᵖ`; `Complexity.mem_PiP_succ_iff` — the dual.
* `Complexity.mem_SigmaP_of_exists` — `∃·Σᵢᵖ ⊆ Σᵢᵖ` for `i ≥ 1`;
  `Complexity.mem_PiP_of_forall` — `∀·Πᵢᵖ ⊆ Πᵢᵖ`.
* `Complexity.preimage_mem_SigmaP`, `Complexity.preimage_mem_PiP` — closure under
  polynomial-time reductions.
* `Complexity.SigmaP_union_PiP_subset` — `Σᵢᵖ ∪ Πᵢᵖ ⊆ Σᵢ₊₁ᵖ ∩ Πᵢ₊₁ᵖ`.
* `Complexity.P_subset_SigmaP`, `Complexity.NP_subset_SigmaP`, `Complexity.mem_PH_iff`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§5.2, Definition 5.3, p. 97, and the discussion
  after it; Theorem 5.4, pp. 97–98; §6.4.)
-/

namespace Complexity

open Turing PolyHierarchy

/-! ### Closure under reductions -/

/-- **`Σᵢᵖ` is closed under polynomial-time reductions**: if `L ∈ Σᵢᵖ` and `f` is
polynomial-time computable then `f⁻¹(L) ∈ Σᵢᵖ`. -/
theorem preimage_mem_SigmaP {i : ℕ} {L : Language Bool} (hL : L ∈ SigmaP i)
    {f : List Bool → List Bool} (hf : PolyTimeComputable f) : f ⁻¹' L ∈ SigmaP i :=
  preimage_mem_altClass hL hf

/-- **`Πᵢᵖ` is closed under polynomial-time reductions**. -/
theorem preimage_mem_PiP {i : ℕ} {L : Language Bool} (hL : L ∈ PiP i)
    {f : List Bool → List Bool} (hf : PolyTimeComputable f) : f ⁻¹' L ∈ PiP i := by
  rw [PiP_eq_altClass] at hL ⊢
  exact preimage_mem_altClass hL hf

/-! ### The first level -/

/-- The splitter recovering `⟨x, u⟩` from `x ++ u` when `|u| = C (|x|+1)^c`. -/
private def certSplit (C c : ℕ) (w : List Bool) : List Bool :=
  match solveSplit C c w.length with
  | some i => pairEncode (w.take i) (w.drop i)
  | none => []

/-- The split search finds the length of the input part. -/
private theorem solveSplit_self (C c n : ℕ) : solveSplit C c (n + C * (n + 1) ^ c) = some n := by
  have hmono : StrictMono (fun j : ℕ => j + C * (j + 1) ^ c) := by
    intro a b h
    have := Nat.mul_le_mul_left C (Nat.pow_le_pow_left (Nat.add_le_add_right h.le 1) c)
    dsimp only
    omega
  unfold solveSplit
  cases h : (List.range (n + C * (n + 1) ^ c + 1)).find?
      (fun i => i + C * (i + 1) ^ c == n + C * (n + 1) ^ c) with
  | none =>
    have := List.find?_eq_none.mp h n (by simp only [List.mem_range]; omega)
    simp at this
  | some j =>
    have hj := List.find?_some h
    simp only [beq_iff_eq] at hj
    rw [hmono.injective hj]

/-- On an exact-length concatenation the splitter returns the pair. -/
private theorem certSplit_append (C c : ℕ) (x u : List Bool)
    (hu : u.length = C * (x.length + 1) ^ c) : certSplit C c (x ++ u) = pairEncode x u := by
  simp [certSplit, hu, solveSplit_self]

/-- **`Σ₁ᵖ = NP`** [AB09, §5.2: "`Σ₁ᵖ = NP`"], with the campaign's `Complexity.NP`
(verifier on the concatenation `x ++ u`) on the right.

**Proof sketch.** Both classes use certificates of length exactly `C (|x|+1)^c`; only the
verifier input differs (`⟨x, u⟩` versus `x ++ u`). From a `Σ₁ᵖ` verifier `V`, the `NP`
verifier runs the catalog's split search on `x ++ u` (recovering `⟨x, u⟩`, since
`n ↦ n + C(n+1)^c` is strictly increasing) and then `V`. From an `NP` verifier `V`, the
`Σ₁ᵖ` verifier concatenates the two components of the pair and runs `V`. Both are
polynomial-time preimages of `V`. -/
theorem SigmaP_one : SigmaP 1 = NP := by
  ext L
  constructor
  · rintro ⟨C, c, V, hV, hL⟩
    have hsp : PolyTimeComputable (certSplit C c) := by
      obtain ⟨M, a, hM⟩ := FinTM.computesFunInTime_splitSolve C c
      exact ⟨M, a, c + 2, hM⟩
    refine ⟨C, c, certSplit C c ⁻¹' V, preimage_mem_P hV hsp, fun x => ?_⟩
    rw [hL x, altQuant_true_succ]
    refine exists_congr fun u => and_congr_right fun hu => ?_
    show pairEncode x u ∈ V ↔ certSplit C c (x ++ u) ∈ V
    rw [certSplit_append C c x u hu]
  · rintro ⟨C, c, V, hV, hL⟩
    refine ⟨C, c, (fun z => pairFstD z ++ pairSndD z) ⁻¹' V,
      preimage_mem_P hV polyTimeComputable_pairConcat, fun x => ?_⟩
    rw [hL x, altQuant_true_succ]
    refine exists_congr fun u => and_congr_right fun _ => ?_
    show x ++ u ∈ V ↔ pairFstD (pairEncode x u) ++ pairSndD (pairEncode x u) ∈ V
    simp

/-- **`Π₁ᵖ = coNP`** [AB09, §5.2], with the campaign's `Complexity.coNP` (complements of
`NP`). Immediate from `Complexity.SigmaP_one`, since both are complement classes. -/
theorem PiP_one : PiP 1 = coNP := by
  ext L
  change Lᶜ ∈ SigmaP 1 ↔ Lᶜ ∈ NP
  rw [SigmaP_one]

/-! ### The inductive characterization -/

/-- **`Σᵢ₊₁ᵖ = ∃·Πᵢᵖ`** [AB09, §5.2]: `L ∈ Σᵢ₊₁ᵖ` iff there are an explicit polynomial
length `C (|x|+1)^c` and a language `L' ∈ Πᵢᵖ` with
`x ∈ L ⟺ ∃ u, |u| = C (|x|+1)^c ∧ ⟨x, u⟩ ∈ L'`. For `i = 1` this is the form of `Σ₂ᵖ`
used in Karp–Lipton (`Complexity.mem_SigmaP_two_iff`).

**Proof sketch.** (⇒) Take `L'` to be the set of `w` satisfying the remaining `i`-block
`∀`-prefix with block length `C (|fst w| + 1)^c`; on `w = ⟨x, u⟩` this is exactly the
inner part of the `Σᵢ₊₁ᵖ` formula, and `L' ∈ Πᵢᵖ` by normalization
(`mem_altClass_of_uniform`), since `C (|fst w|+1)^c` is a unary polynomial-time length.
(⇐) Write `L' ∈ Πᵢᵖ` with block length `C' (|w|+1)^{c'}`; on `w = ⟨x, u⟩` with
`|u| = C (|x|+1)^c` that length is a fixed polynomial of `|x|`, so `L` is a prefix whose
first block has length `C (|x|+1)^c` and later blocks another unary polynomial-time
length; `mem_altClass_of_normal` pads both to a common normal-form length. -/
theorem mem_SigmaP_succ_iff {i : ℕ} {L : Language Bool} :
    L ∈ SigmaP (i + 1) ↔ ∃ (C c : ℕ) (L' : Language Bool), L' ∈ PiP i ∧
      ∀ x : List Bool, x ∈ L ↔
        ∃ u : List Bool, u.length = C * (x.length + 1) ^ c ∧ pairEncode x u ∈ L' := by
  constructor
  · rintro ⟨C, c, V, hV, hL⟩
    refine ⟨C, c, {w | altQuant V (C * ((pairFstD w).length + 1) ^ c) false i w}, ?_,
      fun x => ?_⟩
    · rw [PiP_eq_altClass]
      exact mem_altClass_of_uniform (f := id) hV polyTimeComputable_id
        (unaryPT_poly C c polyTimeComputable_pairFstD)
    · rw [hL x, altQuant_true_succ]
      refine exists_congr fun u => and_congr_right fun _ => ?_
      show _ ↔ altQuant V (C * ((pairFstD (pairEncode x u)).length + 1) ^ c) false i
        (pairEncode x u)
      rw [pairFstD_pairEncode]
  · rintro ⟨C, c, L', hL', hL⟩
    obtain ⟨C', c', V', hV', hL'x⟩ := mem_PiP_iff.mp hL'
    have h₀ : UnaryPT (fun x => C * ((id x).length + 1) ^ c) :=
      unaryPT_poly C c polyTimeComputable_id
    have h₂ := unaryPT_poly C' c' (polyTimeComputable_id.pairEncode h₀)
    convert mem_altClass_of_normal (b := true) (i := i) hV' polyTimeComputable_id h₀ h₂
      using 1
    ext x
    rw [hL x]
    refine exists_congr fun u => and_congr_right fun hu => ?_
    rw [hL'x]
    simp only [id, Bool.not_true]
    have hlen : (pairEncode x u).length =
        (pairEncode x (List.replicate (C * (x.length + 1) ^ c) true)).length := by
      simp [length_pairEncode, hu]
    rw [hlen]

/-- **`Πᵢ₊₁ᵖ = ∀·Σᵢᵖ`** [AB09, §5.2]: `L ∈ Πᵢ₊₁ᵖ` iff there are an explicit polynomial
length and `L' ∈ Σᵢᵖ` with `x ∈ L ⟺ ∀ u, |u| = C (|x|+1)^c → ⟨x, u⟩ ∈ L'`.

**Proof sketch.** Apply `Complexity.mem_SigmaP_succ_iff` to `Lᶜ` and complement the
inner language. -/
theorem mem_PiP_succ_iff {i : ℕ} {L : Language Bool} :
    L ∈ PiP (i + 1) ↔ ∃ (C c : ℕ) (L' : Language Bool), L' ∈ SigmaP i ∧
      ∀ x : List Bool, x ∈ L ↔
        ∀ u : List Bool, u.length = C * (x.length + 1) ^ c → pairEncode x u ∈ L' := by
  rw [← compl_mem_SigmaP_iff, mem_SigmaP_succ_iff]
  constructor
  · rintro ⟨C, c, L', hL', hL⟩
    refine ⟨C, c, L'ᶜ, hL', fun x => ?_⟩
    have h := not_congr (hL x)
    simp only [not_exists, not_and] at h
    exact (not_not (a := x ∈ L)).symm.trans h
  · rintro ⟨C, c, L', hL', hL⟩
    refine ⟨C, c, L'ᶜ, compl_mem_PiP_iff.mpr hL', fun x => ?_⟩
    have h := not_congr (hL x)
    simp only [not_forall, exists_prop] at h
    simpa only [Set.mem_compl_iff] using h

/-! ### Merging quantifier blocks -/

/-- **Merging an outer `∃` block** [AB09, proof of Theorem 5.4: "`∃u ∃v` is one
existential quantifier over the pair `(u, v)`"]: if `i ≥ 1`, `L' ∈ Σᵢᵖ`, and
`x ∈ L ⟺ ∃ u, |u| = C (|x|+1)^c ∧ ⟨x, u⟩ ∈ L'`, then `L ∈ Σᵢᵖ`.

**Proof sketch.** Write `i = j + 1`; the formula for `L` is
`∃ u ∃ u₁ ∀ u₂ ⋯, ⟨⟨⟨x, u⟩, u₁⟩, …⟩ ∈ V`. Merge `u` and `u₁` into one block
`U = ⟨u 1, u₁ 1⟩` of the fixed length `2|u| + |u₁| + 5`; the new root map
`⟨x, U⟩ ↦ ⟨⟨x, u⟩, u₁⟩` un-pads both halves (total and onto, so the merged `∃` is
equivalent to the two `∃`s), and `mem_altClass_of_normal` absorbs the remaining length
mismatch. -/
theorem mem_SigmaP_of_exists {i : ℕ} (hi : i ≠ 0) {L L' : Language Bool}
    (hL' : L' ∈ SigmaP i) (C c : ℕ)
    (hL : ∀ x : List Bool, x ∈ L ↔
      ∃ u : List Bool, u.length = C * (x.length + 1) ^ c ∧ pairEncode x u ∈ L') :
    L ∈ SigmaP i := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hi
  obtain ⟨C', c', V, hV, hL'x⟩ := hL'
  -- The two original block lengths and their unary templates.
  set g₀ : List Bool → List Bool := fun x => List.replicate (C * (x.length + 1) ^ c) true
    with hg₀
  have h₀ : UnaryPT (fun x => C * ((id x).length + 1) ^ c) :=
    unaryPT_poly C c polyTimeComputable_id
  have hg₀p : PolyTimeComputable g₀ := h₀
  set ℓ₂ : List Bool → ℕ := fun x => C' * ((pairEncode x (g₀ x)).length + 1) ^ c' with hℓ₂
  have h₂ : UnaryPT ℓ₂ := unaryPT_poly C' c' (polyTimeComputable_id.pairEncode hg₀p)
  have hg₂p : PolyTimeComputable (fun x => List.replicate (ℓ₂ x) true) := h₂
  have h₁ : UnaryPT (fun x => (C * ((id x).length + 1) ^ c + C * ((id x).length + 1) ^ c +
      ℓ₂ x) + 5) := ((h₀.add h₀).add h₂).add (unaryPT_const 5)
  -- The root map un-pads the merged block into its two halves.
  set f : List Bool → List Bool := fun p =>
    pairEncode (pairEncode (pairFstD p)
      (padDecode (g₀ (pairFstD p)) (pairFstD (pairSndD p))))
      (padDecode (List.replicate (ℓ₂ (pairFstD p)) true) (pairSndD (pairSndD p))) with hfdef
  have hf : PolyTimeComputable f := by
    have hF := polyTimeComputable_pairFstD
    have hS := polyTimeComputable_pairSndD
    have h := (hF.pairEncode (polyTimeComputable_padDecode.comp
        ((hg₀p.comp hF).pairEncode (hF.comp hS)))).pairEncode
      (polyTimeComputable_padDecode.comp ((hg₂p.comp hF).pairEncode (hS.comp hS)))
    convert h using 1
    funext p
    simp [hfdef]
  have hfx : ∀ x U, f (pairEncode x U) = pairEncode (pairEncode x
      (padDecode (g₀ x) (pairFstD U))) (padDecode (List.replicate (ℓ₂ x) true) (pairSndD U)) := by
    intro x U
    simp [hfdef]
  -- The inner length is `ℓ₂ x` whenever the first block has its prescribed length.
  have hlen : ∀ x u, u.length = C * (x.length + 1) ^ c →
      C' * ((pairEncode x u).length + 1) ^ c' = ℓ₂ x := by
    intro x u hu
    simp [hℓ₂, hg₀, length_pairEncode, hu]
  convert mem_altClass_of_normal (b := true) (i := j) hV hf h₁ h₂ using 1
  ext x
  rw [hL x]
  simp only [qStep, Bool.not_true, id]
  constructor
  · rintro ⟨u, hu, hmem⟩
    rw [hL'x, altQuant_true_succ, hlen x u hu] at hmem
    obtain ⟨v, hv, hq⟩ := hmem
    refine ⟨pairEncode (u ++ [true]) (v ++ [true]), ?_, ?_⟩
    · simp [length_pairEncode, hu, hv]
      omega
    · rw [hfx]
      have e₀ : padDecode (g₀ x) (u ++ [true]) = u := by
        simpa using padDecode_marker (s := g₀ x) (u := u) (by simp [hg₀, hu]) 0
      have e₂ : padDecode (List.replicate (ℓ₂ x) true) (v ++ [true]) = v := by
        simpa using padDecode_marker (s := List.replicate (ℓ₂ x) true) (u := v)
          (by simp [hv]) 0
      simpa [e₀, e₂] using hq
  · rintro ⟨U, -, hq⟩
    rw [hfx] at hq
    refine ⟨padDecode (g₀ x) (pairFstD U), by simp [hg₀], ?_⟩
    rw [hL'x, altQuant_true_succ, hlen x _ (by simp [hg₀])]
    exact ⟨_, by simp, hq⟩

/-- **Merging an outer `∀` block**: if `i ≥ 1`, `L' ∈ Πᵢᵖ`, and
`x ∈ L ⟺ ∀ u, |u| = C (|x|+1)^c → ⟨x, u⟩ ∈ L'`, then `L ∈ Πᵢᵖ`. The dual of
`Complexity.mem_SigmaP_of_exists`, obtained by complementation. -/
theorem mem_PiP_of_forall {i : ℕ} (hi : i ≠ 0) {L L' : Language Bool}
    (hL' : L' ∈ PiP i) (C c : ℕ)
    (hL : ∀ x : List Bool, x ∈ L ↔
      ∀ u : List Bool, u.length = C * (x.length + 1) ^ c → pairEncode x u ∈ L') :
    L ∈ PiP i := by
  refine mem_SigmaP_of_exists hi hL' C c fun x => ?_
  have h := not_congr (hL x)
  simp only [not_forall, exists_prop] at h
  exact h

/-! ### Containments -/

/-- **`Πᵢᵖ ⊆ Σᵢ₊₁ᵖ`** [AB09, §5.2]: add a dummy outer `∃` block.

**Proof sketch.** By `Complexity.mem_SigmaP_succ_iff` with the empty certificate
(`C = 0`) and `L' = fst⁻¹(L) ∈ Πᵢᵖ` (closure under polynomial-time preimages). -/
theorem PiP_subset_SigmaP_succ (i : ℕ) : PiP i ⊆ SigmaP (i + 1) := by
  intro L hL
  rw [mem_SigmaP_succ_iff]
  refine ⟨0, 0, pairFstD ⁻¹' L, preimage_mem_PiP hL polyTimeComputable_pairFstD,
    fun x => ?_⟩
  simp only [zero_mul, List.length_eq_zero_iff, exists_eq_left]
  show _ ↔ pairFstD (pairEncode x []) ∈ L
  rw [pairFstD_pairEncode]

/-- **`Σᵢᵖ ⊆ Πᵢ₊₁ᵖ`** [AB09, §5.2]: add a dummy outer `∀` block (the complement of
`Complexity.PiP_subset_SigmaP_succ`). -/
theorem SigmaP_subset_PiP_succ (i : ℕ) : SigmaP i ⊆ PiP (i + 1) := fun _ hL =>
  PiP_subset_SigmaP_succ i (compl_mem_PiP_iff.mpr hL)

/-- **`Σᵢᵖ ⊆ Σᵢ₊₁ᵖ`** [AB09, §5.2].

**Proof sketch.** Induction on `i`. For `i = 0`, `Σ₀ᵖ = P = Π₀ᵖ ⊆ Σ₁ᵖ`. For `i + 1`, write
`L ∈ Σᵢ₊₁ᵖ` as `∃·L'` with `L' ∈ Πᵢᵖ`; the induction hypothesis, complemented, gives
`L' ∈ Πᵢ₊₁ᵖ`, hence `L ∈ Σᵢ₊₂ᵖ`. -/
theorem SigmaP_subset_SigmaP_succ : ∀ i : ℕ, SigmaP i ⊆ SigmaP (i + 1)
  | 0 => by
    intro L hL
    rw [SigmaP_zero] at hL
    exact PiP_subset_SigmaP_succ 0 (PiP_zero ▸ hL)
  | i + 1 => by
    intro L hL
    obtain ⟨C, c, L', hL', h⟩ := mem_SigmaP_succ_iff.mp hL
    exact mem_SigmaP_succ_iff.mpr
      ⟨C, c, L', SigmaP_subset_SigmaP_succ i hL', h⟩

/-- **`Πᵢᵖ ⊆ Πᵢ₊₁ᵖ`** [AB09, §5.2] (complement of `Complexity.SigmaP_subset_SigmaP_succ`). -/
theorem PiP_subset_PiP_succ (i : ℕ) : PiP i ⊆ PiP (i + 1) := fun _ hL =>
  SigmaP_subset_SigmaP_succ i hL

/-- `Σᵢᵖ ⊆ Σⱼᵖ` whenever `i ≤ j`. -/
theorem SigmaP_mono {i j : ℕ} (h : i ≤ j) : SigmaP i ⊆ SigmaP j := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => exact ih.trans (SigmaP_subset_SigmaP_succ _)

/-- `Πᵢᵖ ⊆ Πⱼᵖ` whenever `i ≤ j`. -/
theorem PiP_mono {i j : ℕ} (h : i ≤ j) : PiP i ⊆ PiP j := fun _ hL => SigmaP_mono h hL

/-- **`Σᵢᵖ ∪ Πᵢᵖ ⊆ Σᵢ₊₁ᵖ ∩ Πᵢ₊₁ᵖ`** [AB09, §5.2: "`Σᵢᵖ ⊆ Πᵢ₊₁ᵖ ⊆ Σᵢ₊₂ᵖ`"]. -/
theorem SigmaP_union_PiP_subset (i : ℕ) :
    SigmaP i ∪ PiP i ⊆ SigmaP (i + 1) ∩ PiP (i + 1) := by
  rintro L (hL | hL)
  · exact ⟨SigmaP_subset_SigmaP_succ i hL, SigmaP_subset_PiP_succ i hL⟩
  · exact ⟨PiP_subset_SigmaP_succ i hL, PiP_subset_PiP_succ i hL⟩

/-- **`P ⊆ Σᵢᵖ`** for every `i`. -/
theorem P_subset_SigmaP (i : ℕ) : P ⊆ SigmaP i :=
  SigmaP_zero ▸ SigmaP_mono (Nat.zero_le i)

/-- **`P ⊆ Πᵢᵖ`** for every `i`. -/
theorem P_subset_PiP (i : ℕ) : P ⊆ PiP i :=
  PiP_zero ▸ PiP_mono (Nat.zero_le i)

/-- **`NP ⊆ Σᵢᵖ`** for every `i ≥ 1`. -/
theorem NP_subset_SigmaP {i : ℕ} (hi : 1 ≤ i) : NP ⊆ SigmaP i :=
  SigmaP_one ▸ SigmaP_mono hi

/-- **`coNP ⊆ Πᵢᵖ`** for every `i ≥ 1`. -/
theorem coNP_subset_PiP {i : ℕ} (hi : 1 ≤ i) : coNP ⊆ PiP i :=
  PiP_one ▸ PiP_mono hi

/-! ### The hierarchy -/

/-- `L ∈ PH` iff `L ∈ Σᵢᵖ` for some `i` (the index `i = 0` may be included, since
`Σ₀ᵖ ⊆ Σ₁ᵖ`). -/
theorem mem_PH_iff {L : Language Bool} : L ∈ PH ↔ ∃ i : ℕ, L ∈ SigmaP i := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp h
    exact ⟨i + 1, hi⟩
  · rintro ⟨i, hi⟩
    exact Set.mem_iUnion.mpr ⟨i, SigmaP_subset_SigmaP_succ i hi⟩

/-- Every level `Σᵢᵖ` is contained in `PH`. -/
theorem SigmaP_subset_PH (i : ℕ) : SigmaP i ⊆ PH := fun _ hL => mem_PH_iff.mpr ⟨i, hL⟩

/-- Every level `Πᵢᵖ` is contained in `PH`. -/
theorem PiP_subset_PH (i : ℕ) : PiP i ⊆ PH :=
  (PiP_subset_SigmaP_succ i).trans (SigmaP_subset_PH (i + 1))

/-- `P ⊆ PH`. -/
theorem P_subset_PH : P ⊆ PH := SigmaP_zero ▸ SigmaP_subset_PH 0

/-- `NP ⊆ PH`. -/
theorem NP_subset_PH : NP ⊆ PH := SigmaP_one ▸ SigmaP_subset_PH 1

/-- `coNP ⊆ PH`. -/
theorem coNP_subset_PH : coNP ⊆ PH := PiP_one ▸ PiP_subset_PH 1

end Complexity
