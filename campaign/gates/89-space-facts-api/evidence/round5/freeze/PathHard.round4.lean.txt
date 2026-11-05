/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.SpaceComplexity.Codec.Bridge
import TCSlib.Complexity.SpaceComplexity.Logspace.PathWalk

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The configuration-graph reduction to `PATH`

The reduction of [AB09, Theorem 4.18]: a language `L` decided by a nondeterministic machine
`N` in space `c₀ · logSpace` is mapped, input by input, to a raw `PATH` instance
(`Complexity.pathRaw`) whose vertices are configuration codes of `N` on `x`
(`TCSlib.Complexity.SpaceComplexity.Codec`). With `ℓ = |bits (|x| + 1)|` (at least
`logSpace |x|`), radius `s = c₀ ℓ` and exponent `E = K (c₀ + 1) ℓ + K + 2` (`K = codeK N`),
the graph has `n = 2 ^ E` vertices, polynomially many in `|x|`:

* vertex `0` is the source and vertex `1` the target;
* vertex `c + 2` stands for the code `c`;
* edges `0 → c + 2` for initial codes `c`, `c + 2 → 1` for accepting codes `c`, and
  `c + 2 → c' + 2` for step pairs `(c, c')` (all at radius `s`).

The codes of a space-bounded accepting branch are below `2 ^ (E - 2)`
(`Complexity.Codec.mem_iff_codeChain`), so they all are vertices; conversely any path from
`0` to `1` passes an initial code and ends with an accepting code, which gives membership
(`Complexity.Codec.mem_of_codePath`). The source and the target are the two vertices with the
shortest binary names, so the instance ends in the constant word `⟨bits 0, bits 1⟩`.

This file holds the reduction and its correctness; its implicit logspace computability is
`TCSlib.Complexity.SpaceComplexity.Logspace.PathHardDecide`.

## Main definitions

* `Complexity.PathHard.ell`, `expo`, `nV` — the size parameters.
* `Complexity.PathHard.Edge` — the edge relation of the configuration graph on codes.
* `Complexity.PathHard.adjWordE`, `Complexity.PathHard.red` — the adjacency word and the
  reduction.

## Main results

* `Complexity.PathHard.red_mem_iff` — `x ∈ L ↔ red x ∈ pathRawLang`. [AB09, Theorem 4.18,
  correctness of the reduction]
* `Complexity.PathHard.length_red`, `Complexity.PathHard.length_red_le` — the output length,
  and its polynomial bound.
* `Complexity.PathHard.red_getD` — the bits of the output by position.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.3, Theorem 4.18.)
-/

namespace Complexity.PathHard

open Turing LogProg Codec

/-! ## Size parameters -/

/-- The logarithmic size parameter `ℓ = |bits (m + 1)|` of an input length `m`. -/
def ell (m : ℕ) : ℕ := (Nat.bits (m + 1)).length

/-- The vertex exponent `E = K (c₀ + 1) ℓ + K + 2`. -/
def expo (K c₀ m : ℕ) : ℕ := K * (c₀ + 1) * ell m + (K + 2)

/-- The vertex count `n = 2 ^ E`. -/
def nV (K c₀ m : ℕ) : ℕ := 2 ^ expo K c₀ m

/-- `ℓ` is the bit length of `m + 1`, a `Nat.size`. -/
lemma ell_eq_size (m : ℕ) : ell m = Nat.size (m + 1) := by
  rw [ell, Nat.size_eq_bits_len]

/-- `logSpace m ≤ ℓ`. -/
lemma logSpace_le_ell (m : ℕ) : logSpace m ≤ ell m := by
  rw [ell_eq_size, logSpace]
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · have h1 : m + 1 < 2 ^ Nat.size (m + 1) := Nat.lt_size_self _
    have h2 : 2 ^ Nat.log 2 m ≤ m := Nat.pow_log_le_self 2 (by omega)
    have : Nat.log 2 m < Nat.size (m + 1) :=
      (Nat.pow_lt_pow_iff_right (a := 2) (by norm_num)).mp (by omega)
    omega

/-- `2 ^ ℓ ≤ 2 (m + 1)`. -/
lemma two_pow_ell_le (m : ℕ) : 2 ^ ell m ≤ 2 * (m + 1) := by
  rw [ell_eq_size]
  have hpos : 0 < Nat.size (m + 1) := Nat.size_pos.mpr (by omega)
  have h : ¬ (m + 1 < 2 ^ (Nat.size (m + 1) - 1)) := fun h =>
    absurd (Nat.size_le.mpr h) (by omega)
  have e : 2 ^ Nat.size (m + 1) = 2 * 2 ^ (Nat.size (m + 1) - 1) := by
    rw [← pow_succ']; congr 1; omega
  omega

/-- `ℓ` is monotone. -/
lemma ell_mono {m m' : ℕ} (h : m ≤ m') : ell m ≤ ell m' := by
  rw [ell_eq_size, ell_eq_size]; exact Nat.size_le_size (by omega)

/-- The vertex count is monotone in the input length. -/
lemma nV_mono (K c₀ : ℕ) {m m' : ℕ} (h : m ≤ m') : nV K c₀ m ≤ nV K c₀ m' := by
  unfold nV expo
  exact Nat.pow_le_pow_right (by norm_num)
    (Nat.add_le_add_right (Nat.mul_le_mul_left _ (ell_mono h)) _)

/-- There are at least four vertices. -/
lemma four_le_nV (K c₀ m : ℕ) : 4 ≤ nV K c₀ m := by
  unfold nV expo
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- **The vertex count is polynomial**: `n ≤ 2 ^ (K + 2) · 2 ^ e · (m + 1) ^ e` with
`e = K (c₀ + 1)`.

**Proof sketch.** `2 ^ (e ℓ) = (2 ^ ℓ) ^ e ≤ (2 (m + 1)) ^ e` (`two_pow_ell_le`). -/
lemma nV_le (K c₀ m : ℕ) :
    nV K c₀ m ≤ 2 ^ (K + 2) * 2 ^ (K * (c₀ + 1)) * (m + 1) ^ (K * (c₀ + 1)) := by
  unfold nV expo
  rw [pow_add, mul_comm (K * (c₀ + 1)) (ell m), pow_mul]
  have h := Nat.pow_le_pow_left (two_pow_ell_le m) (K * (c₀ + 1))
  rw [mul_pow] at h
  calc (2 ^ ell m) ^ (K * (c₀ + 1)) * 2 ^ (K + 2)
      ≤ 2 ^ (K * (c₀ + 1)) * (m + 1) ^ (K * (c₀ + 1)) * 2 ^ (K + 2) :=
        Nat.mul_le_mul_right _ h
    _ = _ := by ring

/-! ## The graph -/

variable (N : FinNDTM Bool)

/-- **The configuration-graph edge relation on vertex numbers** (radius `s`): `0 → c + 2`
for an initial code `c`, `c + 2 → 1` for an accepting code `c`, `c + 2 → c' + 2` for a step
pair `(c, c')`. [AB09, §4.3, proof of Theorem 4.18: the configuration graph `G_{N,x}`, with
the source and target vertices made explicit] -/
def Edge (x : List Bool) (s u v : ℕ) : Prop :=
  (u = 0 ∧ 2 ≤ v ∧ pairEncode x (pairEncode (Nat.bits (v - 2)) (Nat.bits s)) ∈ initLang N) ∨
  (2 ≤ u ∧ v = 1 ∧ pairEncode x (pairEncode (Nat.bits (u - 2)) (Nat.bits s)) ∈ acceptLang N) ∨
  (2 ≤ u ∧ 2 ≤ v ∧ StepRel N x s (u - 2) (v - 2))

/-- The row-major adjacency word of `Edge` on the vertices below `n`. -/
noncomputable def adjWordE (x : List Bool) (s n : ℕ) : List Bool :=
  (List.range (n * n)).map fun k => @decide (Edge N x s (k / n) (k % n)) (Classical.dec _)

/-- The adjacency word has `n²` letters. -/
lemma length_adjWordE (x : List Bool) (s n : ℕ) : (adjWordE N x s n).length = n * n := by
  simp [adjWordE]

/-- The letter of the adjacency word at `k < n²` is the edge bit of `(k / n, k % n)`. -/
lemma adjWordE_getD (x : List Bool) (s n k : ℕ) (hk : k < n * n) :
    (adjWordE N x s n).getD k false = @decide (Edge N x s (k / n) (k % n)) (Classical.dec _) := by
  simp [adjWordE, List.getD_eq_getElem?_getD, hk]

/-- The raw edge relation of the adjacency word is `Edge` below `n`.

**Proof sketch.** `rawEdge n w u v` reads letter `u n + v` of `w` for `u, v < n`; that index
is below `n²`, so the letter is the edge bit of `((u n + v) / n, (u n + v) % n) = (u, v)`
(`adjWordE_getD`), in both directions. -/
lemma rawEdge_adjWordE (x : List Bool) (s n u v : ℕ) :
    rawEdge n (adjWordE N x s n) u v ↔ u < n ∧ v < n ∧ Edge N x s u v := by
  unfold rawEdge
  constructor
  · rintro ⟨hu, hv, h⟩
    have hk : u * n + v < n * n := by nlinarith
    rw [adjWordE_getD N x s n _ hk] at h
    have e1 : (u * n + v) / n = u := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hv, Nat.zero_add]
    have e2 : (u * n + v) % n = v := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hv]
    rw [e1, e2] at h
    exact ⟨hu, hv, @of_decide_eq_true _ (Classical.dec _) h⟩
  · rintro ⟨hu, hv, h⟩
    have hk : u * n + v < n * n := by nlinarith
    refine ⟨hu, hv, ?_⟩
    rw [adjWordE_getD N x s n _ hk]
    have e1 : (u * n + v) / n = u := by
      rw [Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hv, Nat.zero_add]
    have e2 : (u * n + v) % n = v := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hv]
    rw [e1, e2]
    exact @decide_eq_true _ (Classical.dec _) h

/-! ## The reduction -/

/-- **The reduction** [AB09, Theorem 4.18]: `x` maps to the raw `PATH` instance on
`n = nV (codeK N) c₀ |x|` vertices with adjacency word `adjWordE` at radius `c₀ ℓ`, source `0`
and target `1`. -/
noncomputable def red (c₀ : ℕ) (x : List Bool) : List Bool :=
  pathRaw (nV (codeK N) c₀ x.length)
    (adjWordE N x (c₀ * ell x.length) (nV (codeK N) c₀ x.length)) 0 1

/-- **Correctness of the reduction** [AB09, Theorem 4.18]: if `N` decides `L` in space
`c₀ · logSpace`, then `x ∈ L` iff the target `1` is reachable from the source `0` in the
graph of `red x`.

**Proof sketch.** (⇒) The bridge lemma at radius `s = c₀ ℓ ≥ c₀ logSpace |x|` gives a chain
of codes `c₀', …, c_t` from the initial code through step pairs to an accepting code, all
below `2 ^ (K (s + logSpace |x| + 1)) ≤ 2 ^ (E - 2)`; so `0, c₀' + 2, …, c_t + 2, 1` is a
path of vertices below `n = 2 ^ E`. (⇐) The output determines its graph (the pairing is
injective). By induction along a path to `1`: from a vertex `c + 2` there is a step path from
`c` to an accepting code, and from `0` a first edge to an initial code `c`; so there is a
step path from an initial to an accepting code, which gives membership
(`mem_of_codePath`). -/
theorem red_mem_iff {L : Language Bool} {c₀ : ℕ}
    (h : N.DecidesInSpace L fun n => c₀ * logSpace n) (x : List Bool) :
    x ∈ L ↔ red N c₀ x ∈ pathRawLang := by
  set n := nV (codeK N) c₀ x.length with hn
  set s := c₀ * ell x.length with hs
  have h4 := four_le_nV (codeK N) c₀ x.length
  constructor
  · intro hx
    obtain ⟨t, c, -, hinit, hstep, hacc, hlt⟩ :=
      (mem_iff_codeChain h x s (Nat.mul_le_mul_left _ (logSpace_le_ell _))).mp hx
    -- every code is a vertex
    have hW : ∀ i ≤ t, c i + 2 < n := by
      intro i hi
      have e1 := hlt i hi
      have e2 : codeK N * (s + logSpace x.length + 1) + 2 ≤ expo (codeK N) c₀ x.length := by
        have := logSpace_le_ell x.length
        simp only [expo, hs]
        nlinarith
      have e3 : 2 ^ (codeK N * (s + logSpace x.length + 1)) * 4 ≤ n := by
        rw [hn, nV, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
        exact Nat.pow_le_pow_right (by norm_num) e2
      have e4 : 1 ≤ 2 ^ (codeK N * (s + logSpace x.length + 1)) := Nat.one_le_two_pow
      omega
    refine ⟨n, adjWordE N x s n, 0, 1, length_adjWordE N x s n, by omega, by omega, rfl, ?_⟩
    have hchain : ∀ j ≤ t, Relation.ReflTransGen (rawEdge n (adjWordE N x s n))
        (c 0 + 2) (c j + 2) := by
      intro j
      induction j with
      | zero => intro _; exact Relation.ReflTransGen.refl
      | succ j ih =>
        intro hj
        refine (ih (by omega)).tail ((rawEdge_adjWordE N x s n _ _).mpr
          ⟨hW j (by omega), hW (j + 1) hj, Or.inr (Or.inr ⟨by omega, by omega, ?_⟩)⟩)
        simpa [StepRel] using hstep j (by omega)
    have first : rawEdge n (adjWordE N x s n) 0 (c 0 + 2) :=
      (rawEdge_adjWordE N x s n _ _).mpr ⟨by omega, hW 0 (by omega),
        Or.inl ⟨rfl, by omega, by simpa using hinit⟩⟩
    have last : rawEdge n (adjWordE N x s n) (c t + 2) 1 :=
      (rawEdge_adjWordE N x s n _ _).mpr ⟨hW t le_rfl, by omega,
        Or.inr (Or.inl ⟨by omega, rfl, by simpa using hacc⟩)⟩
    exact (Relation.ReflTransGen.head first (hchain t le_rfl)).tail last
  · rintro ⟨n', M', s', t', -, -, -, he, hr⟩
    -- the output determines the graph
    have e := he
    simp only [red, pathRaw] at e
    obtain ⟨e1, e2⟩ := pairEncode_inj e
    obtain ⟨e3, e4⟩ := pairEncode_inj e2
    obtain ⟨e5, e6⟩ := pairEncode_inj e4
    have hn' : n' = n := by simpa using (congrArg List.length e1).symm
    subst hn'
    have hs' : s' = 0 := bits_injective e5.symm
    have ht' : t' = 1 := bits_injective e6.symm
    subst hs' ht'
    rw [← e3] at hr
    -- induction along the path
    have key : ∀ a, Relation.ReflTransGen (rawEdge (nV (codeK N) c₀ x.length)
        (adjWordE N x s (nV (codeK N) c₀ x.length))) a 1 →
        (a = 0 → x ∈ L) ∧ (2 ≤ a → ∃ v, Relation.ReflTransGen (StepRel N x s) (a - 2) v ∧
          pairEncode x (pairEncode (Nat.bits v) (Nat.bits s)) ∈ acceptLang N) := by
      intro a ha
      induction ha using Relation.ReflTransGen.head_induction_on with
      | refl => exact ⟨by omega, by omega⟩
      | @head a' b' hab _ ih =>
        obtain ⟨-, -, hE⟩ := (rawEdge_adjWordE N x s _ _ _).mp hab
        rcases hE with ⟨ha0, hb2, hinit⟩ | ⟨ha2, hb1, hacc⟩ | ⟨ha2, hb2, hst⟩
        · refine ⟨fun _ => ?_, by omega⟩
          obtain ⟨v, hp, hacc⟩ := ih.2 hb2
          exact mem_of_codePath h x s (b' - 2) v hinit hp hacc
        · exact ⟨by omega, fun _ => ⟨a' - 2, Relation.ReflTransGen.refl, hacc⟩⟩
        · refine ⟨by omega, fun _ => ?_⟩
          obtain ⟨v, hp, hacc⟩ := ih.2 hb2
          exact ⟨v, Relation.ReflTransGen.head hst hp, hacc⟩
    exact (key 0 hr).1 rfl

/-! ## The output by position -/

/-- **The output length**: `|red x| = 2n² + 2n + 7`. -/
lemma length_red (c₀ : ℕ) (x : List Bool) :
    (red N c₀ x).length = 2 * (nV (codeK N) c₀ x.length) ^ 2 +
      2 * nV (codeK N) c₀ x.length + 7 := by
  simp only [red, pathRaw, length_pairEncode, length_adjWordE, List.length_replicate,
    Nat.zero_bits, Nat.one_bits, List.length_nil, List.length_singleton]
  ring

/-- **The output length is polynomial** in the input length.

**Proof sketch.** `n ≤ D (m + 1) ^ e` (`nV_le`), so `2n² + 2n + 7 ≤ (2D² + 2D + 7)(m + 1)^{2e}`. -/
lemma length_red_le (c₀ : ℕ) :
    ∃ C c : ℕ, ∀ x : List Bool, (red N c₀ x).length ≤ C * (x.length + 1) ^ c := by
  set e := codeK N * (c₀ + 1)
  set D := 2 ^ (codeK N + 2) * 2 ^ e
  refine ⟨2 * D ^ 2 + 2 * D + 7, 2 * e, fun x => ?_⟩
  rw [length_red]
  have hn := nV_le (codeK N) c₀ x.length
  set q := (x.length + 1) ^ e
  have hq : 1 ≤ q := Nat.one_le_pow _ _ (by omega)
  have hq2 : (x.length + 1) ^ (2 * e) = q ^ 2 := by rw [pow_mul']
  rw [hq2]
  have h1 : nV (codeK N) c₀ x.length ^ 2 ≤ (D * q) ^ 2 := Nat.pow_le_pow_left hn 2
  have h2 : q ≤ q ^ 2 := by nlinarith
  have h3 : D * q ≤ D * q ^ 2 := Nat.mul_le_mul_left _ h2
  have h4 : (D * q) ^ 2 = D ^ 2 * q ^ 2 := by ring
  have h5 : 7 ≤ 7 * q ^ 2 := by nlinarith
  have hD : nV (codeK N) c₀ x.length ≤ D * q := hn
  nlinarith

/-- **The bits of the output** by position, with `n` the vertex count and `k = i - 2n - 2`:
the unary block `1²ⁿ`, the separator `01`, the doubled adjacency word (letter `k` is the edge
bit of `(k/2 / n, k/2 % n)`), and the tail `01 01 1`.

**Proof sketch.** `red x` is `pathRaw` of the unary block and the pair of the adjacency word
with the constant `⟨bits 0, bits 1⟩`, so `pairEncode_getD` splits position `i` into the
doubled unary block (`i < 2n`), the separator `01`, and the doubled pair at `i - (2n + 2)`;
applied once more, the latter splits into the doubled adjacency word (`length_adjWordE`,
letter `k / 2` by `adjWordE_getD`) and the tail past `2n²` (a separator and the constant
word), whose five letters are computed by cases. -/
lemma red_getD (c₀ : ℕ) (x : List Bool) (i : ℕ) :
    (red N c₀ x).getD i false =
      if i < 2 * nV (codeK N) c₀ x.length then true
      else if i = 2 * nV (codeK N) c₀ x.length then false
      else if i = 2 * nV (codeK N) c₀ x.length + 1 then true
      else if i - (2 * nV (codeK N) c₀ x.length + 2) < 2 * nV (codeK N) c₀ x.length ^ 2 then
        @decide (Edge N x (c₀ * ell x.length)
          ((i - (2 * nV (codeK N) c₀ x.length + 2)) / 2 / nV (codeK N) c₀ x.length)
          ((i - (2 * nV (codeK N) c₀ x.length + 2)) / 2 % nV (codeK N) c₀ x.length))
          (Classical.dec _)
      else [false, true, false, true, true].getD
        (i - (2 * nV (codeK N) c₀ x.length + 2) - 2 * nV (codeK N) c₀ x.length ^ 2) false := by
  simp only [red, pathRaw]
  set n := nV (codeK N) c₀ x.length
  rw [pairEncode_getD]
  simp only [List.length_replicate]
  split_ifs with h1 h2 h3 h4
  · rw [List.getD_eq_getElem?_getD, List.getElem?_replicate, if_pos (by omega)]; rfl
  · rfl
  · rfl
  · rw [show i - 2 * n - 2 = i - (2 * n + 2) by omega, pairEncode_getD, length_adjWordE,
      if_pos (by nlinarith), adjWordE_getD N x _ n _ (by
        have : (i - (2 * n + 2)) / 2 < n * n := by
          rw [Nat.div_lt_iff_lt_mul (by norm_num)]; nlinarith
        exact this)]
  · rw [show i - 2 * n - 2 = i - (2 * n + 2) by omega, pairEncode_getD, length_adjWordE,
      if_neg (by nlinarith)]
    simp only [Nat.zero_bits, Nat.one_bits]
    rw [sq] at h4 ⊢
    obtain ⟨r, hr⟩ : ∃ r, i - (2 * n + 2) = 2 * (n * n) + r := ⟨i - (2 * n + 2) - 2 * (n * n),
      by omega⟩
    rw [hr, show 2 * (n * n) + r - 2 * (n * n) = r by omega]
    rcases r with _ | _ | r
    · simp
    · simp
    · rw [show r + 1 + 1 - 2 = r by omega]
      rcases r with _ | _ | _ | r <;> simp [pairEncode, List.getD_eq_getElem?_getD]

end Complexity.PathHard
