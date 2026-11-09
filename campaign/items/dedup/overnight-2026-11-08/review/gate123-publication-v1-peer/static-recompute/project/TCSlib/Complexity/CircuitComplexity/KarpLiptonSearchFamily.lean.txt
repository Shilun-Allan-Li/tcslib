/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.CircuitComplexity.KarpLiptonSearch
import TCSlib.Complexity.CircuitComplexity.KarpLiptonPrefix
import TCSlib.Complexity.CircuitComplexity.PPoly

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The Karp–Lipton search circuits from `NP ⊆ P/poly`

[AB09, proof of Thm 6.19, p. 114]: "If `NP ⊆ P/poly`, then there exists a polynomial `p`
and a `p(n)`-sized circuit family `{C_n}` [deciding the extension problem] … we obtain
from the family `{C_n}` a `q(n)`-sized circuit family `{C'_n}`, where `q(·)` is a
polynomial, such that for every such formula `ϕ` and `u`, if there is a string `v` such
that `ϕ(u, v) = 1`, then `C'_n(ϕ, u)` outputs such a string `v`."

This file instantiates the abstract search circuit `BoolCircuit.searchCircuit` from the
hypothesis `NP ⊆ P/poly`, for an arbitrary polynomial-time relation
`R(y, v) :⟺ ⟨y, v⟩ ∈ V` (`V ∈ P`) with witnesses of length `m(n) = C (n+1)^c`:
the prefix language of `V` is in `NP` (`Complexity.KarpLipton.prefixLangOf_mem_NP`),
so it has a polynomial-size fan-in-two family `F`; each decision circuit `D_j` of the
search is `F`'s circuit for the query length with its inputs rewired to read `y`, the
partial witness `p`, and constants (`BoolCircuit.DAGCircuit.rewire`).

## Main definitions

* `BoolCircuit.DAGCircuit.rewire` — feed a circuit's inputs from the inputs of a new
  circuit and two constants.
* `BoolCircuit.KarpLipton.querySrcs` — the wiring that presents `(y, p)` to the prefix
  circuit as the query `⟨y, 1^{m-j} 0 p⟩`.

## Main results

* `BoolCircuit.DAGCircuit.rewire_eval`, `rewire_isFaninTwo`, `rewire_size`.
* `BoolCircuit.exists_searchCircuit_of_NP_subset_PPoly` — [AB09, p. 114]: a polynomial-size
  fan-in-two multi-output circuit family that outputs a witness whenever one exists.

## Divergences from [AB09]

* The book's relation is `ϕ(u, v) = 1` for a formula `ϕ`; here it is `⟨y, v⟩ ∈ V` for an
  arbitrary `V ∈ P` (which covers the book's case, formula evaluation being in `P`).
* The decision circuits are the `P/poly` circuits for the marker-encoded prefix language
  (one circuit length per `n`), rewired, rather than circuits for `SAT` on formulas with
  hard-wired variables.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§2.5, Theorem 2.18; §6.4, proof of Theorem 6.19,
  p. 114.)
-/

namespace BoolCircuit

open Turing Complexity Complexity.PolyHierarchy Complexity.KarpLipton

/-! ### Rewiring the inputs of a circuit -/

/-- The two constant gates `0, 1` read no vertex. -/
private theorem gatesAcyclic_consts (k : ℕ) :
    GatesAcyclic k [constGate false, constGate true] := by
  intro i hi a ha
  have : i = 0 ∨ i = 1 := by simp at hi; omega
  rcases this with rfl | rfl <;> simp at ha

/-- **Rewiring**: a circuit `C` on `N` inputs becomes a circuit on `k` inputs whose input
`i` of `C` reads vertex `srcs[i]`, where vertices `0, …, k-1` are the new inputs and
`k`, `k+1` are new constant gates `0`, `1`. -/
def DAGCircuit.rewire {N : ℕ} (C : DAGCircuit N) (k : ℕ) (srcs : List ℕ)
    (hlen : srcs.length = N) (hsrc : ∀ a ∈ srcs, a < k + 2) : DAGCircuit k where
  gates := [constGate false, constGate true] ++ embedGates C srcs (k + 2)
  output := k + 2 + C.gates.length
  args_lt := (gatesAcyclic_consts k).append (by
    simpa using gatesAcyclic_embedGates C srcs (k + 2) hlen hsrc)
  output_lt := by simp; omega

section rewire

variable {N : ℕ} (C : DAGCircuit N) (k : ℕ) (srcs : List ℕ) (hlen : srcs.length = N)
  (hsrc : ∀ a ∈ srcs, a < k + 2)

/-- The rewired circuit evaluates `C` on the source values, the new inputs followed by the
constants `0, 1`. -/
theorem DAGCircuit.rewire_eval (x : Fin k → Bool) :
    (C.rewire k srcs hlen hsrc).eval x =
      C.eval (fun i => (List.ofFn x ++ [false, true]).getD (srcs.getD i 0) false) := by
  have hinit : runWith DAGGate.eval [constGate false, constGate true] (List.ofFn x) =
      List.ofFn x ++ [false, true] := by
    simp [runWith]
  have hl : (List.ofFn x ++ [false, true]).length = k + 2 := by simp
  simp only [DAGCircuit.rewire, DAGCircuit.eval, DAGCircuit.values]
  rw [runWith_append, hinit]
  have h := runWith_embedGates_getD C srcs hlen (List.ofFn x ++ [false, true])
    (by rw [hl]; exact hsrc)
  rw [hl] at h
  exact h

/-- Rewiring keeps fan-in two. -/
theorem DAGCircuit.rewire_isFaninTwo (hC : C.IsFaninTwo) :
    (C.rewire k srcs hlen hsrc).IsFaninTwo := by
  have h : ∀ g ∈ (C.rewire k srcs hlen hsrc).gates,
      g.args.Nodup ∧ (g.kind = .not → g.args.length = 1) ∧ g.args.length ≤ 2 := by
    intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hg
      rcases hg with rfl | rfl <;> simp [constGate]
    · exact faninTwo_embedGates C hC srcs _ g hg
  exact ⟨fun g hg => ⟨(h g hg).1, (h g hg).2.1⟩, fun g hg => (h g hg).2.2⟩

/-- The size of a rewired circuit: the new inputs, two constants, the gates of `C` and
one copy gate. -/
theorem DAGCircuit.rewire_size :
    (C.rewire k srcs hlen hsrc).size = k + 3 + C.gates.length := by
  simp [DAGCircuit.rewire, DAGCircuit.size]
  omega

end rewire

/-! ### The query wiring -/

namespace KarpLipton

/-- **The query wiring**: with new inputs `y p` (`|y| = n`, `|p| = j`) and constants at
`n + j` (`0`) and `n + j + 1` (`1`), the sources presenting the query
`⟨y, 1^{m-j} 0 p⟩ = ŷ 0 1 1^{m-j} 0 p` (`ŷ` = `y` with doubled bits). -/
def querySrcs (n j m : ℕ) : List ℕ :=
  (List.range n).flatMap (fun i => [i, i]) ++ [n + j, n + j + 1] ++
    List.replicate (m - j) (n + j + 1) ++ [n + j] ++ (List.range j).map (n + ·)

/-- The query wiring has one source per bit of the query `⟨y, 1^{m-j} 0 p⟩`. -/
theorem length_querySrcs (n j m : ℕ) :
    (querySrcs n j m).length = 2 * n + 2 + (m - j) + 1 + j := by
  simp [querySrcs, List.length_flatMap]
  omega

/-- Every source of the query wiring is an input or one of the two constants. -/
theorem querySrcs_lt (n j m : ℕ) : ∀ a ∈ querySrcs n j m, a < n + j + 2 := by
  intro a ha
  simp only [querySrcs, List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons,
    List.mem_nil_iff, or_false, List.mem_replicate, List.mem_map] at ha
  omega

/-- The query wiring reads exactly the query string: reading the sources of the wiring
out of the input `y ++ p ++ [0, 1]` (with `|y| = n`, `|p| = j`) gives the pair encoding
`⟨y, 1^{m-j} 0 p⟩`.

**Proof sketch.** Index `i < n` of the input is bit `y_i`, index `n + i` (for `i < j`) is
bit `p_i`, and indices `n + j`, `n + j + 1` are the constants `0`, `1`. Hence the doubled
block of sources `i, i` (for `i < n`) reads the doubled copy of `y`, the final block
`n + i` reads `p`, and the separator, the run of `1`s and the `0` read the constants.
Concatenating the blocks gives exactly the pair encoding. -/
theorem querySrcs_map (n j m : ℕ) (y p : List Bool) (hy : y.length = n) (hp : p.length = j) :
    (querySrcs n j m).map (fun a => (y ++ p ++ [false, true]).getD a false) =
      pairEncode y (List.replicate (m - j) true ++ false :: p) := by
  set init := y ++ p ++ [false, true] with hinit
  have hY : ∀ i, i < n → init.getD i false = y.getD i false := by
    intro i hi
    rw [hinit, List.append_assoc, List.getD_append _ _ _ _ (by omega)]
  have hP : ∀ i, i < j → init.getD (n + i) false = p.getD i false := by
    intro i hi
    rw [hinit, List.append_assoc, List.getD_append_right _ _ _ _ (by omega), hy,
      Nat.add_sub_cancel_left, List.getD_append _ _ _ _ (by omega)]
  have h0 : init.getD (n + j) false = false := by
    rw [hinit, List.getD_append_right _ _ _ _ (by simp; omega)]; simp [hy, hp]
  have h1 : init.getD (n + j + 1) false = true := by
    rw [hinit, List.getD_append_right _ _ _ _ (by simp; omega)]
    simp [hy, hp]
  have hyl : (List.range n).map (fun i => y.getD i false) = y := by
    apply List.ext_getElem (by simp [hy])
    intro i h1 h2
    simp [List.getElem?_eq_getElem h2]
  have hpl : (List.range j).map (fun i => p.getD i false) = p := by
    apply List.ext_getElem (by simp [hp])
    intro i h1 h2
    simp [List.getElem?_eq_getElem h2]
  have hdouble : ((List.range n).flatMap (fun i => [i, i])).map (fun a => init.getD a false) =
      y.flatMap (fun b => [b, b]) := by
    conv_rhs => rw [← hyl]
    rw [List.map_flatMap, List.flatMap_map]
    refine List.flatMap_congr fun i hi => ?_
    simp only [List.mem_range] at hi
    simp only [List.map_cons, List.map_nil, hY i hi]
  have htail : ((List.range j).map (n + ·)).map (fun a => init.getD a false) = p := by
    conv_rhs => rw [← hpl]
    rw [List.map_map]
    refine List.map_congr_left fun i hi => ?_
    simp only [List.mem_range] at hi
    show init.getD (n + i) false = p.getD i false
    exact hP i hi
  simp only [querySrcs, List.map_append, hdouble, htail, List.map_cons, h0, h1,
    List.map_replicate, pairEncode, List.append_assoc, List.cons_append, List.nil_append]

end KarpLipton

/-- A family circuit evaluated through `getD` on a string of its length is the family's
decision on that string. -/
private theorem family_eval_getD (F : DAGCircuitFamily) {N : ℕ} (q : List Bool)
    (hq : q.length = N) :
    (F.circuit N).eval (fun i => q.getD i false) = true ↔ q ∈ F.language := by
  subst hq
  rw [F.mem_language_iff]
  have : (fun i : Fin q.length => q.getD i false) = q.get := by
    funext i; simp
  rw [this]

open KarpLipton in
/-- **The Karp–Lipton search circuits** [AB09, proof of Thm 6.19, p. 114: "we obtain from
the family `{C_n}` a `q(n)`-sized circuit family `{C'_n}` … such that … if there is a
string `v` such that `ϕ(u, v) = 1`, then `C'_n(ϕ, u)` outputs such a string `v`"]: if
`NP ⊆ P/poly`, then for every polynomial-time relation `⟨y, v⟩ ∈ V` with witnesses of
length `m(n) = C (n+1)^c` there is a polynomial `q(n) = q₀ (n+1)^e` and, for every `n`,
a fan-in-two multi-output circuit `C'_n` of size at most `q(n)` with `m(n)` outputs
that, on every `y ∈ {0,1}ⁿ` having a witness, outputs a witness.

Deviation: the book's relation `ϕ(u, v) = 1` is generalized to any `V ∈ P`.

**Proof sketch.** The prefix language `{⟨y, 1^{m-j} 0 p⟩ : p extends to a witness}` is in
`NP` (`prefixLangOf_mem_NP`), so a fan-in-two family `F` of size `a (N+1)^k` decides it.
For `|y| = n` all queries have length `N = 2n + 3 + m`; the decision circuit `D_j` is
`F_N` rewired to read `(y, p)` as `⟨y, 1^{m-j} 0 p⟩` (`querySrcs_map`), of size
`n + m + 3 + a (N+1)^k`. The search circuit over the `D_j` (`searchCircuit_correct`)
outputs a witness, and its size `n + 1 + m (S + 1)` is polynomial in `n`. -/
theorem exists_searchCircuit_of_NP_subset_PPoly (h : NP ⊆ PPoly) {V : Language Bool}
    (hV : V ∈ P) (C c : ℕ) :
    ∃ q₀ e : ℕ, ∀ n : ℕ, ∃ S : MultiDAGCircuit n,
      S.IsFaninTwo ∧ S.size ≤ q₀ * (n + 1) ^ e ∧ S.outputs.length = C * (n + 1) ^ c ∧
      ∀ x : Fin n → Bool, (∃ v : List Bool, v.length = C * (n + 1) ^ c ∧
          pairEncode (List.ofFn x) v ∈ V) →
        pairEncode (List.ofFn x) (S.eval x) ∈ V := by
  -- the prefix language with witness length `C (|y|+1)^c` and its circuits
  have hℓ : UnaryPT (fun y => C * ((id y).length + 1) ^ c) :=
    unaryPT_poly C c polyTimeComputable_id
  obtain ⟨a, k, F, hF, hS, hFL⟩ := h (prefixLangOf_mem_NP hV hℓ (A := C) (a := c)
    fun y => le_rfl)
  set K₁ := C + 4 + a * (4 + C) ^ k with hK₁
  refine ⟨1 + C * K₁ + C, (c + 1) * (k + 2), fun n => ?_⟩
  set m := C * (n + 1) ^ c with hm
  set N := 2 * n + 3 + m with hN
  -- the decision circuits of the search
  let D : (j : ℕ) → DAGCircuit (n + j) := fun j =>
    if hj : j ≤ m then
      (F.circuit N).rewire (n + j) (querySrcs n j m)
        (by rw [length_querySrcs]; omega) (querySrcs_lt n j m)
    else constCircuit (n + j) false
  have hD : ∀ j, (D j).IsFaninTwo := by
    intro j
    by_cases hj : j ≤ m
    · simp only [D, dif_pos hj]; exact DAGCircuit.rewire_isFaninTwo _ _ _ _ _ (hF N)
    · simp only [D, dif_neg hj]; exact constCircuit_isFaninTwo _ _
  -- the size bound `S` for every `D_j`
  set P := (n + 1) ^ (c + 1) with hP
  have hn1 : n + 1 ≤ P := by
    calc n + 1 = (n + 1) ^ 1 := (pow_one _).symm
      _ ≤ P := Nat.pow_le_pow_right (by omega) (by omega)
  have hmP : m ≤ C * P := Nat.mul_le_mul_left C (Nat.pow_le_pow_right (by omega) (by omega))
  have hP1 : 1 ≤ P := by omega
  have hNP : N + 1 ≤ (4 + C) * P := by nlinarith
  have hFN : (F.circuit N).size ≤ a * (4 + C) ^ k * P ^ k := by
    calc _ ≤ a * (N + 1) ^ k := hS N
      _ ≤ a * ((4 + C) * P) ^ k := Nat.mul_le_mul_left a (Nat.pow_le_pow_left hNP k)
      _ = _ := by rw [mul_pow, mul_assoc]
  have hPk : P ^ k ≤ P ^ (k + 1) := Nat.pow_le_pow_right hP1 (by omega)
  have hP1k : P ≤ P ^ (k + 1) := by
    calc P = P ^ 1 := (pow_one _).symm
      _ ≤ P ^ (k + 1) := Nat.pow_le_pow_right hP1 (by omega)
  have hDS : ∀ j, 1 ≤ j → j ≤ m → (D j).size ≤ K₁ * P ^ (k + 1) := by
    intro j _ hj
    · simp only [D, dif_pos hj, DAGCircuit.rewire_size]
      have hg : (F.circuit N).gates.length ≤ a * (4 + C) ^ k * P ^ k :=
        le_trans (by simp [DAGCircuit.size]) hFN
      have h3 : a * (4 + C) ^ k * P ^ k ≤ a * (4 + C) ^ k * P ^ (k + 1) :=
        Nat.mul_le_mul_left _ hPk
      rw [hK₁]
      nlinarith
  refine ⟨searchCircuit D hD m, searchCircuit_isFaninTwo D hD m, ?_, ?_, ?_⟩
  · -- polynomial size
    have hsz := searchCircuit_size_le D hD m _ hDS
    have hP2 : P ^ (k + 1) * P = P ^ (k + 2) := by ring
    have hPk2 : P ≤ P ^ (k + 2) := by
      calc P = P ^ 1 := (pow_one _).symm
        _ ≤ P ^ (k + 2) := Nat.pow_le_pow_right hP1 (by omega)
    have he : P ^ (k + 2) = (n + 1) ^ ((c + 1) * (k + 2)) := by rw [hP, ← pow_mul]
    rw [← he]
    have : m * (K₁ * P ^ (k + 1) + 1) ≤ C * K₁ * P ^ (k + 2) + C * P ^ (k + 2) := by
      calc m * (K₁ * P ^ (k + 1) + 1) ≤ (C * P) * (K₁ * P ^ (k + 1) + 1) :=
            Nat.mul_le_mul_right _ hmP
        _ = C * K₁ * (P ^ (k + 1) * P) + C * P := by ring
        _ ≤ _ := by rw [hP2]; nlinarith
    nlinarith
  · exact (searchState_struct D hD m).2.1
  · -- correctness: each `D_j` decides the extension problem
    intro x hex
    have hdec : ∀ j, 1 ≤ j → j ≤ m → ∀ y p : List Bool, y.length = n → p.length = j →
        ((D j).eval (fun i => (y ++ p).getD i false) = true ↔
          Extends (fun y v => pairEncode y v ∈ V) m y p) := by
      intro j _ hj y p hy hp
      simp only [D, dif_pos hj, DAGCircuit.rewire_eval]
      have hof : List.ofFn (fun i : Fin (n + j) => (y ++ p).getD i false) = y ++ p := by
        apply List.ext_getElem (by simp [hy, hp])
        intro i h1 h2
        simp [List.getElem?_eq_getElem h2]
      have hfun : (fun i : Fin N => (List.ofFn (fun i : Fin (n + j) => (y ++ p).getD i false) ++
          [false, true]).getD ((querySrcs n j m).getD i 0) false) =
          fun i : Fin N => (pairEncode y (List.replicate (m - j) true ++ false :: p)).getD i false := by
        funext i
        have hi : (i : ℕ) < (querySrcs n j m).length := by
          rw [length_querySrcs]; omega
        rw [hof, ← querySrcs_map n j m y p hy hp]
        exact getD_map_getD (f := fun a => (y ++ p ++ [false, true]).getD a false) hi
      rw [hfun, family_eval_getD F _ (by simp [length_pairEncode, hy, hp]; omega), hFL,
        mem_prefixLangOf_iff]
      simp only [id, hy, Extends]
      exact Iff.rfl
    have := searchCircuit_correct D hD (fun y v => pairEncode y v ∈ V) m hdec x hex
    exact this.2

end BoolCircuit
