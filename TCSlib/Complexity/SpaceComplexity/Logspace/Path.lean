/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Logic.Relation
import TCSlib.Complexity.SpaceComplexity.Logspace.Reductions
import TCSlib.Complexity.SpaceComplexity.ConfigGraph
import TCSlib.Complexity.SpaceComplexity.Logspace.PathWalkProof
import TCSlib.Complexity.SpaceComplexity.Logspace.PathHardDecide

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The language `PATH` and its `NL`-completeness

[AB09, §4.1.2 and §4.3, (4.1) and Theorem 4.18]: directed `s`-`t`
connectivity is the language capturing nondeterministic logarithmic space.
Phase P4.4 of `AroraBarakChapters3-4Plan.md` — the campaign's first graph
encoding.

## Design

* **The encoding** `⟨G, s, t⟩` is
  `pairEncode 1ⁿ (pairEncode (row-major adjacency bits) (pairEncode (bits s) (bits t)))`:
  the unary vertex count makes `n` recoverable by a prefix scan, the matrix
  length is checkable as `n²`, and the endpoints ride in binary. Membership
  is by existential witness over genuine encodings (the `EXPCOM`/`dblLang`
  house pattern), so no total decode is needed; non-encodings are out of
  `PATH`.
* **Reachability is in-house**: `Complexity.GraphReach`, the reflexive-
  transitive closure of the decoded adjacency relation on `Fin n`. The plan
  (§2.6) named `GraphTheory`'s `Digraph.Reachable` as the semantic target;
  that tree currently carries admissions outside the audited closure, so the
  campaign keeps the relation local and records the bridging lemma as future
  work (plan decision log, this phase's row) — a deviation declared for the
  audit.

## Main definitions

* `Complexity.GraphReach` — reachability of the adjacency relation.
* `Complexity.encodePATH`, `Complexity.PATH` — the instance encoding and the
  language. [AB09, (4.1)]

## Main results (phase-P4.4 statements)

* `Complexity.PATH_mem_NL` — the nondeterministic walk (proved, by the
  nondeterministic register machine of `Logspace.PathWalk`). [AB09, Example 4.7,
  the `PATH ∈ NL` paragraph]
* `Complexity.PATH_NLComplete` — [AB09, Theorem 4.18] (proved: hardness by the
  configuration-graph reduction of `Logspace.PathHard`).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1.2, (4.1); §4.3, Theorem 4.18.)
-/

namespace Complexity

open Turing

/-- Reachability of the adjacency relation `A` on `Fin n`: the reflexive-
transitive closure of its edge relation. (In-house; the bridge to
`GraphTheory`'s digraph reachability is recorded future work — see the
module docstring.) -/
def GraphReach {n : ℕ} (A : Fin n → Fin n → Bool) (s t : Fin n) : Prop :=
  Relation.ReflTransGen (fun u v => A u v = true) s t

/-- **The `⟨G, s, t⟩` instance encoding**: unary vertex count, row-major
adjacency matrix, endpoints in binary — each layer an aligned pair, per the
campaign pairing. -/
def encodePATH (n : ℕ) (A : Fin n → Fin n → Bool) (s t : Fin n) : List Bool :=
  pairEncode (List.replicate n true)
    (pairEncode ((List.finRange n).flatMap fun u => (List.finRange n).map (A u))
      (pairEncode (Nat.bits (s : ℕ)) (Nat.bits (t : ℕ))))

/-- **The language `PATH`** [AB09, (4.1)]: encodings of directed graphs with
two designated vertices such that the second is reachable from the first.
Membership is by existential witness over genuine encodings; strings that
encode no instance are not in `PATH`. -/
def PATH : Language Bool :=
  {x | ∃ (n : ℕ) (A : Fin n → Fin n → Bool) (s t : Fin n),
    x = encodePATH n A s t ∧ GraphReach A s t}

/-- The row-major adjacency word of `encodePATH` has `n²` bits. -/
lemma length_adjWord (n : ℕ) (A : Fin n → Fin n → Bool) :
    ((List.finRange n).flatMap fun u => (List.finRange n).map (A u)).length = n * n := by
  simp [List.length_flatMap, List.sum_replicate]

/-- Reading a concatenation of rows of equal length `k` at row `i`, column `j`. -/
lemma getD_flatMap_rows {α : Type} (L : List α) (f : α → List Bool) (k : ℕ)
    (hf : ∀ a, (f a).length = k) (i j : ℕ) (hi : i < L.length) (hj : j < k) :
    (L.flatMap f).getD (i * k + j) false = (f L[i]).getD j false := by
  induction L generalizing i with
  | nil => simp at hi
  | cons a L ih =>
    rw [List.flatMap_cons]
    cases i with
    | zero =>
      simp only [Nat.zero_mul, Nat.zero_add, List.getElem_cons_zero]
      rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by rw [hf]; exact hj),
        ← List.getD_eq_getElem?_getD]
    | succ i =>
      simp only [List.getElem_cons_succ]
      have e : (i + 1) * k + j = k + (i * k + j) := by rw [Nat.add_mul, Nat.one_mul]; omega
      rw [e, List.getD_eq_getElem?_getD, List.getElem?_append_right (by rw [hf]; omega), hf,
        show k + (i * k + j) - k = i * k + j by omega, ← List.getD_eq_getElem?_getD]
      exact ih i (by simpa using hi)

/-- The bit of the row-major adjacency word at `u · n + v` is the edge bit `A u v`. -/
lemma adjWord_getD {n : ℕ} (A : Fin n → Fin n → Bool) (u v : Fin n) :
    ((List.finRange n).flatMap fun u => (List.finRange n).map (A u)).getD
      (u * n + v) false = A u v := by
  rw [getD_flatMap_rows _ _ n (fun _ => by simp) u v (by simp) v.isLt]
  simp [List.getD_eq_getElem?_getD]

/-- **`PATH` is the raw `PATH` language** of `Logspace.PathWalk`: the instance encoding
is the raw format with the row-major adjacency word, and graph reachability is
reachability along the word's edge relation below `n`.

**Proof sketch.** Forwards, lift the path along `Fin.val` (`adjWord_getD`). Backwards,
read the matrix off the word (`A u v = M[u · n + v]`); the word is then the adjacency word
of `A` (every index below `n²` is `(i / n) · n + i % n`), and a path of the word's edge
relation stays below `n`, so it is a path of `A`. -/
theorem PATH_eq_pathRawLang : PATH = pathRawLang := by
  ext x
  constructor
  · rintro ⟨n, A, s, t, hx, hr⟩
    refine ⟨n, _, s, t, length_adjWord n A, s.isLt, t.isLt, hx, ?_⟩
    exact Relation.ReflTransGen.lift Fin.val
      (fun a b h => ⟨a.isLt, b.isLt, by rw [adjWord_getD]; exact h⟩) hr
  · rintro ⟨n, M, s, t, hM, hs, ht, hx, hr⟩
    let A : Fin n → Fin n → Bool := fun u v => M.getD (u * n + v) false
    have hAM : ((List.finRange n).flatMap fun u => (List.finRange n).map (A u)) = M := by
      refine ext_getD' (by rw [length_adjWord, hM]) fun i hi => ?_
      rw [length_adjWord] at hi
      have hn : 0 < n := by
        rcases Nat.eq_zero_or_pos n with h | h
        · rw [h] at hi; simp at hi
        · exact h
      have hq : i / n < n := Nat.div_lt_of_lt_mul hi
      have hr' : i % n < n := Nat.mod_lt i hn
      have he : i = (i / n) * n + i % n := by rw [Nat.mul_comm]; exact (Nat.div_add_mod i n).symm
      have := adjWord_getD A ⟨i / n, hq⟩ ⟨i % n, hr'⟩
      simp only at this
      rw [← he] at this
      rw [this]
      simp only [A]
      rw [← he]
    refine ⟨n, A, ⟨s, hs⟩, ⟨t, ht⟩, by rw [hx, ← hAM]; rfl, ?_⟩
    have key : ∀ a, Relation.ReflTransGen (rawEdge n M) a t → ∀ ha : a < n,
        GraphReach A ⟨a, ha⟩ ⟨t, ht⟩ := by
      intro a h
      induction h using Relation.ReflTransGen.head_induction_on with
      | refl => intro _; exact Relation.ReflTransGen.refl
      | head hac _ ih =>
        intro ha
        exact Relation.ReflTransGen.head hac.2.2 (ih hac.2.1)
    exact key s hr hs

/-- **`PATH ∈ NL`** ([AB09, §4.1.2, the nondeterministic walk]): guess the path vertex by
vertex, keeping only the current vertex and a step counter.

**Proof sketch.** `PATH` is the raw language `pathRawLang` (`PATH_eq_pathRawLang`), which
the nondeterministic register machine `Complexity.LogProg.pathA` decides
(`Complexity.pathRawLang_mem_NL`, by `Complexity.LogProg.narm_decides_poly`). Reading the
input through the logspace bit and length deciders, the machine checks the unary prefix
`1ⁿ` and the shape of the `n²`-pair matrix field, guesses `s < n` and `t < n` and checks
them against the endpoint fields, then walks from `s`: if the current vertex is `t` it
accepts, after `n` steps it rejects, otherwise it guesses the next vertex `v < n`, computes
the position of the bit `A u v` by additions, rejects on a `0`, and moves to `v`. Every
branch halts and every register stays at most `4 (|x| + 1)`; some branch accepts iff `t` is
reachable from `s` within `n` edges, which by path shortening (`Complexity.reach_iff_walkLe`)
is reachability. -/
theorem PATH_mem_NL : PATH ∈ NL := by
  rw [PATH_eq_pathRawLang]
  exact pathRawLang_mem_NL

/-- **`PATH` is `NL`-complete** ([AB09, Theorem 4.18]): membership is
`Complexity.PATH_mem_NL`; hardness maps a language's machine-and-input to its configuration
graph.

**Proof sketch.** Membership is `PATH_mem_NL`. For hardness, `PATH` is the raw language
`pathRawLang` (`PATH_eq_pathRawLang`), and every `B ∈ NL` reduces to it
(`Complexity.pathRawLang_NLHard`): if `N` decides `B` in space `c₀ · logSpace`, the
reduction `Complexity.PathHard.red N c₀` sends `x` to the graph on `n = 2 ^ E` vertices
(`E = K (c₀ + 1) ℓ + K + 2`, `ℓ = |bits (|x| + 1)|`, `K = codeK N`, so `n` is polynomial in
`|x|`) whose vertex `c + 2` is the configuration code `c` at radius `s = c₀ ℓ`, with a
source `0` joined to the initial codes, a target `1` joined from the accepting codes, and the
step pairs of the codec as the remaining edges. Then `x ∈ B` iff `1` is reachable from `0`
(`PathHard.red_mem_iff`, from the bridge lemma `Complexity.Codec.mem_iff_codeChain` and
`Complexity.Codec.mem_of_codePath`); no accepting normalization of `N` is needed, since the
target collects all accepting codes. The reduction is implicitly logspace computable
(`PathHard.implicitlyLogspaceComputable_red`): its length `2n² + 2n + 7` is polynomial, and
a register machine (`PathHard.A`) answers a bit or length query `⟨x, bits i⟩` by parsing the
query, computing `E` and the block lengths by counting loops, decoding `i`, locating it in
the layout (unary block, separator, doubled adjacency word, tail) by comparisons and
subtractions, splitting a matrix offset into a vertex pair by halving and shifting, and
asking the logspace initial-, accepting- or step-code decider of the codec (read through
`Complexity.dropIdx`); `Complexity.LogProg.arm_decides_poly` turns it into a logspace
decider. -/
theorem PATH_NLComplete : NLComplete PATH := by
  refine ⟨PATH_mem_NL, fun B hB => ?_⟩
  rw [PATH_eq_pathRawLang]
  exact pathRawLang_NLHard hB

end Complexity
