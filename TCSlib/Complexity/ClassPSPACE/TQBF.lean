/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.Formulas.QBFEncoding
import TCSlib.Complexity.SpaceComplexity.ConfigGraph
import TCSlib.Complexity.SpaceComplexity.Constructible

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# `PSPACE`-completeness and `TQBF`

[AB09, §4.2]: `PSPACE`-hardness and -completeness (Definition 4.9), the
adjacency-formula half of Claim 4.4(2), and the Stockmeyer-Meyer theorem that
`TQBF` is `PSPACE`-complete (Theorem 4.13). Phase P4.3 of
`AroraBarakChapters3-4Plan.md`.

## Design

* **Def 4.9 verbatim over the campaign's `≤ₚ`** (`Complexity.PolyTimeReducible`,
  chapter 2); the logspace-reduction variant ([AB09, Exercise 4.9]) waits for
  phase P4.4's `≤ₗ`.
* **Claim 4.4(2) at polynomial size, over a packaged codec.** The statement
  supplies, for each machine: a configuration bit-codec (injective on the
  space-`s` window, fixed length linear in `s + n`) **and** a CNF family of
  size polynomial in `s + n` deciding adjacency of coded configuration pairs.
  Two declared deviations from the book's Claim 4.4(2), both harmless to every
  consumer: (i) the codec length is `O(s + n)` rather than `O(s)` — the input
  head is carried on a one-hot track to keep adjacency *local* (the book's
  `O(S)` presumes the binary head encoding of part 1, whose adjacency is not
  local; Cook-Levin's marker discipline is the model); (ii) the CNF size is
  bounded polynomially rather than linearly — Theorem 4.13's reduction only
  needs the formula polynomial and emittable in polynomial time. The codec and
  family are **existentially packaged** (the `exists_comp_partial` precedent
  for guarded interfaces): their sole consumer is `TQBF`'s hardness fill;
  D6-style promotion to named definitions is recorded for when a second
  consumer appears (the phase-P4.4 `PATH` encoding is the candidate).
* **The facade discipline**: `ClassPSPACE.lean` is this phase's own new
  facade; nothing frozen is touched.

## Main definitions

* `Complexity.PSPACEHard`, `Complexity.PSPACEComplete` — [AB09, Definition 4.9].
* `Complexity.TQBF` — the true quantified Boolean formulas, over
  `Complexity.QBF.decode`. [AB09, §4.2, before Theorem 4.13]

## Main results (all sorried; phase-P4.3 statements)

* `Complexity.PSPACE_eq_P_of_pspaceComplete_mem_P` — a `PSPACE`-complete
  language in `P` collapses `PSPACE` to `P`. [AB09, §4.2, after Definition 4.9]
* `Complexity.exists_adjacency_codec_cnf` — Claim 4.4(2), packaged form.
* `Complexity.TQBF_mem_PSPACE` — [AB09, Theorem 4.13, membership half].
* `Complexity.TQBF_PSPACEHard` — [AB09, Theorem 4.13, hardness half]; a fill
  summit (the `ψᵢ` emitter).
* `Complexity.TQBF_PSPACEComplete` — [AB09, Theorem 4.13].

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.2, Definition 4.9, Claim 4.4,
  Theorem 4.13.)
* [SM73] L. Stockmeyer, A. Meyer, *Word problems requiring exponential time*,
  STOC 1973. (Cited through [AB09]; no external text required.)
-/

namespace Complexity

open Std.Sat (CNF)
open Turing

/-- **`PSPACE`-hardness** [AB09, Definition 4.9]: every `PSPACE` language
Karp-reduces to `L'` in polynomial time. (The logspace variant is phase
P4.4's.) -/
def PSPACEHard (L' : Language Bool) : Prop :=
  ∀ L ∈ PSPACE, L ≤ₚ L'

/-- **`PSPACE`-completeness** [AB09, Definition 4.9]: `PSPACE`-hard and in
`PSPACE`. -/
def PSPACEComplete (L' : Language Bool) : Prop :=
  L' ∈ PSPACE ∧ PSPACEHard L'

/-- **A `PSPACE`-complete language in `P` collapses the class**
([AB09, §4.2, the paragraph after Definition 4.9]; spec, fill pending):
if some `PSPACE`-complete `L'` lies in `P`, then `PSPACE = P`.

**Proof sketch.** `⊇` is `Complexity.P_subset_PSPACE` (phase P4.1). `⊆`: a
`PSPACE` member reduces to `L'` (hardness), and `P` is closed downward under
`≤ₚ` (`Complexity.mem_P_of_polyTimeReducible`, chapter 2). -/
theorem PSPACE_eq_P_of_pspaceComplete_mem_P {L' : Language Bool}
    (h : PSPACEComplete L') (hP : L' ∈ P) : PSPACE = P := by
  sorry

/-- **Claim 4.4(2), packaged form** (spec, fill pending — phase P4.3; see the
module docstring's two declared deviations): for every machine there are a
constant `C`, a configuration bit-codec — fixed length `C · (s + n + 1)`,
injective on the configurations whose heads and nonblank cells lie in the
window `[-s, s]` — and a CNF family of size at most `C · (s + n + 1) ^ C`
over variables below twice the code length, such that evaluating the formula
on the concatenated codes of two windowed configurations decides exactly
whether the second is the step of the first.

**Proof sketch.** The codec is the marker discipline of the Cook-Levin
tableau row (`TCSlib.Complexity.CookLevin` precedents): a one-hot state
block, a one-hot input-position track of length `n + 2`, and per work tape a
window track of `2s + 1` cells, each cell three-valued symbol plus a
head-marker bit — total length linear in `s + n` with the machine's
constants in `C`; injectivity on the window mirrors
`Turing.MultiTapeTM.ConfigCount.coreCode_inj`. Adjacency is a conjunction of
local checks — unmarked cells copy, the marked cell and its two neighbors
update by the transition table, the one-hot tracks shift by at most one, the
state block rewrites per the table — each over a constant number of bits per
machine, hence a constant-size CNF per position by the chapter-2 CNF
universality (`Complexity.exists_cnf_boolFun`); summing over `O(s + n)`
positions gives the polynomial (indeed linear, but only the polynomial is
claimed) size. Fill obligations: the codec definition and its injectivity;
the per-position check enumeration; the size ledger; the final eval-iff-step
equivalence. -/
theorem exists_adjacency_codec_cnf (M : Turing.FinTM Bool) :
    ∃ C : ℕ, 0 < C ∧ ∀ (n s : ℕ),
      ∃ (code : (x : List Bool) → Cfg M.k Bool M.State x → List Bool)
        (φ : CNF ℕ),
        (∀ (x : List Bool) (c : Cfg M.k Bool M.State x),
          (code x c).length = C * (s + n + 1)) ∧
        (∀ (x : List Bool), x.length = n → ∀ c d : Cfg M.k Bool M.State x,
          (∀ i, |c.workTapePos i| ≤ (s : ℤ)) →
          (∀ i, |d.workTapePos i| ≤ (s : ℤ)) →
          (∀ i (z : ℤ), (s : ℤ) < |z| → c.workTapes i z = none) →
          (∀ i (z : ℤ), (s : ℤ) < |z| → d.workTapes i z = none) →
          (code x c = code x d → c = d) ∧
          (φ.eval (fun v =>
              ((code x c ++ code x d).getD v false)) = true ↔
            M.tm.step c = d)) ∧
        φ.numVars ≤ 2 * (C * (s + n + 1)) ∧
        (φ.map List.length).sum ≤ C * (s + n + 1) ^ C := by
  sorry

/-- **The language `TQBF`** [AB09, §4.2]: binary strings whose decoded
quantified formula is true. The decoding fallback is the true closed formula,
so non-well-formed strings are members — the `SAT`-polarity convention of
`Complexity.QBF.decode`. -/
def TQBF : Language Bool :=
  {x | (QBF.decode x).truth}

/-- **`TQBF ∈ PSPACE`** ([AB09, Theorem 4.13, membership half]; spec, fill
pending): truth of a quantified formula is decidable in polynomial space.

**Proof sketch.** The recursive evaluator `A` of [AB09]: peel the first
quantifier, evaluate both restrictions, combine by the quantifier — realized
iteratively with a partial-assignment word of one trit per prefix variable
(the book's footnote: the linear-space global-array variant) walked
depth-first by the loop combinator; the base case evaluates the CNF matrix
under the assembled assignment by one scan per clause. Space: the assignment
word (linear), the matrix cursor (linear), the recursion is depth-first on
the word in place — `O(n)` cells, inside `SPACE (n + 1) ⊆ PSPACE`. Fill
obligations, named: the depth-first assignment walker (a §12 loop/catalog
consumer), the CNF evaluator machine (one-pass per clause over the decoded
matrix), the parser reuse (`Complexity.QBF.decode` realized by the chapter-2
parser machinery), and the `DecidesInSpace` packaging. -/
theorem TQBF_mem_PSPACE : TQBF ∈ PSPACE := by
  sorry

/-- **`TQBF` is `PSPACE`-hard** ([AB09, Theorem 4.13, hardness half]; spec,
fill pending — **the phase-P4.3 fill summit**, the `ψᵢ` emitter).

**Proof sketch.** Let `L ∈ PSPACE`, decided by `M` in space `c₀ · (n^c + 1)`.
On input `x` (length `n`, space budget `s := c₀·(n^c + 1)`), the reduction
emits a quantified formula asserting "some accepting configuration is
reachable from the initial one within `2^m` steps", `m := ⌈log₂⌉` of the
configuration count (`O(s + n)` by the codec of
`Complexity.exists_adjacency_codec_cnf`): the midpoint recursion
`ψᵢ(C, C') = ∃ C'' ∀ D₁ D₂ ((D₁,D₂) = (C,C'') ∨ (D₁,D₂) = (C'',C')) → ψᵢ₋₁(D₁,D₂)`
([AB09]'s succinct form, with the `∀`-trick keeping one copy of `ψᵢ₋₁`),
unfolded `m` times down to `ψ₀ :=` the adjacency CNF `φ` of the packaged
claim — all equality/disjunction scaffolding converted to CNF clauses via the
chapter-2 universality, with fresh auxiliary variables per level (the Tseitin
step the CH34-Q5 decision pays here). Size: `O(m)` levels of `O(s + n)`-bit
blocks plus one `φ`, polynomial; truth iff `M` accepts `x` iff `x ∈ L`
(the graph dictionary `Turing.NDTM.reflTransGen_cfgStep_iff` through
`Turing.MultiTapeTM.toNDTM`, with the halting normalization absorbed into
the accepting-configuration predicate — erase-work-tapes normalization per
[AB09], the received `cleanTM` precedent). The emitting machine is a
chapter-2-style streaming emitter (`CookLevin/Hardness.lean` discipline, the
six-stage output-silence contract; §12 catalog routines); **continuation
budget certain**. Fill obligations, named: the level emitter and its
serialization-length ledger; the variable-indexing scheme (level-blocked,
unary-serialized per the CNF grammar); the truth-preservation induction
`ψᵢ true ↔ reachability within 2^i`; the final assembly through
`Complexity.QBF.decode_encode`. -/
theorem TQBF_PSPACEHard : PSPACEHard TQBF := by
  sorry

/-- **The Stockmeyer-Meyer theorem**: `TQBF` is `PSPACE`-complete.
[AB09, Theorem 4.13]

**Proof sketch.** `Complexity.TQBF_mem_PSPACE` with
`Complexity.TQBF_PSPACEHard`. -/
theorem TQBF_PSPACEComplete : PSPACEComplete TQBF := by
  sorry

end Complexity
