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
* **Claim 4.4(2) at polynomial size, over a packaged quotient codec.** The
  statement supplies, for each machine and each `(n, s)`: a configuration
  bit-codec of fixed length linear in `s + n`, **factoring through the input
  and the P4.2 vertex quotient** `Turing.NDTM.coreSum` — full configurations
  are *not* injectively codable at fixed length, the output tape being
  unbounded (round-1 blocker, finding 1) — together with **three** CNFs over
  the code bits: a validity predicate characterizing exactly the codec image
  (unguarded midpoint quantification admits paths through junk codes —
  round-1 finding 3), the adjacency test (true on same-input windowed pairs
  iff the step descends to the vertex quotient; false across distinct
  inputs), and the acceptance test (halted state with `accept` summary).
  Declared deviations from the book's Claim 4.4(2), each argued harmless to
  Theorem 4.13: (i) the codec length is `O(s + n)` rather than `O(s)` — the
  code carries the **input content** and a one-hot input-position track, so
  every check is *local* and the formulas are input-independent (Cook-Levin's
  marker discipline; round-1 finding 7); (ii) the CNF sizes are bounded
  through their **serialized lengths** — polynomial, not linear; a
  literal-occurrence count alone misses empty clauses (round-1 finding 8);
  (iii) adjacency compares `coreSum (step c)` with `coreSum d`, so halted
  vertices are self-adjacent and live ones are not — the ψ-recursion's base
  case supplies `a = b` separately (round-1 finding 6). **The package is
  existence, not an algorithm** (round-1 major 2): the uniform
  polynomial-time emitter of the three formulas is a private, named fill
  obligation of `TQBF`'s hardness proof, never a claim of this statement.
  Sole consumer unchanged; D6-style promotion recorded for a second consumer
  (the phase-P4.4 `PATH` encoding remains the candidate).
* **The facade discipline**: `ClassPSPACE.lean` is this phase's own new
  facade; nothing frozen is touched.

## Main definitions

* `Complexity.PSPACEHard`, `Complexity.PSPACEComplete` — [AB09, Definition 4.9].
* `Complexity.TQBF` — the true quantified Boolean formulas, over
  `Complexity.QBF.decode`. [AB09, §4.2, before Theorem 4.13]

## Main results (all sorried; phase-P4.3 statements)

* `Complexity.PSPACE_eq_P_of_pspaceComplete_mem_P` — a `PSPACE`-complete
  language in `P` collapses `PSPACE` to `P`. [AB09, §4.2, after Definition 4.9]
* `Complexity.exists_adjacency_codec_cnf` — Claim 4.4(2), packaged quotient form.
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

namespace Turing

/-- A configuration lies **in the radius-`s` window** when every work head
sits within `[-s, s]` and every work cell outside `[-s, s]` is blank — the
side condition under which the packaged codec of
`Complexity.exists_adjacency_codec_cnf` is faithful. (The input head needs no
clause: its type bounds it.) -/
def Cfg.InWindow {k : ℕ} {Symbol State : Type} {x : List Symbol} (s : ℕ)
    (c : Cfg k Symbol State x) : Prop :=
  (∀ i, |c.workTapePos i| ≤ (s : ℤ)) ∧
  ∀ (i : Fin k) (z : ℤ), (s : ℤ) < |z| → c.workTapes i z = none

end Turing

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

/-- **Claim 4.4(2), packaged quotient form** (spec, fill pending — phase
P4.3 round 2; see the module docstring's declared deviations): for every
machine there is a constant `C` such that for all `(n, s)` there are a
configuration bit-codec — fixed length `C · (s + n + 1)`, injective **down to
the input and the vertex quotient** `Turing.NDTM.coreSum` on windowed
configurations — and three CNFs: `φv` characterizing exactly the codec image
among the length-matching strings, `φa` deciding adjacency (the step, read on
the vertex quotient) on same-input windowed pairs and rejecting cross-input
pairs, and `φacc` deciding acceptance (halted state, `accept` summary); all
three with `numVars` inside the code width and serialized lengths bounded by
`C · (s + n + 1) ^ C`.

**Proof sketch.** The codec is the marker discipline of the Cook-Levin
tableau row (`TCSlib.Complexity.CookLevin` precedents), now carrying the
input: an input-content track of `n` bits, a one-hot input-position track of
length `n + 2`, a one-hot state block (halt included), per work tape a window
track of `2s + 1` cells — three-valued symbol plus a head-marker bit — and a
two-bit summary block; total length linear in `s + n` with the machine's
constants in `C`, padded to the exact `C · (s + n + 1)`. Injectivity to
`(x, coreSum)` mirrors `Turing.MultiTapeTM.ConfigCount.coreCode_inj` on the
window tracks plus the content track; the output enters only through the
summary block (full-output injectivity is impossible and not claimed —
round-1 finding 1). `φv` conjoins per-track well-formedness (one-hot blocks,
trit ranges, canonical padding); `φacc` reads the halt pattern and the
summary block; `φa` conjoins content-track equality, locality of unmarked
window cells, the marked-cell and neighbor updates by the transition table —
the scanned input bit read from the content track under the position
marker — the one-hot shifts by at most one, the state rewrite, and the
summary update (`Turing.outSummary`'s append table): each check spans a
constant number of bits per machine, a constant-size CNF per position by the
chapter-2 universality (`Complexity.exists_cnf_boolFun`, applied per
**gate**, never per row — a whole-row truth table is exponential); summing
over `O(s + n)` positions bounds clause count, `numVars`, and the serialized
lengths polynomially (the chapter-2 grammar's serialization-length equation —
clause count enters it explicitly, round-1 finding 8). Fill obligations,
named: the codec definition with exact-length padding; the two injectivity
lemmas; the validity characterization in both directions; the per-position
check enumeration; the three serialized-size ledgers; the
step-iff-adjacency equivalence through `Turing.NDTM.coreSum_stepWith`. -/
theorem exists_adjacency_codec_cnf (M : Turing.FinTM Bool) :
    ∃ C : ℕ, 0 < C ∧ ∀ (n s : ℕ),
      ∃ (code : (x : List Bool) → Cfg M.k Bool M.State x → List Bool)
        (φv φa φacc : CNF ℕ),
        (∀ (x : List Bool) (c : Cfg M.k Bool M.State x),
          (code x c).length = C * (s + n + 1)) ∧
        (∀ (x x' : List Bool), x.length = n → x'.length = n →
          ∀ (c : Cfg M.k Bool M.State x) (c' : Cfg M.k Bool M.State x'),
            c.InWindow s → c'.InWindow s → code x c = code x' c' → x = x') ∧
        (∀ (x : List Bool), x.length = n →
          ∀ c d : Cfg M.k Bool M.State x, c.InWindow s → d.InWindow s →
            code x c = code x d → NDTM.coreSum c = NDTM.coreSum d) ∧
        (∀ w : List Bool, w.length = C * (s + n + 1) →
          (φv.eval (fun v => w.getD v false) = true ↔
            ∃ (x : List Bool), x.length = n ∧
              ∃ c : Cfg M.k Bool M.State x, c.InWindow s ∧ w = code x c)) ∧
        (∀ (x : List Bool), x.length = n →
          ∀ c d : Cfg M.k Bool M.State x, c.InWindow s → d.InWindow s →
            (φa.eval (fun v => (code x c ++ code x d).getD v false) = true ↔
              NDTM.coreSum (M.tm.step c) = NDTM.coreSum d)) ∧
        (∀ (x x' : List Bool), x.length = n → x'.length = n → x ≠ x' →
          ∀ (c : Cfg M.k Bool M.State x) (c' : Cfg M.k Bool M.State x'),
            c.InWindow s → c'.InWindow s →
            φa.eval (fun v => (code x c ++ code x' c').getD v false) = false) ∧
        (∀ (x : List Bool), x.length = n →
          ∀ c : Cfg M.k Bool M.State x, c.InWindow s →
            (φacc.eval (fun v => (code x c).getD v false) = true ↔
              (c.state = none ∧ outSummary c.output = OutSummary.accept))) ∧
        φv.numVars ≤ C * (s + n + 1) ∧
        φacc.numVars ≤ C * (s + n + 1) ∧
        φa.numVars ≤ 2 * (C * (s + n + 1)) ∧
        (CNF.serialize φv).length ≤ C * (s + n + 1) ^ C ∧
        (CNF.serialize φa).length ≤ C * (s + n + 1) ^ C ∧
        (CNF.serialize φacc).length ≤ C * (s + n + 1) ^ C := by
  sorry

/-- **The language `TQBF`** [AB09, §4.2]: binary strings whose decoded
quantified formula is true. The decoding fallback is the true closed formula,
so non-well-formed strings are members — the `SAT`-polarity convention of
`Complexity.QBF.decode`. -/
def TQBF : Language Bool :=
  {x | (QBF.decode x).truth}

/-- **`TQBF ∈ PSPACE`** ([AB09, Theorem 4.13, membership half]; spec, fill
pending): truth of a quantified formula is decidable in polynomial space.

**Proof sketch.** Validate the **entire** encoding before any matrix
verdict: trailing garbage makes the total decoder select the true fallback,
so a scanned prefix that "looks unsatisfiable" must not short-circuit
(round-1 answer 5). Then the recursive evaluator `A` of [AB09]: peel the
first quantifier, evaluate both restrictions, combine by the quantifier —
realized iteratively with a partial-assignment word of one trit per prefix
variable (the book's footnote: the linear-space global-array variant) walked
depth-first by the loop combinator, with no per-level formula copies; the
base case evaluates the CNF matrix under the assembled assignment by one
scan per clause, re-reading prefix bits and matrix bytes from the input. Space: the assignment
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
On input `x` (length `n`, window radius `s := c₀·(n^c + 1)`), the reduction
emits a quantified formula asserting "some accepting vertex is reachable
from the initial vertex within `2^ℓ` steps" over the packaged carrier of
`Complexity.exists_adjacency_codec_cnf`: vertices are the
`ℓ := C·(s + n + 1)`-bit codes of input-carrying windowed quotient
configurations, with `Valid := φv`, `Next := φa`, `Accept := φacc`. The
midpoint recursion is
`ψ₀(a, b) := Valid a ∧ Valid b ∧ (a = b ∨ Next (a, b))` — the base includes
length-zero paths, since live vertices are not `Next`-reflexive (round-1
finding 6) — and
`ψᵢ₊₁(a, b) := ∃ z (Valid z ∧ ∀ u v, ((u,v) = (a,z) ∨ (u,v) = (z,b)) → ψᵢ(u,v))`
([AB09]'s succinct `∀`-trick keeping one copy of `ψᵢ`, with the midpoint
**guarded by `Valid`** — unguarded quantification admits paths through junk
codes, round-1 finding 3), unfolded to depth `ℓ` (at most `2^ℓ` codes, so a
shortest path fits), against the emitted initial-vertex code and an
existentially quantified `Accept` target (no unique accepting configuration
is needed). Prenex first, then Tseitin: the gate variables of the CNF
conversion are existentially quantified **after** the original prefix — gate
values must not be fixed before universal variables they depend on (round-1
answer 5) — with constant-arity gate constraints via the chapter-2
universality (`Complexity.exists_cnf_boolFun` per gate, never per level).
Size: `O(ℓ)` scaffolding per level over `ℓ` levels plus the three packaged
CNFs — polynomial by their serialized-length clauses. Truth iff reachability
iff `M` accepts `x`: the quotient dictionary
(`Turing.NDTM.reflTransGen_cfgStep_iff` through `Turing.MultiTapeTM.toNDTM`)
with path lifting via `Turing.NDTM.coreSum_stepWith`, the space bound
keeping every genuine run inside the window. **The packaged existential
supplies no algorithm** (round-1 major 2): the uniform emitter — the
polynomial-time construction and serialization of `φv`/`φa`/`φacc`, the
initial-vertex code, the per-level scaffolding with its level-blocked
variable indexing, and the final assembly through
`Complexity.QBF.decode_encode` — is a set of **private, named fill
obligations of this proof**, in the chapter-2 streaming-emitter discipline
(`CookLevin/Hardness.lean`, the six-stage output-silence contract; §12
catalog routines); **continuation budget certain**. Fill obligations, named:
the three-CNF emitter family and its serialization-length ledger; the
initial-code computation; the level-blocked indexing scheme (unary-serialized
per the CNF grammar); the truth-preservation induction
`ψᵢ ↔ reachability within 2^i`, both directions of the guarded recursion;
the Tseitin-after-prefix equivalence; the final assembly through
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
