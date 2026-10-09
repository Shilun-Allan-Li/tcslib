/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import Mathlib.Logic.Relation
import TCSlib.Complexity.SpaceComplexity.Logspace.Reductions
import TCSlib.Complexity.SpaceComplexity.ConfigGraph

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

## Main results (all sorried; phase-P4.4 statements)

* `Complexity.PATH_mem_NL` — the nondeterministic walk. [AB09, Example 4.7,
  the `PATH ∈ NL` paragraph]
* `Complexity.PATH_NLComplete` — [AB09, Theorem 4.18].

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

/-- **`PATH ∈ NL`** ([AB09, §4.1.2, the nondeterministic walk]; spec, fill
pending — phase P4.4): guess the path vertex by vertex, keeping only the
current vertex and a step counter.

**Proof sketch.** A `Turing.FinNDTM` taking its choice bits as the binary
digits of the successive vertices (the certificate reading): maintain the
current vertex (a `logSpace n`-bit register) and a step counter to `n`;
per round, guess the next vertex, verify the matrix bit `A u v` by indexing
the row-major track on the input (position arithmetic `u·n + v`, binary
counters against the unary prefix — the received `Machines/Parse*`
comparison toolkit on inputs `⟨1ⁿ, w⟩` is the engine), reject on a `false`
edge bit or malformed shape, accept on reaching `t` within `n` steps.
All-branch halting at the uniform budget; branch space: two registers and
the counter, `O(logSpace n)` cells — inside `NSPACE logSpace = NL`. Fill
obligations, named: the guess-register discipline (the nondeterministic
sibling of the received deterministic `LogProg` register walks — the ARM
extension the plan defers to the §12 gate and the colleague sync; this fill
is its first named customer), the matrix-indexing decider, the endpoint and
shape validation, the `DecidesInSpace` packaging with the all-branch
budget. -/
theorem PATH_mem_NL : PATH ∈ NL := by
  sorry

/-- **`PATH` is `NL`-complete** ([AB09, Theorem 4.18]; spec, fill pending —
phase P4.4): membership is `Complexity.PATH_mem_NL`; hardness maps a
language's machine-and-input to its configuration graph.

**Proof sketch.** For `B ∈ NL` decided by `N` in space `c₀ · logSpace`, the
reduction sends `x` to `⟨G_{N,x}, C_start, C_accept⟩`: vertices are the
coded configuration-graph vertices of
`Turing.NDTM.coreSum`/`Turing.FinNDTM.configBound` at window
`c₀ · logSpace |x|` — polynomially many, each code logarithmically
indexable — with the accepting side normalized to a single target vertex
(the erase-and-park normalization — **assigned for discharge here**, not
already closed: the received `Machines/Clean` cleanTM is the model only, and
the P0 record notes it does not reset the input head, so the normalization
must also park the input head and re-prove acceptance, all-branch halting,
and the space constant for the normalized machine; round-1 audit, note 4). `x ∈ B` iff the target is reachable
(`Turing.FinNDTM.DecidesInSpace.mem_iff_acceptsWithin_configBound` with
`Turing.NDTM.reflTransGen_cfgStep_iff`, phase P4.2). The reduction is
**implicitly logspace computable**: a bit query `⟨x, i⟩` locates `i` inside
the layered encoding by binary arithmetic (unary count, matrix block,
endpoint blocks) and, for a matrix bit, decides adjacency of the two decoded
vertex codes by one local transition-table check — a fixed family of
`LOGSPACE` deciders assembled by the received `arm_decides`; the length
query is pure arithmetic in `i`. Fill obligations, named: the vertex
numbering and its index arithmetic; the adjacency decider; the accepting
normalization; the two `indexLang` memberships; and the final
`Complexity.NLComplete` packaging over `≤ₗ`. -/
theorem PATH_NLComplete : NLComplete PATH := by
  sorry

end Complexity
