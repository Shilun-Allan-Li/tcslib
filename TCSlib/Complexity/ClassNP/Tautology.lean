/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.Formulas.DNF
import TCSlib.Complexity.Formulas.CNFEncoding
import TCSlib.Complexity.ClassNP.CoNP
import TCSlib.Complexity.ClassNP.Reductions
import TCSlib.Complexity.CookLevin.Hardness

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# TAUTOLOGY and coNP-completeness

[AB09, §2.6.1, Example 2.21]: `TAUTOLOGY` — formulas satisfied by every
assignment — is `coNP`-complete. This module defines `coNP`-hardness and
completeness (mirroring the audited `NP` notions), the language `TAUTOLOGY`
over the **DNF fragment**, and states Example 2.21.

## Design and deviations from [AB09]

* **`TAUTOLOGY` is rendered on the DNF fragment, and says so** ([AB09] states
  it for general Boolean formulas): the phase-3 round-1 audit verified both
  that the *CNF*-restricted tautology language is polynomial-time decidable —
  a CNF is a tautology iff every clause contains a complementary pair, so it
  is **not** [AB09]'s language — and that Example 2.21's own reduction
  produces exactly a DNF, the De Morgan dual of the Cook-Levin CNF. The
  fragment rendering therefore carries the example's full mathematical
  content (its hardness *is* Example 2.21's argument), while general Boolean
  formulas remain unformalized, per the audit's do-not-silently-identify
  guidance. Strings are read through the **shared** audited serialization
  (`Std.Sat.CNF.decode`), evaluated dually. **Seeded design question (e) for
  the phase-4 audit.**
* **The fallback flips sides**: the empty formula is a CNF tautology but the
  empty *disjunction* is false, so under the DNF reading non-well-formed
  strings are **not** in `TAUTOLOGY` — each language's malformed branch
  follows its own predicate on the fallback (the phase-3 finding-5
  discipline).
* `Complexity.coNPHard`/`coNPComplete` are new definitions on the audited
  phase-1 notions (`coNP`, `≤ₚ`), stated here rather than in the frozen
  `CoNP.lean`/`Reductions.lean`, per standing practice. **Seeded design
  question (f).**

## Main definitions

* `Complexity.coNPHard`, `Complexity.coNPComplete` — [AB09, §2.6.1]
  (Karp-reduction form).
* `Complexity.TAUTOLOGY` — [AB09, §2.6.1, Example 2.21], DNF fragment.

## Main results

* `Complexity.TAUTOLOGY_mem_coNP` — the falsifying assignment certifies the
  complement. [AB09, §2.6.1]
* `Complexity.TAUTOLOGY_coNPComplete` — [AB09, Example 2.21].

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§2.6.1, Definitions 2.19-2.20 and
  Example 2.21, pp. 55-56.)
-/

namespace Complexity

open Std.Sat (CNF)

/-- **`coNP`-hardness** [AB09, §2.6.1]: every `coNP` language Karp-reduces to
`L` — the mirror of the audited `Complexity.NPHard`. -/
def coNPHard (L : Language Bool) : Prop :=
  ∀ L' ∈ coNP, L' ≤ₚ L

/-- **`coNP`-completeness** [AB09, §2.6.1]: membership in `coNP` together
with `coNP`-hardness. -/
def coNPComplete (L : Language Bool) : Prop :=
  L ∈ coNP ∧ coNPHard L

/-- **The language `TAUTOLOGY`** [AB09, §2.6.1, Example 2.21], on the DNF
fragment: binary strings whose decoded formula — the shared audited
serialization, **read dually** as an OR of ANDs — is satisfied by every
assignment. Under the DNF reading the fallback (the empty formula, an empty
disjunction) is *not* a tautology, so non-well-formed strings lie outside
`TAUTOLOGY` (see the deviations list). -/
def TAUTOLOGY : Language Bool :=
  {x | (CNF.decode x).DNFTautology}

/-- **`TAUTOLOGY ∈ coNP`** [AB09, §2.6.1]: a falsifying assignment certifies
the complement.

**Proof sketch.** By the definition of `Complexity.coNP`, exhibit
`TAUTOLOGYᶜ ∈ NP`: `x ∈ TAUTOLOGYᶜ` iff some assignment falsifies the DNF
reading of `CNF.decode x`. Certificate parameters `(1, 1)` exactly as in
`Complexity.SAT_mem_NP` — a certificate of length `|x| + 1` carries the
assignment on the mentioned variables (`Std.Sat.CNF.numVars_decode_le`
bounds them by `|x|`; the evaluation-congruence bridge transfers to `evalDNF`
by the same mentioned-variable argument, a named obligation mirroring
`Complexity.eval_congr_of_lt_numVars`). The verifier machine reuses the
`SAT_mem_NP` obligations — odd-length split with explicit even rejection,
the shared parsing machine, the assignment walk — with the **dual**
evaluation loop: accept iff **every** term contains an unsatisfied literal,
i.e. evaluate `evalDNF` and answer its negation (an empty term forces
rejection, the empty formula forces acceptance — round-1 audit, finding 2,
correcting the drafted some-term phrasing) — and the buffered verdict. Malformed
strings: the fallback is not a DNF tautology, so they lie in `TAUTOLOGYᶜ`,
and the verifier accepts them with any certificate (`evalDNF` of `[]` is
`false` — consistent on both sides). -/
theorem TAUTOLOGY_mem_coNP : TAUTOLOGY ∈ coNP := by
  sorry

/-- **Example 2.21** [AB09]: `TAUTOLOGY` is `coNP`-complete (DNF fragment).

**Proof sketch.** Membership is `Complexity.TAUTOLOGY_mem_coNP`. Hardness:
let `L ∈ coNP`, so `Lᶜ ∈ NP`, and `Complexity.SAT_NPHard` (Lemma 2.11)
supplies `f` with `z ∈ Lᶜ ↔ f z ∈ SAT`. Set
`g z := Std.Sat.CNF.serialize (Std.Sat.CNF.dual (CNF.decode (f z)))` — parse
the Cook-Levin output, take the De Morgan dual, re-serialize. Then for every
`z`: `z ∈ L` iff `f z ∉ SAT` iff `CNF.decode (f z)` is unsatisfiable iff its
dual is a DNF tautology (`Std.Sat.CNF.dnfTautology_dual_iff`) iff
`g z ∈ TAUTOLOGY` (`Std.Sat.CNF.decode_serialize` re-reads the emitted
string; the decode-dual-serialize round trip is exact on every string since
decoding is total). `Complexity.PolyTimeComputable g`: compose `f`'s machine
(`Complexity.PolyTimeComputable.comp`) with the parse-dual-serialize
transducer — the parsing machine and serializer shared with the Lemma-2.14
transform, the dual being a literal-polarity flip emitted in-stream (the
polarity bit is the last bit of each literal record). Conclude
`Complexity.coNPHard` and assemble `Complexity.coNPComplete`. -/
theorem TAUTOLOGY_coNPComplete : coNPComplete TAUTOLOGY := by
  sorry

end Complexity
