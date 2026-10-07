# Chapter 2, Phase 3 (formulas, SAT, TMSAT) — audit loop resolutions (CLOSED)

Protocol: `workflow.md` §3 / `AroraBarakChapter2Plan.md` §4.
External auditor: cross-vendor LLM per decision log. Two rounds.

## Round 1 (`ch2-phase3-pack.md` → `ch2-phase3-findings.md`, audited at `1a7554d1`)

**2 blockers, 1 major, 2 minors, 3 notes — all accepted.** The blockers shared
the chapter's third Argument A, found exactly where the pack invited stress
(the two drafting-time obligations): `Turing.EffectiveMachineCode` constrains
the canonizer's *computability*, not its *cost*, and a lawful effective
scheme — the base scheme behind a one-bit tag, tagged codes decoding to
one-step machines that emit bits of a diagonal decidable language `A ∉ EXP` —
makes its `TMSAT` decide `A` on trivial instances (certificate length `0`,
deadline `1`). `TMSAT_mem_NP` and `TMSAT_NPComplete` were therefore **false at
their stated generality** (via the audited `NP ⊆ EXP`); the auditor also
refuted the drafted hope of bounding the universal simulator's constant "by
inspection" (it contains `canonizerTime`) and supplied the quantified
sufficient repair. The major: the hardness sketch's unary emissions — the
exact certificate length `Q` is not time-constructible in degenerate cases
and **must never be majorized** (explicit false positive at `C₀ = c₀ = 0`);
a case table and an explicit deadline formula were supplied. Minors: a parity
flip in the membership split rejection; overbroad fallback-independence
prose. Notes: all 16 definitions and the other ten statements confirmed
(~262k executable parser checks on the auditor's side); the `TAUTOLOGY`
deferral independently proven justified; attestation accounting consistent.

**Repairs** (commit `8b09a184` — phase 3's two statement-level repairs):
`TMSAT_mem_NP` and `TMSAT_NPComplete` gained the hypothesis
`(hc : PolyBound c.canonizerTime)` (the auditor's minimal option; no new code
interface; Chapter-1 freeze preserved; `TMSAT` and `TMSAT_NPHard` untouched);
the membership sketch gained the Argument-A rationale, the corrected
even-length rejection, the quantified budget chain `C_α ≤ 3r + 14H + 50`, and
the named **new-public-bridge** fill obligation; the hardness sketch adopted
the exact-value emission cases and the explicit `T' n = D(n+1)^(2er)`; the
`SAT.lean` fallback prose was corrected. Statement drift enumerated: exactly
2 signatures, 0 definitions, one precise import.

## Round 2 (`ch2-phase3-reaudit-pack.md` → `ch2-phase3-reaudit-findings.md`, audited at `8b09a184`)

**Zero blockers, zero majors, 2 minors, 2 notes — gate condition met.** The
resolution table verified row by row; both signature repairs judged
sufficient, with the budget chain independently re-derived from the
`Universal` module's concrete bound definitions (every size inequality traced
to the actual serialization format, not to a complexity assumption) and the
hypothesis shown to defeat the round-1 counterexample; an exhaustive
statement-by-statement argument that **no other phase-3 statement needs the
hypothesis** (`TMSAT_NPHard` hardwires one fixed code string); Derivation B
re-verified the exact-value cases and the deadline algebra with **no
off-by-one** in either `timeConstructible_poly` instantiation (43,680
deadline-parameter checks, plus tuple-split and coefficient-bound sweeps);
the parity and fallback repairs confirmed. The auditor also recorded that
`PolyBound c.canonizerTime` is sufficient-but-not-weakest (inflating a
scheme's *recorded* clock destroys the bound without changing the language) —
a fair characterization the statements do not contradict, since they claim
sufficiency only.

**The minors, both audit-history prose (no Lean change):**

| Finding | Resolution (this commit) |
|---|---|
| 1 minor — "the chapter's first statement-level repairs" overlooks phase 1's round-1 statement repairs (the paired Exercise-2.1 restatement; `HALT_NPHard`'s generalization) | The plan row now reads "**phase 3's two statement-level repairs**" with the correction noted; the shipped round-2 pack is preserved and its introduction's same phrase is acknowledged here as an **erratum** (standing precedent: packs are historical artifacts) |
| 2 minor — "false at every `EffectiveMachineCode`" is a quantifier error (one lawful scheme refutes the universally quantified statement; it does not fail for every scheme) | The plan row now reads "false at their stated generality: the universally quantified statements refuted by one lawful scheme" |

**Note dispositions:** (3) the fill obligation is pinned as the auditor
specifies — a public quantitative bridge for **one simulator chosen before
the code and input**, preserving both the success and timeout clauses of
`timed_universal`; the suggested bridge form
`(3|α| + 14·canonizerTime(|α|) + 50)·(t+1)²` avoids importing `PolyBound`
into Chapter 1 and is recorded for the fill brief, which must not infer a
bound on the existing statement's arbitrary existential witness. (4) the
erratum-evidence guidance is adopted — the reproducibility appendix below
supplies the exact corrected command, script hash, refs, nonempty output
counts, and hashes.

## Reproducibility appendix — the comment-stripper erratum (round-2 finding 4)

The original invocations ran `python3 strip.py <file>` against a script that
reads **stdin**, comparing empty outputs — vacuous. Corrected recipe (the
script `strip.py` is the 12-line nesting-aware stripper, SHA-256
`4e1fa13f19bca8ef09efe40c59d3e1125dc8351f2e2762e0b7430e888622c046`):

```
git show <ref>:<file> | python3 strip.py | shasum -a 256
```

Re-run results (nonempty outputs; line counts of the stripped current
version shown):

| File | Refs compared | Stripped lines | SHA-256 equal |
|---|---|---|---|
| `TuringMachine/Nondeterministic.lean` | `e1e68ebd` vs `487f58cb` | 66 | yes (`8c059dcd…f8a831`) |
| `ClassNP/NTIME.lean` | `e1e68ebd` vs `487f58cb` | 28 | yes (`fbb83155…871a783`) |
| `ClassNP/Nondeterminism.lean` | `e1e68ebd` vs `487f58cb` | 24 | yes (`46fcdff1…920de4`) |
| `ClassNP/SAT.lean` | `1a7554d1` vs `8b09a184` | 20 | yes (`4804580b…80ad30`) |
| `ClassNP/TMSAT.lean` | `1a7554d1` vs `8b09a184` | — | no — exactly the attested drift: `+import TCSlib.Complexity.ClassNP.PolyTime` and the two signatures gaining `(hc : PolyBound c.canonizerTime)` (diff exit 1, three hunks, nothing else) |

**Phase-3 audit gate closed** — 16 definitions and 12 sorried statements
(two of them repaired at statement level under audit) stand audited through
two adversarial rounds. Standing human-review item: design question 1
(phase 1) remains open, untouched. Next: the phase-4 skeleton (Cook-Levin:
the snapshot/tableau layer, Lemma 2.11, Theorem 2.10, and the DNF dual layer
with `TAUTOLOGY` + Example 2.21, presented as a fragment per the round-1
guidance), per plan §4.
