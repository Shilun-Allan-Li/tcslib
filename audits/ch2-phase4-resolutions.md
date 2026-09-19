# Chapter 2, Phase 4 (Cook-Levin) — audit loop resolutions (CLOSED)

Protocol: `workflow.md` §3 / `AroraBarakChapter2Plan.md` §4.
External auditor: cross-vendor LLM per decision log. Two rounds.

## Round 1 (`ch2-phase4-pack.md` → `ch2-phase4-findings.md`, audited at `6484ce88`)

**Zero blockers, 1 major, 2 minors, 5 notes — all accepted.** No false
definition or statement anywhere on the summit surface. The round's
certifications: all five locality theorems re-derived (Derivation A — the
cell recurrence with the exhaustive optional-write table, `some none`
erasing to blank, writes on the halting transition, `t = 0`, absorption;
design questions (b)/(c) affirmed); the tableau correctness re-derived end
to end (Derivation B — exact-length normalization with the phase-3
case-split discipline, packing injectivity, constant-arity Claim-2.13
templates under non-injective relabeling, the strong-induction
bitwise-pinning argument, with the **product snapshot encoding**
recommended); **design question (a) resolved affirmatively** (Derivation C —
the no-false-emission acceptance family survives a seven-case adversarial
table, the decider contract invoked exactly where needed); the DNF/TAUTOLOGY
package verified on every string including malformed reduction outputs
(Derivation D; questions (e)/(f) affirmed). **The major**: the
emitting-machine sketch omitted the output-isolation/halt-redirection
contract for its preparatory stages — the `TimeConstructible` machines
answer on the real output tape and the reference simulation emits its
verdict bit, giving the concrete false positive
`[false] ++ serialize φ_x → fallback ∈ SAT` (the phase-1 enumerator lesson
recurring at the emitter); the auditor supplied a six-stage
silent-controller contract table. Minors: an every-term-fails quantifier
slip in the TAUTOLOGY membership prose; two missing precise imports.

**Repairs** (commit `c3579472` — no statement or definition changed; drift
exactly two import lines, established by the corrected stripper recipe):
the `SAT_NPHard` emitter stage rewritten around the **output-silence
contract** with the six-stage table adopted; the product encoding and the
exact serialization-length ledger added; the quantifier phrase corrected;
`ClassNP.TMSAT` and `Robustness.Oblivious` imported.

## Round 2 (`ch2-phase4-reaudit-pack.md` → `ch2-phase4-reaudit-findings.md`, audited at `c3579472`)

**Zero blockers, zero majors, zero minors, 3 notes — gate condition met**,
with nothing to sweep. The resolution table verified row by row; the
six-stage transcription judged **semantically faithful** ("adopted verbatim"
read as substantive adoption — the prose is reformatted and expanded, which
the auditor records without objection) and the emitter obligation list
judged **complete at statement-phase granularity**, re-tested by a
stage-by-stage boundary-check table (capture includes halting-transition
emissions; the virtual reference run's `initCfg` semantics; effects-first
then internal halt; time-`0` and time-`T` recording; strict-earlier/greatest
last visits; the output-prefix invariant across the
preparatory/serialization boundary) and by **re-firing the round-1
counterexample against the repaired contract** — the false-positive
mechanism is closed. The product-encoding passage matches Derivation B
(fields as literal slices; no junk survives; no extra well-formedness
family needed). The length/time ledger independently re-derived: the exact
serializer identity confirmed from the phase-3 definitions, the pinning
family's `n(n-1)/2 + 5n` absorbed via `T ≥ (m+1)^2` (with the neat
observation that the oblivious multiplier satisfies `c ≥ 1` because `c = 0`
would contradict `Turing.FinTM.not_computesInTime_zero`), total
`O_M(T^2) = poly(n)`, and the trajectory/comparison costs charged at
sequential-scan rates with no random-access assumption.

**Note dispositions:** (1) the six-stage contract table **and** the round-2
boundary-check table are inherited verbatim into the eventual emitter fill
brief (epoch E4), whose fills must discharge the native-machine and cost
obligations they name; (2) the **exact** serialization identity is the
fill's length ledger — never charge constant serialized length per pinning
clause — together with the auditor's budget chain (`c ≥ 1`, `T ≥ (m+1)^2`,
the `9/2·(n+1)^2` pinning absorption, `O_M(T^2)` total); (3) the
source-fact/execution-claim separation is retained per standing practice.

**Phase-4 audit gate closed** — 14 definitions and 14 sorried statements
audited through two adversarial rounds; with it, **all four Chapter-2
statement-phase gates are closed**: 59 audited-true admissions
(19 + 14 + 12 + 14) across phases 1-4, every mandatory-core statement of
the chapter on the books. Standing human-review item: design question 1
(phase 1) remains open, untouched. Next, per plan §4: the **fill campaign**
(epochs E1-E5), beginning with the epoch partitioning and briefs.
