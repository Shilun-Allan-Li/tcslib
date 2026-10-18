# Chapter 2, Phase 2 (nondeterminism) — audit loop resolutions (CLOSED)

Protocol: `workflow.md` §3 / `AroraBarakChapter2Plan.md` §4.
External auditor: cross-vendor LLM per decision log. One round.

## Round 1 (`ch2-phase2-pack.md` → `ch2-phase2-findings.md`, audited at `e1e68ebd`)

**Zero blockers, zero majors, 2 minors, 2 notes — gate condition met on the
first round** (phase 1 took three; the phase-1 lessons — explicit length
formulas, pairing, output isolation, explicit rejection branches — were baked
into this skeleton from the start and survived contact). The round: all 11
definitions blind-restated from comment-stripped source and assessed faithful
(exactly two total action tables, absorption under every choice, correct
initialization, acceptance requiring completed output exactly `[true]`, both
`DecidesInTime` conjuncts over every input); all 14 sorried statements
assessed mathematically sound, with the four compilation directions and the
padding theorem **adversarially reconstructed** — the certificate-shape
inequalities at every degree including zero, unique-split strict increase,
the simulator invariant table (input-window clamping, choice alignment,
state/tape separation, output capture with the live-`[true]` and
`[true,false]` rejections), the guess-phase witness coverage/extraction
correspondence, the budget envelopes with `succ_pow_le` normalization, and
the small-length absorption threshold argument; the six proved lemmas'
proof terms checked at source level; design questions (a)-(f) all answered
in favor of the chosen conventions (output acceptance faithful with a
constant-overhead translation to accepting-state machines in both
directions; totality on nonmembers correct and load-bearing for backward
truncation; lists ≡ streams through any finite horizon; exact-length
declarations correct; the `+ 1` union padding correct and the exponential
union correctly unpadded; the certificate-route Theorem 2.22 valid with the
complete padding interface checked, malformed strings included). Limited
executable corroboration: ~1,700 parameter triples for the shape
inequalities, a 6,561-machine finite model for absorption/monotonicity/
truncation, and the pairing invariant on all short words.

**The minors, both prose (no Lean statement or proof changed):**

| Finding | Resolution (this commit) |
|---|---|
| 1 minor — the Theorem-2.22 verifier sketch estimated `E |x|`'s binary length as "about `log₂ |x'|`", using well-formedness before the verifier checks it (counterexample: `x' = pairEncode x []` at `|x| = 31`, degree 2 — a 1025-bit value on a 64-symbol input) | The sketch in `ClassNP/Nondeterminism.lean` now budgets the evaluation by the **pre-validation uniform bound** `bits(E n) ≤ (n+1)^c + bits(C) + 1` — polynomial in the actual input length since the parsed `x` is a substring of the input, with `C = 0` handled — and states that the logarithmic estimate is available only *after* the padding-length check |
| 2 minor — the exact-vs-bounded "interchangeability" prose in two module docstrings was overbroad: the bounded rewriting of all-branch halting as "every word of length ≤ `t` is halted" is false already at the empty word | Both passages rewritten to the auditor's quantified readings: acceptance has an equivalent bounded existential (pad with `false`-bits); all-branch halting's bounded reading is **prefix-shaped** (every length-`t` word has a halted prefix `w.take r`, `r ≤ t`), and under `HaltsWithin x t` any longer word's run *equals* its length-`t` prefix's run — the whole configuration, which is what the truncation directions use (`ClassNP/NTIME.lean` deviations; `TuringMachine/Nondeterministic.lean` deviations, now cross-referencing the class layer) |

Both sweeps verified **comment-only** by comment-stripped diff against
`e1e68ebd`; all three modules and both facades re-gated clean (fresh oleans,
zero errors, admissions unchanged at 2/4/8).

**Note dispositions:** (3) the compilation/padding obligation tables — the
simulator invariant table, the branch-correspondence contract, and the
padding interface sequence — are to be **inherited verbatim into the phase-2
fill briefs**, and fills may not substitute untimed composition or bare
computability appeals for the timed contracts; (4) the attestation
evidence-separation table is adopted per standing practice (since epoch 4),
and — a bundle-composition catch — **future bundles attach
`scripts/ab_ch1_module_order.txt`**, which this round's auditor correctly
noted was claimed but not supplied.

**Phase-2 audit gate closed** — 11 definitions, 14 sorried statements, and
6 proved lemmas stand audited in one adversarial round. Standing
human-review item: design question 1 (phase 1) remains open, untouched by
this round. Next: the phase-3 skeleton (CNF formulas, `SAT`, `TMSAT`), per
plan §4, carrying its seeded design question (in-house CNF type vs.
`Std.Sat.CNF`; serialization and fallback convention).
