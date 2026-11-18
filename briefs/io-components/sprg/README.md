# io-sprg: dispatch pack for the structured-seed PRG job ([JLS26, §2–§4, Theorem 4.1]), Phase A

One end-to-end Codex job in a local checkout on Seyoon's Mac (campaign `IOComponentsPlan.md`):
statements and proofs in one run, a **statements gate** on its first push (checkpoint 0, M0) and a
**proofs gate** on the final. Unit `io-sprg`, branch `fill/io-sprg`, delivery to
`inbox/fills/io-sprg/` on `exchange/pass-shelat-ch5-8`.

**Current revision: r2 (Phase A).** r2 applies Seyoon's rulings of 2026-11-18 made after r1 (records
`ae60dd3a`): the decision-log rows *sPRG rulings*, *Efficiency rulings*, *Strategy and uniformity*,
*`Foundations/Subexponential.lean` written*, *Sampler-bridge rulings* and the RAM-bridge rows. The r1
files stay for the record; the r2 prompt supersedes `dispatch-prompt.md` and the r2 sweep supersedes
`duplication-sweep.md`; `design-r1.md` is still read for the sections `design-r2.md` keeps.

| File | What it is |
|---|---|
| `design-r2.md` | **current** design note: what changed (top), settled points S1–S12 (§0), source map (§1), layout and size (§2), conventions C1–C14 (§3), statement shapes: p as an input, reductions as functions and realisation, the core inequality and corollaries, efficiency targets (§4), milestones M0–M6 (§5), risks, deviations, **Phase B outlook (§9)**, settled and **open questions (§10)** |
| `duplication-sweep-r2.md` | **current** must-reuse list (MR), may-reuse, nearest relatives and do-not-use, with file:line at `cbce64d1`; the Foundations/Subexponential API is MR; machine-building rows in a Phase B appendix |
| `dispatch-prompt-r2.md` | **current** prompt Seyoon pastes into Codex, Phase A only, with placeholders `<BASE>`, `<RECORDS>`, `<EXCHANGE>` |
| `design-r1.md` | r1 design (kept; binding only where design-r2 says "unchanged from r1") |
| `duplication-sweep.md`, `dispatch-prompt.md` | r1 (superseded; kept for the record) |

**Phase A in one paragraph.** Honest algorithms and reductions are explicit Lean functions; the
prime is a public input (`PrimeParam κ`: p with primality and width proofs) and every statement
holds for every prime schedule; correctness, Claim 4.1 and Claim 4.2 are proved; the core theorem
`prop41` is an explicit inequality at every κ, for every NUPPT realising the two reduction functions:
`adv_sPRG A κ ≤ 2κ·adv_LPN BL (ℓ κ) + adv_PRG BG (n κ) + 2·errProb κ (π κ)`; the negligible and the
explicit-exponent subexponential corollaries follow (through `SubexpSmall`/`SubexpHard` of #374),
under realisability hypotheses that Phase B discharges. Efficiency is written as uniform
`PolyTimeComputable` targets, not proved; with Q-S11 A the job also proves "targets ⇒ realisers ⇒
∃ NUPPT" through `NUPPT.exists_reparam_pre_post`. No machines, no RAM, no sampler bridge.

**Size.** About 4,600–7,900 Lean lines in ~22 new files (20 modules, 2 facades) (central ≈ 6,000); M0 alone 1,900–2,900.
About r1's total: the machine construction left, the realisation layer, encodings and targets came
in. Every Stage 2 touch on the job's imports is additive or proof-level (design-r1 §2.4).

**Settled** (design-r2 §10.1): Q-S1 A, Q-S2 A refined (p an input, every schedule), Q-S4 A, Q-S5 A,
Q-S8 A; Q-S3 and Q-S6 superseded by the two-phase and uniformity rulings; Q-S7 withdrawn in r1.

**Open questions for Seyoon** (design-r2 §10.2; recommended option first): Q-S9 home of the
realisation predicate (a shared owner file stacked on #374, reused by PHFE; its form to be
reconciled with the PHFE r2 draft's `NUPPT.Realizes`, design-r2 §10.2) · Q-S10 efficiency
statements as named `PolyTimeComputable` targets incl. Q_I generation and the sampler cores ·
Q-S11 Phase A proves "targets ⇒ realisers ⇒ ∃ NUPPT" · Q-S12 the generic sPRG keeps a modulus
schedule, the construction takes `pp` as input.

**Maintainer, before dispatch.**
1. Get Seyoon's answers to Q-S9–Q-S12; write them to `rulings.md` here, together with the settled
   rows (design-r2 §10.1); if any is not the recommended option, edit the prompt items marked
   *(Q-S…)*.
2. If Q-S9 A: write the shared `TCSlib/Cryptography/Asymptotic/Realization.lean` in-house (design-r2
   §4.8, ≈ 80–150 lines), stacked on `foundations/subexp`, and coordinate the PHFE pack r2 to reuse
   it. `<BASE>` is then that head; otherwise `cbce64d1c135c710b7c036968ed9d4f21414aa72` (and the job
   writes the predicate locally).
3. Dispatch timing (row *Strategy and uniformity*): Phase A goes out after the PHFE PDFs and the PHFE
   pack r2, so both jobs run alongside.
4. Stage the source: `outbox/io-components/sources/jls26.pdf` (SHA-256
   `bb357e8d01cc0932899453f3d877b67b58f33253eabf2564854f8f38721e2f3d`) with a `SHA256SUMS`, shared
   with io-phfe (one copy); push the exchange; put that commit in `<EXCHANGE>`.
5. Commit this folder (with `rulings.md`) and a decision-log row in `IOComponentsPlan.md`; put that
   commit in `<RECORDS>`.
6. Put the base in `<BASE>` (`git rev-parse`). If it is not `cbce64d1`, re-check the sweep's line
   numbers there and the Subexponential names (design-r2 item 4 of *What changed*).
7. Check that the host addendum and `lean-slot.sh` at `<EXCHANGE>` still hash to `02a6af16…` and
   `ff64d8d5…`, and that the bb1-sim tools at exchange `2467bc3b…` are reachable.
8. Tell Seyoon the two Codex jobs share the Mac with one Lean slot each (`io-sprg`, `io-phfe`).

**Not yet ready to dispatch: placeholders, the base (Q-S9), the staged source, Seyoon's answers to
Q-S9–Q-S12 and the PHFE pack r2 are pending.**
