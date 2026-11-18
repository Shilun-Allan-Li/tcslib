# io-sprg: dispatch pack for the structured-seed PRG job ([JLS26, §2–§4, Theorem 4.1]), Phase A

One end-to-end Codex job in a local checkout on Seyoon's Mac (campaign `IOComponentsPlan.md`).
- Statements and proofs come in one run.
- A **statements gate** sits on its first push (checkpoint 0, M0) and a **proofs gate** on the
  final.
- Unit `io-sprg`, branch `fill/io-sprg`, delivery to `inbox/fills/io-sprg/` on
  `exchange/pass-shelat-ch5-8`.

**Current revision: r3 (Phase A).** r3 applies:
- the decision-log rows *Phase A rulings, first batch* and *second batch* (Q-S9 A, Q-S10 A,
  Q-S11 A, Q-S12 A);
- *Sampler bridge implemented* (#378);
- *Shared `Asymptotic/Realization.lean` written* (`foundations/realization` `cdc0934f`).

These are read at records `43eacf95`. r3 is a delta: `design-r3.md` and `duplication-sweep-r3.md`
amend the r2 files, which stay binding where not changed. `dispatch-prompt-r3.md` is complete and
supersedes the r2 and r1 prompts.

| File | What it is |
|---|---|
| `design-r3.md` | **current** delta design note: what changed; the shared realisation API with lines (§1, must-reuse); statement changes (§2: none to the statements; the Q-S11 link through `exists_realizesOn_of_preTarget`); layout and size (§3); Phase B outlook with #378's real names (§4); Dv16 (§5); all questions settled (§6) |
| `duplication-sweep-r3.md` | **current** delta sweep: amended r2 rows; the shared realisation API (§R, MR); the sampler bridge at `<BASE>` (§S, X in Phase A, B for the outlook) |
| `dispatch-prompt-r3.md` | **current** prompt Seyoon pastes into Codex, Phase A only, with placeholders `<BASE>`, `<RECORDS>`, `<EXCHANGE>` only |
| `design-r2.md`, `duplication-sweep-r2.md` | r2; **binding** wherever r3 does not amend them |
| `dispatch-prompt-r2.md` | r2 prompt (superseded; kept for the record) |
| `design-r1.md` | r1 design (binding only where design-r2 says "unchanged from r1") |
| `duplication-sweep.md`, `dispatch-prompt.md` | r1 (superseded; kept for the record) |

**Phase A in one paragraph.**
- Honest algorithms and reductions are explicit Lean functions.
- The prime is a public input (`PrimeParam κ`: p with primality and width proofs), and every
  statement holds for every prime schedule.
- Correctness, Claim 4.1 and Claim 4.2 are proved.
- The core theorem `prop41` is an explicit inequality at every κ, for every NUPPT realising the
  two reduction functions:
  `adv_sPRG A κ ≤ 2κ·adv_LPN BL (ℓ κ) + adv_PRG BG (n κ) + 2·errProb κ (π κ)`.
  - Realising is the shared `NUPPT.RealizesOn`, which constrains only encoded challenges and
    coin strings of the layout's length.
- The negligible and the explicit-exponent subexponential corollaries follow (through
  `SubexpSmall`/`SubexpHard` of #374), under realisability hypotheses.
- Efficiency is written as uniform `PolyTimeComputable` targets T1–T4, not proved. The job also
  proves "targets ⇒ realisers ⇒ ∃ NUPPT" through the shared `exists_realizesOn_of_preTarget`.
- No machines, no RAM, no sampler bridge: #378 is in the base for Phase B's outlook only and is
  not imported.

**Size.** About 4,550–7,700 Lean lines in 21 new files (19 modules, 2 facades), central ≈ 5,900.
M0 alone is 1,850–2,900. Compared with r2 (4,600–7,900), the local `Realization.lean` is gone and
the targets link is shorter. Every Stage 2 touch on the job's imports is additive or proof-level
(design-r1 §2.4).

**Settled.**
- Q-S1 A, Q-S2 A refined (p an input, every schedule), Q-S4 A, Q-S5 A, Q-S8 A.
- Q-S9 A, Q-S10 A, Q-S11 A, Q-S12 A (design-r3 §6.1).
- Q-S3 and Q-S6 are superseded by the two-phase and uniformity rulings; Q-S7 was withdrawn
  in r1.

**Open questions:** none.

**Maintainer, before dispatch.**
1. Write `rulings.md` here: Q-S1–Q-S12 with the decision-log rows (design-r2 §10.1, design-r3
   §6.1), and the `<BASE>` branch name.
2. Build `<BASE>`: one branch stacking #374 (`cbce64d1`), `foundations/realization` (`cdc0934f`)
   and #378 (`foundations/coin-sampling`, `51dc7672`). Both of the latter sit directly on
   `cbce64d1` and touch disjoint files except the root facade lines (realization edits
   `Asymptotic.lean`; coin-sampling edits `TCSlib.lean` and `Games.lean`). A ref-free
   `git merge-tree --write-tree` of the two heads merges with no conflict (rc 0, tree
   `20460248…`).
   - Check that it elaborates (`Asymptotic/Realization`, `CoinSampling` facade) with one Lean
     process.
   - Push it, and share it with the PHFE pack (same `<BASE>`).
   - If its tree is not "#374 + the two branches' files", re-check `duplication-sweep-r3.md`'s
     lines there.
3. Stage the source on the exchange at `outbox/io-components/sources/jls26.pdf` (SHA-256
   `bb357e8d01cc0932899453f3d877b67b58f33253eabf2564854f8f38721e2f3d`), with a `SHA256SUMS`.
   - The folder is shared with io-phfe (its PDFs and `agw20.pdf`, `iw14.pdf` go in the same
     folder).
   - Push the exchange, and put that commit in `<EXCHANGE>`.
4. Commit this folder (with `rulings.md`) and a decision-log row in `IOComponentsPlan.md`; put
   that commit in `<RECORDS>`.
5. Put the base in `<BASE>` (`git rev-parse`).
6. Check that `outbox/fills/codex-host-2026-11-15/host-addendum.md` and `lean-slot.sh` at
   `<EXCHANGE>` still hash to `02a6af16…` and `ff64d8d5…` (they did at the exchange tip on
   2026-11-18), and that the bb1-sim tools at exchange `2467bc3b…` are reachable (they were).
7. Tell Seyoon the two Codex jobs share the Mac with one Lean slot each (`io-sprg`, `io-phfe`;
   cap 3 in all).

**Not yet ready to dispatch.** Pending: the stacked `<BASE>`, `rulings.md`, the staged source,
the placeholders, and the records and exchange pushes.
