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
- *Shared `Asymptotic/Realization.lean` written* (`foundations/realization` `cdc0934f`);
- **standing rule 15**: *Efficiency is mandatory* and *Efficiency baked into definitions*.

These are read at records `32a40963` (rule 15).
- **Rule 15 is the largest change.** Every primitive the job defines (`SPRG`, `BoolPRG`,
  `LPNFamily`) carries its honest algorithms' efficiency as structure fields:
  - deterministic maps as uniform `PolyTimeComputable` with the modulus on the input;
  - samplers as an exact-law core plus #378's `UniformSampler`.
- The construction is the raw bundle `jlsSPRG_raw`, proved correct and secure.
- The primitive `jlsSPRG P π hT : SPRG` is assembled from it and the efficiency targets T1–T6.
- The statements gate checks "definitions carry efficiency" right after source fidelity
  (design-r3 §§ 1, 5). r3 is a delta: `design-r3.md` and `duplication-sweep-r3.md`
amend the r2 files, which stay binding where not changed. `dispatch-prompt-r3.md` is complete and
supersedes the r2 and r1 prompts.

| File | What it is |
|---|---|
| `design-r3.md` | **current** delta design note: what changed; **rule 15** (§1: raw bundles vs primitives, efficiency fields, `SamplesEfficiently`, targets T5–T6, assembly, renamed results); the shared realisation API (§2, must-reuse); Phase B outlook with #378's real names (§3); layout and size (§4); statements-gate order (§5); Dv16–Dv18 (§6); questions (§7: Q-E1 open) |
| `duplication-sweep-r3.md` | **current** delta sweep: amended r2 rows; the shared realisation API (§R, MR); the sampler bridge at `<BASE>` (§S: `UniformSampler` type MR for the efficiency fields; the rest X/B) |
| `dispatch-prompt-r3.md` | **current** prompt Seyoon pastes into Codex, Phase A only, with placeholders `<BASE>`, `<RECORDS>`, `<EXCHANGE>` only; one item marked `[Q-E1]` |
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
- Efficiency is baked into the definitions (rule 15). The construction is the raw bundle
  `jlsSPRG_raw`; the primitive `jlsSPRG P π hT : SPRG` is assembled from the efficiency targets
  T1–T6 (uniform `PolyTimeComputable` forms and `UniformSampler`s), which are written, not
  proved.
- The job proves "targets ⇒ realisers ⇒ ∃ NUPPT" through the shared
  `exists_realizesOn_of_preTarget`, and "targets ⇒ an efficient, secure sPRG exists"
  (`exists_sprg_of_targets`).
- No machines, no RAM, no samplers built: of #378 only the type `UniformSampler` is used.

**Size.** About 4,950–8,450 Lean lines in 21–22 new files (19–20 modules, 2 facades), central
≈ 6,500. M0 alone is 2,100–3,200. Compared with r2 (4,600–7,900):
- the local `Realization.lean` is gone (−0–150);
- rule 15 adds the raw/primitive splits, the efficiency fields, T5–T6 and the assembly
  (+500–900). Every Stage 2 touch on the job's imports is additive or proof-level
(design-r1 §2.4).

**Settled.**
- Q-S1 A, Q-S2 A refined (p an input, every schedule), Q-S4 A, Q-S5 A, Q-S8 A.
- Q-S9 A, Q-S10 A, Q-S11 A, Q-S12 A; rule 15 (design-r3 §7.1).
- Q-S3 and Q-S6 are superseded by the two-phase and uniformity rulings; Q-S7 was withdrawn
  in r1.

**Open question** (design-r3 §7.2; the same as the PHFE pack's Q-E1; rule them together):
- **Q-E1**, where `SamplesEfficiently` (the sampler-efficiency predicate both jobs use) lives:
  - **(A) a shared in-house file `CoinSampling/Contract.lean`, stacked into `<BASE>` before
    dispatch** (recommended);
  - (B) one per job, unified later;
  - (C) inline fields.

**Maintainer, before dispatch.**
1. Get Seyoon's answer to Q-E1. Write `rulings.md` here: Q-S1–Q-S12, rule 15 and Q-E1 with
   the decision-log rows (design-r2 §10.1, design-r3 §7), and the `<BASE>` branch name. If Q-E1
   is (A), write `TCSlib/Cryptography/CoinSampling/Contract.lean` in house (design-r3 §1.2's
   `SamplesEfficiently` with readers, ≈ 60–120 lines, on #378) and stack it into `<BASE>`.
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

**Not yet ready to dispatch.** Pending: Q-E1 (and its file if (A)), the stacked `<BASE>`,
`rulings.md`, the staged source, the placeholders, and the records and exchange pushes.
