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
| `rulings.md` | **every ruling in force** for this job (decision-log rows of 2026-11-18, rule 15, Q-E1 (A), the source rule, the base); it takes precedence over every other file here |
| `design-r3.md` | **current** delta design note: what changed; **rule 15** (§1: raw bundles vs primitives, efficiency fields, `SamplesEfficiently`, targets T5–T6, assembly, renamed results); the shared realisation API (§2, must-reuse); Phase B outlook with #378's real names (§3); layout and size (§4); statements-gate order (§5); Dv16–Dv18 (§6); questions (§7: Q-E1, since ruled (A), `rulings.md`) |
| `duplication-sweep-r3.md` | **current** delta sweep: amended r2 rows; the shared realisation API (§R, MR); the sampler bridge at the base (§S: `UniformSampler` type MR for the efficiency fields; the rest X/B; `SamplesEfficiently` MR from `CoinSampling/Contract.lean`, present) |
| `dispatch-prompt-r3.md` | **current** prompt Seyoon pastes into Codex, Phase A only; base filled (`iO/phase-a-base` at `5ed465f62e4ae0f93ded1a1ba49e807591b589eb`); one placeholder left, `dbea2807532392781304e004715f3b0190025f5e`; the `[Q-E1]` items take the must-reuse arm |
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

**Q-E1 ruled (A)** (with the PHFE pack's Q-E1): `SamplesEfficiently` lives in the shared
in-house `TCSlib/Cryptography/CoinSampling/Contract.lean` (`foundations/coin-contract`
`8e01b720`), which is at the base; must-reuse, with `DrawSamplable`, `CoreComputable`, their
readers and closure (`../contract/REPORT.md`). Disclosed limits: no product-of-draws sampler
(Phase B), and the unused `Fintype` binder of design-r3 §1.2 was dropped.

**Base.** `iO/phase-a-base` at `5ed465f62e4ae0f93ded1a1ba49e807591b589eb`: #374
`foundations/subexp` (`cbce64d1`), #378 `foundations/coin-sampling` (`51dc7672`),
`foundations/coin-contract` (`8e01b720`) and #380 `foundations/realization` (`cdc0934f`);
shared with the PHFE pack.

**Sources.** No PDF is committed or pushed anywhere (pairing ruling Q12 (A); the ePrint PDFs are
not ours to redistribute). Seyoon gives Codex a local folder with `jls26.pdf` (SHA-256
`bb357e8d01cc0932899453f3d877b67b58f33253eabf2564854f8f38721e2f3d`) when he dispatches; nothing
is staged on the exchange. Delivery is unchanged: `inbox/fills/io-sprg/` on the exchange.

**Maintainer, before dispatch.**
1. Done: Q-E1 (A); `CoinSampling/Contract.lean` written and stacked; the base built and pushed
   (`iO/phase-a-base`, `../contract/REPORT.md`); `rulings.md` written; the base filled in the
   prompt; the source rule applied (no staging).
2. Commit this folder (with `rulings.md`) and a decision-log row in `IOComponentsPlan.md`; put
   that commit in `dbea2807532392781304e004715f3b0190025f5e` (`git rev-parse`) and push the records.
3. Check that `outbox/fills/codex-host-2026-11-15/host-addendum.md` and `lean-slot.sh` at the
   exchange commit the prompt pins (`bc9d982b83cb35ea351e2fb373752e8688945b1c`) hash to
   `02a6af16…` and `ff64d8d5…` (they did on 2026-11-18), and that the bb1-sim tools at exchange
   `2467bc3b…` are reachable (they were).
4. Seyoon prepares the local source folder (here: `jls26.pdf`; with the PHFE PDFs if he uses one
   folder for both jobs) and names it when he dispatches.
5. Tell Seyoon the two Codex jobs share the Mac with one Lean slot each (`io-sprg`, `io-phfe`;
   cap 3 in all).

**Not yet ready to dispatch.** Pending: the records commit and push, then `dbea2807532392781304e004715f3b0190025f5e`.
