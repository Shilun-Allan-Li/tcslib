# GSW 6b fills and EF-R1: rulings in force

Seyoon, 2026-11-18/19. Every question in `README.md` §Questions is answered; all as recommended (A).
These take precedence over the other files in this folder where they differ.

| Question | Ruling |
|---|---|
| **Q-6BF-1** EF-R1's placement | **A.** Its own unit `ef-r1-gsw-reductions`, in new files. `GSW/Asymptotic.lean` does not change; U18-U19 fill A1/A3 from `heff` in parallel. |
| **Q-6BF-2** Grouping | **A.** Five GSW units: U12, U13, U14-U16 (shared gate step), U15-U17 (same transport technique), U18-U19 (shared family bound). |
| **Q-6BF-3** Public helpers | **A.** Exactly two public glue lemmas are allowed: `encrypts_bootGate` (`Bootstrap.lean`) and `Parameters.ofFamily_columns_le` (`PolyRatio.lean`). Pure insertions, decls2 ADDED = 1 each, each sealed with its own controls. Any other new public declaration is E-SCOPE. |
| **Q-6BF-4** EF-R1's base | **A.** The deterministic local merge `tools/mkbase-ef-r1.sh` of B6 with EF-R2-R3's maintainer-accepted head (accepted 2026-11-18, EF-R23-R1 A: landing edit LE-coins), plus U18-U19's accepted final if available. EF-R1 lands stacked. |
| **Q-6BF-5** EF-R1's names | **A.** `reductionEfficient`, `leveledReductionEfficient`, `indCPA_of_dlwe`, `leveledINDCPA_of_dlwe`; the string maps `encryptStr`, `spliceStr` in `GSW/EncryptPoly.lean`. |
| **Q-6BF-6** EF-R1's coins | **A.** All of each reduction's own coins are fixed by averaging into advice; `D'`'s coins are `D`'s; no sampler anywhere. |
| **Q-6BF-7** `exists_fixCoins` | **A.** Import `ZeroKnowledge/CommitmentLemmas.lean` read-only now; a promotion request moves `exists_abs_uexp_le` and `exists_fixCoins` to `Foundations/` after Stage 2's J6. |

## Related rulings recorded elsewhere

- **U12, U13** were dispatched (pin `bbc930b3`) before this file existed. Q-U12-1/Q-U13-1 (A): no ruling applied to
  them; both accepted with no landing edit; landed as PR #392 (Gate 53). Q-U12-3 (A): `IsFiveCycle.apply_ne` stays
  private. Gate 46 F2 is discharged as planned by U13's proof of `decDepth_le`.
- **Standing rules 17 and 18** (handoff §2) apply to every dispatch from this folder: Codex audits run in the cloud
  and do not replay; every message for Seyoon to paste is complete.
- **Lean replay** of each delivery is the maintainer's; a worker's own build is its evidence, not the replay.
