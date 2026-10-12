# Maintainer fill: `POracle_eq_P_of_mem_P` and `baker_gill_solovay` (proved modulo)

Two chapter-3 targets whose proofs are short derivations from the §12.10 oracle-call layer and
B5's `EXPCOM` identities. Both derivations were already elaborated in the wave-1 statement
gate's probe (`audits/evidence/wave1-statements/S1210StatementsProbe.lean.txt`), which that
gate audited. Following the B1 light half's and B8's precedent, the maintainer transcribed
them; no agent batch was issued (user: "start on the unblocked fronts", 2026-10-11).

| Target | Book | Proof | Proved modulo |
|---|---|---|---|
| `Complexity.POracle_eq_P_of_mem_P` (`ClassOracle/Classes.lean`) | [AB09, Example 3.6(2)] | `⊇` is `P_subset_POracle`; for `⊆`, `FinOracleTM.exists_plain_decider` gives a plain decider within `a·(t + 1)·(t + 1 + C·(t + 1)^d)`, and the private `b1_budget` bounds it by a polynomial of degree `k·(d + 2)`, so `mem_P_of_dtime_le` concludes | W2-S, `Turing.FinOracleTM.exists_plain_simulation` |
| `Complexity.baker_gill_solovay` (`Diagonalization/Relativization.lean`) | [AB09, Theorem 3.7] | `A := EXPCOM` with `POracle_EXPCOM_eq_NPOracle_EXPCOM`; `B` from the proved `exists_oracle_ne` | the `EXPCOM` identity (B5a, B5b), and `Turing.exists_uniformMachineCode` (B5a), on which the language `EXPCOM` itself rests through `expCode := Classical.choice exists_uniformMachineCode` |

## Changes

- **`Classes.lean`:** imports `Build/OracleSim`, flagged with a comment; this edge is acyclic.
  Two private ledger lemmas transcribed from the probe (`b1_poly_succ_le`, `b1_budget`), with
  sketches. The target's body is filled, and a flagged **Fill appendix** names the §12.10 route.
  The audited sketch's direct-simulation obligations (i)–(iii) are discharged once, by W2-S.
- **`Relativization.lean`:** the target's body is filled; a flagged **Fill appendix** names both
  modulo dependencies, and states that the `B` half is admission-free.
- No statement changed; no public declaration was added.

## Verification

- **Freeze** (`audits/logs/k1-fill-freeze.log`). Only the two target bodies changed (authorized).
  Two privates were added in `Classes`. The only import change is `Build/OracleSim` in `Classes`.
  The only removed lines are the two `sorry`s and the two lines ending the docstrings, which were
  extended. No forbidden token.
- **Elaboration.** Both files elaborated read-only before the commit: 0 errors, 0 warnings.
- **Replay** (`audits/logs/k1-fill-replay.log`, user-run): the downstream closure of the two
  files, 6 modules at `023a904f`. **0 errors.** `Classes` and `Relativization` have 0 sorry
  warnings (1 each before); `EXPCOM` keeps its 6.
- **Axioms and admission walks** (`audits/logs/k1-fill-axioms.log`; probe
  `audits/evidence/k1/K1Axioms.lean.txt`). Both targets print `sorryAx`, and only through the
  named modulo rows:
  - `POracle_eq_P_of_mem_P` rests on `exists_plain_simulation` alone;
  - `baker_gill_solovay` rests on the `EXPCOM` identity and `exists_uniformMachineCode`;
    `exists_oracle_ne` is admission-free.

  The private-constant censuses find none that uses `sorryAx`: 24 in `Classes`, 140 in
  `Relativization`.
- **The comment-only correction** `9910bf76` comes after the replay. The walk showed that the
  language `EXPCOM` itself rests on `exists_uniformMachineCode`, and the appendix now says so.
  The comment-stripped code is identical to the replayed file.
- **Duplication** (`audits/logs/k1-fill-screen-{before,after}.txt`, population
  `audits/evidence/k1/screen-population.txt`): 185 → 189 declarations, **15 → 15 pairs**,
  identical list. **New copies: none.**
- **Lint** (`audits/logs/k1-fill-stylelint.log`): 0 FAIL, 0 WARN over `ClassOracle` and
  `Diagonalization`.

## Disposition

Both targets lose their `sorry` now, and their axiom prints clear when the modulo rows land:
W2-S (`briefs/w2-fill-oraclesim.md`) for the first; B5a and B5's summit for the second. **Fill
gate:** each goes to the fill gate of the batch that discharges its modulo rows, so the auditor
sees it admission-free: `POracle_eq_P_of_mem_P` with the §12.10 fill, `baker_gill_solovay` with
B5. The user may instead ask for a separate gate now.
