# Gate 132 round 3 resolutions for #296

Round 2 audited `ce427bde6ee5464a4146dce2b3add69b7a05677d` and returned **HOLD** with one minor,
G132-04, and notes N1 to N7 (`findings-r2.md`, SHA-256
`4ed091be660390c0b224ea8e7c2023fe4131abadbb8514a05f3c29fa8869d24a`). It found G132-01, G132-02 and
G132-03 resolved, and no soundness defect or new failing seal root. The current PR head is
`befb73f97a63ce449fe1a9a1b7dfc3fdbda65969`, against the same campaign Lean
`7b6bd1685a1436313dfbc13ce191f40c7dd065d3`. It changes one line after `ce427bde`.

| Finding | Resolution |
| --- | --- |
| G132-04 · `Bidirectional.foldCfg_run`'s one-step base | **Repaired** in `befb73f9` with the proposed replacement: `\| zero => simpa only [Nat.zero_add, MultiTapeTM.runFrom_one, MultiTapeTM.runFrom_zero] using foldCfg_init M x`. It elaborates natively and with `runFrom` locally irreducible. Bidirectional joins the PR, which now changes 70 files: Deterministic and 69 citing owners. The sweep dispositions and the ledger are corrected (below), and the replay, seals, controls and copy screen are fresh at `befb73f9`. |

## Why the site was missed

The `zero` case is a one-step run (duration `0 + 1`) from a zero-step source run.

- **Round 1** tried `simpa only [MultiTapeTM.runFrom_one]`. That normalizes neither `0 + 1` nor
  the source's `runFrom … 0`, so it closed the goal only by unfolding `runFrom` natively, and
  `2a9f32da` restored the campaign text. The conclusion drawn, that the site needs native
  unfolding, was wrong: the failure came from the missing normalization.
- **Round 2's mutation** made the same substitution. Its mutant passed natively but failed with
  `runFrom` irreducible (the confirmation log expects `runFrom … (0 + 1)`), so it was recorded
  as a shift or definitional closing. The original cites the explicit successor and zero
  equations, so the irreducibility pass could not see it either.

The blind spot is therefore a one-step run written with the explicit successor and zero
equations. Round 3 closes it in three ways.

1. **Every passing mutant re-read.**
   - The other six rows confirmed as needing native unfolding fail with `runFrom` irreducible at
     general durations: `j + 1` (EXP), `counterCarry bs + 1` (TimeConstructible), `r + 1`
     (Hardness), `u + 1` (WindowRun, two rows) and `d'` (Universal).
   - The eight rows in declarations that already fail sealed are successor rewrites at general
     durations, read in the source: `s`, `u`, `t` and `w.length`.
   - A scan of every confirmation log for a `runFrom` duration that is a closed term equal to 1
     finds Bidirectional's `(0 + 1)` and nine mutation artifacts, where the mutant's
     `← runFrom_one` turned `step c` into `runFrom c 1` inside a longer run.
2. **A census of explicit successor-and-zero rewrites** (`r3-evidence/SUCC-ZERO-CENSUS.json`,
   script in the carrier). It lists every `runFrom_succ_eq_step(')` at the head with
   `runFrom_zero` nearby: 9 within the same tactic and 75 more within eight lines, in 97 files. Each row was read by hand and none is an uncited one-step run.
   The six tight rows in Primitives are the disclosed two-step runs; the others are induction
   pairs with a zero-step base, CfgRecord's two-step `(t := 1)` equation, the lemma itself or prose.
3. **Bidirectional re-swept at the head** (`r3-evidence/SWEEP-BIDIRECTIONAL-r3.json`): 4 site mutations in 2 jobs, 0 passing natively; the irreducibility pass has 1 error, `foldTM_nonnegative`'s zero-step base `exact foldSafe_init M x` (408), as at ce427bde; no one-step row and no tagged error.

## Corrections to the round 2 records

- `r2-evidence/SWEEP-FINAL.json`: the Bidirectional 301 row's disposition ("the disclosed
  definitional zero-step base") was wrong. `SWEEP-BIDIRECTIONAL-r3.json` supersedes it.
- `resolutions-r2.md`, "Left as they are": the Bidirectional `foldCfg_run` bullet is withdrawn.
  The other disclosed sites stand: RecordTable 2325 and 2336, Primitives' six `(0 + 1) + 1`
  two-step runs, `pre_scan`'s two-step branch, the zero-step bases, general iteration and OracleTM.
- `campaign/duplication-ledger.md`, RO-1: now `befb73f9`, 69 citing owners, and Bidirectional's
  base among the repairs.

Round 2's library-wide sweep (`r2-evidence/SWEEP-FINAL.json`, with its logs in the round 2
carrier) stands for every other file: `befb73f9` changes only Bidirectional
(`patch/round2-to-head.patch`).

## Notes N1 to N7

Each is accepted within its stated scope. This round's evidence replaces their source, replay,
seal, control and screen inputs. The qualifications stand:
- N3: an earlier error can hide a later tactic, and durations fixed only by a hypothesis are not
  classified. The census covers the explicit-equation form that both passes missed.
- N4: the seals give a comparative result (no new failing root), not universal rule-10
  compliance.
