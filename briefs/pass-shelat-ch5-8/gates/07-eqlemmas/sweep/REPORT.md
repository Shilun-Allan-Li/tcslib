# Rule-10 statement sweep at #210's head `fff0430c7c9db136e60ed14b069e972c2ea56fc8`

(The sweep agent's report, saved verbatim by the maintainer; the agent could not write `.md` files.)

## Rule-10 statement sweep at PR #210's head (`fff0430c`): 125 reads found, and REPORT.md was not written

The sweep is complete. Every file the brief named was swept, with no exclusions and no fallbacks: 135 files under `TCSlib/Cryptography/` plus `audits/pass-shelat/Checks.lean`. No TCSlib source was changed, nothing was committed or pushed, and the worktree is clean at `fff0430c`.

**One deliverable is missing.** The harness blocks subagents from writing `.md` files, so `REPORT.md` does not exist. All its content (method, coverage, counts, fixes, checks) is below. Please save it as `briefs/pass-shelat-ch5-8/gates/07-eqlemmas/sweep/REPORT.md`, or tell me where else to put it. Everything else is in that directory:
- `reads.tsv`: every read, with the columns you asked for (file, declaration, kind, foreign definition(s), defining file, minimal-unseal evidence) plus declaration kind, lines, first sealed error and a log path.
- `by-definition.tsv`, `files.tsv` (per-file status), `instances.tsv` (foreign instances and other unsealed constants met).
- `tools/*.txt` and `logs/`.

## Counts
- **Files:** 36 have reads. 74 pass with every collected foreign definition sealed. 26 had nothing to seal. All 136 unsealed statement-only copies elaborate with 0 errors.
- **Reads:** 125 in total.
  - **87 statement reads** in 29 files (84 theorems, 2 examples, 1 structure).
  - **38 def-body reads** in 21 files (a kept definition's value only typechecks by reducing a foreign definition).
- **Where the definitions live:**

| Definitions needed by the read | Statement | Def-body |
|---|---:|---:|
| Complexity layer only (`TCSlib/Complexity/Randomized/*`) | 45 | 20 |
| Cryptography only | 11 | 10 |
| Both | 31 | 8 |

**By file (statement / def-body), under `TCSlib/Cryptography/`:**
- **Asymptotic:**
  - `HardCorePermutation` 13/1, `HardCore` 9/5, `OneWay` 4/2, `PublicKey` 4/2, `HardCoreClaims` 4/0
  - `Universal` 4/0, `Collections` 3/2, `PRF` 3/2, `OneWayYao` 2/1, `UniversalPadding` 2/0
  - `Encryption`, `Ensembles`, `MultiMessage` 1/1 each
  - `CollectionsHelpers`, `HardCoreGL`, `HardCoreGLColl`, `HardCoreGLFamily`, `PRFLemmas` 1/0 each
  - `HardCoreCollection` 0/2, `PublicKeyLemmas` 0/1
- **Candidates:** `DiscreteLog` 4/0, `Factoring` 3/3, `RSA` 2/0, `Rabin` 1/3.
- **Games:** `Hopping` 5/0, `Protocols` 2/4, `Simulate` 0/1.
- **ZeroKnowledge:** `Commitment` 5/0, `GraphIsomorphismZK/Closeness` 4/0, `NP` 3/0, `Encryption` 1/0, `GraphIsomorphism/SoundnessRep` 1/1, `GraphIsomorphism/Soundness` 0/2, `GraphIsomorphism/SoundnessRepGI` 0/1, `Defs` 0/1, `ThreeColoring/Simulator` 0/1.

**By foreign definition (statement / def-body):** 34 definitions in all. A read that needs several definitions is counted under each.

| Definition | Defining file | Stmt | Body |
|---|---|---:|---:|
| `Complexity.PolyExpr.eval` | `Complexity/Randomized/PolyExpr.lean` | 59 | 26 |
| `NUPPT.coinLen` | `Complexity/Randomized/PPT.lean` | 25 | 11 |
| `NUPPT.ofPolyTime` | `Complexity/Randomized/PPT.lean` | 23 | 9 |
| `PermFamily.toFunFamily` | `Asymptotic/OneWay.lean` | 19 | 0 |
| `FunFamily.glPad` | `Asymptotic/HardCore.lean` | 14 | 0 |
| `NUPPT.ofPolyTimeUniform` | `Complexity/Randomized/PPT.lean` | 11 | 7 |
| `Games.OracleSpec.add` | `Games/OracleComp.lean` | 2 | 5 |
| `Strategy.coinLen` | `ZeroKnowledge/Interaction.lean` | 2 | 4 |
| `FunFamily.ofString` | `Asymptotic/OneWay.lean` | 5 | 0 |
| `Games.QueryImpl` | `Games/Simulate.lean` | 5 | 0 |
| `Protocol.withV` | `ZeroKnowledge/Interaction.lean` | 3 | 1 |
| `PolyExpr.normal` | `Complexity/Randomized/PolyExpr.lean` | 1 | 2 |
| `DistinctPrimes.p`, `DistinctPrimes.q` | `Candidates/Concrete.lean` | 0 | 3 each |
| `NUPPT.precomp` | `Asymptotic/HardCoreGL.lean` | 2 | 0 |
| `Collection.index` / `Collection.trap` | `Asymptotic/Collections.lean` | 0 | 2 / 1 |
| `GI.gniProtocolRep`, `GI.gniVerifierRep` | `GraphIsomorphism/Proofs.lean` | 1 each | 1 each |
| 6 other `GI.*` protocol/verifier definitions | `GraphIsomorphism/Proofs.lean` | 0 | 1 each |
| `GIZK.blockLen` | `GraphIsomorphismZK/Simulator.lean` | 1 | 0 |
| `PRG.oneBit`, `owpGenPRG` | `Asymptotic/HardCore.lean` | 1 each | 0 |
| `PRG.expand` | `Asymptotic/HardCore.lean` | 0 | 1 |
| `FunFamily.prod` | `Asymptotic/OneWay.lean` | 0 | 1 |
| `NUPPT.Uniform`, `NUPPT.advInput` | `Complexity/Randomized/PPT.lean` | 0 | 1 each |
| `NUPPT.wrap` | `Asymptotic/HardCoreLemmas.lean` | 0 | 1 |
| `ProperColoring` | `ThreeColoring/Language.lean` | 0 | 1 |

## Sanity checks
- **F01 is found.** All eight examples F01 named are statement reads:
  - In `HardCorePermutation`: `PermFamily.glHalf_f_even`, `glHalfBit_even`, `predProb_glHalf_even`, `invProb_glHalf_even`, `PermFamily.glHalf_f_odd`. Each needs `FunFamily.glPad`, `PolyExpr.eval` and `PermFamily.toFunFamily`.
  - In `HardCoreClaims`: `thm_87_3_1`, `thm_87_3_2`, `thm_87_3_3`. Each needs `FunFamily.glPad` and `PolyExpr.eval`.
  - The sweep also finds reads F01 did not list:
    - `thm_87_3_9`;
    - the `glHalf` statements `glHalfBit_odd`, `predProb_glHalf_odd`, `invProb_glHalf_odd_le`, `glHalf_predProb_even`, `glHalf_predProb_odd`;
    - `ofFn_oddCoins`, `OneWayPermutation.glHalf`, `exists_owp_hardCore`;
    - `oddCoins`, a def-body read.
  - I ran F01's own reproducer. Unsealed it passes. Sealing any one of `glPad`, `PolyExpr.eval` or `toFunFamily` makes the statement line fail.
- **The three statements #210 restated now pass:**
  - `fullDLCollection_hardCore`: `DiscreteLogHardcore` passes with all 69 collected definitions sealed, including `expCollection`.
  - `glPad_tdpBitScheme_singleBitSecure` and `exists_glPad_singleBitSecure`: neither is among PublicKey's 6 reads, with `TrapdoorCollection.glPad` sealed.
  - As a positive control, I planted the pre-#210 forms of all three as `example`s in the head files. All three pass unsealed and fail sealed, so the method finds the reads #210 fixed without any hand-picked list.

## Method
1. **Bring the oleans to the head.** All 116 modules downstream of the 33 changed files were re-checked in dependency order, and all passed. 15 imports that had no olean in the base tree (`Games/*`, `MPC/*`, `SecretSharing/*`, all unchanged by #210) were also checked, and all passed. I ran one `lean` process at a time and never used `lake build`. No probe copy writes an olean.
2. **Make a statement-only copy of each file.** Every theorem/lemma/example proof becomes `sorry`, line numbers are kept, and definitions keep their bodies.
3. **Elaborate the copy unsealed.** This is the control, and it must have 0 errors. A meta-program appended to the copy collects every foreign TCSlib plain definition that elaboration could unfold. It reads:
   - the types of every constant the file declares;
   - the values of every definition, instance and abbreviation the file declares;
   - transitively, the types of every foreign TCSlib constant reached, and the bodies of every foreign definition reached.

   Over all files that is 3669 (file, definition) pairs: 1641 that appear in the file itself and 2028 reached only through other definitions.
4. **Seal and attribute.** Elaborate again with all of them sealed. Each error is assigned to its declaration and classed as statement or body by its position.
5. **Fixpoint.** Each failing declaration gets everything unsealed around it alone, and the run repeats until the file passes. This also catches reads hidden in the first sealed run, because Lean suppresses errors on terms containing `sorry`.
6. **Minimise.** Shrink each declaration's unsealed set to a 1-minimal one by binary partition, then re-seal each name alone to check it is needed. A trial result is only counted if nothing the declaration depends on (within the file) failed in the same run.
7. **Final evidence.** The final run with all minimal sets must pass, and each name has a re-seal run in which its declaration fails.

The final evidence took 1401 Lean runs.

**Three passes.** Pass 1 found 13 control failures caused by bugs in my statement/body splitter: `match` and `|x|` in statements, and `haveI` in statements. `GGM` and `SubHybrids` also hit their own seal lines. Passes 2 and 3a were stopped when I found that a failing earlier theorem, or a proof embedded in a definition, could hide a later error. Pass 3 is the final run, fresh for 44 files. The other 92 files either pass or have nothing to seal, and their results come from passes 1 and 2. Those results depend only on the unsealed control and the first sealed run, which the later fixes did not change. I re-checked all 136 copies at the end: each is identical to the final splitter's output, and each control has 0 errors.

## What "complete" means, and what it does not cover
For every swept file, take the set of definitions the collector found. Every declaration not in `reads.tsv` elaborates with that whole set sealed. Every listed read fails sealed, has a sufficient 1-minimal unseal set, and each name in it is shown needed by its own re-seal run.

This matters in practice: a collection from types alone, limited to names appearing in the file, would have missed 2 reads outright (`ofFn_oddCoins` and `GIZK.sim_ofFn_eq`) and reported 48 others incompletely.

**Not covered:**
- **Unsealed constant kinds:**
  - Mathlib definitions.
  - Foreign instances (4), `abbrev`/reducible definitions (21), projections (68), and private or auxiliary definitions (72). Their bodies were walked, so plain definitions behind them were sealed.
  - Definitions already globally `@[irreducible]`.
- **Proofs.** Proofs are out of scope. A foreign definition reachable *only* from a proof embedded in a definition body (Lean's `proof_N` helpers) may be missing from the sealed set. That could hide a def-body read, but statements are unaffected.
- **Reductions the seal does not block.** The kernel, `native_decide`, `with_unfolding_all`, and explicit `unfold`/`simp [X]` inside a statement are not blocked. I saw none in statement position.
- **Minimal sets are not unique.** Where either of two definitions would do, one is reported.
- **The statement/body split is by error position.** Def-body reads include proof fields of definitions, such as `expands`, `omega`, `rw [tdpGen_runAt]`.
- **No module failed to run.** Sealing never broke typeclass resolution wholesale, and `Checks.lean` passes.

## Fixes the planning will need, by definition
Existing `rfl` equation lemmas cannot fix a statement read, because the statement needs the two sides to be definitionally equal. The fix in each case is one of:
- **(E)** publish an equivalence or transport beside the definition and restate the consumers through it, as #210 did; or
- **(R)** rule the definition notation and make it `abbrev`/reducible, which policy already exempts.

1. **`PolyExpr.eval`** (85 reads, 22 files). Typed lengths like `Fin ((.add p q).eval n)` are used where `Fin (a + b)`, `Fin (a * b)` or `Fin n` is expected. Option (R) on `eval` is the only one that scales. The (E) alternative is a `Fin`-equivalence per constructor (and for `PolyExpr.normal`), with every consumer restated. This is an interface question for the Complexity layer.
2. **`NUPPT.coinLen` with `ofPolyTime` / `ofPolyTimeUniform`** (the `*_runAt` coin types; `precomp`, `wrap`, `Uniform` and `advInput` are the same pattern). Fix with (E): publish `coinsEquiv_ofPolyTime : (ofPolyTime …).Coins n ≃ (Fin (c.eval n) → Bool)` and its `ofPolyTimeUniform` analogue in `PPT.lean`. The existing `coins_ofPolyTime` is an ordinary equation and cannot retype the coin argument. Option (R) on `coinLen` alone removes only part of the problem.
3. **`PermFamily.toFunFamily`** (19 reads). Every `HardCore P.toFunFamily h` with `h : ∀ n, (Fin n → Bool) → Bool` is a read. These are headline statements:
   - `owp_hardcore_prg`, `cor_81_7`, `owp_commitment`, `exists_commitment_of_owp_hardCore`, `HardCore.bitHiding`;
   - `zk_proof_of_owp_levinReduction`, `zk_proof_of_mem_NP_of_owp`;
   - `OneWayPermutation.glHalf`, `exists_owp_hardCore`.

   Fix with (E): `toFunFamily_domEquiv` plus `toFunFamily_f` through it, or a `PermFamily.HardCore` predicate beside the definition; or with (R). `toFunFamily` itself also reads `PolyExpr.eval`, so this decision interacts with item 1.
4. **`FunFamily.glPad`** (14 reads, F01). Fix with (E): publish `glPad_inEquiv` (`inLen + inLen`), `glPad_outEquiv` (`outLen + inLen`) and `glPad_f` through them in `HardCore.lean`, then restate the 14.
5. **`Games.OracleSpec.add`** (`Party.step`/`stepT`/`close`/`closeT`, `QueryImpl.sum`, two examples). Option (R) fits, since it is a `Sum.elim` combinator. Option (E) would need `add_dom_inl`-style transports, which are awkward inside pattern matches.
6. **`Games.QueryImpl`** (5 reads in `Hopping`, error "Function expected"). It is a `def` that only renames a function type. Option (R), make it an `abbrev`, or give it a `CoeFun`.
7. **ZeroKnowledge coin types:** `Strategy.coinLen`, `Protocol.withV`, the `GI.*` protocol/verifier definitions, `GIZK.blockLen`. Fix with (E): publish `Coins`/`ExecCoins` equivalences beside each protocol and for `withV`; or (R) for `coinLen` and `blockLen`.
8. **`FunFamily.ofString`** (5 reads in `Universal` and `UniversalPadding`). Fix with (E): `ofString_domEquiv`.
9. **Single cases:**
   - `PRG.oneBit` + `owpGenPRG`, `PRG.expand`, `FunFamily.prod`: (E) length transports beside each definition.
   - `Collection.index` / `trap` (proof fields): use the published equations.
   - `DistinctPrimes.p` / `q` (Rabin's default parameters): use the `p_eq`/`q_eq` lemmas #210 added, or (R) on the accessors.
   - `ProperColoring`: publish an elimination lemma beside it.

## Paths
Output directory: `/home/user/tcslib/briefs/pass-shelat-ch5-8/gates/07-eqlemmas/sweep/` (untracked, 5 MB).
- **Tables:** `reads.tsv`, `by-definition.tsv`, `files.tsv`, `instances.tsv`.
- **Tools** in `tools/`, as `.txt`:
  - `stmtonly.py`, `sweep.py`, `collect_tail.lean`, `plant.py`, `aggregate.py`, `needbuild.py`;
  - `declx.py`, unchanged from gate 04;
  - `F01Repro.lean` and two `plant-*.lean` controls.
- **Logs:**
  - `logs/runs/`: the olean ladders, all sweep passes, the list of reused results.
  - `logs/files/<tag>/`: for each file, the unsealed control, the first sealed run, the final run, every trial, the result and the collector output.
  - `logs/controls/`: F01 reproducer, planted base statements, and paired logs for `glHalf_f_even`, `thm_87_3_1`, `Ensemble.copies_X`, `prob_eq_until_bad` and `tdpBitScheme`.

Known-good files that pass sealed, with their candidate counts: `HardCoreLemmas` 51, `GGMReductionEval` 104, `DiscreteLogHardcore` 69, `GraphIsomorphismZK` 65.

Scratch (`SP=/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad`):
- `$SP/sweep/work/`: all probe copies and logs.
- `$SP/sweep-oleans`: now at the head for the 116 downstream modules plus the 15 previously missing imports.
- `$SP/wt-sweep`: the worktree, unmodified.