# Fill s2b-efficiency — final payload

**Worker** Claude. **Unit** `s2b-efficiency`. **Issue base**
`b50f0a416cbf0a9f05acf14a254ba53cd97a7701` on `cryptography/pass-shelat-ch2-4`. Package read at
exchange commit `81449bb35998cc291d2f083ab2b07ccbce7fb2a9`: `shasum -a 256 -c SHA256SUMS` all OK
(`evidence/logs/package-sha256.log`); `SOURCE-SHA256SUMS` all OK on the clean issue checkout
(`evidence/logs/source-sha256.log`). The proof branch `fill/s2b-efficiency` is local. It starts at the
issue base and its head is `bc53a51865103bc20bb4dfbbf2ad302078a9a363`. Lean 4.25.0; Mathlib at the
manifest revision `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`.

## 1. Status

| Target | Declaration | Status |
|---|---|---|
| T1 | `exists_handlerMachine` | **proved** |
| T2 | `exists_interactiveHandlerMachine` | **proved** |
| Companion | `exists_toCompOn_of_toComp` | **proved** |
| T4 | `exists_toOracleAdversary_of_bitCodec` | **proved** |

The four targets have no remaining admissions. Each target uses only the axioms
`propext`, `Classical.choice` and `Quot.sound` (`evidence/logs/axioms.log`).

The statements, every non-target declaration and the statement prose of all docstrings are
unchanged. A script compared all 28 declarations of `Efficiency.lean` against the base: their
statements and their docstrings up to `**Proof sketch` are identical, and only the four target
sketches differ. Global simp attributes are unchanged. No new `@[simp]` was added and no
`private` declaration was used.

Checkpoints delivered on `exchange/pass-shelat-ch5-8` (`fill s2b-efficiency: checkpoint 1` …
`4`): companion, T1, T4, T2. The fifth patch was added after checkpoint 4, following the
explicit-unfold scan (§6.3).

## 2. Changed files (`patches/` = the full `git format-patch` series from the issue base; `src/`)

| File | Lines | Change |
|---|---:|---|
| `TCSlib/Cryptography/Games/Efficiency.lean` | 706 | four proof bodies, four sketches (EF-2), six imports, module docstring |
| `TCSlib/Cryptography/Games/Efficiency/Strings.lean` | 549 | new (EF-1): S1 string layer, activation loop, machine glue |
| `TCSlib/Cryptography/Games/Efficiency/Replay.lean` | 117 | new: S3 replay lemma, cost scaling |
| `TCSlib/Cryptography/Games/Efficiency/Handler.lean` | 516 | new: T1 raw machine and functional equation |
| `TCSlib/Cryptography/Games/Efficiency/OracleBridge.lean` | 321 | new: T4 translators and evaluation lemma |
| `TCSlib/Cryptography/Games/Efficiency/Interactive.lean` | 838 | new: T2 replay machine, polynomial time, round lemmas |
| `TCSlib/Cryptography/Games/Efficiency/InteractiveSpec.lean` | 849 | new: T2 functional equation |

All helper files are under 1000 lines, and all new declarations are in the namespace
`TCSlib.Cryptography.Games.EffFill`. The imports are precise and acyclic.
`Strings` is the first consumer of the GGM reduction module and imports
`TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.GGM.Reduction` directly. The helpers add no
new Mathlib root: the recomputed roots are identical to the supplied 68
(`evidence/logs/mathlib-roots-final.txt`). The order with the helpers inserted before
`Games/Efficiency` is `evidence/logs/order-final.txt` (143 modules). A check confirmed that every
`import TCSlib…` of every module appears earlier in that order.
`Efficiency.lean` is now a facade, so it imports every child module and lists them under
`## Contents`.

Commits (`patches/0001…0005`):
1. `46fb87d…` companion; 2. `d7d3623…` T1 (+`Strings`, `Handler`); 3. `a695df2…` T4
(+`OracleBridge`); 4. `4a04a94…` T2 (+`Replay`, `Interactive`, `InteractiveSpec`); 5. `bc53a51…`
replaces `simp only [id, …]` by `id_eq` and the simproc `reduceCtorEq` by `List.cons_ne_nil`.

**Edit to the module docstring.** The title no longer says "skeleton". The "Status: skeleton"
paragraph now says "Status: proved", and a `## Contents` section was added. The maintainer may
prefer other wording.

## 3. The proofs

**Companion.** `NUPPT.exists_comp A polyTimeComputable_pairSndD polyTimeComputable_id`. `φ` is
`NUPPT.coinsCongr` (`runAt_coinsCongr`), then `pairSndD_pairEncode`, `runAt_eq`, `toCompOn_eq` and
`toComp_eq`.

**T1.** `B := EffFill.exists_splitMachine A (hRaw_poly …) adv (n ↦ ⟨A.advice n, H.init n⟩) _
H.seedLen`, built from `NUPPT.ofPolyTime` and then `NUPPT.exists_split`.
- **The initial state is advice.** `init` is an arbitrary function of `n`, so `B` is non-uniform
  even when `A` is uniform. The advice bound is `2·A.adv + 2 + stateLen`.
- **The loop.** `EffFill.hRaw` is the activation loop `actLoop` over `GGMRed.stateLoopFun`, with at
  most `q + 1` rounds. Its state is `⟨encodeLog hist, ⟨s, 1^t⟩⟩`, and the context and `A`'s input
  are recomputed in every round.
- **A round.** The move goes through the canonical decoder (`canonWord_eq`). The answer is decoded
  componentwise with `fixLen` (`ofFn_getD_decodeFin`, `answer_of_pairDecode_eq_none/some`), which
  includes the case where `run`'s output is not a pair. A query at `t = q(n)` gives
  `0^{dα(n)}`, as `buildComp_zero_of_query` does.
- **The functional equation.** `hRaw_spec` is an induction on the remaining budget. It uses
  `GGMRed.stateLoopFun_eval`, wrapped as `runsTo_stop`, at the exact stopping round.

**T4.** `B' := NUPPT.exists_comp B bridgePre_poly bridgePost_poly` and `φ := coinsCongr`.
- `bridgePre` emits one piece per suffix, using `polyTimeComputable_iterateEmit` with the step
  `pairSndD`. `bridgePre_encodeHist` maps the history of a log to `⟨[], encodeLog⟩`, with
  `1^0 = []` for the index of the only oracle.
- `bridgePost_spec` shows that both decoders read corresponding moves on every word. This
  includes a payload of the wrong length (the verdict `false` on both sides), `ℓ₁(n) = 0` (an empty
  payload is a valid query), the word `⟨[true], [false]⟩`, and the default verdict.
- `eval_buildTree_bridge` is an induction on the budget. At the timeout, the verdict `false` is
  bit `0` of `zeroBits 1`.

**T2.** `B := exists_splitMachine` of `EffFill.iRaw`, with the same advice as T1.
- **The replay machine.** On `⟨z, O⟩` it replays the reduction, one activation per round. The
  state is `iSt ph L s 1^b cur L' 1^c O'`, where `O'` is the part of the log not yet replayed.
- **Defaults.** The joint default of `call`, at budget `0` or on a malformed result, splits into
  `0^{dout}` and `0^{stateLen}`. A pending query at budget `0` gives the timeout without asking
  its oracle, for the adversary, for a call and for the finalization.
- **The round bound.** `2 + finCall + q·(perCall + 2)`, which equals the design's
  `(q + 1) + q·(perCall + 1) + finCall + 1`. No extra initialization activation is needed, since
  `iStart` computes the initial state.
- **Cost bound.** The reduction tree is `CostBoundedBy (fun _ => 1) (q·perCall + finCall)`, from
  `toCompOn_costBoundedBy`, `costBoundedBy_mul` (the probe's scaling lemma),
  `buildComp_costBoundedBy`, `simulate_costBoundedBy` and `CostBoundedBy.bind`. These bounds are
  proved before the replay lemma is used.
- **The replay.** The machine's next-move function replays the tree from the empty log
  (`ReplaysFrom`). The invariant `IInv` quantifies over every extension of the replayed prefix,
  and three nested inductions cover the phases: `adv_phase` on the adversary's budget, then
  `call_phase` and `fin_phase` on the call and finalization budgets. Outer answers are arbitrary
  and are copied from `O` without being checked.
- **Conclusion.** `buildComp_of_replaysFrom` gives the equality of computation trees.
  `impl_apply`, `call_eq`, `input_eq`, `finish_eq`, `finInput_eq` and `seedIn_eq` match `H` with
  the raw `EffFill.iImpl` and `iFinish`.

## 4. Published helpers cited

These are the providers named in the brief, each read only through its public lemmas:
- **Machines and closure.** `NUPPT.coinLen_eq`, `runAt_eq`, `runAtL_eq_output_layout`,
  `runAtL_ofPolyTime`, `coins_ofPolyTime`, `coinsCongr`, `runAt_coinsCongr`, `exists_comp`,
  `exists_split`, `layout_eq`, `in*_layout`, `advInput_eq`, `polyTimeComputable_output`.
- **PRF layer.** `decodeOracleMove_pairEncode_ofFn`, `_pairEncode_false_of_length_ne`,
  `_true_two`; `decodeFin_eq`, `decodeFin_ofFn`, `decodeFin_eq_some_iff`.
- **GGM loop.** `GGMRed.stateLoopFun`, `stateLoopFun_poly`, `stateLoopFun_eval`,
  `pairEncode_append_right`; `StateLoop.orbit_zero/succ`, `lenLe_comp`, `unaryPoly_comp`,
  `cons_poly`; `polyTimeComputable_iterateEmit`.
- **Codec and machines.** `decodeBitMove_query/ret/of_not_canonical`, `encodeBitMove_query/ret`,
  `bitCodec_decodeMove/encodeEntry/timeout`, `encodeLog_bitCodec`, `ofFn_zeroBits`,
  `zeroBits_apply`; `NUPPT.toComp_eq`, `toCompOn_eq`, `toCompOn_costBoundedBy`, `buildComp_*`
  case lemmas, `buildComp_costBoundedBy`.
- **Simulation and evaluation.** `simulate_pure/query`, `simulate_costBoundedBy`,
  `OracleComp.pure_bind/query_bind/bind_assoc`, `costBoundedBy_query/pure`, `CostBoundedBy.bind`;
  `OracleComp.evalFn_pure/query`, `QueryTree.eval_ret/query`, `toOracleAdversary_eq`,
  `buildTree_*` case lemmas, `encodeHist_cons/nil`.
- **Pairing calculus.** `takeLen_poly`, `dropLen_poly`, `EnsembleLemmas.polyTimeComputable_zeros`,
  and the pairing combinators (`polyTimeComputable_pairEq`, `_lenEq`, `_lenLe`, `_ite`, `_and`,
  `_or`, `_not`, `_isNil`, `_tail`, `_unary`, `_unaryPoly`, `_const`).

The proofs did not need `toComp_singleCodec` or `decodeIdx_*`. The provider files and their proof
bodies are untouched. Inherited dependency findings, such as `StateLoop.gstep` inside
`GGMRed.stateLoopFun_poly`, stay in the cleanup ledger.

**Missing readers: none.** Every definition of another file had a published lemma.

## 5. New shared helpers (namespace `EffFill`) and requests

- **Requested for the shared layer (S1).** `encodeLog_append_single`, `length_encodeLog_le`,
  `fixLen` (+`ofFn_getD_decodeFin`, `fixLen_poly`), `selLen`/`sumPoly`, `canonWord`/`canonFun`
  (+`canonWord_eq`, `canonFun_poly`), `actLoop`/`RunsTo`
  (+`runsTo_zero/succ/stop`, `actLoop_poly`), `exists_splitMachine`, `entryPoly`,
  `exists_ofFn_eq`.
- **Requested for the shared layer (S3).** `ReplaysFrom`, `buildComp_of_replaysFrom` and
  `costBoundedBy_mul`. The scaling lemma is the supplied probe's statement with `p` in place of
  `scale * cost`.
- **Target-specific (stay in `EffFill`).** `hRaw` and its round, `iRaw` and its round, `iSt` and
  its readers, `iCall`/`iImpl`/`iFinish` (the raw terms of `InteractiveHandler.call/impl/finish`),
  and the bridge translators.
- **Duplication disclosure.**
  - **The handler round.** `hAct`/`hRaw` repeat the structure of GGM's round (`GGMRed.step`,
    `rawFun`) generically, as the design anticipated, until F-4.
  - **Small wrappers.** `zeros_poly`, `eq_poly`, `lenEq_poly` are applied forms of
    `EnsembleLemmas.polyTimeComputable_zeros`, `polyTimeComputable_pairEq` and `_lenEq`.
  - **Generalized GGM lemmas.** `encodeLog_append_single` generalizes
    `GGMRed.histEnc_append_single` to any codec. `length_le_length_encodeHist` and
    `length_encodeLog_le` follow `GGMRed.length_histEnc`.
  - **Mathlib-adjacent.** `ofFn_take_drop_add` restates `List.ofFn_add` with `take`/`drop`.
    `exists_ofFn_eq` may duplicate a Mathlib lemma.
  - No proof is copied verbatim.
- **Public definitions without lemmas: none.** Every public definition has its `_eq`/`_iff`
  lemma, so check 8 of the campaign lint is clean.

## 6. Evidence

### 6.1 Environment (addendum v1)

- **Preflight** (`logs/preflight.log`). `nproc` 4. Cgroup v1 with no memory limit, so the headroom
  is `MemAvailable` = 15.18 GiB; memory in use is 34.9 MiB (`usage − total_cache + total_shmem`).
  25.33 GiB were free on `/dev/vda` (ext4); no tmpfs was used. **Pass.** Lean 4.25.0 was
  installed with `elan` after the preflight (`logs/toolchain.log`). The re-check before the cache
  showed 23.95 GB free.
- **Cache.** The archive store was absent before the fetch (`logs/cache-store.log`). The fetch
  used 68 roots, identical to `roots.txt`: `Attempting to download 2066 file(s)`,
  `Decompressing 2066`, `Completed successfully`, exit 0 (`logs/cache-get.log`). There is no
  zero-size olean, and the root probe passes (`logs/cache-probe.log`).
- **Packages** (`logs/packages-check.log`). Every present package matches the manifest. ABSENT:
  `doc-gen4`, `UnicodeBasic`, `BibtexQuery`, `MD4Lean`; no module of the order imports them. Last
  line: `RESULT: all present packages match the manifest`.
- **Bootstrap** (`logs/bootstrap.log`). Modules 1–130 of `order.txt`, everything before
  `Games/Efficiency`, built first: 130/130 exit 0.
  - The detached background sweep was ended twice, while checking `Build/Primitives`. A sampler
    started alongside was ended at the same moment, and there was no OOM event (`oom_kill 0`).
  - A standalone check of `Primitives` passed (1:35, 2.40 GB).
  - All later sweeps ran in the foreground, in chunks of at most four minutes, one Lean process at
    a time.
- **Resources.** Peak RSS was 2.67 GB (`Efficiency`-area modules). The longest module was 69 s.
  Per-module start, end, time and max RSS are in every log.

### 6.2 Checks

- **Checkpoints.** `logs/checks-cp1.log` … `checks-cp4.log` record the module checks at each
  checkpoint.
- **Final sweep** (`logs/sweep.log`, proof-branch `bc53a51`). All 143 modules of `order-final.txt`
  passed, exit 0, including `Games/Efficiency` and the downstream `Advantage`,
  `Bridges/Experiments`, `Protocols`, `ZeroKnowledge/Interaction`, `Bridges/Strategies` and the
  `Bridges` facade. The new modules have no error and no warning.
- **Admissions** (`logs/sorry-census.txt`). 18 sorry warnings. This is `base-sorries.txt` (22)
  minus exactly the four `Games/Efficiency` targets. The owner check of `Games/Efficiency` has no
  sorry warning.
- **Axioms** (`logs/axioms.log`, `seal/AxiomsS2b.lean`). The four targets, `hRaw_spec`,
  `iRaw_spec`, `eval_buildTree_bridge` and `canonWord_eq` use
  `[propext, Classical.choice, Quot.sound]`. `buildComp_of_replaysFrom` uses `[propext, Quot.sound]`.
- **Lint.** `python3 -I scripts/campaign_style_lint.py TCSlib/Cryptography/Games --check8b` gives
  0 FAIL and 0 WARN both before (14 files, base worktree) and after (20 files)
  (`logs/lint-before.log`, `logs/lint-after.log`).

### 6.3 Seal (`logs/seal-scan.log`, `logs/seal.log`, sources in `seal/`)

- **Scan** (`SealScan.lean`). The roots are every declaration of the six helper modules plus the
  four targets: 262 roots, 316 declarations scanned with their auxiliary declarations (matchers,
  `proof_`, `eq_`, internal names).
  - **89 foreign TCSlib definitions** were found. Of these, **69 are non-reducible and sealable**.
    They include `pairEncode`, `pairDecode`, `pairFstD`, `pairSndD`, `PolyExpr.eval`,
    `PolyTimeComputable`, `NUPPT.{output, runAt, runAtL, layout, in*, coinLen, ofPolyTime,
    toComp, toCompOn, toOracleAdversary, coinsCongr, advInput}`, `StateLoop.orbit`,
    `GGMRed.stateLoopFun`, `buildComp`, `simulate`, `OracleComp.{bind, CostBoundedBy, evalFn}`,
    `MachineCodec.encodeLog`, `bitCodec`, `decodeBitMove`, `encodeBitMove`, `zeroBits`,
    `decodeFin`, `decodeOracleMove`, `encodeHist`, `buildTree`, `QueryTree.eval`.
  - Helper definitions are also sealed wherever another module uses them, for example
    `canonWord`, `fixLen`, `actLoop`, `iRaw` and `iImpl` inside `Efficiency.lean`.
  - **Instances:** the scan flags every instance, and none of the foreign definitions is a TCSlib
    instance.
  - **Not sealable (20).** Reducible abbreviations, projections and auxiliary recursors such as
    `NUPPT.Coins`, `bitSpec`, `QueryLog`, `QueryImpl`, `unifSpec`, `QueryTree`/`.ret`/`.query`,
    `OracleSpec.dom/rng`, `MachineCodec.decodeMove/encodeEntry/timeout`, `NUPPT.advice/coins/adv`,
    `Move.casesOn`, `OracleComp.casesOn/brecOn/below`. These are notation.
- **Sealed copies.** Verbatim copies of each helper module and of `Efficiency.lean` were checked
  with every foreign definition they use made irreducible. Each copy imports only the original's
  imports. All seven elaborate with exit 0 and no warning (`Seal*.lean`). `PolyExpr.eval` was
  sealed too, and the code reads it only through `eval_add/mul/const/var`.
- **Controls.** Six readings through a body: `pairEncode`, `encodeLog []`, `EffFill.fixLen`,
  `PolyExpr.eval (.const 3)`, `buildComp` at budget 0, and `EffFill.actLoop`. **All six pass
  unsealed and fail sealed**, at lines 18, 21, 24, 27, 31 and 36 of `SealControlsSealed.lean`, so
  the seal is active.
- **Explicit-unfold scan** (`seal/RwIds.lean`, `logs/rwids.log`, `logs/rwids-files.tsv`).
  `irreducible` does not block `rw [f]`, `simp [f]` or `unfold f`, so a separate scan collected
  every identifier passed to `rw`, `rwa`, `simp`, `simp only`, `simp_rw`, `dsimp` or `unfold` in
  the added lines: 284 in total.
  - 234 are theorems and 41 are local hypotheses or text fragments.
  - The 9 definitions are each passed only in their own file: `canonFun` in `Strings`; `gPh`,
    `gLin`, `gS`, `gB`, `gCur`, `gLc`, `gC`, `gO` in `Interactive`.
  - No core, Mathlib or foreign TCSlib definition is passed. The scan found `simp only [id]` and the
    simproc `reduceCtorEq`, and commit 5 removed both.

**Readings disclosed: none of a foreign definition.**

## 7. Notes for the maintainer

- **Elaboration cost.** The new modules elaborate in under 15 s each. Two patterns were very slow when the
  terms were not syntactically identical: re-elaborating a `Σ` literal such as `⟨j, x', y⟩` inside a
  dependent invariant, and propagating an expected type into lemmas with many implicit section
  variables. `InteractiveSpec` avoids both by taking these terms from the goal (`_`) and by
  building the invariant in tactic mode (`beta_reduce`).
- **Scope of the statements.** As in the design, `B`'s running time is polynomial in `n + |z|`,
  and `B` is non-uniform.

**Final payload delivered — ready for maintainer review and the gate**
