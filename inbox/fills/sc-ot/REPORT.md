# Fill sc-ot — checkpoint 2 (Alice's side of `otProtocol_simulators`)

**Unit** `sc-ot` · **Worker** Claude · **Issue base** `107f1e8c218733eac12d6b9bee6fece441271317`
(`cryptography/pass-shelat-ch2-4`) · **Proof branch** `fill/sc-ot` (local), commits
`fc7d0366067738271851488a8d1d7d7240cb70f1` (checkpoint 1) and
`a643e566b57d450d4abdad7b8484215385179233` (checkpoint 2) · **Lean** 4.25.0, Mathlib at the base's manifest.

## Target status at checkpoint 2

| Target | Status |
|---|---|
| `otProtocol_polyTime` | **proved** (standard axioms only) |
| `otProtocol_simulators` | `sorry` (unchanged statement); Alice's side proved in the helpers (`OT.distAdv_realA_idealA_le`), Bob's side in the final delivery |

`otProtocol_hbcSecure` and `YaoReal.yaoProtocol_hbcSecure` still depend on the second target's
`sorry`.

## 1. Environment (addendum v1)

- **Preflight** (`evidence/logs/preflight.log`): 4 CPUs; cgroup v1 limit unlimited, so the
  headroom is `MemAvailable` = 16503980032 B = 15.37 GiB (floor 4 GiB); the clone's filesystem
  (ext4, `/dev/vda`) had 16496836608 B = 15.36 GiB free (floor 12 GiB): `PREFLIGHT PASS`. To get
  there the git worktree of this host's delivered `canonizer` fill (`/workspace/canon`, branch
  kept) was removed. No dependency tree was copied or moved.
- **Clone:** a new worktree `/workspace/scot` of the local repository, branch `fill/sc-ot` at the
  issue base; its sources match `SOURCE-SHA256SUMS` (159 files, `source-sha256.log`).
- **Cache:** the store (`~/.cache/mathlib`, `cache-store.log`) held 2403 archives (120576651 B)
  from this host's earlier fills of this campaign (not downloaded by this session). The narrowed
  `lake exe cache get` for the 74 roots (`mathlib-roots.txt`, the same list as `roots.txt`)
  reported "No files to download", decompressed 2082 files and exited 0 (`cache-get.log`). No
  zero-size olean among 2091 (`zero-size-oleans.log`); the probe importing
  `Mathlib.Algebra.BigOperators.Field` elaborates (`cache-probe.log`, `probes/CacheProbe.lean`).
- **Packages** (`packages-check.log`): `RESULT: all present packages match the manifest`
  (`doc-gen4`, `UnicodeBasic`, `BibtexQuery`, `MD4Lean` ABSENT; no module of the order imports
  them).
- **Bootstrap** (`bootstrap.log`): the 159 modules of `order.txt`, one `scripts/lean_check_tree.sh`
  call each (through `tools/check.sh`), in order: 159/159 status 0, no error; maximum RSS
  2726572 KiB. Sorry census = `base-sorries.txt` (31 declarations in 14 modules;
  `census-bootstrap.txt`, `census-bootstrap-vs-base.diff`: identical).
- **Host restart.** The VM restarted once during this checkpoint (after the downstream sweep,
  during the seal runs). The interrupted seal run (variant B-strict of `Efficiency.lean`) was
  rerun from the start; no log was moved or edited (the raw `.out` of that variant holds the rows
  of the completed runs only). It restarted once more during development work between the two
  checkpoints (a scratch check, not evidence); the checkpoint-2 checks ran afterwards, unbroken.

## 2. The proof

`otProtocol_polyTime := OT.polyTime_of_isOT T hH (otProtocol_isOT T H)`.

- **Shape** (`ObliviousTransfer/Shape.lean`, new). The helper modules cannot import the owned
  file (it imports them), so the protocol is described by a predicate on protocols: `OT.IsOT T H π`
  says that `π.P.next = OT.senderNext T H`, `π.V.next = OT.receiverNext T H` (the bodies of
  `otSender` and `otReceiver`, with `otMask`, `otKnown`, `otRaw` expanded; `OT.mask` is the body of
  `otMask`), that the coins are `coins_Gen` and `coins_Sample + coins_Sample`, five messages and
  Alice first. The owned file proves `otProtocol_isOT : OT.IsOT T H (otProtocol T H)` from its field
  equations (`otSender_next`, `otReceiver_next`, `otMask_eq`, `otKnown_eq`, `otRaw_eq`,
  `otSender_coins`, `otReceiver_coins`, `otProtocol_rounds`, `otProtocol_verifierFirst`). The
  module also has the messages on histories of length 0, 1, 2 and the five moves of a prover-first
  execution (`OT.exec_five`), hence the transcript `([y, []], [i, z, []])`
  (`OT.transcriptWith_isOT`). These are reused by the simulator proofs.
- **Efficiency** (`ObliviousTransfer/Efficiency.lean`, new).
  - Alice's raw function `OT.senderRaw` reads the history length off the encoded history `w`
    by the emptiness tests `w = []` and `snd w = []` (`polyTimeComputable_isNil`), and branches
    (`polyTimeComputable_ite`). The branches are `Gen`'s output (`OT.genRaw`), the two masks
    (`OT.maskRaw`: the inverter on the all-`true` tape `polyTimeComputable_unaryPoly`, `H`, XOR)
    and `[]`. Bob's `OT.receiverRaw` adds a third test and uses the sampler on the two coin blocks
    (`polyTimeComputable_pairTakePoly`/`DropPoly`) and `eval_poly`.
  - `OT.senderRaw_advInput`/`OT.receiverRaw_advInput`: on the raw input of an activation they
    compute `senderNext`/`receiverNext` for every history (cases `[]`, `[m]`, two, three or more
    messages; `Gen`, the sampler and the inverter are uniform, `NUPPT.runAtL_eq_output_layout`).
    So `NUPPT.ofPolyTimeUniform` of them, with coins `coins_Gen` and `coins_Sample + coins_Sample`,
    witnesses `Strategy.Efficient` for both parties.
  - Messages (`OT.exists_messages_le`): `|i| ≤ Q₁(n)` (`Gen`'s `runLenPoly`), the samples
    `≤ Q₂(n)` (the sampler's `runLenPoly` at `Q₁`), the evaluation `≤ Q₃(n)` (`eval_poly`'s
    bound at `2Q₁ + 2 + Q₂`), masks one bit each; `B = Q₁ + (3(Q₂ + Q₃) + 2) + 5`.
    `OT.length_runAtL_le` is the list form of `NUPPT.length_runAt_le_runLenPoly`.
- **Owned file** (671 → 702 lines): imports of the two helpers, `## Contents`, the new
  `otProtocol_isOT`, the proof of `otProtocol_polyTime` and its sketch rewritten to describe the
  delivered proof, and the `## Main results` status of the target. The title keeps
  "(statement phase)" until the final delivery.

### New declarations (all in namespace `TCSlib.Cryptography.SecureComputation`)

- Owned file: `otProtocol_isOT`.
- `OT.` in `Shape.lean`: `mask`, `mask_eq`, `senderNext`, `senderNext_eq`, `receiverNext`,
  `receiverNext_eq`, `IsOT`, `isOT_iff`, `senderNext_nil`, `senderNext_single`, `senderNext_pair`,
  `receiverNext_single`, `receiverNext_pair`, `exec_five`, `transcriptWith_isOT`.
- `OT.` in `Efficiency.lean`: `headD_eq_pairFstD`, `pairSndD_nil'`, `getD_one_eq`,
  `runAtL_eq_layout`, `advInput_layout`, `genRaw`, `genRaw_eq`, `polyTimeComputable_genRaw`,
  `maskRaw`, `maskRaw_eq`, `polyTimeComputable_maskRaw`, `senderRaw`, `senderRaw_eq`,
  `polyTimeComputable_senderRaw`, `genRaw_layout`, `maskRaw_layout`, `getD_zero_eq`,
  `getD_one_eq'`, `senderRaw_advInput`, `knownRaw`, `knownRaw_eq`, `rawRaw`, `rawRaw_eq`,
  `outRaw`, `outRaw_eq`, `pairRaw`, `pairRaw_eq`, `receiverRaw`, `receiverRaw_eq`,
  `polyTimeComputable_receiverRaw`, `knownRaw_layout`, `rawRaw_layout`, `receiverRaw_advInput`,
  `length_runAtL_le`, `length_zipWith_singleton_le`, `length_mask_le`, `exists_messages_le`,
  `polyTime_of_isOT`.

Every public `def` has its `_eq`/`_iff` reader; no `@[simp]` was added.

## 2b. Checkpoint 2: Alice's side

- **The simulators' shape** (`ObliviousTransfer/Simulators.lean`, new). As for the protocol, the
  helpers restate the simulators' raw functions (`OT.simSeg`, `OT.simIndex`, `OT.simSampled`,
  `OT.simAView`, `OT.simZbit`, `OT.simZpair`, `OT.simBView`: the bodies of `coinSeg`, `simIdx`,
  `simSample`, `otSimAFun`, `otSimZb`, `otSimZ`, `otSimBFun`) and the predicates `OT.IsSimA`,
  `OT.IsSimB` (coins and run equation). The owned file proves `otSimA_isSimA` and
  `otSimB_isSimB` from `otSimA_coins`, `runAt_otSimA`, `otSimB_coins`, `runAt_otSimB` and the
  simulator-function readers. The module also has the coin spaces: `OT.splitLen` (a tape of length
  `a + b` as two blocks, `splitCoins` after a length cast), `OT.realCoins` (the real
  `ExecCoins ≃ Coins_Gen × (Coins_Sample × Coins_Sample)`), `OT.simACoins`, `OT.simBCoins`, with
  the `_ofFn` readers giving the assembled tapes; the simulated views on assembled tapes
  (`OT.simAView_layout`, `OT.simBView_layout`); and the OT inputs read as bits (`OT.inA2`,
  `OT.inB1`, `OT.ofFn_f_fst`, `OT.ofFn_f_snd`, from the published `otFunctionality_*` readers).
- **Alice's side** (`ObliviousTransfer/ViewA.lean`, new).
  - `OT.realA_realCoins`, `OT.idealA_simACoins`: on `(r, s₁, s₂)` Alice's real sampler is
    `⟨⟨⟨1^n, a⟩, ⟨r, [y, []]⟩⟩, [a_b]⟩` with `y = ⟨eval ⟨i, w₁⟩, w₂⟩` (`⟨w₂, eval ⟨i, w₁⟩⟩` if
    `b`), the ideal one the same with `y = ⟨w₁, w₂⟩`, `w_j = Sample(i; s_j)`, `i = index n r`
    (the transcript `OT.transcriptWith_isOT`, Bob's output `otProtocol_outV` passed as a
    hypothesis, `S_A`'s view `OT.simAView_layout`).
  - `OT.statClose_eval_sample`: at every generated index, `eval ⟨i, Sample(i; s)⟩` is
    `2δ(n)`-close to `Sample(i; s)` under `SampleClose δ` (`δ` to the uniform element mapped by
    `encD ∘ perm`, `0` from `perm` being a bijection, `δ` back to the sample by canonical
    decoding).
  - `OT.statClose_prod_of_forall`: closeness for every value of a shared first coordinate gives
    closeness of the joint samplers.
  - `OT.distAdv_realA_idealA_le`: every distinguisher's advantage on Alice's side is at most
    `2δ(n)` (`acceptProb_comp_equiv` along the two coin equivalences, `StatClose.prod` with the
    identical raw sample, swapping the blocks when `b`, `distAdv_le_of_statClose`). The edge cases
    `b = 0, 1` are the two branches; small `n` needs nothing, `SampleClose δ` holding at every `n`.
- **Owned file** (checkpoint 2 state, 730 lines): imports of `Simulators` and `ViewA`, the two
  shape lemmas, `## Contents` and `## Main results` updated. The target keeps its `sorry`.

New declarations of checkpoint 2: owned file `otSimA_isSimA`, `otSimB_isSimB`; `OT.` in
`Simulators.lean`: `splitLen`, `splitLen_symm_ofFn`, `simSeg`, `simSeg_eq`, `simIndex`,
`simIndex_eq`, `simSampled`, `simSampled_eq`, `simAView`, `simAView_eq`, `simZbit`, `simZbit_eq`,
`simZpair`, `simZpair_eq`, `simBView`, `simBView_eq`, `IsSimA`, `isSimA_iff`, `IsSimB`,
`isSimB_iff`, `simSeg_layout`, `length_ofFn_coins`, `simIndex_layout`, `simSampled_layout`,
`simAView_layout`, `simBView_layout`, `realCoins`, `realCoins_symm_fst_ofFn`,
`realCoins_symm_snd_ofFn`, `simACoins`, `simACoins_symm_ofFn`, `simBCoins`, `simBCoins_symm_ofFn`,
`inA_eval`, `inB_eval`, `inA2`, `inA2_apply`, `ofFn_inA2`, `inB1`, `inB1_apply`, `ofFn_inB1`,
`ofFn_eq_inB1`, `ofFn_f_fst`, `ofFn_f_snd`; in `ViewA.lean`: `statClose_prod_of_forall`,
`statClose_eval_sample`, `realA_realCoins`, `idealA_simACoins`, `distAdv_realA_idealA_le`.

## 3. Overlap and reuse (checkpoints 1 and 2)

Searches: `logs/checkpoint1-searches.log` and `logs/final-searches.log` (TCSlib at the base,
Mathlib/Batteries, Lean core).

| New declaration | Nearest relative | Relation | Why not reused |
|---|---|---|---|
| `OT.mask`, `OT.senderNext`, `OT.receiverNext` | `otMask`, `otSender`, `otReceiver` (`ObliviousTransfer.lean:99,112,160`) | restatements of the bodies (with `otKnown`/`otRaw` expanded) | the helpers cannot import the owned file; `otProtocol_isOT` proves the equality from the published field equations |
| `OT.exec_five`, `OT.transcriptWith_isOT` | `exec_succ`/`exec_zero` (`ZeroKnowledge/Interaction.lean:262,266`); the unfolding inside `otProtocol_outV` | the five-move unfolding, stated once | no five-move lemma exists |
| `OT.headD_eq_pairFstD` | `Strategy.pairFstD_encodeMsgs` (`Interaction.lean:143`) | its symmetric form | used as a rewrite from left to right |
| `OT.pairSndD_nil'`, `OT.getD_one_eq` | private `pairSndD_nil` (`Asymptotic/BlockEncryptor.lean:156`); `GI.pairSndD_encodeMsgs`, `GI.encodeMsgs_eq_nil_iff` (`GraphIsomorphism/EfficiencyRep.lean:93,110`) | re-derived from the public `length_pairSndD_le` (`ClassNP/PolyTimeBlockLoop.lean:187`) | the first is private; `EfficiencyRep` comes after the owned module in `order.txt`, so importing it would reorder the bootstrap |
| `OT.runAtL_eq_layout` | `NUPPT.runAtL_eq_output_layout` (`Randomized/Closure.lean:159`) | its uniform specialization | removes the advice |
| `OT.advInput_layout` | `NUPPT.advInput_eq`, `NUPPT.layout_eq` | composite of the two | used to match `NUPPT.runAtL_ofPolyTimeUniform` |
| `OT.getD_zero_eq`, `OT.getD_one_eq'` | `List.getD_cons_zero`, `List.getD_cons_succ` (core `Init/Data/List/Lemmas.lean:330`) | the `headD` forms for every list | the core lemmas cover the cons case only |
| `OT.length_runAtL_le` | `NUPPT.length_runAt_le_runLenPoly` (`Asymptotic/CollectionsHelpers.lean:132`) | its list form, proved from it through `List.ofFn_get` | the strategies' tapes are lists |
| `OT.length_zipWith_singleton_le`, `OT.length_mask_le` | `List.length_zipWith` | a two-line consequence | — |
| raw functions `OT.genRaw` … `OT.receiverRaw` and their lemmas | `GI.giProver_efficient` and the GI/3-col machines (`GraphIsomorphism/EfficiencyRep*.lean`, `ThreeColoring/Machines.lean`) | the same construction pattern (raw layout function, `ofPolyTimeUniform`) for other strategies | specific to Protocol 160.4 |
| `OT.simSeg`, `OT.simIndex`, `OT.simSampled`, `OT.simAView`, `OT.simZbit`, `OT.simZpair`, `OT.simBView` | `coinSeg`, `simIdx`, `simSample`, `otSimAFun`, `otSimZb`, `otSimZ`, `otSimBFun` (`ObliviousTransfer.lean:357–513` at the base) | restatements of the bodies | the helpers cannot import the owned file; `otSimA_isSimA`/`otSimB_isSimB` prove the equality from the published readers |
| `OT.splitLen`, `OT.splitLen_symm_ofFn` | `splitCoins`, `ofFn_splitCoins_symm` (`Asymptotic/CollectionsHelpers.lean:147,172`); `Fin.appendEquiv` | `splitCoins` after the cast `Fin c ≃ Fin (a + b)`, proved from `ofFn_splitCoins_symm` | the coin lengths are `coinLen`/`PolyExpr.eval` terms equal to, not syntactically, sums |
| `OT.realCoins`, `OT.simACoins`, `OT.simBCoins`, `OT.length_ofFn_coins` | `Collection.owfCoinsEquiv`, `NUPPT.coinsEquivPoly` (`Asymptotic/Collections.lean:695`, `Randomized/PPT.lean`) | coin equivalences of the same kind for these coin spaces | specific coin layouts |
| `OT.inA2`, `OT.inB1`, `OT.ofFn_f_fst`, `OT.ofFn_f_snd` | `otFunctionality_inA`, `_inB`, `_outA`, `_f_snd_apply` (`SecureComputation/Defs.lean:202–232`) | consequences of the published readers | the cast inputs are needed as `Fin 2`/`Fin 1` functions for `otProtocol_outV` |
| `OT.statClose_prod_of_forall` | `StatClose.prod`, `StatClose.abs_uprob_sub_le_prod` (`Asymptotic/Sampling.lean:237,262`) | the dependent form (second sampler depending on the shared first coordinate), by `uprob_prod` and `abs_uexp_sub_le` | `StatClose.prod` needs independent coordinates |
| `OT.statClose_eval_sample` | the closeness step `hclose` inside `TrapdoorCollection.tdpBitScheme_singleBitSecure` (`Encryption/PublicKey/Trapdoor.lean:425`) | a related use of `SampleClose`; here `eval ⟨i, Sample⟩` against `Sample` itself | different samplers |

No private lemma was copied. **Promotion requests:** `OT.exec_five` (beside `exec_succ` in
`ZeroKnowledge/Interaction.lean`) and `OT.length_runAtL_le` (beside
`NUPPT.length_runAt_le_runLenPoly` in `Asymptotic/CollectionsHelpers.lean`) are general; they may
be promoted at landing; so may `OT.statClose_prod_of_forall` (beside `StatClose.prod` in
`Asymptotic/Sampling.lean`).

## 4. Scope requests

None. No frozen file was edited.

## 5. Checks

**Checkpoint 1** (commit `fc7d0366`):
- **Module checks** (`logs/checkpoint1-checks.log`): the two helpers, the owned module and every
  module after it in the order (40 modules: `order.txt` with `ObliviousTransfer/Shape` and
  `ObliviousTransfer/Efficiency` inserted before `ObliviousTransfer`), status 0. Census of that
  sweep (`logs/census-checkpoint1-checks.txt`): the owned module's only `sorry` is
  `otProtocol_simulators`; the other modules' rows equal `base-sorries.txt`.
- **Axioms** (`logs/checkpoint1-axioms.log`, `probes/AxiomsCP1.lean`): `otProtocol_polyTime`,
  `otProtocol_isOT` and every declaration of `Shape.lean` and `Efficiency.lean` (55): only
  `propext`, `Classical.choice`, `Quot.sound` (subsets), no `sorryAx`.
- **Seals** (`seal-cp1/`): whole-file seals of the three changed or new files, in all four
  variants (A = `PolyExpr.eval` open, B = sealed; strict and coe), with the sealed copies in
  `seal-cp1/sources/`: **12/12 runs status 0, 0 errors** (`seal-*.jsonl`, raw `seal-*.out`;
  counted with `error[:(]`).
- **Width** (`logs/checkpoint1-width.log`), **lint** (`logs/checkpoint1-lint.log`,
  `logs/checkpoint1-lint-diff.log`: 92 FAIL / 101 WARN, line sets identical to the base),
  **reproduction** (`logs/checkpoint1-repro.log`).

**Checkpoint 2** (commit `a643e566`):
- **Module checks** (`logs/checkpoint2-checks.log`): `Shape`, `Efficiency`, `Simulators`,
  `ViewA`, the owned module and every module after it (42 modules, from `order.txt` with the four
  helpers inserted before `ObliviousTransfer`), status 0. Census (`logs/census-checkpoint2-checks.txt`):
  unchanged from checkpoint 1.
- **Axioms** (`logs/checkpoint2-axioms.log`, `probes/AxiomsCP2.lean`): every declaration of
  `Simulators.lean` and `ViewA.lean`, `otSimA_isSimA`, `otSimB_isSimB` and `otProtocol_polyTime`
  (52): only `propext`, `Classical.choice`, `Quot.sound` (subsets), no `sorryAx`.
- **Seals** (`seal-cp2/`): the owned file, `Simulators.lean` and `ViewA.lean`, four variants:
  **12/12 runs status 0, 0 errors**; sealed copies in `seal-cp2/sources/`.
- **Width** (`logs/checkpoint2-width.log`: owned file 730 lines, `Simulators` 418, `ViewA` 186, no
  line over 100), **lint** (`logs/checkpoint2-lint.log`, `logs/checkpoint2-lint-diff.log`, on an
  archive of the commit: 92 FAIL / 101 WARN, line sets identical to the base).
- **Patches** (`patches/`, `patches/COMMITS.tsv`): two commits. Reproduction
  (`logs/checkpoint2-repro.log`): `git am` at the base in a scratch clone (`/tmp/scot-repro`,
  deleted afterwards), with the committer data of `COMMITS.tsv`: every hash reproduced.

## 6. Next (final)

Bob's side (written and compiling locally): `ObliviousTransfer/Predictor.lean`, the view-building
distinguisher `OT.viewDist` (on `⟨i, ⟨s', [β]⟩⟩` with coins `s₁ ++ ρ` it runs `D` on Bob's view
with tape `s₁ ++ s'` and unselected mask `β ⊕ a_{1−b}`), run inside `tdpPredictor` of
Algorithm 104.3; `ObliviousTransfer/ViewB.lean`, the signed-predictor identity for uniform coin
challenges, Bob's real and ideal acceptance probabilities, the bound `|ε_false(n)| + |ε_true(n)|`
from `hEHC` for the inputs' bits, and the negligible sum over the sixteen predictors; then the
target from the two sides, the docstrings, the base seals and the paired controls.

## 7. Evidence (`evidence/`, manifest `evidence/SHA256SUMS`)

- `logs/`: `preflight.log`, `source-sha256.log`, `order.txt`, `mathlib-roots.txt`,
  `cache-store.log`, `cache-get.log`, `packages-check.log`, `zero-size-oleans.log`,
  `cache-probe.log`, `bootstrap.log`, `census-bootstrap.txt`, `census-bootstrap-vs-base.diff`,
  `checkpoint1-checks.log`, `census-checkpoint1-checks.txt`, `checkpoint1-axioms.log`,
  `checkpoint1-searches.log`, `checkpoint1-width.log`, `base-lint.log`, `checkpoint1-lint.log`,
  `checkpoint1-lint-diff.log`, `checkpoint1-repro.log`; `checkpoint2-checks.log`,
  `census-checkpoint2-checks.txt`, `checkpoint2-axioms.log`, `checkpoint2-width.log`,
  `checkpoint2-lint.log`, `checkpoint2-lint-diff.log`, `checkpoint2-repro.log`,
  `final-searches.log` (the searches for checkpoint 2 and the final helpers).
- `seal-cp1/`, `seal-cp2/`: `seal-{As,Ac,Bs,Bc}.jsonl` and `.out`, `sources/` (sealed copies).
- `probes/`: `CacheProbe.lean`, `AxiomsCP1.lean`, `AxiomsCP2.lean`.
- `tools/`: the scripts used.

The top-level `SHA256SUMS` lists every delivered file under `inbox/fills/sc-ot/` except itself.
