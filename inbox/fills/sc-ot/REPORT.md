# Fill sc-ot — checkpoint 1 (`otProtocol_polyTime`)

**Unit** `sc-ot` · **Worker** Claude · **Issue base** `107f1e8c218733eac12d6b9bee6fece441271317`
(`cryptography/pass-shelat-ch2-4`) · **Proof branch** `fill/sc-ot` (local), checkpoint commit
`fc7d0366067738271851488a8d1d7d7240cb70f1` · **Lean** 4.25.0, Mathlib at the base's manifest.

## Target status at this checkpoint

| Target | Status |
|---|---|
| `otProtocol_polyTime` | **proved** (standard axioms only) |
| `otProtocol_simulators` | `sorry` (unchanged statement; checkpoints 2 and final) |

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
  of the completed runs only).

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

## 3. Overlap and reuse (checkpoint 1)

Searches: `logs/checkpoint1-searches.log` (TCSlib at the base, Mathlib/Batteries, Lean core).

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

No private lemma was copied. **Promotion requests:** `OT.exec_five` (beside `exec_succ` in
`ZeroKnowledge/Interaction.lean`) and `OT.length_runAtL_le` (beside
`NUPPT.length_runAt_le_runLenPoly` in `Asymptotic/CollectionsHelpers.lean`) are general; they may
be promoted at landing.

## 4. Scope requests

None. No frozen file was edited.

## 5. Checks at this checkpoint

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
  counted with `error[:(]`). The base seals and the paired controls come with the final delivery.
- **Width and size** (`logs/checkpoint1-width.log`): every line within 100 characters; files of
  702, 206 and 519 lines.
- **Lint** (`logs/base-lint.log`, `logs/checkpoint1-lint.log`, `logs/checkpoint1-lint-diff.log`):
  92 FAIL / 101 WARN at the base and at this checkpoint (checked on an archive of the checkpoint
  commit); the FAIL/WARN line sets are identical.
- **Patches** (`patches/`, `patches/COMMITS.tsv`): one commit. Reproduction
  (`logs/checkpoint1-repro.log`): `git am` at the base in a scratch clone (`/tmp/scot-repro`,
  deleted afterwards), with the committer data of `COMMITS.tsv`: every hash reproduced.

## 6. Next

Checkpoint 2 (Alice's side, written and compiling locally): `ObliviousTransfer/Simulators.lean`
(the simulators' shapes `OT.IsSimA`/`OT.IsSimB`, the coin equivalences, the views on assembled
tapes) and `ObliviousTransfer/ViewA.lean` (`OT.statClose_eval_sample`: `eval ⟨i, Sample⟩` is
`2δ(n)`-close to `Sample` at every generated index; `OT.distAdv_realA_idealA_le`: the bound `2δ(n)`).
Final: Bob's side through a signed predictor for `⟨i, s'⟩` challenges and the view-building
distinguisher run inside `tdpPredictor`.

## 7. Evidence (`evidence/`, manifest `evidence/SHA256SUMS`)

- `logs/`: `preflight.log`, `source-sha256.log`, `order.txt`, `mathlib-roots.txt`,
  `cache-store.log`, `cache-get.log`, `packages-check.log`, `zero-size-oleans.log`,
  `cache-probe.log`, `bootstrap.log`, `census-bootstrap.txt`, `census-bootstrap-vs-base.diff`,
  `checkpoint1-checks.log`, `census-checkpoint1-checks.txt`, `checkpoint1-axioms.log`,
  `checkpoint1-searches.log`, `checkpoint1-width.log`, `base-lint.log`, `checkpoint1-lint.log`,
  `checkpoint1-lint-diff.log`, `checkpoint1-repro.log`.
- `seal-cp1/`: `seal-{As,Ac,Bs,Bc}.jsonl` and `.out`, `sources/cp1{As,Ac,Bs,Bc}/` (sealed copies).
- `probes/`: `CacheProbe.lean`, `AxiomsCP1.lean`.
- `tools/`: the scripts used.

The top-level `SHA256SUMS` lists every delivered file under `inbox/fills/sc-ot/` except itself.
