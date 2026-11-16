# Paused for relocation · 2026-11-16 02:51 UTC

The user explicitly requested a checkpoint and will pause/resume later. Do not resume
proof work until the user resumes. This is a local relocation snapshot, not checkpoint3
proof delivery. Checkpoint2 is already pushed. Full objective remains unfinished.

## Durable state and authorization

- Lead checkout: /Users/seyoonr/.codex/worktrees/sc-yao/tcslib-exchange
  branch fill/sc-yao, local only. Proof HEAD:
  9b7b1147b2b27a1bfb9845f7b9c5ab104574c860.
- Latest delivered checkpoint2: 816971fc6922646f056a47efd41b1407f762320d,
  exchange/pass-shelat-ch5-8, only inbox/fills/sc-yao/.
  Delivery checkout: /Users/seyoonr/.codex/worktrees/sc-yao-delivery/tcslib-exchange;
  branch codex/sc-yao-delivery, clean at pause.
- yaoHybrid_polyTime proved: full narrowed sweep224/224 PASS, standard axioms only,
  no admitted dependency. yaoHybrid_simulators still has its BASE admission/sketch.
- Yao currently1062 lines,1090 combined with sc-garble; maximum1200.
- User authorized full objective, proof edits, scoped commits/pushes and lean-slot checks
  despite AGENTS prohibition: “Yes, follow the full objective and wrapper rules”.
- Four extra helper imports already approved; exact requests/answers in
  evidence/scope-request/: ThreeColoring.Machines, FromPRF.ReductionMachine,
  FromPRF.HybridLemmas, Asymptotic.BlockEncryptor. Do not ask again.
- Read objective first on resume:
  /Users/seyoonr/.codex/attachments/41fc96df-a223-4248-a1bb-f1acfaa74483/goal-objective.md
  Issued pack /private/tmp/sc-yao-issued/outbox/fills/sc-yao/. Packs/pins verified.

## Host and proof discipline

Every Lean/Lake/tree-check command through /private/tmp/sc-yao-lean-slot.sh;
LEAN_SLOT_TAG=sc-yao (children sc-yao-a/b/c), at most THREE host-wide processes.
Never set LEAN_SLOT_DIR/LEAN_SLOTS, never lake build; python3 -I only.
Root owns .lake/packages; child worktrees symlink read-only, separate olean trees.
Root TCSLIB_OLEANS is .lake/sc-yao-oleans under lead checkout.
Fresh macOS memory/disk/orphan-process preflight before resumed checks.
Only lead edits frozen Yao.lean/DAGCircuit.lean/Uniform.lean, commits and delivery.
No helper imports or names Yao definitions. Do not duplicate seed/message/hybrid semantics
in helpers; pass these as parameters with equations. Cite frozen sc-garble statements.
Maintain docstrings/sketches, Rule10 readers/seals, exact source hashes, all raw evidence.
Do not broaden frozen scope. See issued brief/ruling for exact requirements.

## Completed after checkpoint2, currently outside proof commits

Lead helper sources (all whole declarations, no new admissions):
- GateOccurrences, RelabelGarbling, CoinSeedRelabel, GateHybrids, GateHybridMessage.
- FakeObjects/FakeProgram/FakeMessage/FakeSimulator and refactored RowFromCoins,
  TablesFromCoins; generic fake simulator fixed before distinguisher, PTC derived internally.
- SliceReduction: exists_adviceReduction, reconstruction_negligible (max finite advice),
  distAdv_fibers_le, distAdv_chain_le, chain_negligible. All5 normal and4seals PASS.
- SimulationBound: output/statistical switch and final common-bound assembly;
  strategyTapeEquiv/readers and acceptProb_firstTape. Latest normal PASS; older seals/trace
  PRE-DATE added tape transport: rerun4seals and full stored-constant trace.
- OTAnswerWords: answersB length, active-answer equality, answersA_nil. Normal PASS;
  four seals/trace pending. SY5 disclose general sc-compose length_answersA/B overlap.
- AliceStatistical: generic Alice real→ideal statistical coupling. Normal PASS;
  four seals/trace pending.
- Lead facade is STALE: regenerate imports/meaningful Contents after all integration;
  normal-check facade+Yao+YaoReal and rerun4facade seals. Do not commit stale facade.
- Root actual probes AliceStatGlue/BobAnswersGlue/BobViewGlue/InputValuesGlue all PASS,
  saved under evidence/probes. They provide concrete final-target instantiation recipes.

## Verified handoffs not yet integrated in lead

- a CoordinateSwap v5:
  /private/tmp/sc-yao-a-coordinate-handoff-v5-20261116/
  66files incl manifest, all4seals PASS, 15owned-module trace296 constants std/noadmission.
  Generic matching coordinate-swap equiv; acceptProb_swap/fill handle arbitrary retained P,
  actual XOR shifts and padding; no uniform-full-permutation assumption.
- a BobViewShape v6:
  /private/tmp/sc-yao-a-bobview-handoff-v6-20261116/
  78files incl manifest, clean normal0errors/0warnings/style0;4seals PASS;
  full16-owned-module trace297 constants std/noadmission, aggregate64/64seals PASS.
  encode_viewV_eq with actual raw inputs/OT reply adapters, no extra premise.
- c SamplerEndpoints:
  /private/tmp/sc-yao-c-verified-sampler-endpoints.tar.gz plus adjacent manifest.
  Archive SHA256: 0c44358d91abec76d6f3b6160d8a721b685fc8226f00aca7066b8f4d96044222.
  238lines,8source/10stored; normal07/4seals/trace/style PASS.
  Real sampler is parameter+hReal, pairEncode(view.encode)(AliceOutput) order.
  real↔stage0 via full seed relabel; final stage↔fixed FakeSimulator ideal endpoints.
Verify manifests, copy sources/evidence without overwriting history, normal-check lead.

## Exact remaining security route

b builds all-occurrence selected-key challenge description/reconstruction and polynomial
advice; c builds actual tape↔retainedRest×independent key/nonce Data; a completed generic
coordinate-swap transport. Retained Rest must contain ALL actual XOR shifts and unused
blocks; never claim uniform full permutations. Repeated key values are allowed, using
symbolic label separation. Two gate substeps (2i/2i+1) suffice, including constant/one-input
rows. Challenge joint length7n+2, inner4n+2, direct slice(0,n), outer slice(2n,4n+2).

Next assemble exact sampler law/reconstruction and B1 per-neighbor negligible bound with
SliceReduction.reconstruction_negligible, average retained coordinates via fibers, chain
at most2S via chain_negligible. SamplerEndpoints gives endpoints. FakeSimulator provides
fixed uniform SB. AliceStatistical plus actual correctness gives Alice δ; Bob output switch
uses same δ; SimulationBound combines δ+μ. Instantiate only in target body, line budget
~110 plus shortening original47line security sketch (~40space). Generic view/answer
contracts reduce concrete boilerplate.

Do not mark objective complete on efficiency alone. Full target and final delivery still
required unless explicitly taking brief's allowed partial-final route with all disclosures.

## Audits and tools to resume

- Checkpoint2 full224-module sweep PASS; source/evidence manifests and patch-hash
  reproduction checked. evidence/checkpoint2-sweep-summary.json (32→31 base admissions,
  only yaoHybrid_polyTime removed). Target std axioms, sorryclosure[].
- Efficiency canonicalA strict/coe PASS. B17errors=15baseline+2call-input applications
  using exempt PolyExpr.eval equality; attribution in evidence/efficiency-seal-summary.json.
- Frozen reader audits unchanged errors,24necessity controls expected; all historical raw
  logs retained including initial basename collision archiver and corrected pathhashrunner.
- Lead foreign explicit-definition scan8946files/1355refs:9same-basename local-hypothesis
  candidates, all resolved as local,0foreign-definition violations. Exact source contexts in
  evidence/unfold/explicit-definition-review-resolution.json (verified exists at pause).
  Rerun after final new helpers; seals also needed for TCSlib foreign implicit reduction.
- evidence/tools/check_modules.py --phase NEW_PHASE [modules] retains source+SHA/logs,
  wrapper/time, both error forms, fresh olean, exclusive per-tree driverlock; never reusephase.
- make_seals.py +run_probes.py: A/B ×strict/coe, full-file -DmaxErrors=0, controls;
  stored axioms trace every new owned declaration, admission/axiom closures.
- prepare_payload.py/finalize_payload.py export exact refs, whole patches, COMMITS.tsv
  signing column, git-am hash reproduction, exact manifests. See checkpoint2 stages:
  /private/tmp/sc-yao-checkpoint2-stage and -reproduce.
- Remaining checkpoint3/final: headers, style, clash(base/sc-garble/sc-ot/sc-compose),
  duplicate/overlap disclosures, SY4 promotion drafts, Gate27 mapping, full expanded sweep,
  helper/target seals and dependencies, report attribution, exact payload manifests and
  patch reproduction. Delivery only inbox/fills/sc-yao, rebase before non-force push;
  final ZIP with sc-yao/ root. Do not push source branch.

## Relocation snapshot

This RESUME supersedes the previous relocation notes. Historical RESUME is preserved in
  evidence/checkpoints/relocation-20261116T0251Z/RESUME.previous.md
Exact current source, status and evidence snapshot inventory/archive recorded alongside it.
Agent pause notes and final process verification are appended below before pausing goal.

## Final agent pause state (all stopped)

- a: no live jobs. CoordinateSwap v5 and BobViewShape v6 fully audited, pending lead integration.
- b: /private/tmp/sc-yao-b-handoff-v5-paused/ and .tar.gz; archive SHA256
  83edc86cc395c187af1601ca020e649bc6737f45cd2f6408c8219da09a9e5de8.
  93files,8 b-owned sources plus checked root SliceReduction copy, all b5 logs/RESUME.
  SelectedTables.record_reconstruct normal04 PASS. Complete coordinate/row/plan core
  normal-pass. Remaining table/view lifting, polynomial advice bound, final b5 seals/trace.
  Two files only line-wrapped since last PASS; exact recheck boundary in b5/RESUME.md.
  Last session32001 finished; no live checks. Its note about c normal05 is stale: use normal10.
- c: /private/tmp/sc-yao-c-tape-values-checkpoint-20261116-pause/ and .tar.gz; SHA256
  644dbfc9e73972ad9fcd95df09f8a3e3e960293cc68d75373cebede8778c7544.
  TapeValues326lines/17public declarations, normal10 PASS0errors/0warnings, exact matching
  olean and normal01–10 evidence retained. Full tape↔Rest×Data, key/nonce-half/shift/unused
  block readers and derived permutation present. Next UNWRITTEN: actual seed_perm, seed_eq,
  seed_on_inverse. Final seals/trace/style pending. Last session85924 finished; no live checks.
- Lead verified all four directory manifests and all three archive hashes above (including
  SamplerEndpoints) before snapshot. No integration or new proof commit attempted for pause.

## Verified checkpoint archive and shutdown

- Local relocation archive (all4source/evidence trees plus pending immutable handoffs):
  evidence/checkpoints/relocation-20261116T0251Z/sc-yao-relocation-snapshot.zip
- 4,842 ZIP entries,48,248,174bytes compressed;915,460,737 uncompressed bytes. CRC verified.
- Archive SHA256: 7660a37c7aeafa84348934225795b1f01b4014b1ca4f702c3d8912ef2e33fb84.
- Full per-entry SHA256 inventory inside ZIP at sc-yao/SHA256SUMS; source-path inventory
  and archive checksum retained beside ZIP. Current checkpoint directory excluded from
  self-recursive evidence capture. Final RESUME/process notes are separate verified sidecars.
- Final process check2026-11-16T02:55:17Z: no live proof-check process; lead driverlock free;
  all3agents completed/paused, no retained live sessions. No check was interrupted midway.
- No new proof commit or delivery push during this relocation pause. Last committed proof
  remains9b7b1147; last pushed delivery remains816971fc. Resume allwork from these saved files.
