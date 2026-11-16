# sc-yao working state (not a checkpoint delivery)

Issue base: 6ce4658db08a1dc2a03a149987197660db078011.
Issued exchange: f41e1b4ddaff2a140c893d510bdd8d227f83fed8.
Proof branch: fill/sc-yao, local only. Lead worktree is sc-yao; agents a/b/c have separate
worktrees, packages symlinked to lead, separate TCSLIB_OLEANS and shared three-slot wrapper.

Both issued packs and all pinned source hashes passed their SHA-256 checks. Initial macOS
preflight: 6.060 GiB headroom, >150 GiB free; later long-elaboration measurement 5.589 GiB.
Lean 4.25.0 starts correctly. Original76 Mathlib roots: 2082 cached files unpacked; scoped
Coloring root:941; scoped Choose.Bounds root:566. All downloads0 (existing global cache
archives); each fetch exited0. Package pins11present/4documentaryabsent, zero mismatches.
The supplied184-module bootstrap passes with32baseline sorry warnings and0errors. Seven
approved import dependencies and HybridLemmas also pass (192 modules total).

Explicit user authorization resolved initial automatic-review refusal and AGENTS shell-check
conflict: full objective, commits/delivery, and lean-slot.sh checks are authorized. Three
extra helper imports were subsequently explicitly approved; verbatim requests/answers are
under evidence/scope-request/. No further scope request is pending.

Lead source ownership: Yao.lean, Uniform.lean, DAGCircuit.lean; CoinRead, BobIO, BobInit,
and eventual final strategy/glue/hub modules. Only approved readers have changed frozen files.
DAGCircuit.encode_parts avoids an existing encode_eq name in LogspaceUniformAdjBasic.
Exact-scope/header checker passes and both negative controls detect one violation each.
Name scan compares base, sc-garble, sc-ot and sc-compose; initial collision was fixed.

Lead rechecks pass for CoinRead, BobIO (including full output-vector layout), BobInit
(including initial-entry/list layouts), and merged agent helpers ChunkScanner, CoinGarbling,
Garbling, WordLists, DescriptionDecoder, RunWithHost, Decryption, FirstTagged, EvalGate,
GarbledRun, Lengths, OTInputs, TwoMoveViews. No target body has changed yet.

One BobIO elaboration was manually interrupted for source-directed instrumentation after
stack sampling (not a resource failure); its source/sample/raw log are retained. Explicit
function/padding normalization fixed the elaboration issue. Profile diagnostics then exposed
an unknown Boolean lemma and one missing comp normalization; repaired module passes.
BobInit layout required only Fin.coe_cast normalization; failed/source repair evidence kept.
The module runner now captures source snapshots and SHA256 before every future check.

Agent a owns decoder/scanner, garbling leaves, coin-addressing, WordLists and RowFromCoins;
its real row semantic bridge passes, with raw-row output-bit core factoring for fake rows
underway. Full table/key/pair program assembly remains.
Agent b owns generic runWith host, tagged decryption/search, evalGate, garbled run and
BobTables. Six modules pass; its full seals/controls/trace handoff is being finalized.
Agent c owns Lengths, OTInputs, TwoMoveViews and StatisticalSwitch/Alice statistical route.
The first3 modules and101 evidence files were verified/integrated from an immutable snapshot;
all12seals and8pairedcontrols have correct outcomes, all28constant closures contain no sorry.
StatisticalSwitch has the approved HybridLemmas import and completed dependency seed.

Remaining: complete garbler/Bob strategy machines and all input-shape glue; prove
yaoHybrid_polyTime; checkpoint1/2 payloads; continue full simulator route (Alice simulator,
Bob fake garbling and efficiency, coin bijections, all-occurrence B1 embeddings/hybrids);
final lead seals/control/header/lint/clash/axioms/dependency/sweep/evidence checks; scoped
proof commits/format-patch reproduction; delivery worktree commits/pushes and final ZIP.
Do not mark the goal complete on these infrastructure passes alone.


## Resumed work, 2026-11-15 23:53 UTC

The user explicitly resumed after relocating. Saved worktrees, archives and manifests were
intact, with no live leftover Lean process; resumed headroom was 7.327 GiB. No duplicate
check was started. Three agents resumed on their original owned modules and slot tags.

All actual Alice garbling-message and Bob evaluation programs now pass in the lead tree.
Concrete Alice.Efficient, Bob.Efficient, sender/receiver call-input and arbitrary-answer
message-bound probes all pass. Their assembled yaoHybrid_polyTime proof passed at
1057 lines (1085 with sc-garble's28), with no new sorry. Its source change is retained for
checkpoint2. Header scope passes after fixing the checker's mask to include a split Main
results bullet; its earlier false-positive raw output is preserved. Name scan:290 added
explicit names, zero clashes. Lint has no new FAIL; the sole new warning is the approved
SY-2 Yao size exception. Circuit reader WARN changes remove missing-reader entries.

Local infrastructure proof commits: ab507ce9e plus63c8abd51 (explicit size reader repair),
then the approved single hub import. The checkpoint1 payload keeps both original target
bodies and sketches; checkpoint2 will contain the efficiency proof. No delivery pushed yet.
All own helper seals completed so far pass. Agent a's original40 probes found exactly two
proof-only issues (negative gate-kind comparisons and a default size branch); repairs pass
normal checks, and repaired seals are running. Agent b's evaluator, BobProgram and
BobSimulator all pass four variants and axiom/closure traces. Agent c's CoinRelabel passes
all four variants and37 stored-constant traces. Mathematical seed relabeling and all-key
occurrence/padding contracts are progressing; fake-program and B1 reconstruction remain.


## Second resume and checkpoint2 delivery

User explicitly resumed. Fresh macOS preflight recorded6.463GiB headroom and>130GiB free;
no orphan checks existed, wrapper hashes match. Resumed remaining197modules in newphase.
All224 modules pass,31sorrieddeclarations: onlyyaoHybrid_polyTime removed,noneadded.
Exactcheckpoint2sourceheaders/clash/lint pass; cryptography92FAIL/102WARN includesonlythe
approved1062-lineYaoexception; circuits0FAIL/79WARN. Fourunsignedpatches reproduceexactly.
Checkpoint2 payload2391files includingtopmanifest, exacthash/pathsetsverified; pushedonly
inbox/fills/sc-yao at816971fc6922646f056a47efd41b1407f762320d. Proofbranch9b7b1147b stayslocal.

Integrated immutablefakev3 andCoinSeedRelabelhand-offs aftersweep; prior3overwritten evidence
versions preserved underhistory/integration-resume2. Leadnormalchecks pass updatedrows/tables,
AllTables/GarblingProgram/AliceProgram,FakeObjects,FakeProgram,FakeMessage,CoinSeedRelabel.
RootSliceReductionall5theorems pass; SimulationBound commonεassembly/outputswitch pass.
GateHybrids handoff verified42files and integrated; exactselectedsubsteps/allzero/endpoints
proved byc with4seals andall49storedclosuresstd/noadmissions. AliceStatGlue probe underway.
FakeSimulator/FakeMessage contractbundle bya andGateHybridMessage byc are finishingaudits;
b completesrankedselectedseed/ciphertextreconstruction. a will separatelyown genericselected
coordinate-swap uniformlaw, coordinatingwithb. The securitytargetremainsunproved.
