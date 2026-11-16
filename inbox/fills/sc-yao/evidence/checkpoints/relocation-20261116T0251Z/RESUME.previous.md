# Active again · resumed 2026-11-16

The user explicitly resumed. Fresh preflight passed, no orphan checks remained, and the
224-module checkpoint2 sweep completed. Checkpoint2 is pushed at
816971fc6922646f056a47efd41b1407f762320d. The relocation checkpoint below is historical.

# sc-yao relocation checkpoint · 2026-11-16 00:23 UTC

User requested a checkpoint before relocating and will resume later. All agents are paused.
Do not start work until the user resumes. No check process or batch driver remains live.

## Saved delivery and proof state

- Checkpoint1 PUSHED to exchange/pass-shelat-ch5-8:
  f0a9a6163c5c91599147eb550fd5bb929cc68aa0, only inbox/fills/sc-yao/.
  https://github.com/Shilun-Allan-Li/tcslib/commit/f0a9a6163c5c91599147eb550fd5bb929cc68aa0
- Local proof branch fill/sc-yao (never push):
  9b7b1147b2b27a1bfb9845f7b9c5ab104574c860.
  yaoHybrid_polyTime proved, normal checkPASS, canonical A strict/coePASS,
  standard axioms only, no admitted dependency. Yao1062lines;1090 withsc-garble.
- Checkpoint1 proof tip f5f6fae4b4b45cb20bd42e1c9d9119e232c59513,3patches.
  All commit hashes reproduced. Source+evidence exact manifests verified.
- Delivery worktree /Users/seyoonr/.codex/worktrees/sc-yao-delivery/tcslib-exchange,
  branch codex/sc-yao-delivery. Proof/source lead remains sc-yao worktree.
- yaoHybrid_simulators still admitted; its base sketch is unchanged.

## Interrupted sweep

The checkpoint2 complete narrowed sweep has27/224 PASS, zero errors so far. User-pause
SIGINT stopped own process group49775; unified session68848 closed exit130. This is a
requested pause, not a resource failure. Partial EXP log/source are retained. Shared locks
are released. Resume from evidence/inputs/checkpoint2-sweep-resume-order.txt (197modules,
first TCSlib/Complexity/ClassNP/EXP) using a NEW phase, e.g.checkpoint2-sweep-resumed-1:

python3 -I evidence/tools/check_modules.py --phase checkpoint2-sweep-resumed-1 \
  --order evidence/inputs/checkpoint2-sweep-resume-order.txt

All Lean/Lake/direct probes must still use /private/tmp/sc-yao-lean-slot.sh, tagsc-yao,
with own TCSLIB_OLEANS and the host-wide THREE-process cap. Python3-I; neverlakebuild.
Fresh headroom/disk preflight before long resumed checks. Existing user approval explicitly
authorizes full objective, proof edits/commits/pushes, and wrapper checks despiteAGENTS.

## Sources outside checkpoint2

Lead has untracked GateOccurrences (verified), RelabelGarbling (verified), SliceReduction.
SliceReduction first3theorems pass lead+b checks; fourth distAdv_chain_le is written but
UNCHECKED. Do not commit it until checked/sealed/traced. Source snapshots of every changed
or new Lean source in all4worktrees are under evidence/checkpoints/relocation-20261116/.
A checksummed ZIP is /private/tmp/sc-yao-relocation-20261116-sources.zip.

Agent a, /root/decoder, sc-yao-a:
- COMPLETE immutable fake handoff /private/tmp/sc-yao-a-fake-handoff-v3-20261116-pause/,
  454files/SHA256SUMS. Includes all12sources, matching FakeObjects.olean seed, allrawlogs.
  Full FakeProgram tables/message/activeAnswers/key0/swappedpairs PT;48/48sealsPASS,
  196storedconstants standardaxioms/noadmissions. FinalnormalchecksPASS. No live process.
- Integrate after verifying manifest, rootcheck affectedmodules, then seed c with
  FakeObjects source+matching completedolean. This refactors RowFromCoins/TablesFromCoins
  beyond checkpoint1; do not overwrite older evidence.

Agent b, /root/evaluation, sc-yao-b:
- Previous immutable v1/v2/v3/v4a integrated. GateOccurrences372lines/34storedconsts,
  foursealsPASS; noadmissions. Wholeoccurrence enumeration/padding/labelseparation complete.
- New SliceReconstruction normal12PASS (PT rows/tables/view, encoding/lengthreaders),
  SelectedSlices normal08PASS (zero/only/inner/outer, inner4n+2, direct/wrapped readers, fit).
- SelectedSeed rowIndex/slotIndex through03PASS; laternonce/filldefs+readers and
  nonce_of_none UNCHECKED. No v5seals/handoff yet; source/logs saved in b.
- b5 has independent rootSliceReduction check01/02PASS; snapshot copies under relocation.
  No live process/driver.

Agent c, /root/lengths, sc-yao-c:
- CoinRelabel and RelabelGarbling handoffs integrated; normal/fourseals/tracePASS.
- COMPLETE immutable CoinSeedRelabel handoff:
  /private/tmp/sc-yao-c-verified-coin-seed.tar.gz plus adjacentSHA256SUMS.
  ArchiveSHA256 e9c0357cedc1953e8c1503b20cad957fc0ecfffb4ef4ba4b2285eaa90ed3c744.
  399lines,29source/49storedconstants; normal11,4seals,axiomtracePASS; noadmissions.
  Proves full tape→seed relabeling from4seedreaders, including width0.
- GateHybrids.lean saved UNCHECKED155lines, backup
  /private/tmp/sc-yao-c-GateHybrids-paused.lean. Needs FakeObjects seed.
  Semantic rowWith/tableWith, trueBit, outputBit/stageBit; cowns. No live checks.

## Next substantive work

1. Resume sweep; finish checkpoint2 REPORT/export/reproduction/manifests/deliverypush.
2. Verify/integrate fake and coin-seed handoffs; update hub imports/meaningful Contents.
3. b finishes SelectedSeed, exact B1 sampler/table/view reconstruction, PT/advicebounds.
4. c finishes GateHybrids stages2i/2i+1, H0=H1 and last=fakesimulator endpoints;
   coordinate b/a to reuse stable FakeObjects and avoid duplicated definitions.
5. Root checks fourth SliceReduction lemma, adds negligible polynomial chain bound and
   full statistical/security assembly. Instantiate concrete simulators inside frozen target.
6. Finish checkpoints3/4/final with allrequiredsweeps/seals/axioms/lint/clash/headers,
   overlap and Gate27 mapping; finalZIP sc-yao/root. Do not mark complete on efficiencyalone
   unless explicitly taking the brief's permitted partial-final route with allremaining steps
   disclosed. Full objective remains active once resumed.

Fourth extra helper import approved by user "Yes": Asymptotic.BlockEncryptor for
encodeList_eq_flatMap. Exact closure193modules (onlyBlockEncryptor new), noMathlibroots.
NormalPASS and source/olean seeded to b. All4import approvals in evidence/scope-request/.

## Audit history

- Checkpoint1: own24and a40and b/c allstored helper variantsPASS;391helperconstants
  stdaxiomsonly/noadmission among769storedconstantsenumerated.
- Frozenbase/currentdiagnosticsidentical: DAG0; Uniform4pervariant in two unchanged
  declarations; YaoA0/B15. Readernecessity24/24expected (8sealednegativeexactly1each).
- Efficiencyrepaired: canonicalA2/2PASS. B17each=15baseline+2call-inputapplications
  whose call-length equality relies on exempt PolyExpr.eval notation; fullyattributed.
  evidence/efficiency-seal-summary.json. Earlier padFin rfl failure repaired viareader.
- Allbaseline/newlogs retained. The first frozen-audit runner reusedbasenames, but a
  concurrent archiver preserved all48completedrawlog/source rows before reuse under
  immutable-rows; hasheschecked. Future runner pathhashlabelsareunique.
- Large complete stack samples delivered losslessly in evidence/raw-parts ZIPs withentry
  lists/hashes (original390MB+190MB). Do not omit raw evidence forsize.
