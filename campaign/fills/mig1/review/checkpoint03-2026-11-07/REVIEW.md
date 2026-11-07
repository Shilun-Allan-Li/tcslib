# MIG-1 cp03 incoming checkpoint review

2026-11-07; internal source/evidence review by Codex. **Not yet clear to merge.** This is a
partial recovery checkpoint from the running fill. The five F-C target admissions are filled
in source; API, seal coverage, and assigned factoring work remain unresolved. No gate or fill
acceptance is granted here.

## Receipt and cumulative freeze

Original ZIP and REPORT are preserved verbatim under `original-zips/` and `reports/`.
[receipt.json](/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4/campaign/fills/mig1/review/checkpoint03-2026-11-07/receipt.json)
and `cp03-inventory.json` record safe names, lengths, modes, and SHA256 values.

- ZIP: 1,254,677 bytes; SHA256
  `d65316ee9f8b073c8ccabd7a694d2f9613ac76e1bbf7c40153db45e1b7538c4a`.
- 563 members, 539 regular files; all 538 supplied payload checksums verified independently.
  No unsafe/duplicate paths, symlinks, case/normalization collisions, uncovered payloads, or
  CRC failures. Payloads were read before extraction; extracted Lean filenames all end in
  `.lean.txt`. No actual `.lean` file was written.
- Relative to cp02, **only Loop changes**: nine public proof bodies; three private additions
  (`loopCall_heads`, `segment_heads`, `seamed_space`); four private proof changes; retirement
  of private `loop_rewind_bounded`.
- Across all eleven owned files against pinned base
  `83ac315ed9e7089466bd16a32f3b71fbadc556d2`, public count stays 357. Complete headers,
  names, visibility, homes, surviving order, public definition bodies, and witness tables
  are unchanged. No new import since cp02; the cumulative Simulation import remains the
  approved `Mathlib.Algebra.BigOperators.Fin`. Cumulative changed public proofs: 31.
- Independently reconstructing all three textual patches in memory from base gives every
  supplied source snapshot exactly, with exact hunk/context matches and only owned paths.
  The first two source changes remain intact; patch-number subject metadata changes for
  the cumulative three-patch series. Bundle header agrees with delivered HEAD metadata
  `0d03f8f959ba7d84fc8e9bdc5e932e28c24da30b` and pinned prerequisite. Pack objects were
  not imported or validated as Git objects.

No Git command was run for this review. Base bytes were recovered by reversing the previously
reviewed cp02 patches, checking cp02 snapshot hashes against its immutable comparison record,
and checking the reverse/forward round trip. Details: `pinned_source.py`,
`source-comparison.json`, `patch-consistency.json`, and `cp02-to-cp03-source.diff`.

## Actionable findings

1. **Confirmed new reader gap: `Turing.captureCfg` in Wrappers.** It is an ordinary
   structure-valued definition, with no existing field-reader family in the pinned source
   ([definition at 128](/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4/campaign/fills/mig1/review/checkpoint03-2026-11-07/cp03/fill-mig1-mega-cp03/source/TCSlib/Complexity/TuringMachine/Build/Wrappers.lean.txt:128)).
   New `loopCall_heads` explicitly unfolds it and `leftCfg` at Loop
   [2056–2058](/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4/campaign/fills/mig1/review/checkpoint03-2026-11-07/cp03/fill-mig1-mega-cp03/source/TCSlib/Complexity/TuringMachine/Build/Loop.lean.txt:2056).
   Implicit output reads also occur in `emitLoopTM_computes` at
   [5210–5211](/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4/campaign/fills/mig1/review/checkpoint03-2026-11-07/cp03/fill-mig1-mega-cp03/source/TCSlib/Complexity/TuringMachine/Build/Loop.lean.txt:5210),
   where `rfl` reads the candidate's empty physical output through `loopCall`/`captureCfg`.
   The old explicit `rightCfg` read remains in the changed `loopHost_prepare` at 1249.
   The supplied Loop seal excludes all three definitions. Obtain a ruling on the
   `captureCfg` reader family in its home, alongside the unresolved configuration readers;
   cover state/input/tapes/heads/output and replace implicit conversions too. The report's
   proposed formulas are unelaborated API candidates, not approval. Earlier `branchTM`
   shape/operational gaps remain unchanged and separate.

2. **Confirmed seal coverage omission.** There are **16** changed/new surviving Loop
   declarations, but `Seal_Loop.gen` and the sealed source contain only 15 regions.
   Changed private `loopHost_input_rewind`
   ([664–677](/Users/seyoonr/.codex/worktrees/ab34-records/tcslib-arora-barak-ch3-4/campaign/fills/mig1/review/checkpoint03-2026-11-07/cp03/fill-mig1-mega-cp03/source/TCSlib/Complexity/TuringMachine/Build/Loop.lean.txt:664))
   is missing. It now calls public `timed_rewind` directly; static inspection suggests
   straightforward API reuse, but this is not a successful seal by inspection. Add that
   region, correct the report's “all 15” claim, and rerun after resolving the actual reader
   gaps. This finding is an omitted check, not a demonstrated Lean failure.

3. **Completion label needs qualification.** REPORT lines 8–10 combine cp03/cp04 and say
   “F-C complete,” while lines 31–33 leave assigned MIG-24 T3 unfinished and T2 sharing
   incomplete. Record **all five F-C target proofs filled; F-C factoring/acceptance pending**.
   Keep T3 on the worker's remaining list. T2's claimed need for a public first-entry
   interface is a reported design gap, not an approved exemption or a verified minimal API.
   The brief permits precise gap reporting and incomplete families; it does not authorize
   new debt. Combining recovery points is disclosed and does not close those obligations.

## Supplied evidence, independently parsed

The final Loop sealed copy restores the submitted source code when only its seal wrappers
are removed. Its supplied output records exit 0, zero errors, and 61 warnings. The warning
multiset, excluding source positions and base admission warnings, exactly equals the base's
61 non-sorry warnings. It certifies only the supplied partial list if replayed successfully;
it does not resolve the omitted region or excluded definitions.

`Ax_fc.out` contains ten standard-axiom results: all nine changed public Loop proofs plus
unchanged `callTM_run`, exactly. Each lists only `propext`, `Classical.choice`, `Quot.sound`.
The final `fc6.summary` records exit 0, zero errors/sorries, 61 warnings; retained `fc1` and
`fc3` are failed intermediate attempts, followed by passing checks. The 36-module bootstrap
tail records zero failures. These are worker-produced logs, not fresh maintainer runs.
`evidence-check.json` records the independent parsing and coverage mismatch.

Paired control sources/logs are byte-identical to reviewed cp02 controls: 19 definition pairs,
with multiplicity and negative diagnostics already checked there. No `captureCfg` control
was added. The previous process-deviation disclosure is also byte-identical. Compiled census,
screens, full 641-module sweep, policy lint, and maintainer elaboration remain NOT RUN.

Source review confirms reuse of the published first-halt, bounded-rewind, head-envelope,
and radius-to-space APIs. Catalog's segment/seam material is moved into Loop's home pending
the explicitly deferred F-D deletion; no new generic radius copy is introduced. The argument
scanner's `words`/`cfg` matches are local `let` names, not the foreign definitions named by
its heuristic. No added source execution or proof-bypass candidate was found. This review
read the new changes and their relevant source contexts, not every unchanged Loop proof.

Remaining source admissions are exactly:

- `Turing.FinTM.polyUnaryTM_spaceUsed`
- `Turing.FinTM.unaryTokenTM_computes`
- `Turing.FinTM.appendBitTM_computes`
- `WordRAM.WordSizeComputable.mono`
- `WordRAM.wordSizeComputable_logSpace`
- `WordRAM.wordSizeComputable_of_spaceConstructible`

The three allowed forwarding exports, F-B retirements, F-D retirements/re-points, T3, and
unresolved API/factoring gaps remain pending. No Lean, Lake, screens, cache operations, Git,
pushes, payload script execution, external messages, or writes outside this new review folder
were performed. The cp01/cp02 review folder was read only and remains unchanged.
