# Gate 129 round 4 — input readers and shared word seams

**Not yet clear to merge** · PR #251 is a draft. Seyoon dispatches and merges.
Round 4 reviews 39dfa843b02ae7fdd0acaeacfadf5bba17a60feb against campaign Lean ef98f1685ddfb8da40d8e97890c0fff6d145523b.
The round 3 return is included verbatim as `findings-r3.md`.

## Source scope

There are four approved non-simp public equations. The previous three are
`FinTM.controlAction_def`, `inputMoveAction_eq` and `inputFoldTM_tr_bwd`.
Round 4 adds `Cfg.ofWords_mapState` beside the seam constructor in Convention.
The approval covers its StateRenaming import and reuse of the exact old
private Seam contract. The proof uses the published map-state field
equations. It is used in the split startup and restoration, the three Seam
proofs and the pre-existing CodeSimulator call proof.

All retained literal declaration headers and definition bodies match the
round 3 source. The same-file reorder preserves the exact buffer definition,
support equations and input reader in Simulation, and the silent control
and right-moving step proofs in Primitives. The uncalled private prefix
wrapper and the superseded private Seam equation are removed. Reductions
keeps the approved PolyTimePairing donor and import.

## Audit questions

1. Check each round 3 major against `resolutions-r4.md` and the exact current
   proof bodies. In Primitives, check the complete split preparation and
   round, the right-moving step, and the fixed-pair donor. The one-step run
   and live-step reductions must use their published equations. Reconcile
   the split word seams and the new owner equation.
2. Check that all three Simulation input reads are tied to the unchanged
   input position across different state and tape types. Inspect the
   complete probes for `leftCfg_step`, `rightCfg_step` and
   `bufferedFirstCfg_step`. The moved buffer reader and support are also
   in the source freeze.
3. Check that `scanCopy_finish` now specializes the suffix proof, including
   the empty-word case. Verify the live right-moving reuse and the no-write
   field proofs. At the audited replay and rewind sites the action requests
   outer `none`, preserving the buffer. The later erase uses `some none`.
4. Check the approved import and declaration scope. Verify the exact
   CodeSimulator re-point and the removal of the old private Seam equation.
   Check the retained definitions and headers against both supplied patches.
5. Verify the full proof and replay evidence, including the population and
   current status of every flagged copy family. Report any remaining exact
   reusable proof in the changed scope with its full premise and owner.

## Evidence

- `r4-evidence/SOURCE.json` pins the eight owners and four equations.
- `r4-evidence/APPROVAL.json` records the word-seam ruling.
- `r4-evidence/REPLAY.json` pins all 1,004 source blobs and 896 physical
  objects. The initial 395-module merged-tree pass and the final
  141-module Seam replay bind each compiled source, log and object hash.
  All 65 inherited admissions retain exact source bytes.
- `r4-evidence/CHECKED-SUMMARY-r4.json` records 119 complete proof probes
  across eight owners. The boundary traversal stops at foreign definition
  values and other theorem proofs. The grouped probes seal the selected
  ordinary foreign definitions and use a matching native and sealed control
  for every head. All 70 paired identities and all standard axiom
  checks pass.
- `r4-evidence/COPY-REVIEW.md` explains the equal 53-file populations and
  220 exact text-span dispositions. The current scores are 2,429 and 2,345.
  The carrier supplies the exact prior inputs where scores are reused.
- `r4-evidence/DATA-CARRIER-r4.json` and its recovery map contain 2014
  logical files. Decode each gzip+base64 blob and validate it against its
  listed length and SHA-256. The carrier includes raw execution, complete
  Lean probe sources, copy populations, new tilings, current ref transcripts,
  comparison patches and replay drivers. The interrupted predecessor
  replay is listed only as superseded.

Use the campaign finding table and give a CLEAR or HOLD verdict.
**Deliver your findings as a downloadable file named
`gate129-input-readers-r4-findings.md`** (the findings table and the verdict
line, no other wrapping), and also paste its content in your reply.
