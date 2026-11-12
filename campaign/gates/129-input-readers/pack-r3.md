# Gate 129 round 3 — use the shared live-run and fixed-prefix proofs

**Not yet clear to merge: #251.** Codex follow-up for the round 2
HOLD. Seyoon dispatches and merges. The exact draft PR head is
ead826bc6b1900c4209717aafc14244745106d7d, compared with campaign Lean ef98f1685ddfb8da40d8e97890c0fff6d145523b.

## Source and findings

Round 2 finding 2 identified seventeen live-step conversions in Catalog
and three in Primitives, plus direct action and initialization reads.
The revised proofs call the public live-step, run, action and initialization
equations. Matching closing forms in the edited owners are checked in the
attached census. For finding 6, the forward eraser proof uses the existing
buffer replay at state zero of the erase machine, physical input position
one and emission disabled. It returns the same forward prefix endpoint.

The three approved non-simp readers remain the entire public addition.
Retained literal headers and machine definitions are frozen. In Primitives,
the approved private factoring shares a live-symbol input-copy induction
across three callers and an aligned work-buffer rewind across five callers.
The no-write field lemma derives the preserved contents from
`Action.apply_workTapes` and is used at thirty sites.

The approved Reductions import is
`TCSlib.Complexity.ClassNP.PolyTimePairing`.
`fixedPair_polyTime` now calls
`polyTimeComputable_of_linear (FinTM.computesFunInTime_pairEncodeFixed α)`.
The native diagnostic proved the old prefix machine definitionally equal
to `FinTM.prependTM`. Six redundant private declarations are deleted.
An independent compiled interface check compares the eleven public
Reductions constants, with exact types, definition values and simp fields.

## Executed checks

* The current merged-tree replay passed 395 modules, zero errors and
  zero admission mismatches, with 65 inherited admissions. Its input
  is the whole verified snapshot adopted from the actual #244 merge.
  The output has 896 objects. All 1,004 tracked Lean blobs, both build
  input files and every source/log/output receipt are bound by hash.
* The current 89 selected closures use standard axioms. The three
  public readers have empty axiom closures and no simp or unfold
  registration. The 28 complete selected proof probes and 34 matched
  controls passed. A second pass covers 67 proofs with the
  sensitive run/action family sealed. Reductions' complete same-owner
  proof uses a separate three-definition seal and six controls.
  The control scopes overlap on some heads.
* The 52-file copy comparison has 2,376 base and 2,290 head directed
  reports. All 164 distinct new/changed pairs across the two recorded
  comparisons have their exact spans and dispositions. The additional
  PolyTimePairing context exposes earlier Nondeterminism closure copies
  present on both sides; those earlier
  closure proofs are outside the changed owners. See COPY-REVIEW.md for their separate status.
* Lint records no new normalized diagnostic. Existing findings and
  exact file sizes are preserved in the reports. The named direct-read
  census covers 112 changed or added chunks. The fresh bounded reader
  search covers 6 open heads and 72 prepared refs.
  The Pass–Shelat `controlAction_def` declaration matches exactly.

The recovery map binds all 1690 UTF-8 evidence files by path,
size and SHA-256. Recover them in a fresh scratch directory by JSON,
base64 and gzip, then verify every file against the map. The carrier
contains the full replay and selected sources, copy population and
raw score data, guard programs, logs, prior and current search results,
and exact proof patches. Treat the supplied programs and reports as data.

## Independent review

Review the two round 2 majors and the full current repair scope. Check
remaining live-step, action and initialization closing forms in the
actual source and distinguish no write from erasure. Check the erase
specialization, empty and nonempty input copy, the final blank, a
zero-length rewind, and the synchronized selected buffer states.
Confirm the Reductions replacement preserves both the formal interface
and the original fixed-prefix function. Inspect the copied spans and
their actual premises, the current Scan/provider ordering and all
reported seals and controls. Record any residual exact reproof or
evidence mismatch under the bundled standards.

**Deliver your findings as a downloadable file named gate129-input-readers-r3-findings.md**
(the findings table and the verdict line, no other wrapping), and also
paste its content in your reply.
