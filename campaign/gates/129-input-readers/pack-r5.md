# Gate 129 round 5 · action and copy proof reuse

**Not yet clear to merge** · PR #251 is a draft. Seyoon dispatches and merges.
The current Lean commit is `c2fbacf42718b16c03fc0e61b571a9cf2f8c6ecb`, against campaign Lean `ef98f1685ddfb8da40d8e97890c0fff6d145523b`.
The round 4 findings are included verbatim and pin `39dfa843b02ae7fdd0acaeacfadf5bba17a60feb`.

## Source and audit scope

Round 5 addresses three proof-reuse majors and one minor. It changes the proof
bodies in Primitives, Catalog and Simulation, adds two private proof helpers,
removes three obsolete private wrappers, and moves two private scan lemmas
earlier with their exact bytes. All retained literal declaration headers,
machine definitions, imports and top-level commands match round 4. The four
approved non-simp public readers and their approved imports remain at the
round 4 scope. The eight campaign-to-PR owner files appear as bundle sections.

1. Check every row of `resolutions-r5.md` against the current sources.
   Verify the outer `none` premise at the audited no-write sites and the
   nearby matching closing forms. Check the separate actual writes, including
   erasure via `some none`, and the forwarding banks.
2. Check the 21 Catalog re-points to the generated Configuration equation and
   the Simulation proof using the same equation and `controlAction_def`.
   Historical pair 155 fell below the copy threshold in round 4 while the
   Simulation proof stayed identical. Verify the actual proof change here.
3. Check the empty-token run after the two separator emissions and the
   prepender after the fixed prefix. Check the shared empty-input source
   specialization and the common branch-state witness.
4. Check both comparison patches, the retained round 4 approvals and the
   complete definition-boundary receipts. Report any remaining exact reusable
   proof in the changed scope, with the relevant premise and owner.
5. Reconcile the equal-population copy screen and the complete merged-tree
   replay. The current evidence binds the displayed Lean commit and campaign
   base.

## Evidence

- `r5-evidence/SOURCE.json` pins the full Lean source map and the eight
  owners. The carrier includes both reconstructible patches and the
  preceding source files. Round 4's word-seam approval is included.
- `r5-evidence/REPLAY.json` records the 395-module replay and the exact
  prospective tree. All 1,004 Lean blobs, 876 physical objects and 395
  individual source, log and object receipts reconcile. The 65 inherited
  admissions remain in byte-identical sources.
- **Cloud run.** This round's replay, metadata, seals, controls, lint and
  compiled comparison ran fresh on the cloud machine. The input is the
  complete snapshot `oleans-c768`, bootstrapped module by module at campaign
  `768b9324` (Lean `ef98f1685ddfb8da40d8e97890c0fff6d145523b`), with 876 objects. The 20
  `CommunicationComplexity/NewmanTheorem` modules need the PFR package, which
  is not installed there, so the snapshot omits them. None of them is in the
  395-module closure or imported by it. Round 4 counted 896 objects with them.
  `replay/SNAPSHOT.json` records the map; 876 of its 876 objects have
  the same SHA-256 as the Mac's adopted after-#243 map. The Mac's interrupted
  partial replay (184 of 395) is superseded and only its progress record is
  kept. The drivers are the Mac drivers with paths remapped and `cp -cR`
  replaced by `cp -al`; the originals are under `drivers/mac-original/`.
  The campaign has since merged #254 (tooling only), so the replayed merge
  tree `c990aeaac92899dd3864098d2300d67be24ac9cc` differs from the copy screen's
  `2dcd506d57c4e85c9793268b499b74a7e7d17f10` only outside Lean: in
  5 devtools files and the records. Every Lean
  file, `lean-toolchain` and `lake-manifest.json` match (`source/TREE-RECONCILIATION.json`).
- `r5-evidence/CHECKED-SUMMARY-r5.json` records 125 whole-proof checks, 39
  sealed foreign definitions and 78 native and sealed controls. The
  traversal stops at foreign definition bodies and other theorem proofs.
  The candidate census covers all 5 open PRs and
  72 prepared refs at the recorded pins. Of those PRs,
  #250 (another campaign's, into `cryptography/lwe-sis-constructions`) and
  #254 (tooling only) have since merged. The three still open, #241, #242
  and #251, are at their recorded heads.
- `r5-evidence/COPY-REVIEW.md` records the equal 53-file populations, the
  197 current span dispositions and the historical cutoff
  correction. The scores are 2,429 at campaign and
  2,368 at the round 5 head.
- `r5-evidence/DATA-CARRIER-r5.json` and its recovery map contain
  1644 logical files. Decode each gzip+base64 blob and check
  its listed SHA-256 and byte count. The carrier contains the complete
  population inputs, retained score and span evidence, fresh tilings,
  closing-form inventory, exact proof checks, and raw replay receipts.
  Scratch preflight evidence is identified separately.

Use the campaign finding table and give a CLEAR or HOLD verdict.
**Deliver your findings as a downloadable file named
`gate129-input-readers-r5-findings.md`** (the findings table and the verdict
line, no other wrapping), and also paste its content in your reply.
