# External audit pack — B5b fill gate, round 2: the packet repairs

Round 1 (`audits/ch34-b5b-fill-findings.md`, preserved verbatim) found **0 blockers, 2 majors and
3 minors, and no mathematical defect**. Both majors concern the packet: the bundle's identity,
and the union screen's missing population. The repairs are in
`audits/ch34-b5b-fill-resolutions.md`. **Round 2 audits the repairs.** Round 1's notes 6–22 stand,
unless a repair contradicts them.

**Two attachments.**
- **The round-1 bundle** `audits/ch34-b5b-fill-bundle.md`, unchanged: SHA-256
  `6e4ad39959ca9b0387f045a9f9958aff03a062dc3283be42fed41332dcc578f5`, 67 sections. Its erratum
  (major 1) makes these bytes authoritative.
- **The round-2 bundle** `audits/ch34-b5b-fill-r2-bundle.md`, which holds:
  - this pack, the standards, the round-1 findings and the resolutions;
  - the corrected records: the B5b pack with its erratum, the CH34-D4 record with its erratum,
    the backlog, and the regenerated D4 freeze log with the maintainer's tool;
  - the current `EXPCOM.lean`, with note 20's patch;
  - **the supplement:** the 66 union-population files at `56258cb5`, the 22 delivery-population
    files at the delivery base `ebc58d67`, and the delivered `EXPCOM.lean` at `7a2ed9ed`, each
    section labelled with its revision; the two population lists; the screen script; and the
    maintainer's rerun of the delivery screen.

## Brief for the auditor

1. **Identity (major 1).** State both attachments' SHA-256s and section counts. Check that the
   round-1 bytes are the ones named authoritative, and that the erratum explains the superseded
   digest truthfully.
2. **The union screen (major 2).** Rerun the attached screen script
   (`audits/evidence/retrofit/copy-text-screen.py`) on the 66 files at `56258cb5`, in the
   population list's order. Compare the result with `audits/logs/fills-6-ch34-screen-combined.txt`
   (in the round-1 bundle). The maintainer checked that the 66 files are the very tree that screen
   read, but did not rerun it.

   Then measure and classify the SAT pair yourself: `expcom_front_poly` against
   `SAT.sat_pipeline_poly`, 255/505. The maintainer's reading is that they share only the
   names of the polynomial-time closure rows they cite, composed over different functions.
3. **The delivery screen (major 2).** Rerun the screen on the 22 files at `ebc58d67` (before), and
   with `EXPCOM.lean` replaced by its `7a2ed9ed` version (after). The maintainer's rerun reproduces
   `audits/logs/ch34-b5b-1-screen-{before,after}.txt` byte for byte: 871 → 887 declarations,
   522 → 524 pairs.
4. **Minors 3–5.** Check:
   - the 37.31% ledger erratum, in backlog CH34-D4 and the pack;
   - backlog CH34-D4 and F6-1(a), (e) against `audits/ch34-d4-record.md`, including what stays
     open;
   - the census correction (16 → 16) and the regenerated freeze log, against the tool's change
     (`declfreeze-v2.py.txt`).
5. **Note 20.** The `expcom_summit_budget` sketch now states `g + 1 ≤ G`. Confirm that the patch is
   comment-only.
6. Report anything else the repairs or records misstate, in the standard table.

## Repository-side attestations (verify or challenge)

* **Supplement fidelity.** Every supplement section is `git show <revision>:<path>` at the revision
  in its label. The 66 union files were compared, file by file, with the tree the fills-6 union
  screen read: all identical.
* **Rerun:** `audits/logs/ch34-b5b-fill-r2-delivery-screen-{before,after}.txt`, byte-identical to
  the historical logs.
* **Elaboration after note 20:** `EXPCOM.lean` elaborates read-only with no errors and no
  warnings. A scratch copy with an appended false example was rejected, confirming that the
  check really runs.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `audits/TEMPLATE.md`. Findings go verbatim into
`audits/ch34-b5b-fill-r2-findings.md`. The gate closes when it has zero blockers and zero majors.
