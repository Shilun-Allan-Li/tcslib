# §13d G4 continuation 3: integration erratum to `g4-cont3-REPORT.md`

## Erratum (at integration; gate 61, minor 11 and note 17)

**Scope.** Three passages of the worker's report (`g4-cont3-REPORT.md`, beside this file, blob
`4c2055cd…`), as corrected at integration. The report itself stays as delivered. Sources: the
maintainer's review
(`campaign/fills/s13d/reviews/g4-cont3/REVIEW.md`, F1–F3) and gate 61, the fill gate of PR #148
(`campaign/gates/61-s13d-g4-cont3-fill/`). None changes the delivered Lean. Both targets stay
admitted, and the 12 new or changed privates are on `[propext, Classical.choice, Quot.sound]`.

1. **Verification, paragraph 2: the citation inventory.**
   - "New TCSlib citations are within the supplied inventory: … `two_le_zoneStart` …" is wrong
     for that name. `Turing.two_le_zoneStart` (a public theorem, `Build/ZoneTape.lean:184`) is
     cited by `zr_rightPass_bounds` and `zr_rightPass_tape`. It is in none of: the brief's probe,
     the expanded probe, `evidence/g4/external-citations.txt`. The frozen
     `zoneRebalancePost_frames` already cited it at the base.
   - Cause: `audit-scope.py` collects namespace-qualified names plus four literals, and the
     lemma is cited unqualified.
   - The counts: the supplied probe is 439 checks of **428 distinct names**; the expanded probe
     is 445 checks of **434 names**. With `two_le_zoneStart`: 446 checks of 435 names, 0 errors,
     0 warnings (the review's `G4C3WorkerProbePlus`, row 22).
2. **Verification, paragraph 3: the rule-10 evidence.**
   - The final seal `evidence/g4/SealCp1.lean` has no controls: no `rfl` example fails inside
     the seal and passes outside it.
   - `logs/g4/rewrite-audit-cp1.txt` is five lines of fixed text written by `audit-scope.py`. It
     lists no argument. The shipped script writes "The 49-definition seal", while the shipped file
     says 57, so the file came from another version of the script.
   - Both checks were replaced by the review's and pass: its 57-definition seal with four
     controls that fail inside and pass outside (`out/seal-head.out`, `out/seal-tip.out`), and its
     argument-by-argument inspection (`out/rwargs.txt`, `out/kinds.txt`).
3. **Packaging and records.**
   - `logs/g4/package-cp1.log` is empty (0 bytes).
   - `evidence/g4/Work.lean` is a stale development copy. Its extension status paragraph and one
     line wrap differ from the delivered file.
   - The item-start free disk is 25,530,650,624 B in `logs/g4/disk-before-item.log`, not
     25,530,646,528 B (4,096 B apart; both far above the floor).
