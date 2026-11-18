# Gate 162 resolutions

## Round 1: CLEAR (0 blockers, 0 majors, 3 minors, 22 notes; `findings.md`, verbatim)

A statement gate. The auditor found every sorried statement true and achievable within its
bounds, at the boundaries (G162-09 to G162-22). It found the interfaces sufficient for both
frozen targets by the pack's argument (G162-23), and the readers faithful with the freeze held
(G162-24).

**The three minors are repaired at `80e762e9`**, in docstrings only, with no statement or proof
changed:
- **G162-01, repaired.** `TableOf`'s docstring: a lookup finds the stored word when the cell has
  an entry, and finds nothing only when the word is `0`. An entry may hold `0`, as the start-up's
  `-1` entry can. The definition is unchanged.
- **G162-02, repaired.** The proof sketches of `exists_keyLookupTM` and `exists_keyAssignTM` now
  describe the marker adapter. Blank the marker cell, run the delimited word row on the payload,
  and write the marker back; an empty payload is then an empty delimited word. Job B's brief
  carries the intermediate delimiter facts.
- **G162-03, repaired.** The introduction to `Extended`'s reader section drops "policy rule 10;
  Seyoon, 2026-11-18". The provenance stays in these records and the HANDOFF. The PR adds no other
  dated provenance to Lean text.

**Notes carried into the job briefs:**
- **G162-11 (job A):** prove a reusable internal carry lemma with an arbitrary frame. The
  exported adder's blank-scratch precondition does not cover multiplication's occupied scratch
  tapes.
- **G162-15, G162-16 (job A):** reuse `Turing.scanTM_run_ofCfg` for the sign and zero tests.
- **G162-17, G162-18 (job B):** the marker adapter (G162-02) in lookup and assignment.
- **G162-21, G162-23 (jobs D, E):**
  - handle the coin's entry choice explicitly, then slice the rest deterministically;
  - use phases indexed by position and parity for self-jumps, and a separate halting verdict
    phase;
  - use the R1 embedding of the eight tapes.

## Merge

**Run 2 of the gate kit on the repaired head `80e762e9`** gives the same results as run 1 on the audited head: replay 88/88 (30 admissions, the same), 49 proofs sealed, controls 32/64, 0 read candidates, 7 copy pairs as at the base (0 new); `SOURCE.json` again gives 69 declarations added and no header or definition change. Seyoon
merges #372. After the merge the branch's build is the replay output of whichever PR merges
second, checked on the merged tree.
