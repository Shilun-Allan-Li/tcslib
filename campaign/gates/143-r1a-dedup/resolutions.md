# Gate 143 resolutions

Round 1 CLEAR: 0 blockers, 0 majors, 2 minors, 3 notes (`findings.md`, verbatim).

- **G143-01 (minor), fixed in Lean** at `ba93b96c566bbb56ec8185cb1c09b708b0169285`, docstring-only:
  the six campaign labels (`(BW-1)` four times, `(CH34-D4)` twice) are removed; the lemma
  citations stay. The diff from the audited head touches only those six docstring lines; the
  three files re-elaborate cleanly. The same rule is applied to the next PR (R2a) before it ships.
- **G143-02 (minor), fixed in records:** the refactor plan's R1 row now describes four retained
  private aliases. The accepted deviation: BW-1's 2026-10-18 ruling said to delete the four
  privates; they are kept as one-line citations so that their use sites stay byte-identical,
  because deleting them exposed pre-existing foreign-definition reads in those use sites
  (`first-attempt/` in the carrier). The proofs are retired; the declarations remain; the use
  sites' legacy rule-10 reads are separate, pre-existing debt and are not cleared by this gate.
  The ledger's BW-1 status records the retirement upon merge.
