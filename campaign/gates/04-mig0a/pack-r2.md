# External audit pack — MIG-0a gate, round 2: the contract structure's records and documentation

Round 1 (`audits/mig0a-findings.md`, preserved verbatim) found **0 blockers, 1 major and 5
minors**. No proved statement was false. The major concerned the migration interface: a
first-exit `Turing.Contract` does not directly replace `CfgRecord`'s `RecordRun` segments, the
return-or-escape rounds, or `CounterLoop`'s joint head-vector relation, yet the records said it
would. The repairs are in `audits/mig0a-resolutions.md`. **Round 2 audits them.**

**No statement or proof of the file changed.** The repaired file is
`audits/evidence/mig0/Contract-proposed-r2.lean.txt`, 1,100 lines, against round 1's 888.
Removing comments, docstrings and module docs from both leaves identical code, except the import
lines: `CounterLoop` is replaced by `Catalog` and `Mathlib.Tactic.Linarith`. If the gate closes,
this file lands unchanged, with an import in the `TuringMachine` facade.

**Bundle:** `audits/mig0a-r2-bundle.md` holds:
- this pack, the standards, the round-1 findings and pack, and the resolutions;
- both versions of the file and their diff;
- the code-identity script and its log, and the elaboration and axiom logs;
- the design document and the backlog;
- the Build and core files the repaired records and docstrings cite: `CfgRecord`,
  `RecordTable`, `CounterLoop`, `Loop`, `Scan`, `Seam`, `Embed`, `Catalog`, `Simulation`,
  `StateRenaming`, `Deterministic`, `Configuration`;
- the three vendored [AFM26] files whose headers record the consulted revision.

## Brief for the auditor

1. **The major.** Check design §16a's *MIG-0a gate, round 1*, the revised MIG-0b list, and
   backlog MIG-0, MIG-12, MIG-13, MIG-15 and MIG-17, against your round-1 counterexamples and the
   attached `CfgRecord`, `RecordTable` and `CounterLoop`.
   - Do the planned segment, round and joint-trajectory layers cover what those rows need?
   - Is assigning them to MIG-0b, ahead of every dependent migration, enough?
   - Does any record still claim a direct replacement?
2. **The code is unchanged.** Rerun `audits/evidence/mig0/codeid.py` on the two versions, and
   compare the declaration headers and data fields as you did in round 1 (note 16).
3. **Minor 2, imports.** Are `Seam`, `Catalog` and `Linarith` the right set? Check the layering
   facts in design §16a item 4: `CounterLoop` is no longer in the closure; `Loop` still is,
   through `Catalog`; `spaceUsedByTape_le_card_Icc` moves down first.
4. **Minor 3, sketches.** Check each new `**Proof sketch.**` against its proof, and `frames_iff`'s
   prose.
5. **Minor 4, attribution.** Check the `[AFM26]` entry and its tags against the vendored headers.
6. **Minors 5–6.** Check the corrected `ReturnContract` description (the install and emit calls
   split on `entry = exit`; the advancing writer returns), the 843-line count, the deferral of
   `seamReleaseTM_runFrom_pos`, and the exports' relocation notes.
7. **The swept notes** (9, 10, 12, 14, 17, 20): check that the documentation now says what you
   asked.
8. Report anything else the file or its records misstate, in the standard table.

## Repository-side attestations (verify or challenge)

* **Elaboration** (`audits/logs/mig0a-r2-elaboration.log`): read-only against the
  fills-6/CH34-D4 snapshot, 0 errors and 0 warnings.
* **Axioms** (`audits/logs/mig0a-r2-axioms.log`): the 27 explicit public declarations, with
  prints identical to round 1's.
* **Code identity** (`audits/logs/mig0a-r2-code-identity.log`): only the three import lines
  differ.
* **Names:** unchanged from round 1 (`audits/logs/mig0a-names.log`), since no declaration was
  added, removed or renamed.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `audits/TEMPLATE.md`. Findings go verbatim into
`audits/mig0a-r2-findings.md`. The gate closes when it has zero blockers and zero majors; the
file then lands.
