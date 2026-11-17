# Gate 153 resolutions

Round 1 CLEAR: 0 blockers, 0 majors, 2 minors, 5 notes (`findings.md`, verbatim). The
dispatched pack and evidence are preserved; the errata below correct the live records.

- **G153-01 (minor), procedure.** The bundle omitted the citation homes that WORKFLOW.md requires
  ("Bundles carry citation homes", G147-02): it carried the 18 changed owners but none of the
  modules listed in `defsweep/CITATION-HOMES.json`. The auditor retrieved the four it needed
  (CfgFacts, Configuration, Nondeterministic, StateRenaming) at the audited head and found them
  byte-identical at base and head. From gate 154 on, `BUNDLE-FILES.txt` is built from the changed
  owners **plus every module in `CITATION-HOMES.json`**, pinned at the audited head.
- **G153-02 (minor), records erratum.** The pack's controls line reported one part's counts as the
  total. Corrected: the two control parts are disjoint, **54 sealed definitions and 108 paired
  identities** in all, every one native-PASS and sealed-FAIL. The seal covers the **50 ordinary
  proof-boundary heads** of the 25 changed proofs; the 54 sealed control heads are a separate count.
- Notes G153-03 to G153-07: no action. G153-06's distinction between verified execution records and
  an independent Lean rerun stands; G153-07's carried families stay in `CARRIED-REGISTER.md`.
- **Merge condition.** The gate's replay is the merged-tree replay against campaign Lean
  `b913bbc9`, and the campaign's Lean has not changed since. Its output `oleans-cl153-cb913b`
  becomes the snapshot when #349 merges unchanged. **Clear to merge: #349.**
