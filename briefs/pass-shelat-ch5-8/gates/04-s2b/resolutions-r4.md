# Gate 04 (S2b, #195): round 4 resolutions (repair in progress)

- **Round 4:** findings `findings/gate04-s2b-r4-findings.md`, verbatim, SHA-256 `4340ef76b07b324721a3b634335c303384eabe11c634a2a6b85fd6611956df43`; head
  `a588adfed01eefe6971abd0846e3938ad02e8624`. **DO NOT CLOSE: 0 blockers, 1 major (R4-01), 1 minor (R4-02).**
  R3-01, R3-02 and N7 fixed; F02 not resolved (through R4-01). The thirteen re-proofs and the two
  `abbrev`s (R-04-4) are accepted.
- **Repair:** commissioned 2026-11-06 on #195 (the gate 04 worker); this file is completed when it
  lands.

| Finding | Severity | Resolution |
|---|---|---|
| R4-01 | major | **Confirmed** (the maintainer checked the three `variable` lines at the head: `Defs.lean:53` `{I O : Type}`, `GGM.lean:70` `{S : Type}`, `SubHybrids.lean:70` `{P S V : Type}`). The classifier compared declaration text only, so twelve declarations whose ambient binders changed were classed `SAME` and kept their exclusions. **Repair:** the classifier compares elaborated signatures as well; every declaration it classes changed or added is re-proved through published equations (`acceptProb_def`, `distAdv_def`, `oracleDist_apply`, `OracleAdversary.boundedBy_iff`, and an equation for `randomFunction` beside its definition if missing); exclusions, seals and scans are regenerated. |
| R4-02 | minor | **Confirmed. Repair:** the scanner reads `nth_rw`/`nth_rewrite` and multi-line `unfold`; the collector records private names; the def-aux limit is fixed or stated. The report describes the result as coverage of the collected candidates and the inspected syntax, states the control log literally, and the evidence bundles the candidate tables, `unseal.json`, `declchanges.tsv`, `declx.py`, `run_collect.sh`, the classifier and the minimization logs. |
