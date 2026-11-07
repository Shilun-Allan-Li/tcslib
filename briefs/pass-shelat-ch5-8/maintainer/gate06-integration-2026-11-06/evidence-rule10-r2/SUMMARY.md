# Gate06 Rule-10 collector and initial survey

Pinned source: `e9d64158461bfe24ddc88ab885bc4017899b4c16`.
Comparison base: `c7d8753a548ced71c1e1ea70e012c365af5c2171`.

- Collector completed natively: rc 0, no errors/warnings, 1430.776 seconds, peak RSS
  2,632,499,200 bytes. Exact source/log/result retained as collect1.*.
- All stored constants of the 51 changed math modules were traversed, including private and
  generated constants; types and proofs/values participate. The ordinary foreign-definition
  import-closure supplement covers anonymous commands. Seven other changed files were
  verified import/options-only. Source pinning compares the complete library tree to HEAD.
- 939 term-collected pairs are subsets of 51,470 conservative module/name pairs, covering
  4,171 distinct requested names. Instance/reducible-nonmatcher filtering and exact notation
  exceptions are retained. Matcher descendants are retained; no unsafe override is used.
- Canonical complete axiom parsing (`axioms-full.json`) has 2,721 unique actual declaration
  identities: 2,675 standard-only sets, 46 with sorryAx, no other axioms. This is statement-
  phase evidence, not proof completion. The raw inventory's axiom_display fields are first-
  line previews of formatted output; canonical parsing handles multiline lists.
- The new quantitative 3COL negligibility lemma is standard-only. PerfectZKAbort.seqRep and
  the efficient-prover 3COL corollary depend on sorryAx through the generic repetition
  statements, as recorded; removing a local sorry did not finish those dependencies.
- All 11 controls pass their expected-outcome checks: five unsealed passes / sealed proof
  failures, plus one sealed positive file with three published-reader proofs. Exact full
  DLHash closure: 1,369 names = 1,351 active + 18 already irreducible. Anonymous and matcher
  sensitivity verified; zero harness diagnostics. Installation and EOF status checks pass.
- Initial PRFMAC pilot installs/verifies all 1,705 names (1,686 active + 19 already), with
  EOF verification intact, then reports one real source failure: its correctness proof treats
  generator coins as Fin n using a hidden coin-length reduction. A public-reader/Fin-transport
  repair proposal is saved, unapplied and uncompiled.
- Primary-source review found two documentation corrections: distinguish collapsed copies
  from COPY and distinguish strict-PPT abort from arbitrary expected-time truncation.
  Comment-only proposed patches are saved; they are not in the frozen source.
- The full 51-module initial whole-file survey is running. Its source failures need manual
  source/base classification and repairs, followed by native affected replay and final seals.
  Prepared probes and passing controls do not constitute a passing library seal.

**Not yet clear to merge — the initial survey, repairs and final attestations remain.**
