# seq-zk-b normalized suffix and canonical-reader result

All 12 public SuffixMachine declarations are proved and checked. phaseStep_poly is a general
normalized append leaf; phaseSuffix_poly accepts arbitrary PT X,Z,RV,RS, unary Start/Count,
and any initial message family with PT encoding. The additive bound is
|encodeMsgs pre0| + t*k(|x|)*(2*B(|x|)+2). No initial message bound or start/count range
premise occurs. The raw adapter is total on malformed words through BinArith.decWords.
At zero steps the initial prefix is preserved, and phaseSuffix_zero_nil publishes the exact
specialization to the existing whole-prefix semantics. Global coin blocks start+i are used.

The implementation directly instantiates public ColMachines.polyTimeComputable_loopState';
no host/control implementation or hand-built machine was added. The new general leaf
re-derives the private local assembly in phasePrefix_poly from public readers, with full
explicit overlap/promotion disclosure in suffix-machine-overlap.md. The typed counterpart
PrefixFolds.simStep and phasePrefix_succ are also disclosed there. Stable old proof/definition
bodies were preserved.

As requested by the lead, added canonical phaseVerifier_eq, phasePrefix_eq and phaseSuffix_eq
readers, with no simp attributes. Final checked hashes:
- WrappedVerifier (207 lines, max96):
  d053592bf581166445470bb59d089bb816605c157834b3f801be6185c800aa81
- SimulatorMachine (348 lines, max97):
  b26c84a1f408bafa18f8fee0d747817d541d73c776b9f390aeaa701fcf5dda64
- SuffixMachine (323 lines, max99):
  59d7b3b5dcc6ca78a3a0f5bfdd39348f7a00fd2f06517cdc7bfc78c71a06509e
These supersede the earlier-stage WrappedRESULT/SimulatorRESULT source hashes. All preexisting
statements/bodies remain unchanged; only their new public Eq readers were added.

Final native checks all exit0 without diagnostics: wrapped-check-04-eq-reader (3.13s),
simulator-check-04-eq-reader (2.75s), suffix-machine-check-02 (2.38s, maxRSS2256748544 bytes).
Initial suffix attempt retains one omega proof-local alias-alignment error and one unused
binder warning. The proof was fixed by normalizing only its local p/aux/raw lets; the bound
statement was unchanged. Its exact initial source was inverse-patch reconstructed and
SHA256-checked against the original recorded hash before retention.
All 14 new suffix/canonical-reader axiom prints are standard only (propext, Classical.choice,
Quot.sound or subsets); no sorryAx. Probe source and raw output are retained. Final style lint
across eleven local helpers: 0 FAIL / 0 WARN. All source/search/raw evidence is included.

These SuffixMachine and canonical-reader additions are FUTURE WORK after the CP2 source
snapshot e978a28274fdeb545e622ae28747221088352512; they do not describe code in that commit.
Earlier helper result summaries record their earlier source-stage checks accurately.
No owned main file, frozen file, previous logical body, package tree, or Git commit changed.
All Lean commands used seq-zk-b's own olean tree/tag and the shared cap3 wrapper; no Lake ran.
