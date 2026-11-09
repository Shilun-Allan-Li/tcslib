# Gate 06 combined verification at the final PR head

[PR #232](https://github.com/Shilun-Allan-Li/tcslib/pull/232) at
`54ee105020f24d6de08aba62a1914dbeb723d87c` targets
`cryptography/pass-shelat-ch2-4`. The actual comparison base is
`067c5d8d6dd436e62681d7dc607984c705dc80a2`. The live records target at
`e9b0982aac89698127efde9ec303cc0edd7b6a01` has the same relevant Lean source,
toolchain, checker and manifest bytes.

The PR contains the four audited Chapters 5–8 prongs, all 15 minor comment
fixes, and the two approved explicit probability-projection repairs.
It changes 61 Lean paths. S2 is already on the target via #231. The survey
includes all five S2 files in the combined source. Cleanup #248 remains
deferred.

## Results at the final head

| Check | Measured result |
|---|---|
| Ordinary native compilation | 1,075 source-matched local modules. The final tree retains 1,065 checked objects and rechecks the nine affected local modules and campaign Checks. The rebuilt modules include `TCSlib`. All 3,810 external objects were revalidated. |
| Whole-file seals | 59 valid harnesses. Five were rerun for the approved repairs and their audited importers. The other 54 retain identical source and dependency objects. Of the 59 sealed sources, 38 elaborate and 21 retain inherited source failures. |
| Sensitivity controls | All 13 verified in the full DLHash closure, which retains its source and dependency objects at the final head. Six unsealed negatives pass, six sealed negatives fail only at the intended `rfl`, and the sealed published-reader control passes. |
| Declaration and axiom census | 4,172 actual declarations. Every axiom set and the direct type/value reference census agree with the pre-repair combined head. There are zero unexpected axioms. The 33 designated admissions and 46 actual names depending on `sorryAx` are unchanged. |
| Explicit and generated reference review | 154 raw C1 observations, 10 separate selected-open observations, 12 C2 source locations and four C3 reference pairs. All measured observations are retained. |
| Style | The two repaired files passed the style and campaign checks with zero findings requiring a fix. |

The `FinDist.prob` repair in Extraction fixes two new diagnostics and
preserves the structurally identical stored type of `samplerLaw_apply`.
The Samples repair fixes nine new diagnostics. Its two affected audited
theorem types agree structurally after alignment of universe parameter
names and removal of binder labels and source annotations, with binder
visibility preserved. The complete final source changes are in the
approved source delta. The final native census and seal replay cover
both fixes.

The instance harness keeps the ordinary local irreducibility seal and
masks the imported instance's separate unfolding membership. It checks
exact identities, the scoped-registration guard, full lookup-table
preservation at installation, and the seal at EOF. The isolated pilot
also verifies exact synthesis for its concrete target. The measured
control and lookup properties describe the check's scope.

The first BPPBridge and Derandomization probes stopped in Lean's quoted
string parser before source elaboration. Both attempts are retained.
The two native retries split the generated strings into bounded tokens
and restore the same decoded requests, original source bytes and line
maps. Both retries pass. The first survey retains its actual exit code
and the effective selection is stored separately.

## Inherited diagnostics

All 146 retained diagnostics occur in 116 unchanged actual-base
declarations. The prior diagnostic comparison has 142 exact text matches,
two changed continuations in Extractors, and one manually resolved
`GI.unaryMul_poly` source boundary with identical diagnostic text. The
stricter seal also observes `sum_sub_eq_zero` in Extractors.

The exact actual-base Extractors replay rebuilt its six local modules.
Its full closure seal reproduces the same four failing declarations.
The one-instance diagnostic independently reproduces the three original
coercion dependencies. Moving the published probability lemma changes
the first failing step in `statDist_le_of_epsClose`. The declaration
already reads the coercion at the actual base. Other historical groups
are supported by their source, dependency and diagnostic comparisons.
The frozen cleanup ledger and all failed native outcomes are retained.

The S2 splitter remains a measured C3 observation. It comes from the
approved `split` case analysis on the host statement. The foreign
matcher is among the verified requests. The one generated congruence
theorem recorded under a different import in the broader census has
the same native axiom set.

## Evidence

`final-disposition.json` indexes the current outcome and the retained
diagnostic groups. `survey-native.zip` preserves the original survey,
the controls and the two targeted retries. `final-validation.zip`
contains the approved repair witnesses, final replay, actual-base
Extractors comparison, final scans and source dispositions. Both
archives have closed, checked file manifests. The earlier full native
replay, isolated mask pilot and source preflight are in the sibling
checkpoint directories.

**Clear to merge — the audited, corrected #232 head has no unresolved new seal diagnostics.**
