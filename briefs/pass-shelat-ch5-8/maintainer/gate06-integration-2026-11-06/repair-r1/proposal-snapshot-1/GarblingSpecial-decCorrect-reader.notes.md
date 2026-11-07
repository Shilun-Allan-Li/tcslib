# GarblingSpecial: one correctness-predicate reader repair

**UNAPPLIED; native elaboration and sealing pending.** Proposal contexts were read with
`git show e9d64158461bfe24ddc88ab885bc4017899b4c16:<path>` exactly; no library edits, Lean/cache, Git mutations or apps were used.
The library may be changed by root after the survey, so these contexts and fingerprints
refer to the pinned frozen commit, not an assumed future working-copy state.

The completed `runs-v3/survey-summary.json` identifies the valid source-failure record for
`TCSlib.Cryptography.SecureComputation.GarblingSpecial` and supplies its actual `attempt_log`.
This is **ordinal29**, whereas ordinal28 is `GarblingSecurity` and passed. The selected log
reports one diagnostic, at probe143 -> pinned source93, inside `nestedSpecial_decCorrect`.
INSTALL and EOF verify all 721 requested names (721 active, zero already irreducible).

`intro ks hks o r` cannot introduce binders from sealed foreign `MultiEnc.DecCorrect`.
The existing public `MultiEnc.decCorrect_iff` reader is already present in the pinned owner
`Garbling.lean` at line141. This proposal adds only:

`rw [MultiEnc.decCorrect_iff]`

before that `intro`, in the same existing proof block. It exposes exactly the original
correctness contract (at most two keys, every plaintext and random coin), then leaves the
entire existing case split and special-encryption argument byte-for-byte unchanged.
No missing owner reader is required. All headers, premises, definitions/data algorithms,
existing admissions and the `by` count are unchanged. No substantive proof is filled.

The remaining `nestedSpecial`/`innerLen` body reads in this proof are home-local definitions;
special-encryption correctness is used through its published `spDecStr_spEncStr` and length
readers. This is a minimal repair to the observed predicate-opening failure, not a native
claim that no further diagnostics can appear after that blocker is removed.

Static checks validated the pinned source against the completed V3 manifest, the summary's
actual-attempt binding, verified seal markers and source-line map, unchanged proof body
apart from this line, unchanged header/admission counts, and one-hunk patch application in
memory. Root retains application and serial native checking.

| Artifact | SHA-256 |
|---|---|
| Pinned `GarblingSpecial.lean` | `49123012fca34b318e4f975540641147ecf7062246ac8ad98c7a391158089f30` |
| Proposed `GarblingSpecial.lean` | `bd5fd95a4860e4eb3736ce865d151b26e23edbfcfc361a43e0f8bd64c7787fe2` |
| Proposal patch | `6084d10b4dbeb0646a09e5c3f844a9edd3588b99c2ac7275495b9ce759757e6f` |
| Pinned public-reader owner `Garbling.lean` | `2ecb46029b8a66f043f2b71c0c5d25ab5094bd36091ccc375c0aa06033d5c076` |
| Actual attempt log | `b90909deb22294aa0e69261b299312a981ceef6a0eef76e3a29acdb6d22426f2` |
| Survey summary | `672085e62d50fa3e4f710de667e2a135fee52fc5e9164556a4526a6dc4a7cbfd` |
| V3 seal manifest | `e0f7721d5a8b366fee1e247576741d152e9900423344bd200916fb38c93583af` |

Actual log: `/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-pass-shelat-ch2-4/briefs/pass-shelat-ch5-8/maintainer/gate06-integration-2026-11-06/evidence-rule10-r2/runs-v3/G06Seal_029_TCSlib_Cryptography_SecureComputation_GarblingSpecial_HarnessV3.log`.
