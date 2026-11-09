# Foundation landing evidence for PR #236

This PR fills the 14 audited LWE/SIS representation and input-budget proofs.
The source update registers Pei16 and attaches the approved attribution records
for the foundation slice. The checked Lean tree is the audited tree at
`0769cba3e44c56700349f954190fc99d9e622270`. The central target at verification
was `2c37f3f486822a52f4a9e337c6b742e995ebb118`, an ancestor of the candidate.

The registered reference covers Definitions 4.1.1, 4.2.1 and 4.2.3 from PDF pages
20 and 24. The 11 approved mappings document adaptations to the source statements.
The comparison records therefore remain outside automatic proof-source insertion.
The source status tool lists the registered reference with zero blueprint citation
macros. See `source-approval.json` and `comparisons.jsonl` for the approval and scope.

The archived PDF is the exact frozen source. The tracked raw extraction contains
all 90 page payloads, with one terminal blank line removed for Git whitespace
hygiene. The existing parser returns identical raw page data before and after
that formatting change. The repository's PDF ignore rule keeps the original PDF
in the pinned exchange archive. [Original PDF](https://github.com/Shilun-Allan-Li/tcslib/blob/a4e19bd3cf029b9bf5fb2e53989ddc0d61006ac1/lwe-sis-constructions/outbox/source-policy/01-earlier-stack-r1/inputs/peikert2016-lattice-survey.pdf)

| Check | Result |
|---|---|
| Scoped references | Registry, 2 anchors and 11 attribution records pass |
| Fresh serial Lean sweep | 55 modules in 172.809 s, 0 errors and 0 owned admissions |
| Inherited Lean warnings | 17 admissions in dependencies outside the foundation scope |
| Fresh axiom check | 61 source prints and 166 owned constants match the audited inventory |
| Campaign style | 0 failures and 2 existing reader warnings across 10 files |
| Dataset hygiene | 0 hard failures |
| Strict blueprint | 857 orphan labels, 0 dangling uses and 0 cycles. The output is byte-identical at the exact central base. |

The Lean sweep covers the Encoding, LWE and SIS facade closures using a fresh
owned olean directory and the manifest-pinned packages. Root export membership
was checked separately. The execution record gives the scope and process visibility
limits. `landing-checks.json` and `check-output.log` retain the evidence.

The approval covers the Pei16 attribution and registry update. The published PR
still points to the audited proof commit. The client must publish the checked
records commit because shell Git cannot resolve GitHub and the connector returned
HTTP 403 for the write attempt. The user's merge decision follows publication
and verification of the published head and target.

**Ready to run. Publish the checked foundation update on the existing PR branch.**
