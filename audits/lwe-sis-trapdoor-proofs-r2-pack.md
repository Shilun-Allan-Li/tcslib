# Gate 12 round 2 review of SIS encoding and finite trapdoor proofs

Re-audit the 40 fills on draft #250 after the approved shared subset-sum repair.
The draft targets `cryptography/lwe-sis-constructions`.

| Pin | Revision |
|---|---|
| Repaired Lean and root | `93dc88648f117877e42aaf58ba7b911c76a4b63a` |
| Round 1 Lean and root | `3bf1cb424b10abef3ae7a438c6b7d0e1916d0800` |
| Round 1 exchange | `7200aafd9ae628aeef6a7dd69f2125618b903433` |
| Round 1 records | `aff0a82679c201834415cbe293393fef7477f6e7` |
| Statement freeze | `17b2a282b545c6ebca3fccc88d518d18ae78f485` |
| F02 documentation repair | `d3bb52db5aaf249a35e83506371a3c86e76cb69a` |
| Exact approved patch and findings | `089c8dacf161a475ffff85b1b108b11529bd094c` |
| Central target with #255 merged | `41aaf0a1acf29318fa8d741dadd9f5f585e43c93` |

Read `AGENTS.md`, `policy.md`, `workflow.md`, the campaign plan, the
round 1 findings and dispositions, and the evidence under
`briefs/lwe-sis-constructions/fills/07-sis-trapdoor/`. Verify both ordered
indexes and the payload checksums. Use the pinned round 1 exchange for the
original packet and keep its findings separate from your new report.

1. Resolve F01 against the exact approved diff and policy §1. Review the
   statement, proof, ownership, and attribution of
   `LWE.binaryErrorSum_bound`. Verify that
   `Regev.subsetError_bound` and `Lossy.error_sum_bound` now apply it,
   preserving both signatures and their consumers. The proof generalizes
   the original Regev argument to a finite sample count with no lattice
   parameter dependencies. Check the new direct Mathlib import and the
   lossy module's import of the LWE owner.
2. Resolve F02 by checking the PW10 page ranges and the reference to
   `Lossy.Experiments`. Check that the F02 commit changes only comments.
3. Re-audit the full round 1 scope of 24 encoding and SIS fills and 16
   finite trapdoor fills. See the bundled first-round pack for the
   mathematical checks. Verify that the repaired library diff changes
   exactly the four disclosed paths, with 149 of the 153 frozen files
   byte-identical, two existing proof bodies replaced, and one added theorem.
   Check the 220 previous elaborated level/type representations, the 309
   axiom prints, the full owned inventory, and the exact 18 remaining
   admissions. Reconcile the fresh serial 144-module sweep and both probes.
   Report which native checks you independently run.
4. Carry N01–N04 forward. The scoped PW10 preflight and source-policy review,
   remaining counted-loop and gadget proofs, anti-cyclic rank, primitive
   bridges, and target and export landing checks have separate scopes.
   Verify the #255 prerequisite and the current merge preview.

Return `lwe-sis-trapdoor-proofs-r2-findings.md` in chat with the verdict,
severity totals, exact audited pins, separate F01 and F02 dispositions,
and any new findings. The user dispatches the review and controls merges.
