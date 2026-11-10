# Gate 14 review of the counted-loop host registration

Review H16 on draft [#250](https://github.com/Shilun-Allan-Li/tcslib/pull/250),
which targets `cryptography/lwe-sis-constructions`. This is the host gate
for the seven counted-loop and dependent efficiency fills. The two
asymptotic SIS CRH proofs depend on the collision-output postprocessor.

| Pin | Revision |
|---|---|
| Gate 13 passed Lean and root | `713093c36ac66f7e56e9354581f0bb3f59772341` |
| Exact proposal and registry preimage | `00ad74933f5755cc80f2a4d1d1788a81cae6a2b9` |
| Approved registry change | `2055a7425549d9d0e9cbd1f4c2bb9b9a7a8aeb11` |
| Central target at preparation | `41aaf0a1acf29318fa8d741dadd9f5f585e43c93` |
| Merge preview tree | `ee4ae5a44ced65dc3b80985e023e16a5485b43af` |

Read the bundled policy, workflow, registry, Gate 13 disposition, and
`prerequisites/02-counted-loop-registration/README.md`. Verify the payload
checksums and both ordered revision-qualified indexes.

1. Verify that the isolated registry commit adds exactly the approved H16
   row to `machine-library-design.md`. Match the patch and before/after hashes
   to the approval receipt. Check the pinned Lean tree, root, and build pins.
2. Check the actual public `forLoop_pairEncode`, `polyTimeComputable_forLoop`,
   and `forLoop_bound_of_ctx` contracts in `BinaryArith/Loops.lean`.
   Distinguish the intermediate word-length bound from a machine head bound.
   Check that the raw-word time guarantee and paired-state equation agree
   with the registry wording.
3. Check the composition with the existing H14 `clean_install` and
   `Clean.envelope` contracts. It must install the very same loop result
   on every argument, first halt within its polynomial budget, and bound
   every work head throughout the run by that budget. Verify the checked
   specialization and its six axiom prints.
4. Verify the exact 45-module dependency closure for the two probe
   imports. For independent native replay, use the bundled order and
   `scripts/lean_check_tree.sh` serially with the pinned Lean and Mathlib and a
   fresh object tree. Then check the bundled `HeadEnvelope.lean`. Report
   the checks actually replayed.
5. Review the named consumers and the host-policy disposition. The seven
   efficiency proofs and two CRH proofs remain a separate fill wave.

Return `lwe-sis-counted-loop-registration-findings.md` as Markdown in chat
with the verdict, severity counts, exact pins, and findings. The maintainer
dispatches the review and approves any merge.
