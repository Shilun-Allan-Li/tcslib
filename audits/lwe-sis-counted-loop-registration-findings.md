# Gate 14 round 1 findings

**PASS** for the H16 registration and its public time and work-head contracts. **0 blockers, 0 majors, 0 minors, 1 scope note.** [Draft PR #250](https://github.com/Shilun-Allan-Li/tcslib/pull/250)

## Exact pins

| Item | Revision or value |
|---|---|
| Exchange `exchange/pass-shelat-ch5-8` | `20436a1bea0ebeb636c2a0ca39acfa9969a4caae` |
| Lean library and root | `713093c36ac66f7e56e9354581f0bb3f59772341` |
| Proposal and registry preimage | `00ad74933f5755cc80f2a4d1d1788a81cae6a2b9` |
| Approved registry commit | `2055a7425549d9d0e9cbd1f4c2bb9b9a7a8aeb11` |
| Bundled records and draft head | `a65cc24d64766786fa43f2cc43ca91dbba8076ef` |
| Central target `cryptography/lwe-sis-constructions` | `41aaf0a1acf29318fa8d741dadd9f5f585e43c93` |
| Pass–Shelat registry preimage comparison | `8fae4be42ba253578165e8449f0aa65cac71edf0` |
| Approved-revision merge preview tree | `ee4ae5a44ced65dc3b80985e023e16a5485b43af` |
| GitHub draft merge ref and tree | `f2353f32d55aea2af316ec01339654d95354cfe5` · `5024759af6b45d3b7e918ea1b83f4d0a47a11480` |
| Lean and Mathlib | `leanprover/lean4:v4.25.0` · `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e` |
| Bundle SHA-256 | `fe14943b939a24faf179a3965a1c8c1ee447f190384bc4bd7aff4551c06c8fad` |
| Bundle extent | 2,126,042 bytes across 77 sections |

## Findings

**Packet and approval.** All five outer and three nested checksums passed. Both ordered indexes agree on revision, path, byte count, and SHA-256. All 77 sections matched their pinned Git blobs, including the first-section pack. The isolated commit inserts exactly one row, H16 immediately after H15. I applied the approved patch to the pinned preimage and reproduced the postimage byte for byte. Both base pins carry the same registry preimage. [Exchange packet](https://github.com/Shilun-Allan-Li/tcslib/tree/20436a1bea0ebeb636c2a0ca39acfa9969a4caae/lwe-sis-constructions/outbox/gates/14-counted-loop-registration-r1) · [Approval receipt](https://github.com/Shilun-Allan-Li/tcslib/blob/a65cc24d64766786fa43f2cc43ca91dbba8076ef/briefs/lwe-sis-constructions/prerequisites/02-counted-loop-registration/approval.json)

| Approval fingerprint | Verified SHA-256 |
|---|---|
| Registry preimage | `f4f5cba99f0321f044340adfb3f3221170ed4ec1bfc212c3fdb7dd318b495292` |
| Exact patch | `ba2c8e1f1b163552337cac3c589c0a4c0e4db323a7638897a1789ef678c276fa` |
| Registry postimage | `e769794acf6922696b8b174fbdae22b2b5bf931b55085cf02591becb89acf0a5` |

I independently recomputed both merge trees against the pinned target. The proposal, approval, draft head, and both merge trees match the Gate 13 `TCSlib/` tree, `TCSlib.lean`, toolchain, Lake configuration, and manifest. [Registry change](https://github.com/Shilun-Allan-Li/tcslib/commit/2055a7425549d9d0e9cbd1f4c2bb9b9a7a8aeb11)

**Counted-loop contract.** `forLoop_pairEncode` gives `forLoop f (pairEncode c d) = pairEncode [] (f^[c.length] d)`, including an empty counter. An undecodable raw word is fixed. Given an FP leaf and the uniform length bound `B * ((pairEncode c d).length + 1)^b` on `f^[j] d` for every `j ≤ c.length`, `polyTimeComputable_forLoop` gives an FP implementation on every raw word. `forLoop_bound_of_ctx` gives the intermediate word-length bound with coefficient `A + 1` and exponent `2` when the first projection is preserved and each step adds at most `A * ((pairFstD d).length + 1)` bits for every body argument. [Loop contracts](https://github.com/Shilun-Allan-Li/tcslib/blob/713093c36ac66f7e56e9354581f0bb3f59772341/TCSlib/Complexity/ClassP/BinaryArith/Loops.lean#L74-L194)

**Clean installation.** Applying `clean_install` to that FP proof gives one finite machine and a polynomial budget `C * (arg.length + 1)^e` for every native input and raw argument. By `clean_iff`, the call first halts at a positive time within the budget, at the seam holding exactly `forLoop f arg`, with empty output. `Clean.envelope` bounds the absolute position of each work head by the same budget at every time. Before the halt this follows from unit moves from the origin, and the configuration stays fixed after the halt. [Clean contracts](https://github.com/Shilun-Allan-Li/tcslib/blob/713093c36ac66f7e56e9354581f0bb3f59772341/TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean#L198-L259) · [Installer](https://github.com/Shilun-Allan-Li/tcslib/blob/713093c36ac66f7e56e9354581f0bb3f59772341/TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean#L305-L331)

## Independent native replay

- Recomputed the transitive closure of the two probe imports and verified the exact 45-module topological order. Ran `scripts/lean_check_tree.sh` serially using the pinned Lean and verified package caches. The fresh object tree contains 45 library objects. The logs show zero errors, 17 inherited admission warnings, and 131 other warnings in the frozen sources. [Module order](https://github.com/Shilun-Allan-Li/tcslib/blob/a65cc24d64766786fa43f2cc43ca91dbba8076ef/briefs/lwe-sis-constructions/prerequisites/02-counted-loop-registration/module-order.txt)
- Checked the bundled `HeadEnvelope.lean` against those fresh objects. Its six axiom prints matched the supplied log byte for byte. The specialization, the three loop theorems, `clean_install`, and `Clean.envelope` each depend exactly on `propext`, `Classical.choice`, and `Quot.sound`. [Probe and log](https://github.com/Shilun-Allan-Li/tcslib/tree/a65cc24d64766786fa43f2cc43ca91dbba8076ef/briefs/lwe-sis-constructions/prerequisites/02-counted-loop-registration/evidence)
- Checked a separate scratch specialization with `forLoop` and `Clean` locally irreducible. It derives the length premise from the retained context, uses `clean_iff` and `forLoop_pairEncode` to obtain the exact paired endpoint and first-halt clause for the same machine, and obtains the head bound for every raw argument. Its axiom print has the same three axioms.

## Consumer scope

| Pending FP proof | Use of H16 |
|---|---|
| `polyTimeComputable_expandPoly`, `polyTimeComputable_dotWords` | Direct loops over `expandStep` and `dotStep` |
| `polyTimeComputable_dotPoly`, `polyTimeComputable_matVecStep` | Compose the packed dot-product contract |
| `polyTimeComputable_matVecPoly`, `polyTimeComputable_collisionOutputPoly` | Direct loops over `matVecStep` and `collisionOutputStep` |
| `polyTimeComputable_hashPoly` | Composes expansion and matrix-vector evaluation |

Each of the four direct loop bodies has public context-preservation and growth lemmas over all raw words, with growth coefficient eight. The registration satisfies the host-first prerequisite through the existing public contracts. [Host policy](https://github.com/Shilun-Allan-Li/tcslib/blob/713093c36ac66f7e56e9354581f0bb3f59772341/policy.md#L103-L116) · [H16](https://github.com/Shilun-Allan-Li/tcslib/blob/2055a7425549d9d0e9cbd1f4c2bb9b9a7a8aeb11/machine-library-design.md#L3093)

**N01 (scope).** The seven FP proofs and two SIS collision-resistance proofs are the separate fill wave. `negligible_collisions_of_SIS` uses the collision-output postprocessor, and `dyadic_collision_negligible` specializes that result. Gate 13 tracks the remaining source matching and landing checks. [SIS reduction sketch](https://github.com/Shilun-Allan-Li/tcslib/blob/713093c36ac66f7e56e9354581f0bb3f59772341/TCSlib/Cryptography/Hashing/SIS/Asymptotic.lean#L60-L88) · [Gate 13 disposition](https://github.com/Shilun-Allan-Li/tcslib/blob/a65cc24d64766786fa43f2cc43ca91dbba8076ef/audits/lwe-sis-gadget-inversion-proofs-resolutions.md)

**Notation.** FP is polynomial-time computability of word functions. `f` is the leaf, `c` the counter word, `d` the body argument, and `f^[j]` the `j`-fold iterate. `B, b` are the iterate-length coefficient and exponent, `A` is the per-step growth coefficient, `arg` is a raw call argument, and `C, e` are the clean-call budget coefficient and exponent.
