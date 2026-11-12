# Pass–shelat Gate 17 — CPA/CCA1 proofs, PR #293

**Verdict: CLEAR.** Findings: **0 blockers, 0 majors, 2 minors, 0 notes**. The pack closes the gate at zero blockers and zero majors.

| Pin | Revision |
|---|---|
| Exchange packet | `93dfe35805c56c063a111f0cf7bbe9817c77c53f` |
| Campaign records | `8260a492ed740fcfc6019b355d142ac7bb587c3d` |
| PR base | `ce22c4da63633601aa068dcc26dc0fcb7b6907f9` |
| Audited Lean head | `63ca0eb3dccb65542e90c181b7ceb0a4a4a46272` |

Scope: `Composability.prfFixedScheme_cpa`, `Composability.prfFixedScheme_cca1`, the six `OracleFromPRF/` helpers, the four authorized `OracleSecurity` readers, and the maintainer's landing edits. The packet, repository, worker report and maintainer review were treated as claims to verify. No source fixes, GitHub comments, pushes, dispatches or merges were made.

## Findings

| ID | Severity | File · declaration | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|
| G17-01 | minor | `OracleFromPRF/Lazy.lean:54` · `PRFGame.LState` | The new public abbreviation lacks its required equation lemma. | The pinned policy explicitly says a new public `abbrev` still lands with its `_iff` or `_eq` lemma. No such lemma accompanies `LState`. Maintainer review item 9 dismisses this because it is an abbreviation, overlooking the separate API requirement. | Add a public, non-`@[simp]` `LState_eq` beside the abbreviation, stating its product-type expansion in its docstring. |
| G17-02 | minor | `OracleFromPRF.lean:390` · CPA theorem docstring | The deviation paragraph attributes the brief's explicit quantitative bound and seed layout to the textbook. | PS10, Theorem 168.2 and its proof (book pp. 168–169; PDF pp. 180–181) give a qualitative negligible-collision argument and a PRF reduction, without that formula or a challenge-bit seed layout. Those details are proposed in the issued brief. | Replace “the source's bound” with “the issued brief's suggested bound” and attribute the seed layout to that brief. |

Both are API/documentation defects; neither invalidates the security proofs.

Evidence links: [LState at the audited head](https://github.com/Shilun-Allan-Li/tcslib/blob/63ca0eb3dccb65542e90c181b7ceb0a4a4a46272/TCSlib/Cryptography/Encryption/PrivateKey/OracleFromPRF/Lazy.lean#L54), [pinned abbreviation policy](https://github.com/Shilun-Allan-Li/tcslib/blob/8260a492ed740fcfc6019b355d142ac7bb587c3d/policy.md#L72), [deviation paragraph](https://github.com/Shilun-Allan-Li/tcslib/blob/63ca0eb3dccb65542e90c181b7ceb0a4a4a46272/TCSlib/Cryptography/Encryption/PrivateKey/OracleFromPRF.lean#L390), [issued brief](https://github.com/Shilun-Allan-Li/tcslib/blob/8260a492ed740fcfc6019b355d142ac7bb587c3d/briefs/pass-shelat-ch5-8/fills/pk-cpa-cca1/issued-r1/brief.md), [PS10](https://github.com/Shilun-Allan-Li/tcslib/blob/63ca0eb3dccb65542e90c181b7ceb0a4a4a46272/Pass%E2%80%93Shelat.pdf#page=180).

## Integrity and scope preservation

- **16/16** outer `SHA256SUMS` entries and **527/527** entries in the verification archive's inner manifest pass.
- All **16 ordered bundle sections** match their revision-qualified Git blobs. All **168 source modules** in `sources.zip`, and the local sources used for replay, match the pinned head's Git blob identifiers. The eight `source-head.json` hashes agree.
- The packet's PR diff equals the independently generated base-to-head diff: **eight files, 3003 insertions, 24 deletions**. The issue-base-to-PR-base changes do not alter Lean sources.
- Both target statement lines are byte-identical to the base. The owned file's original construction declarations and complete CCA2 suffix are preserved byte for byte. The permitted changes are the helper imports/section, module documentation, and target documentation/proofs.
- Removing exactly the four authorized readers from `OracleSecurity.lean` reproduces its base bytes. Each is public, has a formula docstring and adds no simp attribute. No other change occurs in that file.
- The landing diff removes the two duplicate lemmas, redirects their uses to `NUPPT.toComp_costBoundedBy` and `List.ofFn_injective`, and changes documentation/line wrapping. It preserves the statements and proof route.
- The source book matches Git blob `695a6b18d3e4c3fd9a7cacfc45b301c94b8c24b3` and SHA-256 `7624556077a7a272ba0b3ddb7cd47b96574fb0b4b4947a25467d1f91bb61bda8`.

## Proof review

1. **Reduction to a random function.** `exists_prfReduction` chooses a machine for each challenge bit before quantifying over the security parameter and oracle function. T2, the input-free companion and T4 preserve acceptance for every function. `comp_pkAbs`, `simulate_eq_of_abs_bounded` and `expect_eImpl` justify the state abstraction and uniform nonce tapes. The counter cannot exhaust its tapes while another budgeted query remains. The reduction's oracle budget is `qRed q`, evaluating to the original query budget.
2. **Matching the actual scheme.** The key and nonce equivalences preserve the corresponding strings and uniform distributions. `ofFn_prf_encryptAt`, `ofFn_prf_decAnswer` and `expect_indImpl_fImpl` match the three oracles call by call. Well-formed decryption uses the evaluator only where its agreement hypothesis applies; malformed decryption returns rejection. Width transports use proved equalities. The positive-parameter restriction in this matching is discharged separately at zero in the final bound.
3. **Lazy sampling.** `expect_lazyImpl` relates a uniformly sampled full function to the lazy table and challenge record. The bad flag covers a first challenge nonce already queried by encryption or pre-challenge decryption, and an encryption nonce hitting the challenge after it. `lazyImpl_agree` gives equal laws on good successors by the XOR permutation. Decryption closes after the challenge under both audited attacks. `lazyImpl_step`, `lazyImpl_grow` and `prob_bad_le` supply the quadratic collision bound.
4. **Closing security.** `prf_advantage_le` uses the triangle inequality through the two random-function experiments. Its bound is

   `advantage ≤ prfAdv(F_n, D₀) + prfAdv(F_n, D₁) + (q(n)² + 1)·2⁻ⁿ`.

   At zero, the extra constant covers `advantage ≤ 1`. `prf_indSecure` applies PRF negligibility twice, polynomial-times-exponential negligibility, and closure under addition. Both final theorems retain their frozen hypotheses and conclusions.

Budget zero, no challenge, repeated challenges, challenge-ciphertext decryption, malformed decryption and timeout outputs are covered by the same computations and branch equations. Repeated challenges reuse the record; CPA and post-challenge CCA1 decryption reject.

One reduction per bit is sound. The quadratic finite bound is weaker than the brief's suggested linear bound, but remains negligible and proves the unchanged asymptotic statements; the brief permits the exact bound proved. Covering later encryption collisions does not establish the maintainer review's stronger assertion that a quadratic bound is necessary.

## Verification

Lean **4.25.0**, compiler commit `cdd38ac5115bdeec5f609e9126cce00f51ae88b3`; Mathlib **`029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`**.

- **Fresh build:** 168/168 modules pass in dependency order into a new olean tree, through `lean_check_tree.sh`; zero errors. All eight changed modules have zero warnings and admissions. The closure's 18 remaining admission warnings occur in unchanged dependencies.
- **Axioms:** from that freshly rebuilt closure, both targets, both preserved CCA2 results and all **432 stored constants** of the eight modules use only `propext`, `Classical.choice` and `Quot.sound`.
- **Whole-file seals:** all **8/8** pass over their complete TCSlib import closures, with **678–2,281 definitions** sealed per file. Probe bodies match the pinned source; request sets were compared with the compiled environment catalogue. The harness verifies actual names, home modules, metadata, installed seals and persistence at EOF.
- **Additional evaluation check:** `PolyExpr.eval` is excluded by the supplied harness as notation. Independently sealing it also passes for all six helpers, `OracleSecurity`, and the owned file through both new target proofs. Thus the new proofs do not rely on that exclusion; the frozen CCA2 suffix is outside this focused check.
- **Controls:** all **16 paired unsealed/sealed probes** have the expected outcomes: **226/226** deliberate body reads pass unsealed and fail sealed, while the reader-positive controls pass. Error locations match the individual expected failures, with no stray errors.
- **Explicit reads:** reviewed the supplied **1,376-item** classification, its unresolved names, the actual proof text and the landing delta; no forbidden new explicit definition read was found.
- **Style/API:** independent lint has **0 FAIL**, with five warnings confined to unchanged files. Every changed file is below 1000 lines; the facade imports and lists all six helpers. The two findings above require review beyond the mechanical lint.

The accompanying ZIP contains the report and independent build receipts/logs, axiom output, whole-file seals, paired controls, focused evaluation probes and lint output.

The supplied broader integration evidence was checked separately: the pre-landing **251-module** build, the final **10-module** rebuild and **28-module** downstream checks report zero failures. The final downstream source hashes match the pinned Git bytes. These broader runs were inspected as supplied evidence; the independent rebuild is the 168-module proof closure, rather than the entire downstream library.

The generic copies and promotion requests recorded in **DL-34** remain under the pack's stated consolidation disposition. No additional undisclosed copy or new private machine host was identified.

**Disposition:** correct proofs and preserved scope; address G17-01 and G17-02 as minor API/documentation repairs. Dispatch and merge remain with the user.

Notation: `n` is the security parameter; `q(n)` is the query budget; `F_n` is the keyed function family at that parameter; `D₀`, `D₁` are the PRF distinguishers for the two challenge bits. Other names are Lean declarations from the audited source.
