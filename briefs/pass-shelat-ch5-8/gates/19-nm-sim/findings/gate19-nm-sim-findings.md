# Pass–shelat Gate 19 — external Codex audit

**Verdict: CLEAR.** Both target proofs pass. There are **0 blockers, 0 majors, 1 minor, 0 notes**. The documentation minor below does not prevent closure under the pack's zero-blocker/zero-major rule.

| Pin | Audited revision |
|---|---|
| Draft PR | [#297](https://github.com/Shilun-Allan-Li/tcslib/pull/297) |
| Lean head | `5da558b4d97aca00efd6dc396a1b0f3bffff268b` |
| Comparison base | `691f30f81af5c1c28d3d2c9abaadb88dc42bd4b0` |
| Campaign records | `40213c18618ed1fa6df725b32a6bd3ed9c4054a3` |
| Exchange | `d17ee1ca7e57fa3e9e0e7425fff5e8991b666678` |

Scope: the two frozen implications in `FixedLengthPKScheme`, the ten `NonMalleability/Simulation/` helpers, and the maintainer's landing edits. The source formulation is the previously gated, single-message SIM-NME′ convention documented in `Simulation.lean`.

## Finding

| # | Severity | File · declaration | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|
| G19-01 | minor | [Simulation/IndSim.lean:20](https://github.com/Shilun-Allan-Li/tcslib/blob/5da558b4d97aca00efd6dc396a1b0f3bffff268b/TCSlib/Cryptography/Encryption/PublicKey/NonMalleability/Simulation/IndSim.lean#L20) · module docstring | The required `## Main definitions` section is absent. | The module introduction proceeds directly to `## Main results`, then `## References`. [Policy §1, File header](https://github.com/Shilun-Allan-Li/tcslib/blob/40213c18618ed1fa6df725b32a6bd3ed9c4054a3/policy.md#L135) requires both sections in every math-file module docstring. | Add `## Main definitions`, stating that this module introduces no definitions. |

## Verification

| Check | Result |
|---|---|
| Pack integrity | `sha256sum -c SHA256SUMS`: **16/16**; all **17** pack files, including the manifest, match the pinned Git bytes. Bundle SHA-256: `d4786c2600a1a877ff3743abec3b95af035ad64764ff76085d7c954dd22ffb2a`. |
| Inner review archive | **685/685** checksums pass; no unlisted payload files. |
| Bundle provenance | All **21** ordered, revision-qualified sections match their designated commits byte for byte. |
| Source and diff | All **171** archived Lean source files match the head and the independently assembled closure. The complete supplied diff matches Git; exactly **11** authorized files change. |
| Fresh build | **171/171 modules**, zero errors, using Lean **4.25.0** (`cdd38ac5115bdeec5f609e9126cce00f51ae88b3`) and Mathlib `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`. |
| Statement freeze | `decls2`: **269 added, 0 changed, 0 removed**. Declaration-body comparison confirms that only the two authorized pre-existing theorem bodies/sketches changed. Security definitions, experiments and the existing equivalence are preserved. |
| Axioms | Independently checked **all 574 stored constants**. Dependencies are subsets of `{propext, Classical.choice, Quot.sound}`; none uses `sorryAx` or another axiom. This includes both targets and `simNMSecure_cpa_iff_nmSecure_cpa`. |
| Rule 10 seals | **22/22 head seals** and **2/2 base controls** pass, including the variant sealing `PolyExpr.eval`. Request sets, exact Lean name components, module ownership and elaborated foreign references agree with a fresh environment census. |
| Independent paired controls | Published-reader proofs pass unsealed and under both seals. The four direct-reduction controls pass unsealed and fail individually under each seal: **8/8 intended failures**, with no reader failures. Together with the two census probes, **32/32 runs** have the expected outcome. |
| Explicit unfold scan | Fresh scan: **1,850 items**, zero forbidden foreign-definition reads. The **320** unresolved/local entries were inspected: local proof terms, proof fields and dot-notation/open-namespace theorem readers. |
| Lint and API | PublicKey lint: **0 failures, 6 warnings**, identical to the base. All 11 files are below 1,000 lines and have no lines over 100 characters. No new global simp attributes; public definitions have their equation, field or machine readers. |
| Landing edits | All 11 files preserve their code tokens outside comments, relative to delivered head `61ebc3962708c4fe6ac6f1f16381735b87d0611a`. The added formulas and sketches describe the implemented route. |

The fresh closure build reports 18 pre-existing admission warnings in other modules. The transitive axiom census above confirms that none is a dependency of any of the 574 audited constants.

## Proof review

1. **Experiment transport.** `castImpl_snmImpl`, the two view equalities, and `accept_snmReal_eq` / `accept_snmIdeal_eq` identify the frozen experiments with the helpers' acceptance rates. These equalities cover the codecs' actual padding and timeout behavior.
2. **`nmSecure_of_simNMSecure`: PASS for every attack.** The sampler has exactly one uniform coin. The forwarding handler preserves decryption availability and challenge refusal for each attack. The same simulator is chosen before applying both derived distinguishers. The real identity uses equal-until-bad coupling on equal challenge messages; the ideal identity uses the empty history's independence from the sampler coin. `abs_le_of_gap` gives the stated constant-factor bound, and the negligible-function closure finishes the proof.
3. **Budget reduction: PASS.** `buildComp_budget_eq` inducts on the smaller budget. A positive-budget query consumes one unit on every continuation; the zero-budget timeout case is handled separately. The simulator's handler makes at most one outer query on every path, and finalization makes none. Its declared finalization allowance ensures the constructed budget is at least one even when the adversary budget is zero, so `toCompOn_budget_eq` legitimately transfers it to the ideal experiment's budget one.
4. **`simNMSecure_of_nmSecure_cpa`: PASS.** `exists_simulator` fixes a simulator independently of the distinguisher and identifies its ideal experiment with the independent-draw hybrid. `exists_nmAdversary` identifies both NM experiments with the two hybrids for positive message length. Correctness makes the two bit-encoding ciphertexts distinct, so at most one is refused as the challenge; recovery is exact. For empty messages the hybrids agree, giving zero advantage. Sampler advice is hard-wired through the published NUPPT interface.

| Boundary case | Resolution checked |
|---|---|
| Zero query budget; no challenge | The whole-run equalities retain timeout outputs and the default zero parameter. |
| Repeated challenges | The first challenge's record is replayed without a second outer query. |
| Empty output tuple or auxiliary string | Empty ranges and tails are handled by the exact list/finite-string equalities. |
| Challenge copied in the output | The copy flag is preserved; dropping it yields precisely NM's refusal value. |
| Invalid ciphertext | The existing total decryption/decoding and refusal conventions are preserved. |
| Empty ciphertext | The simulator has an explicit branch; positive message length implies positive ciphertext length. |
| Equal challenge messages | The coupling and distinguisher identities include this case. |

## Recorded dispositions and evidence scope

DL-36/DL-37 record the accepted duplication and its named consolidation payback. I found no additional duplication requiring a new disposition, and no defect in the recorded payback or landing order.

My fresh build covers the 171-module import closure. The supplied full-library landing evidence has **15 successful, source-bound rows**, including the three downstream facades and root `TCSlib`; those records were checked against the pinned sources.

The companion ZIP contains this report, independent build and probe logs, the prepared probes, the statement comparison, checksum results and reproduction instructions. Dispatch and merge remain with the user.
