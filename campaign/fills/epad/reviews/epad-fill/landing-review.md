# E-PAD incoming-delivery review and landing repairs

Delivery commit: `7d16731e963f60a4ba97e79ec7dba41c86dca1bb`. Landing repair commits: `3a0cb27fe50868317ced9710769add53036f52e8` and `b6c2f5e4b8ce3bc18c385a09a3bf5dc26b75c205`.
PR: [#228](https://github.com/Shilun-Allan-Li/tcslib/pull/228), based on `complexity/arora-barak-ch3-4`.
Gate 115 is reserved; it has not been dispatched. **Not yet clear to merge.**

## Evidence handling

The pinned exchange archive passed all 118 payload checksums, path/size/symlink checks, and the outer REPORT comparison (`receipt.json`). The Git bundle verifies and matches the delivered source. Four patches were applied with `git am -3` on the current campaign, preserving the original authors and using Codex as committer. Only `SpaceComplexity/Padding.lean` changes. The original delivered source is retained as `delivery/Padding.lean.txt`.

The maintainer read all 1,762 delivered library-source lines before elaboration. A separate internal review also read the complete source; it ran no Lean or delivered tooling. Its findings are retained verbatim in `internal-review.md` (SHA-256 `f5c9db8a84ee464b348f48909ad1640f67daaf86b4110dc81935efefb8d9cc26`). The delivered REPORT is retained verbatim (SHA-256 `238582d877084f606af224e7d5768a2046d8f5877d7ae6ac4895fc9f284a9767`); its claims are attributed to the delivering agent, not converted into maintainer attestations. No delivered shell or Python tool was executed.

## Dispositions of the internal findings

| Item | Disposition in the landing repair |
|---|---|
| R1, duplicate `2^|bits n|` bound | Deleted `epad_two_pow_bits`. The decoder cap now splits at zero and cites the already reachable `LogProg.two_pow_bits_le` for the positive case. It uses no unmerged NatBits declaration. |
| R2, two inline binary-length bounds | Both now cite `Turing.length_bits_le_self`, with the existing surrounding inequalities. |
| R3, name removed by NatBits | Code and explanatory prose cite the canonical `LogProg.bitsVal_lt_two_pow`. Removed the now-unneeded `Codec.Word` import. This makes either PR's merge order possible without that deleted explicit name. |
| R4, non-private-constant count | The REPORT's three source declarations are correct, but its claim of only three non-private constants is contradicted by its own axiom log: `mem_SPACE_padLang._proof_1_1`, `._proof_1_2`, `._proof_1_3` are also present. They are compiler-generated proof auxiliaries. The original report is unchanged; the fresh landing census confirms six non-private constants (three source declarations and three internal proof auxiliaries); all 506 compiled constants use only the standard three axioms. |
| R5, proof sketches | Added substantive English sketches to `epad_ones_loop`, `epad_mul_loop`, `epad_pow_loop` and `epad_val_run`. |
| R6, source prose | Removed new checkpoint/campaign provenance and corrected the old statement-only/copying description to describe the completed virtual-input proof. Mathematical statements remain frozen. |

The maintainer also replaced two zero-case update-extensionality blocks in `epad_mul_loop` and `epad_pow_loop` with `Function.update_eq_self` and arithmetic equations. These are the existing identity-update facts, used directly through the published Mathlib API.

The current source census is **3 → 3 public source declarations, 0 → 49 private**; no public additions/removals, no statement changes, no surviving public/private order changes, and only the authorized public proof body changes. The delivered source had 50 privates before R1's deletion. Current size: **1,769 lines**. The policy linter reports only size; size is not a split or delay driver under WORKFLOW §2.

## Architecture and remaining execution

The virtual input is empty on malformed words. The validator and the two bank languages use concrete register machines; the run phase uses the published `OIS.compile_decides` host; the final conditional rejects invalid padding. The constant `S 0` is absorbed by the linear lower bound on `T`, without monotonicity or computability assumptions on the bound functions. The internal source review found no new private host needing a design ruling.

The review's supplied seal inventory has 36 definitions and explicitly excludes abbreviations, projections, one generated eliminator and a matcher in a published statement. Maintainer probes are prepared, including a first-equation and parameter-abstracted-equation control for each definition. The module plus three boundary probes pass; the independent replay passes two modules with zero failures/static mismatches; all 506 constants use only the standard axioms; all 72 controls close unsealed and fail sealed. The fresh walk partitions 46 foreign definitions into the 36 effective seals and ten explicit exclusions, and all 122 citations from 20 modules are covered by the 23-file screen population. The matcher limitation and four reducibility rejections were reproduced. Gate 115 contains the exact inputs, outputs and cross-checks.

The follow-up Core list-equation repair preserves the reduced import set after removing Codec.Word. Its initial failed preflight is retained separately. The final gate evidence, not the original delivery report, is the authority for the landing execution results.
