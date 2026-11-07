# ComposeSecurity: explicit dependent-tape length chains

**Unapplied, unchecked follow-up.** This proposal changes only the existing `hrA` and `hrB` bodies inside `HybridProtocol.compose_msg_bound`; it adds no tactic block or owner API. The parent theorem's header, all premises, algorithms, definitions and admissions are unchanged.

## Input and observed failures

Worktree: `/Users/seyoonr/.codex/worktrees/ps-gate06-integration/tcslib-pass-shelat-ch2-4`.

Observed Git HEAD: `55404e9dbb48c5d3e020e55bcd670491c8b2e028`. The patch is based on the archived **diagnostic original-source snapshot**, not a claim that the mutable file equals that Git blob. The snapshot and current library bytes were verified equal before proposal generation:

- File: `TCSlib/Cryptography/SecureComputation/ComposeSecurity.lean`.
- Snapshot: main records `briefs/pass-shelat-ch5-8/maintainer/gate06-integration-2026-11-06/evidence-rule10-r2/diagnostic-evidence/OLD_COLLECTOR_DIAGNOSTIC_NOT_FINAL_COVERAGE_R2_ComposeSecurity/OLD_COLLECTOR_DIAGNOSTIC_NOT_FINAL_COVERAGE_R2_ComposeSecurity.original.source.txt`.
- Input SHA-256: `040577e7d6e02546a02c7bd55b92c2b1e894ab46fca16e5abd2fc23b80f0e23f`.
- Proposed complete-file SHA-256: `168080a558796644fe60752ee0942fa5ac719f27fcc2fec55991e11eef57c3df`.
- Separate patch SHA-256: `ca1857d4e3ca6d80de05f28f80b92f71315eb0c75fc1663d092c8a0108e8d496`.

Native diagnostic log (read only): the same diagnostic directory's `native/OLD_COLLECTOR_DIAGNOSTIC_NOT_FINAL_COVERAGE_R2_ComposeSecurity.log`, SHA-256 `691e6a561ed2bc88e5971898172139a48ca4500ba9384269969f72b9bca9abe8`.

| Local have | Original source | Instrumented probe | Log line | Observed mismatch |
| --- | --- | --- | --- | --- |
| `hrA` | 212–216, failing 215 | 265:4 | 636 | Supplied equality starts with the composed Alice strategy's evaluated coin polynomial; target still starts with `(List.ofFn r.1).length`. |
| `hrB` | 217–221, failing 220 | 270:4 | 646 | Same mismatch for Bob and `r.2`. |

The metadata records two error diagnostics and a failed run with no fresh object. The log's label explicitly says **OLD_COLLECTOR_DIAGNOSTIC_NOT_FINAL_COVERAGE**. This is useful source-level failure evidence, not a final coverage seal or acceptance result. Its local seal line reports requested/active/verified 632; no inference is made about completeness of that older collector.

## Repair and public contracts

The earlier `simpa only [List.length_ofFn, Strategy.coinLen_eq] using ...` does not rewrite the target's dependent `List.ofFn` applications under the seal. The follow-up supplies the dependent function explicitly to the length theorem and joins concrete equalities, avoiding rewriting inside the coin function's type.

For Alice, the term chain is:

1. `List.length_ofFn (f := r.1)` identifies the list length with `(H.compose ρ).P.coinLen |1^n|`. The domain is read from the type of `r.1` through the allowed `ExecCoins`/`Coins` abbreviations.
2. `H.compose_P_coinLen ρ |1^n|` gives `H.main.P.coinLen |1^n| + H.calls.eval |1^n| * ρ.P.coinLen |1^n|`.
3. `congrArg₂` for the function `(a,b) ↦ a + H.calls.eval |1^n| * b`, with two `Strategy.coinLen_eq` terms, converts the component lengths to their evaluated coin polynomials.

Bob uses the identical chain with `r.2`, `compose_V_coinLen`, and the two verifier strategies. These are term proofs, with no `simp`/`rw`/`unfold` list and no direct foreign body read. `PolyExpr.eval` remains approved notation. No `Fin` cast or new logical hypothesis is needed.

Existing owner interfaces read during this review:

- `ZeroKnowledge/Interaction.lean:126`: `Strategy.coinLen_eq (S) (n) : S.coinLen n = S.coins.eval n`.
- `Interaction.lean:129,339`: the reducible `Strategy.Coins` and `Protocol.ExecCoins` abbreviations give the two finite coin-domain types.
- `SecureComputation/Compose.lean:443,463`: `compose_P_coinLen` and `compose_V_coinLen` have exactly the component-length contracts used above.
- Core `List.length_ofFn`, instantiated with the named `f` argument; current Mathlib uses that instantiation in `Mathlib/Data/List/OfFn.lean`.

Reader input fingerprints:

- `Interaction.lean`: `12141ce2905f6be5a7266b4e0abce797abe75c8c1d802f32b5ee6a30a0440198`.
- `Compose.lean`: `59529af613014714e30f7a484a537a29a9041534a1ba88ee812db20f0d7fba5c`.

## Scope and remaining check

Static checks verified one existing parent proof declaration changed, every byte outside that declaration identical, the theorem header identical, and the admission census unchanged. The patch replaces two existing nested `by` bodies with terms: zero new tactic blocks and two fewer existing nested tactic blocks. All other proof text, including the existing proof sketch, is untouched. The sketch continues to describe the mathematical proof accurately.

Earlier ComposeSecurity proposals and their notes remain separate and unchanged. This patch applies to the current archived diagnostic snapshot after those earlier changes; it should not be applied directly to the original frozen `e9d64158461bfe24ddc88ab885bc4017899b4c16` source. No additional module enters the touched scope.

Only this unapplied patch and notes were saved in ignored repairs. No library edits, Lean/cache/build commands, computer apps, Git mutations or received-program execution occurred. Root must check the updated module with its current dependency objects and final collector/seal. This proposal does not declare the earlier diagnostic or any final gate passing.

**Not yet clear to merge — the two explicit equality chains are unapplied and require root's serial native check.**
