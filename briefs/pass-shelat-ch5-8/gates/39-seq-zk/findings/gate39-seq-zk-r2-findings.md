# Pass–shelat Gate 39 — seq-zk, round 2

**Verdict: CLEAR. Open findings: 0 blockers, 0 majors, 0 minors, 0 notes.**

**G39-01 is closed.** No new mathematical defect, regression, or undisclosed duplication was identified. The round-1 confirmations still hold at the audited head.

| Item | Audited revision |
|---|---|
| [Draft PR #327](https://github.com/Shilun-Allan-Li/tcslib/pull/327) | `a94ba750b2f21ea5f2c3e58bc7959ad5ac9de871` |
| Round-1 head | `bd19c433a4cf3d4027ffc891d7d3c06e927e9dfa` |
| Exchange | `30acab69c5ca5ad4b2dae1344736a6039d6010c6` |
| Campaign records | `2c42911bf538feb40d2f124a6cc8c21f0cbe3307` |
| PR base | `05d26fe5b41fcb9426ec220d877d03264b9c8e8c` |

This is a source re-audit and an independent verification of supplied native build/probe evidence, **not a fresh Lean build**. Live PR metadata confirmed the pinned head and draft status. No repository source, PR, dispatch record, or merge was changed.

## Round-1 finding

Paths below are under `TCSlib/Cryptography/Composability/SequentialZK/`.

| ID | Round-1 severity | File · declaration | Round-2 disposition | Evidence | Further fix |
|---|---|---|---|---|---|
| G39-01 | major | `RealPrefixBounds.lean:85` · local `hsource` in `PaddedProverSpec.realPrefix_bounds` | **CLOSED.** The inline re-proof is replaced by the existing public lemma; the added import is acyclic. | Exact Git diff, unchanged header/prose, independently computed closures, successful rebuilds and four seals. The resolution and decision log record the removed overlap. | None. |

The repaired proof is exactly:

```lean
  have hsource (hist : List (List Bool)) : (ρ.P.next x y tape hist).length ≤ B :=
    d.next_length_le y B hbound tape hist
```

`hbound` has the public lemma's required hypothesis. Applying its universally quantified conclusion to `tape` and `hist` gives exactly the local bound. Both later uses of `hsource` remain unchanged. The duplicate is removed rather than retained as debt; no duplication-ledger acceptance is needed.

## What is new since round 1

The head's sole parent is the round-1 head. The one additional commit, **LE-gate39**, changes only `RealPrefixBounds.lean`, **+5/−5**. Its SSH signature validates against the embedded public key; this does not independently authenticate the human operator.

The complete delta is the added `ProofTransfers` import, the replacement above, and one inserted sketch sentence naming `next_length_le`. An exact reconstruction from those three edits reproduces the head file. The statement header and statement prose are byte-identical. The other **40 unit files** are byte-identical to round 1.

The source checks reproduce:

| Check | Result |
|---|---|
| Named declaration headers and definition blocks | **264/264** headers and **42/42** definition blocks unchanged; the separate anonymous Prop-valued instance is also unchanged. |
| `decls2` against round 1 | **Empty**. |
| `decls2` against the PR base | **196 ADDED, 0 CHANGED, 0 REMOVED**. |
| `RealPrefixBounds` import closure, including itself | **144 → 145**; the only added module is `ProofTransfers`. |
| `ProofTransfers` closure, including itself | **136** modules; excludes `RealPrefixBounds`, and lies inside its former closure plus `ProofTransfers`. |
| Union of the unit's source closures | **185** files, unchanged. Every supplied source matches its pinned Git blob. |
| Frozen facade and `ZeroKnowledge/Defs` | Unchanged from round 1; frozen-header/prose/definition comparison still passes. |
| Lint | FAIL/WARN line set identical to round 1: **92 FAIL / 101 WARN**, with no new failure. |

The new import contributes two theorems, with no new definitions, instances, or simp attributes. Together with the unchanged sources and the refreshed seals, this supports carrying forward the other 40 files' round-1 seal results.

## Rebuilds, seals, and axioms

All **20 outer manifest entries** verify; the **21 pack files**, including `SHA256SUMS`, match the pinned exchange blobs. All **934 landing**, **1248 integration**, and **23 verification** manifest entries verify, with exact ZIP file sets. All ten bundle components match their listed Git revisions. The round-1 pack copy and findings match the earlier materials.

The two build-tree hashes were independently reconstructed from the pinned tip and disjoint PR deltas; verification does not depend on obtaining the maintainer's unpublished scratch commits.

| Evidence | Independent result |
|---|---|
| #327 alone on the tip containing #326; tree `daac61401cafe36fb036598e1bb33cdf6d5e743e` | **679/679 rc 0**. Every raw log hash and source hash verifies; both diagnostic forms (`error:` and `error(`) and the error substring count are zero. There are 420 warnings, including 59 existing admission warnings. The affected eight-module seed set has no admission warning; its sole warning is the disclosed unused `hQ`. |
| Solo reference comparison | **678/679** source/olean hash pairs match an earlier reference build. The sole exception is the newly edited `RealPrefixBounds`. |
| Solo admissions | Source-matched native records reproduce **202 → 197**, removing exactly the five `SequentialZK` admissions. |
| Final combined tree with #324; tree `129810e45fa842afa19219804e6cde7fe64cee7c` | **26/26 rc 0**, zero errors, zero admission warnings, one disclosed unused-`hQ` warning. The other **1306** modules have the expected combined-build source and recorded olean hashes. |
| Combined continuity | The only source change from the prior combined build is `RealPrefixBounds`. Its rebuilt source/olean pair matches the solo rebuild; the other 25 rebuilt pairs match the earlier combined build. All **1332** modules in the build closure have successful source-matched records and matching snapshot olean hashes. |
| Combined admissions | **194**, identical module by module to the earlier combined census. |
| `RealPrefixBounds` seals | Strict A/B and coe A/B all have **rc 0, zero errors, zero failing declarations**. Requests are **1875/1876** and **1874/1875**, respectively. Executed-probe hashes, instrumentation removal back to the exact owner source, and install/EOF mask records verify. |
| Paired controls | Coe: all **7** sealed negatives fail exactly once; readers and unsealed controls pass. Strict: all **9** negatives fail exactly once, plus the two previously documented `ctlCoeReader` failures. The raw diagnostics identify the sealed `FinDist` coercion instance as the cause. No stray errors occur. Coe-A remains canonical. |
| Axioms | All five targets and the reported consumers, including `realPrefix_bounds`, use only `propext`, `Classical.choice`, and `Quot.sound`; `next_length_le` uses only `propext`. No `sorryAx` appears. |
| Restore | Pre/post snapshot bytes agree, SHA-256 `457ba704d26757307f14131aa534929ffd70d30a732b0c744b104ca3fc96a15f`. |

The collector has **2507 `CAT` entries** plus its `CAT-COUNT` line, explaining the provenance's count of 2508 CAT-prefixed lines. The strict-control `ALL_OK False` and doc-only check's `RESULT FAIL` have the disclosed interpretations; neither indicates a failure of the repaired proof.

This evidence is sufficient for the single-module proof repair and shows no regression in the audited states.

## Duplication and carried-forward confirmations

I inspected the complete source delta and repeated the targeted inline-proof check. The only remaining reply-equation rewrite of the G39-01 pattern is inside `next_length_le` itself. Its two consumers now call the public lemma. There is no new inline re-derivation.

A supplementary exact and binder-renamed statement scan compared the **175 new theorems**, including private helpers, against **20,640** other parsed theorems at the audited head and against the changed-file theorem pools of the pinned tip and #324/#331/#332/#333. Both scans return **zero hits**. These are syntactic aids, not a decision procedure for semantic duplication. No further undisclosed copy was identified.

The round-1 confirmations remain valid:

- All five target proofs; the uniform strict-PPT repeated simulator; computational error `Q·|ε|`, statistical error exactly `Q·δ`, and adaptive soundness `s^Q`.
- The zero-phase, zero-round, odd-round, first-mover, filler-message, and malformed-simulator boundary cases.
- Frozen statements, S-01 (`StatZK_iff`), the historical docstring-only LE-doc edit, all eleven truncated-formula dispositions, and the strict-PPT source distinction.
- Zero new Rule-10 failing declarations, standard axioms, and the ownership and final-sweep record assessments. The earlier limits on authenticating host operators remain unchanged.

The merge order (**#327 before #324; #324 last**) and integration with #331/#332/#333 remain maintainer-run merge conditions, outside this audit. No concrete new name, instance, or build obstruction was found. The user dispatches and merges.

**Source notation:** `π`, `ρ`: original and repeated protocols; `Q`: phase-count polynomial; `ε`, `δ`, `s`: computational, statistical, and soundness error bounds. The Lean fragment retains the source's local parameter names.
