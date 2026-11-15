# Pass–shelat Gate 30 — promotion audit

**Verdict: CLEAR, with one minor documentation finding.**

| Severity | Count |
|---|---:|
| Blocker | 0 |
| Major | 0 |
| Minor | 1 |
| Note | 0 |

The promotion satisfies ruling F-01 within this PR's scope. The remaining prf-mac re-point is a subsequent landing edit; DL-44 is not fully discharged by this PR alone. The user dispatches and merges.

**Audited pins**

| Item | Revision |
|---|---|
| Draft [PR #314](https://github.com/Shilun-Allan-Li/tcslib/pull/314), Lean head | `5757bc0604527602d790a1a57e9703374ce02c7b` |
| Parent and comparison base | `8aefdab4cdb372d0787a9be83bc65f1567ceb8b4` |
| Campaign records | `7bd85992f8bd61df48f43092bc5c845d5fac1b27` |
| Exchange pack | `341f61def10e0481a7c29fa4787a80d6ece7d5df` |
| Lean tree | `6e784db3a2644929e03e47727c075eaf1e5908d1` |

I read the pinned README, pack, bundle, policy, F-01 review and ledger, and checked their claims against repository objects and the archived evidence. Repository material was treated as evidence under audit. No repository changes, review submissions or merges were made.

**Finding**

| # | Severity | File · declaration | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|
| G30-01 | minor | `Encryption/PrivateKey/EncryptThenTag/Reduction.lean` · `ETTGame.prfAdv_eq_expect` | The retained documentation describes the former local derivation after the proof has become an application of the promoted theorem. | [Lines 340–348](https://github.com/Shilun-Allan-Li/tcslib/blob/5757bc0604527602d790a1a57e9703374ce02c7b/TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag/Reduction.lean#L340) say “re-derived here” and retain the rewrite-chain sketch; [line 356](https://github.com/Shilun-Allan-Li/tcslib/blob/5757bc0604527602d790a1a57e9703374ce02c7b/TCSlib/Cryptography/Encryption/PrivateKey/EncryptThenTag/Reduction.lean#L356) applies `TCSlib.Cryptography.prfAdv_eq_expect`. Policy §3 requires sketches to track proof changes. | Keep the overlap as provenance, remove the claim of a local derivation, and replace the sketch with direct specialization of the promoted theorem. This is a docstring-only repair. |

The inserted specialization sentence is correct. It does not, by itself, update the adjacent description of how this declaration is proved. This finding does not block the gate under its stated threshold.

**Integrity and frozen API**

- All **14/14** outer pack hashes verify. `verification.zip` has exactly its **37** manifest-listed files plus its manifest, all verified. The nested promotion evidence has **665/665** verified hashes and exactly those files plus its manifest: 666 files and 66 directory entries.
- All **164** supplied Lean files match the pinned head's Git blob identities. Independently computing the changed modules' import closures reproduces precisely those 164 files. For the broader import and copy checks, **1,276** project and audit Lean files were checked against the same head.
- All 11 bundle sections match their indicated source contents. The archived records explicitly come from parent records commit `f52a24be…`; the requested records commit adds one decision-log row and the gate artifacts. The ruling, review, ownership brief and ledger used here are unchanged at the requested pin.
- The actual commit changes exactly the two disclosed Lean files, **40 insertions / 8 deletions**. Its provider-returned patch hunks match `pr.diff.txt`. In `Defs.lean`, removing the disclosed import, results bullet and new section recovers the entire parent file. In `Reduction.lean`, everything outside the disclosed docstring insertion and theorem body is unchanged.
- Direct comparison preserves **all 21 pre-existing source declaration headers**, including private `gOuter_pair`. The supplied 20-header comparison enumerates the public declarations. There is one added public theorem, no removed declaration, and no changed existing header. The ETT API is unchanged.

**Placement and identity**

`TCSlib.Cryptography.prfAdv_eq_expect` belongs beside `prfAdv`, its defining equation and nonnegativity reader. It is a generic expectation-form reader, uses the existing namespace, introduces no attribute or instance, and touches no prf-long-owned file. The `open Games ProbComp` is confined to `section Expect`; it ends before the following existing declaration.

The statement has the correct absolute difference, uniform key/function-table sampling, and independent adversary-coin expectation in each branch. Its proof proceeds through published equations:

1. `prfAdv_def` and `distAdv_def` expose the two acceptance probabilities.
2. `Bridge.acceptProb_eq`, `accept_eq` and `Bridge.acceptGame_eq` express each as a sampling game.
3. `prob_bind` and `prob_pure` produce the nested indicator expectations; `oracleDist_apply` and `randomFunction_apply` identify the verdicts.

The promoted tactic proof is identical to the previous ETT proof. Nonempty keys and coins are required by the current `sample` API; nonempty outputs supply a nonempty function-table type. No nonempty-input assumption is imposed. The universe-zero restriction agrees with the game sampler and query-tree layer. The new formula, results bullet and attribution to the expectation reformulation of the definition already cited by `prfAdv` are appropriate.

**Import and downstream effects**

The new `Games.Bridges.Experiments` import is justified by the bridge readers used in the proof. Its seven-module upstream closure excludes `Pseudorandom.Functions.Defs`, so there is no cycle. Independently recomputed counts agree with the pack:

| Check | Result |
|---|---|
| `Defs` upstream closure | 6 → 9 modules |
| Newly added modules | `Games.Probability`, `Games.Advantage`, `Games.Bridges.Experiments` |
| Modules downstream of `Defs` | 95 |
| Downstream modules gaining the import | 42 |
| ETT Reduction closure | 163, unchanged |
| Root `TCSlib` closure | 1,239, unchanged |

I also retrieved the referenced earlier build records from Gate 29's verification archive at the requested records commit, verified that archive's Git blob and nested manifests, and recomputed the comparison. **125 unchanged modules** have byte-identical recorded objects relative to builds without this promotion. Adding the pre-rebase references gives the claimed **127 identical / 0 different**; those two additional matches are the edited modules themselves. The two #311 modules have no same-source reference, as disclosed. Thus the comparison supports unchanged elaboration for the 125 matched unchanged modules; it is not an exhaustive before/after comparison for all 129 modules.

**Other copies and dispositions**

Searching the current project and audit sources for `prfAdv`, its defining reader, the bridge acceptance conversion and the expectation identity found no additional unrecorded copy requiring a change in this PR. The hybrid proofs in `FromPRF/Hybrid.lean` and `GGM.lean`, the asymptotic reader, and the single-acceptance conversions in BitwiseCPA/PaddedCPA are different results. The existing `prfAdv_eq` remains the probability-form reader.

The private `prfAdv_prfReduction` in `OracleFromPRF.lean` remains within the explicit DL-40/DL-44 deferral and is **not a finding**. The unmerged prf-mac local `hadv` is the separately required follow-up. The ETT theorem now consumes the promoted theorem directly; its consumers in `exists_tagStep` and `ccaScheme_cca2` are unchanged.

**Rule 10 and validation boundary**

All eight archived seals pass: A/B for both files, in both strict and projection-coercion variants. I checked the probe source hashes, that each contains the actual audited source body, the run/log hashes, and the install/EOF evidence. Request counts agree with the pack: Defs strict 72/72, coe 71/71; Reduction strict 2271/2272, coe 2270/2271. Reconstructing controls from diagnostic line locations confirms **8 probes and 11 intended negative failures per harness**, with readers and unsealed controls passing and no stray diagnostics. The new proof's rewrite and simplification lists name published theorems; no forbidden explicit unfolding was found in the changed proof material. Reading `prfAdv` through its defining-file reader is appropriate.

The archived build has **129/129 successful modules**, zero errors under both diagnostic forms, and covers all **96 affected modules** in dependency order. Every recorded source hash matches the pinned head, and every build log matches its recorded hash. Its ten admissions are the disclosed pre-existing admissions. The four requested axiom prints contain only `propext`, `Classical.choice` and `Quot.sound`. The lint evidence preserves the 92 FAIL / 101 WARN baseline, with only the disclosed INFO changes; widths are 97 and 99 characters. Landing extracts equal their original evidence entries, and the pre/post artifact snapshots match.

**I did not rerun Lean:** this audit environment has no installed Lean executable. Compilation, seal and axiom results above are checked archived evidence, supplemented by independent source, hash, import, header, control-outcome and artifact-comparison checks. The disclosed combined #313/#314 tree remains unbuilt; the second landing still needs its integration rebuild. Neither limitation is represented here as a completed check.
