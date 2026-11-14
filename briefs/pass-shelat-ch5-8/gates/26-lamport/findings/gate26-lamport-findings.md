# Gate 26 — Lamport findings

**Verdict: CLEAR under the pack’s rulings.** No blocker, major, or minor finding. One nonblocking evidence-tooling note. The proof establishes the frozen `lamport_oneTimeSecure` statement; no Lean change is requested.

| Severity | Count |
|---|---:|
| blocker | 0 |
| major | 0 |
| minor | 0 |
| note | 1 |

| Audit pin | Revision |
|---|---|
| [Draft PR #309](https://github.com/Shilun-Allan-Li/tcslib/pull/309), Lean head | `987efb5156b3ae20cff4576b379eb1c607f33cb0` |
| Lean tree | `dc1fb8fb5ba7fb427c6c94a03a6d64accf04e695` |
| PR base | `dee0de32ee33d7188afe97bdc3089fac68412057` |
| Issue base | `eff2dcd0a63f0c371118a17c67b9a5dfc046f4e9` |
| Campaign records | `156949a315a04a8fe7035a67680979de6d949905` |
| Exchange | `81225b67422a472381f041a3dc57c4f2de2d0e8b` |

This verdict concerns these pins. Dispatch and merge remain with the user.

## Finding

| # | Severity | File · item | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|
| G26-N1 | note | `review-evidence.zip`: `lamport-r1/tools/runner.py:31`; seal-run JSON metrics | The runner counts the literal `error:` and omits Lean’s `error(...)` diagnostics. Its Lamport seal-B rows report 19 errors at the head and 12 at the base; the raw logs contain 26 and 15, respectively, in both variants. The seal tables correctly count all diagnostics. Return codes, the 16/11 failing-declaration sets, controls, and the verdict are unaffected. | `independent-seals.json`, `runner_metric_discrepancies`; retained diagnostic excerpts and result rows in `evidence/runner-counts.txt`. | Before reusing the runner, count both diagnostic forms, for example anchored `^\S+\.lean:\d+:\d+: error[:(]`. Preserve historical logs and annotate the metric discrepancy. |

## Integrity and frozen scope

Read the pinned [README, pack and bundle](https://github.com/Shilun-Allan-Li/tcslib/tree/81225b67422a472381f041a3dc57c4f2de2d0e8b/outbox/gates/26-lamport-gate), the brief, policy, review, worker report, decision log and duplication ledger as audit material.

| Check | Independently checked result |
|---|---|
| Top `SHA256SUMS` | All 15 entries verify. Every pack file also matches its blob in the pinned exchange tree. |
| Nested manifests | Verification: 47 payload files plus its manifest; review: 573 payload files plus its manifest; landing edits: exactly 217 manifest files. All hashes and file sets verify. ZIP inventories have no duplicate entries. |
| Bundle and source closure | All 25 bundle sections match pinned Git content, allowing separator newlines. All 177 source files match head Git blobs. |
| PR diff | Exactly 18 paths, 3256 insertions and 7 deletions. The supplied diff reproduces exactly with nine-digit index hashes. The unit’s diff is the same from the issue and PR bases. |
| Frozen declarations | All 47 original headers are byte-identical. The other 46 original bodies and attached docstrings are unchanged. The recorded elaborated census preserves all 67 base constants and their type hashes; only the target’s axiom set changes. |
| Frozen providers | `Signatures/Defs`, `HashAndSign`, `Asymptotic/Collections`, `Asymptotic/OneWay` and `Games/Efficiency` are unchanged. No new instance or global simp attribute. |
| Facade | Exactly the sixteen approved helper imports, alphabetically after `Signatures.Lamport`; no removal or non-import change. Source import traversal finds no cycle and exports every helper. |

The verification archive’s records match the requested records commit. Its earlier decision-log snapshot is an unchanged prefix with the subsequent Gate 26 row appended at the requested commit, as the pack’s provenance explains.

## Proof against Theorem 137.2

Compared with Protocol 137.1, Definition 136.2 and Theorem 137.2 in the repository’s Pass–shelat reference, printed pages 136–138. The frozen formulation’s strong one-wayness and length-guard deviations remain as documented.

1. **Actual game.** `lamport_forgeGame_accept_eq_honestProbability` identifies the actual logged forgery game with the typed experiment. The coin-table equivalence identifies key generation, the signing expectation handles every answer/state continuation, and the verifier and freshness readers identify the winning event. This is an equality for the actual machine forger, rather than an assumption about an ideal forger.
2. **Coupling and counting.** `planted_coupling` preserves the honest signature on safe queries. Fresh messages differ at a coordinate, giving favorable fraction at least `1/(2n)`; no-query runs have fraction exactly `1/2`. `coordinate_reduction_bound` uses invariance under replacement of the unused preimage to resample the challenge independently. It does not multiply probabilities after conditioning on non-abort.
3. **One fixed inverter.** `exists_best_position` selects a position at each positive parameter. `exists_realization_machine` applies T1 to a polynomial-time handler with one state bit, `1+2n²` seed bits and the forger’s coins. `exists_withIndexAdvice` supplies exactly `Nat.size n` index bits, bounded by `n`, and preserves the coin polynomial. The coin equivalences therefore transport the uniform distributions to one legitimate NUPPT inverter.
4. **Success and conclusion.** `safe_of_nonabort` and the realization proof transport only nonaborting typed successes to actual encoded inverses. `fairBit_redProbability_le_invProbAt` gives event inclusion into the actual inversion game. The closing lemmas multiply the lower bound by the positive denominator and apply `mul_pow`, `const_mul` and eventual `mono`.

The zero parameter is a permitted finite exception to the eventual negligible bound; advice and machines remain total there. Empty query logs are handled separately. Reusing the queried message fails freshness. Malformed machine words are handled by the same fixed-width codec in both games, and the guarded verifier is used through its proved reader. Aborted runs need not correspond between the two simulations: only nonaborting successes are transported. The target’s edited step 5 accurately describes this route.

## Rule 10, landing edits and opacity

Recovered the original pinned source bytes from **all 84 archived whole-file probes** by removing only their recorded insertions. Checked probe/source/log hashes, conservative request sets against the collectors, actual-name metadata, stored-root counts, term exclusions, and installation/EOF records.

| Phase | Strict A | Coercion A | Strict B | Coercion B |
|---|---:|---:|---:|---:|
| Base | 2/2 pass | 2/2 pass | 1/2 pass | 1/2 pass |
| `1023834e` | 18/18 pass | 18/18 pass | 16/18 pass | 16/18 pass |
| Realization after LE-rule10 | pass | pass | pass | pass |

At the final head, carrying these results forward gives A passing all 18 files and B passing 17, with only the 16 dispositioned declarations in `Lamport.lean` failing. Their diagnostics begin with the frozen `Fin n` versus `Fin (var.eval n)` mismatch and its cascades. No additional failure class was found. The target’s structured identifier diagnostics are cascades of that same failed elaboration.

The 16 review control probes have 37 sealed negatives; the eight LE-rule10 probes have 30. Recounting raw diagnostics gives exactly one error per sealed negative, passing reader controls, and no stray errors. The explicit-unfold evidence records 797 items and no foreign definition unfold; source inspection found no contrary read.

- **LE-facade:** import order only, with the same line multiset.
- **LE-width:** whitespace only.
- **LE-rule10:** only the proof of `exists_realization_machine`. The `Fin.cast` directions, `List.ofFn_congr` round trips and substitution of the query, answer, output and budget widths agree with T1. All declaration headers remain unchanged; its four re-seals pass.
- **LE-doc:** 188 changed declaration doc comments in sixteen files, with executable code and all 268 headers unchanged. Reviewed all 188 formulas and seven added sketches against their declarations and proofs; no mismatch found. The omitted `LamportFill.` qualifiers are unambiguous, and the Statistics expectation/indicator shorthand is defined inline.

The three opacity commands address exactly `ProbComp.expect`, `ProbComp.sample` and `OracleComp.bind`. They only add local irreducibility and skip already irreducible names. They do not remove a seal, alter a declaration, or export the attributes. The downstream status probe and the in-file negative/reader controls support these conclusions. LE-rule10 changes no import; LE-doc changes no executable code, so the stated seal carry-forward is sound.

## Duplication, axioms and build evidence

The DL-42 and DL-43 items and the disclosed overlaps are retained as the pack directs. No additional copied private proof or duplicate public lemma requiring a new disposition was identified. Searches covered the full head TCSlib source and relevant finite-average/list APIs at the pinned Mathlib revision. In particular, `SecureComputation/Yao.encodeMsgs_inj` concerns a different encoding API with an equal-length premise; the new unrestricted `encodeList` proof is independently derived from published pairing/encoding readers. The removed prefix/suffix wrappers are absent and public `takeLen_poly`/`dropLen_poly` are used.

The 321-constant census uses only `propext`, `Classical.choice` and `Quot.sound`; the final target and edited realization axiom probes agree. The admission census removes only the target, 22 → 21. Sizes, the two inherited over-width lines, the 999-line split follow-up, seven linter warnings, and the #308 combined-tree follow-up agree with the stated dispositions.

Verified the final build’s 24 successful result rows against head source hashes and retained raw-log hashes. The archived whole-tree check reports 1217 modules at the recorded source/object hashes, and lint has no new FAIL or WARN.

**Execution limit:** Lean and Lake are not installed in this auditor environment. Compilation, axiom and seal execution results above are verified archived observations, not a fresh compiler replay. The independent work consists of source/proof review, Git-object and archive verification, probe reconstruction, and raw-result/control recounts.

## Evidence included

The accompanying ZIP contains this Markdown, independent integrity and seal results, the two read-only checking scripts, the declaration-by-declaration documentation review list, and the runner-count excerpts. The pinned input archives remain the source for the complete historical logs and probes.

**Notation:** `n` — the security parameter, as in the audited source.
