# Pass–shelat Gate 25 — hash-and-sign findings

**Verdict: CLEAR.** No findings under the pack’s rulings and dispositions.

| Severity | Count |
|---|---:|
| Blocker | 0 |
| Major | 0 |
| Minor | 0 |
| Note | 0 |

Audited [draft PR #308](https://github.com/Shilun-Allan-Li/tcslib/pull/308), specifically:

| Pin | Commit |
|---|---|
| Lean head | `4f0280c85fae8730ca0dfad980b41749452980fa` |
| PR base | `dee0de32ee33d7188afe97bdc3089fac68412057` |
| Campaign records | `b01c150512fe6668ee6dddb1c6b429d1b9c822bf` |
| Exchange | `e7b9e53e4a41ffa84b52deb17d34d144877d31f3` |

**Validation boundary.** This is an independent source and evidence audit. I recomputed checksums, compared pinned Git objects and source bytes, and checked the raw build, census, seal and control records. Lean, Lake and Elan were unavailable locally; I did **not** perform a fresh Lean compilation or kernel replay. The build and elaborated-term conclusions below rely on the supplied, hash-verified execution evidence.

## Integrity and scope

All **15/15** entries of the gate’s `SHA256SUMS` pass. The bundle’s SHA-256 is:

```text
21f55d7685a7b1d0d2625f9b75263bcab05c9a510997d26f4e6acaa0ad2bbd74
```

The nested manifests also pass, with exact file sets:

| Material | Verified manifest entries |
|---|---:|
| `verification.zip` | 38, plus its manifest |
| `review-evidence.zip` | 419, plus its manifest |
| `ledoc-evidence.zip` | 110 |

Both nested evidence ZIPs pass CRC checks. All **169 source files** in `sources.zip` match the pinned Lean tree’s Git blob hashes. The ten source sections in the bundle match those files. The source import graph is acyclic.

The reproduced PR diff is byte-identical to `pr.diff.txt` using Git’s nine-character index abbreviations; SHA-256:

```text
65c703eead6f0a01da894a4108858251c7e6767c9273fe47442f09013184ca9e
```

Its ten paths are exactly the owned file, eight helpers and the approved facade. All 31 original declarations other than the target are unchanged; the target’s complete header is byte-identical. The issue and PR bases agree on the two pre-existing changed Lean files.

The facade adds exactly the eight imports in `worker/escalations/proposed-authentication-imports.patch`, in alphabetical order, and removes no lines. The authorization is recorded in `worker/inputs/session-overrides.md`. No other facade export changes.

The embedded decision log is explicitly from the earlier records snapshot. Comparing it with the requested records pin finds only the subsequent Gates 23–25 packaging row; the applicable rulings are unchanged.

## Proof against the frozen theorem

The [target at line 609](https://github.com/Shilun-Allan-Li/tcslib/blob/4f0280c85fae8730ca0dfad980b41749452980fa/TCSlib/Cryptography/Authentication/Signatures/HashAndSign.lean#L609) establishes the frozen composition statement. It implements the two reductions in [PS10, Theorem 144.1’s proof, book pp. 144–145](https://www.cs.cornell.edu/Courses/cs4830/2010fa/lecnotes.pdf). The source’s arbitrary-message existential statement is represented separately; the fixed-width convention and the remaining Lamport admission are disclosed dispositions.

1. **Common law.** `one_query_cases` follows from unit query cost at most one: a computation is pure, or one query followed by a pure answer-dependent continuation. Therefore `expect_simulate_sample_once` proves the claimed equality for **every real payoff of both output and full log**, including the pure/no-query case. `expect_hashAndSign_sign` transports the wrapper’s uniform signing tape through its coin bijection. `runAt_hsGen_split` similarly splits generator coins. Together with the codec and verification readers, these establish `hashAndSign_forge_eq_common`.

2. **Collision branch.** `collisionHandler` has polynomial-time input, round and output functions and a seed consisting of the original key-generation and signing tapes. T1 supplies a machine in the required `NUPPT` class. The transcript invariant identifies the remembered state with the sole logged query. A collision witness excludes an empty log; freshness supplies distinct messages; `hdom` supplies both domain clauses. The finalization and concatenation readers identify exactly the two inputs decoded by the CRH game. `exists_collisionGame_bound` then averages the pointwise implication through explicit seed and machine-coin bijections.

3. **Forward branch.** The hashing handler uses `perCall = 1` and `finCall = 0`; T2’s outer budget is exactly one. `forward_transcript` preserves signature answers and maps each logged query to its hash. Finalization hashes the output message and preserves its signature. `originalSuccess_forwardOutput` proves equivalence of acceptance **and freshness**, so `exists_forwardGame` gives an exact probability equality, rather than only an implication.

4. **Union and negligibility.** `hashAndSign_success_cases` uses the following exhaustive split: either some logged query has the final message’s CRH hash, or none does. In the latter case, equality of forwarded hashes would imply equality of CRH hashes by evaluation at `Fin.cast (hlen n) j`, contradicting that branch’s hypothesis. Thus, for every parameter, the formal proof obtains

   $$
   \begin{aligned}
   \Pr[\mathrm{Success}]
   &\le \Pr[\mathrm{CollisionCase}]
      +\Pr[\mathrm{ForwardSuccess}]\\
   &\le \operatorname{accept}(H.\mathrm{collisionGame}\ B\ n)
      +\operatorname{accept}(S.\mathrm{forgeGame}\ C\ 1\ n)\\
   &\le \varepsilon_B(n)+\varepsilon_C(n).
   \end{aligned}
   $$

   The hypotheses provide negligible bounds for these two fixed machines; `Negligible.add` completes the universal-forger conclusion.

No query follows the forward branch. A queried final message is excluded by source freshness. Zero widths require no positivity assumption: the vector and coin bijections still apply. Malformed words and codec timeouts are covered by equality of the complete forger codecs, including timeout fields, and T1/T2’s tree contracts. The collision machine’s default no-query output causes no gap because collision soundness is invoked only when the log contains a collision witness.

## Rule 10 and execution evidence

I checked all **40 head-side** and **8 base-side** seal records: A/B, strict/coercion variants. Removing the recorded harness insertions reconstructs the exact LE-facade source or issue-base source in every case. Every insertion and raw log matches its recorded hash.

The collector’s ten head import closures agree with an independent traversal of the pinned source imports. Request sets cover their eligible foreign definitions, including matchers; elaborated references are either requested or explicitly accounted for by the permitted exclusions. Stored-constant coverage is **176 at the head**, **40 at the base**. All 48 logs have complete native-name/component, irreducibility-installation, instance-mask and EOF verification. They report zero errors. The base target’s admission warnings are expected.

The **20 control probes** reproduce the claimed outcomes: all **57 sealed negatives** fail exactly once, all **57 corresponding reader positives** pass, unsealed probes pass, and no error falls outside its planned declaration.

The explicit scans contain 406 head items and 57 base items. I reviewed the head’s 59 local/unresolved rows: 20 are public theorem method/open aliases and 39 are local bindings. There is no forbidden foreign-definition item.

`MachineCodec.ext_of_fields` eliminates a structure into its three fields and substitutes field equalities. This uses structure elimination, not the implementation of a foreign defined function. The coercion exclusion is exactly the recorded projection instance, `⟨FinDist.prob⟩`; strict and coercion variants both pass.

The seal inputs precede LE-doc. Their applicability to the audited head is supported by the independent check that LE-doc changes only docstrings. The final-head build records cover all 15 changed/downstream modules with rc 0, zero errors and zero admission warnings; all ten changed-source hashes match. The supplied whole-tree result covers 1209 modules.

The raw axiom census contains 176 constants. The target uses only `propext`, `Classical.choice` and `Quot.sound`. The sole `sorryAx` carrier is the pre-existing `exists_oneTimeSecure_of_crh_owf`, through Lamport. The target does not depend on that admission. No new simp attribute or instance appears.

## Documentation, landing edits and duplication

All 109 added formulas agree with their declarations, including tape order, logs, casts and final-output widths. The new `polyTimeComputable_collisionRun` sketch follows its projection, tape-suffix, key/hash, signer, padding and pairing constructions. The target sketch describes the delivered reductions.

Independent byte comparisons confirm: LE-width changes whitespace only; LE-facade preserves the line multiset; and blanking docstrings makes all nine LE-doc files identical to their predecessors. The facade is untouched by LE-doc.

Independent searches across all 311 Cryptography modules at the pinned head, together with comparison of the relevant providers, found no additional copy outside DL-42 and the two disclosed overlaps. The existing forwarding handler cannot directly express the different message widths and hash query map. The padding corollary, eager-sampling relationship and parallel Lamport overlaps remain within DL-42. The seven unused declarations remain within their accepted API disposition.

The final lint’s actual FAIL/WARN lines equal the records baseline: **92 FAIL / 102 WARN**. Source hashes, line counts and widths match `source-head.json`; the only over-width line is the inherited facade line.

**Gate disposition: CLEAR.** No repository, exchange, PR or merge state was changed.

**Notation glossary.** `A`: original forger; `B`: collision finder; `C`: original-scheme forger. `Pr[·]`: probability in the common experiment, averaged over its four independent tapes. `εB, εC` (displayed as \(\varepsilon_B,\varepsilon_C\)): the negligible security bounds for `B` and `C`. All other identifiers are the audited Lean declarations and parameters.

