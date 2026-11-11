# Gate 11 — Levin padding proof

**Verdict: CLEAR.** No blocker, major, or minor findings. One nonblocking provenance note.

| Severity | Count |
|---|---:|
| Blocker | 0 |
| Major | 0 |
| Minor | 0 |
| Note | 1 |

Auditor: external Codex. Date: 2026-11-11. Read-only audit; no repository changes or GitHub submissions.

## Audited inputs

| Input | Exact revision |
|---|---|
| [Exchange pack](https://github.com/Shilun-Allan-Li/tcslib/tree/117c5882ef91b87cc2489992cea90cdca5661833/outbox/gates/11-levin-gate) | `117c5882ef91b87cc2489992cea90cdca5661833` |
| [Draft PR #286](https://github.com/Shilun-Allan-Li/tcslib/pull/286), Lean head | `a1293a6970b4039a9cf19fd475b9f8cf304a44b3` |
| Campaign records | `deb8885bab195b3cc3bdd14ea37687e99b459bdf` |
| PR base | `5bcf11aaf08963ab33ce608ea7509e7403e4351a` |
| Campaign revision used for the verification trial merge | `4a09f3993eb9344fc5714610e41ab141a0144db8` |

The head consists of the production proof commit `9ada398e06c00656f96207f5254a826c74130c15` and the maintainer's reader-repair commit. I reviewed the exchange README, gate README, pack, complete bundle, exact diff, worker report, policy, provider-reuse ruling, repair record, sixteen changed Lean files, and verification evidence through r4. Repository and packet contents were treated as audit evidence.

## Findings

| # | Severity | File and declaration | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|
| N1 | Note | `TCSlib/Cryptography/Foundations/Negligible.lean`; `Negligible.comp_of_le` | The disclosed trial-merge build has one additive dependency difference from the supplied PR-head source closure. This does not invalidate this gate. | Of the 362 source-closure files, 361 match the latest successful bootstrap/replay source hashes. The remaining file has SHA-256 `5e6d2c9e69dbfe012c36a92bad05ec27e691c044dae73a7277b9599902074e1a` at the audited head and `56dc45fc34915f176899a3f6c1585cc3356929ff12519da77eee6a2f3b364a6d` in the bootstrap. Comparing pinned Git bytes shows only the appended theorem `Negligible.comp_of_le`, with no changed older declarations, new attributes, or instances. The padding implementation does not use this added theorem. All sixteen changed files match the final build records exactly. | Optionally document this precise dependency difference in `verification.md`. No Lean repair is required for Gate 11. |

## Integrity and verification evidence

Independent checks passed:

- All **12** entries of the outer `SHA256SUMS`.
- All **22** ordered `BUNDLE-FILES.txt` sections against the exact pinned Git bytes, accounting for bundle framing newlines.
- All **16** changed files against the bundle, source archive, pinned Git contents, and `source-head.json` hashes. Applying `pr.diff.txt` to the pinned base reproduces every final file.
- All **362** archived Lean sources against Git blob identities from the audited head's tree. Their TCSlib import closure is complete and exact.
- All **2,679** entries of `verification.zip`'s internal `final/SHA256SUMS`.
- Exact recovery of the sixteen final seal-source files after removing recorded harness insertions; the Primitives segment probes also preserve their original source bytes.

| Artifact | Verified SHA-256 |
|---|---|
| `bundle.md` | `1cfde27a0be2f8a9c5964a4de89ff062036b9122eded0bcf80d0e025714372a1` |
| `sources.zip` | `cf96a5ba6e886760abc871743699311929720fd5397fde61eb2c2fb228cfc4a9` |
| `verification.zip` | `622fbc0bef25aad83e54c99fcd6b3f372456c3d8bd2841c8747c5e732b62367f` |
| `Pass–Shelat.pdf` | `7624556077a7a272ba0b3ddb7cd47b96574fb0b4b4947a25467d1f91bb61bda8` |

The archived fresh bootstrap records **1,195/1,195** successful module checks. Successful r2, r3, and r4 replays contain **242**, **244**, and **244** modules respectively. I verified all **1,925** successful records against their raw log hashes and checked the final source hashes for all sixteen changed files. The r4 root and campaign `Checks` checks pass. N1 records the sole source-closure difference in the trial-merge environment.

The r4 axiom probe contains **182** selected constants with only `propext`, `Classical.choice`, and `Quot.sound`. Its three headline prints give the same standard axiom set for `PadQuad.exists_linearTime_gStr`, `lemma_64_3`, and the conditional `theorem_63_1`.

**Execution limit:** I independently checked source bytes, diffs, evidence, and mathematical models. I did not perform a fresh Lean compilation in this audit environment. Compiler and axiom results above are verified archived results, not new auditor executions.

## Padding and timing argument

The original header of `PadQuad.exists_linearTime_gStr` is preserved exactly. In particular, it retains the original finite-machine hypothesis for every `F` computed within `C(k+1)^c`, the positive-degree assumption, and the eventual domination hypothesis. No stronger premise was introduced.

For an input `z`, put

\[
m=|z|,\qquad n=\nu_d(m),\qquad v=\max(n-1,0).
\]

1. **Parameter recovery.** `BinaryRoot` preserves an interval containing the root, halves its width in each nonempty round, and stops with width one. Its midpoint test is valid because
   \[
   a^d\le m\iff a\le\nu_d(m)\qquad(d\ge1).
   \]
   The state has linear size in the binary input width. The existing bounded iteration therefore computes the shifted root in polynomial time in that width. Computing `bits(m)` costs linear time in `m`; `exists_pow_width_bound` absorbs the fixed polynomial in its width into a constant times `m+1`.

2. **Unary emission.** For `d=1`, the dedicated transducer emits `m-1` tokens in one scan. For `d≥2`, let `w=|bits(v)|`. The supplied-fuel emitter gives
   \[
   T_{\rm unary}
   \le K(w+1)^k(2^w+2)
   \le KH(v+1)\,4(v+1)
   =4KH(v+1)^2
   \le4KH(m+1).
   \]
   The last inequality is `shifted_root_sq_le`, including `m=0`. On arbitrary binary words the countdown emits exactly their numerical value; its extra zero-emission rounds cause no off-by-one error.

3. **Charge the actual source argument.** The encoded call has length
   \[
   |\operatorname{advInput}(n,z.\operatorname{take}(\ell(n)))|
   =2n+2+\min(\ell(n),m).
   \]
   Consequently, when `n≥n₁`,
   \[
   \begin{aligned}
   \ell(n)+C\bigl(|\operatorname{advInput}(n,z.\operatorname{take}(\ell(n)))|+1\bigr)^c
   &\le\ell(n)+C(2n+3+\ell(n))^c\\
   &\le n^d\le m.
   \end{aligned}
   \]
   For `n<n₁`, monotonicity of the natural-coefficient polynomial and the call bound give the fixed bound
   \[
   B=\ell(n_1)+C(2n_1+3+\ell(n_1))^c+1.
   \]
   Thus the cost is at most `B(m+1)` at every length. The implementation restores `v+1`; this equals `n` on every nonempty input. At the empty input, the separate bound adds `ℓ(1)+C5^c`, and the final `take 0` makes the result exactly empty.

4. **Assemble the result.** The sharp unary-polynomial evaluator costs a constant times `ℓ(v+1)+v+1`; expansion over nonzero monomials avoids an extra input-length factor. The payload wrapper charges `40(time + encoded-pair length + 1)` for the actual call. Concatenation has additive time overhead, and `exists_comp_on_image` charges both stages against the original input. Intermediate word lengths are bounded by their production times. These bounds give the claimed constant multiple of `m+1` for pairing, splitting, retaining the suffix, calling `F`, concatenating zeros, and the final cut.

The final output is precisely

\[
\left(z.\operatorname{drop}(\ell(n))\mathbin{++}
F(\operatorname{advInput}(n,z.\operatorname{take}(\ell(n))))
\mathbin{++}0^{2m}\right).\operatorname{take}(2m).
\]

The proof covers lengths between consecutive powers and finite-prefix truncation as well as exact padded lengths.

The source target is PS10 Lemma 64.3, book page 64 (PDF page 76). The every-length root convention and output representation are documented deviations from its padding sketch. The existing `quadraticCode_of_linear` transport turns this linear multitape evaluator into the required quadratic one-work-tape coded evaluator.

## Infrastructure and reader repair

- The five moved `nu` declarations, including their proof bodies, are verbatim. `nu_eq` is an additional reader.
- `exists_emitIterTM_withFuel` reuses the existing public emitting-loop host and retains the separate `R(n)+2` factor. Specializing its fuel machine recovers the **unchanged** original `exists_emitIterTM` header.
- The pointwise `pairMap_computes_at` supports actual-input charging; the original private `pairMap_computes` header remains unchanged. The new public payload contract is proved from the same machine construction.
- `safeRun_iff` states exactly the existing conjunction. Its consumer now uses that reader instead of destructuring the foreign predicate.
- `pairSplitAt` is exactly the old match expression, including `[]` on malformed inputs. Its three readers cover encoded pairs and both parser outcomes. The two restated existence propositions are definitionally the old propositions. The typed take/drop consumers preserve their original statements and outputs.
- The private split copies are gone. `split_computes` is restored verbatim to its base code; its inherited explicit reads therefore remain deferred debt. `exists_family` also has verbatim code: its documentation-only change is treated under the recorded F3 ruling.
- The new modules are exported through the existing facades and library root. I found no new global simplification/reducibility attributes, private host, undeclared copied proof, or new admission. The updated proof sketches describe the actual binary-search and unary-emission construction.

## Rule 10 and boundary checks

Combining the latest source-matching seal evidence for each file leaves **zero touched-declaration failures** after the recorded rulings. The remaining diagnostics are **311** failures matched at the base plus the one documentation-only F3 case. These are not reclassified as new violations; the 52 approved provider pairs remain governed by the supplied reuse ruling.

The Primitives seals cover the file in three overlapping passes, with later installations at source lines 2557 and 5512. The touched payload-map proofs are covered before the second pass reaches its error cap. The facade probes use 1,000-name harness chunks. Installation/EOF checks, original-byte preservation, and the explicit-reader scans support the stated coverage. All **250** recorded control rows across r1–r4 have their expected outcomes. Superseded symlink, stack-overflow, segment-scope, reader-edit, and control attempts are retained and were not counted as passing evidence.

Independent Python model checks all passed:

| Check | Cases |
|---|---:|
| Binary search and invariant, including noncanonical words and power boundaries | 33,160 |
| Binary-to-unary countdown and orbit-width bound | 2,047 |
| Split on raw words, including malformed encodings | 8,191 |
| Split on valid encoded pairs, including empty data and overlong cuts | 4,335 |
| Original versus shifted-root padding formula | 131,520 |
| Finite-prefix image budgets and square bounds | 16,388 |

These are checks of word formulas and arithmetic, not executions of the constructed Lean machines. They include degrees 1–8, empty words, lengths immediately around powers, constant/zero/nonlinear length polynomials, and outputs that force truncation.

The 15 known module-docstring lines over 100 characters are cosmetic; I found no mandatory line-length limit in the supplied policy and do not raise a minor finding for them.

`exists_canonizerExp` remains admitted and outside this gate. The clearance concerns the padding proof and its infrastructure; `theorem_63_1` retains its explicit `CanonizerExp` hypothesis.

## Notation

`z`: input word; `m`: its length; `n=ν_d(m)`: recovered parameter; `ν_d`: the repository's `nu d`; `v=max(n−1,0)`: shifted parameter; `w`: canonical binary width of `v`; `bits`: canonical binary encoding; `a`: candidate root; `ℓ`: the supplied length polynomial, with `ℓ(n)=ℓ.eval n`; `F,C,c,d,n₁`: the function and parameters of the audited theorem; `K,k,H`: fixed witnesses in the conversion and width bounds; `B`: the displayed finite-prefix bound; `T_unary`: unary-conversion time; `advInput`: the repository's encoded parameter/data pair; `++`: word concatenation; `0^{2m}`: a word of `2m` false bits; `R`: the supplied round-count function.
