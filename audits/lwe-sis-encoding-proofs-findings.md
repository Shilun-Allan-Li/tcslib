**LWE/SIS representation-proof fill, round 1 — audit findings**

**Recommendation: PASS the frozen representation-proof gate.** All 14 proof routes are sound on review, and the 61 source declarations retain their interfaces and non-theorem bodies. No blocking or corrective finding was identified. The three continuing notes below remain open; this recommendation grants no merge approval or construction-security clearance.

| Severity | Count |
|---|---:|
| Blocker | 0 |
| Major | 0 |
| Minor | 0 |
| Note | 3, carried forward |

Audit date: 2026-11-07, America/Los_Angeles. This was a static source and evidence audit with independent integrity checks, source comparisons, style runs, and finite mathematical checks. I did not run Lean, install or borrow build objects, edit repository source, dispatch workers, push, or merge.

The reviewed identities are:

| Item | Pin |
|---|---|
| Repository | `Shilun-Allan-Li/tcslib` |
| Exchange branch | `exchange/pass-shelat-ch5-8` |
| Exact exchange commit | `ebe777ba3bf904f6a6909aaf8b931fcb0c53f358` |
| Audited statement freeze | `4364d0e0fe9accd649b6acb4751e8684aa93ad1e` |
| Filled source | `893e921bf2afeca293be9da9d495613bb1486796` |
| Bundled records | `7a9dfa6bf05eebb9ea736067351be3cbb438857c` |
| Lean / Mathlib | `v4.25.0` / `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e` |
| Proposed branch / target | `cryptography/lwe-sis-encoding-proofs` / `cryptography/pass-shelat-ch2-4` |
| Bundle | `lwe-sis-encoding-proofs-r1-bundle.md`, 3,033,293 bytes, 259 sections |
| Bundle SHA-256 | `2f8308efa0f737d09cf9554c45407855b76756ee73a2d9fe28fa582962a49ff0` |

I read the root exchange README, campaign README, and gate README at the exact exchange commit, then the pack in the first bundle section. Retrieval by the gate's pinned Git blob `3fd06f3dbc45afb56b67578752528cd9cd33bc6a` supplied the complete bundle. Integrity checks passed:

- All five entries in the exchange gate's `SHA256SUMS`.
- Exact agreement of `BUNDLE-FILES.txt` and `.json`, including ordered revision-qualified paths, lengths, and hashes.
- All 259 extracted sections: 63 assigned to the filled-source pin and 196 to the records pin, with no duplicate paths. The first section is the 11,172-byte proof-review pack.
- All 63 current source-freeze entries; all 86 current and 82 historical nested evidence checksums.
- The verbatim prior findings, including their SHA-256 `87ce303895f81064891eb7ab1401b4be601dbc3671d02e28428b5acd4386a906`, and their resolutions.

For interface invariance, I separately fetched all 13 foundation/facade files at the statement freeze and all eight changed files at the filled-source pin. The former match the historical source-freeze hashes; the latter match the bundled bytes and Git blob identities. GitHub's comparison reports the filled source four commits ahead of the statement freeze, with that freeze as the merge base. Within Lean source, its changed-file list contains exactly the five proof files and three facade-comment updates. I also checked every hunk of the supplied `proof-diff.json` in memory: its eight file patches exactly transform those independently fetched originals into the bundled filled files, with matching old/new Git blob identities.

Using the supplied comment stripper and invariant checker on those independently obtained originals reproduced the attestation: **61 ordered declarations unchanged; exactly the 14 inventoried admission bodies changed; all 50 other frozen files byte-identical.** Manual examination of the complete diff confirms that the masking did not conceal a changed declaration, attribute, instance, namespace, option, or definition. All quantifiers, hypotheses, widths, bounds, parser guards, encodings, owner readers, and both assumption predicates are unchanged. `DLWEAssumption` and `SISAssumption` remain propositions for consumers to assume, not asserted hardness axioms.

The sole import addition is `Mathlib.Algebra.BigOperators.Group.List.Lemmas`. I read its block-extraction theorem at the pinned Mathlib revision and checked its use below. The module already occurs in the historical selected official-archive inventory. Package and toolchain pins are unchanged. This establishes a source-level invariant and direct mathematical agreement; it is not an independently reproduced elaborated type-hash comparison.

All 14 targets were reviewed. Names below are relative to `TCSlib.Cryptography`; file locations are relative to `TCSlib/Cryptography/`.

| Target | Location | Independent assessment |
|---|---|---|
| `Encoding.Modular.encodeVector_length` | `Encoding/Modular.lean:79` | Flatten length is the sum of coordinate-block lengths. `ofFn` mapping and the public numeral-length lemma give exactly coordinate count times width. |
| `Encoding.Modular.encodeMatrix_length` | `Encoding/Modular.lean:89` | Sum the proved row lengths and reassociate multiplication. |
| `Encoding.Modular.encodeVector_injective` | `Encoding/Modular.lean:101` | Equal flattened strings and equal lists of block lengths imply equal coordinate blocks. Numeral injectivity applies because each representative is strictly below the covered modulus; representative injectivity then recovers residues. |
| `Encoding.Modular.encodeMatrix_injective` | `Encoding/Modular.lean:126` | Recover equal fixed-length row blocks, then use vector injectivity and function extensionality. |
| `LWE.encodeChallenge_length` | `LWE/Encoding.lean:60` | Add matrix and value-vector lengths, then distribute multiplication to obtain the stated sample-count times dimension-plus-one budget. |
| `LWE.encodeChallenge_injective` | `LWE/Encoding.lean:72` | `List.append_inj` splits equal challenges using equal matrix-prefix lengths. The two common injectivity results recover the product components. |
| `LWE.Family.encodeChallenge_length_le` | `LWE/Assumption.lean:102` | Substitute exact length and public `PolyExpr.eval_*` equations; apply the stored sample and dimension inequalities by natural-number monotonicity. |
| `SIS.encodeChallenge_length` | `SIS/Encoding.lean:123` | Read the owner equation and reuse common matrix length. |
| `SIS.encodeChallenge_injective` | `SIS/Encoding.lean:131` | Read the owner equation and reuse common matrix injectivity with the unchanged width hypothesis. |
| `SIS.encodeSolution_length` | `SIS/Encoding.lean:143` | Every coordinate contributes one sign bit and exactly the prescribed number of magnitude bits. Sum the block lengths. |
| `SIS.decodeSolution_encodeSolution` | `SIS/Encoding.lean:155` | Exact length opens the successful parser branch. Prefix sums recover the complete coordinate block; its head and tail recover sign and numeral; numeral round trip and integer sign identities recover the coordinate. |
| `SIS.decodeSolution_encodeSolution_of_isSolution` | `SIS/Encoding.lean:234` | The integer absolute-value/square inequality, nonnegative coordinate squares, and the stored squared-norm bound establish every strict magnitude-fit hypothesis. |
| `SIS.Family.encodeChallenge_length_le` | `SIS/Assumption.lean:112` | Substitute exact matrix length and bound row and column counts using the family's fields. |
| `SIS.Family.encodeSolution_length_le` | `SIS/Assumption.lean:124` | Substitute exact signed-output length and apply the stored column bound. This length statement correctly covers arbitrary candidates, including ones whose magnitudes truncate. |

The modular injectivity proofs use the public `List.eq_iff_flatten_eq`, whose pinned Lean statement requires equality of both flattens and lists of sublist lengths. They provide both hypotheses. They never divide by or cancel a block width. At zero width, `NeZero q` and the coverage hypothesis force modulus one, whose residue type is a singleton. Empty vectors, empty row sets, and empty column sets are handled by the same extensional arguments. Length formulas require no coverage assumption. Below coverage, deliberate truncation remains possible and injectivity is not claimed.

The signed round trip warrants a more explicit check. Write the column count as \(m\), magnitude width as \(t\), integer vector as \(z\), and its encoded word as \(w\). The proof establishes

\[
|w|=m(t+1),\qquad
\sum_{j<i}(t+1)=i(t+1)\quad(0\le i<m).
\]

The public prefix-sum extraction theorem therefore gives coordinate block \(i\) at offset \(i(t+1)\), with length \(t+1\). Taking its head and dropping that head yield precisely

\[
w[i(t+1)]=\operatorname{decide}(z_i<0),
\]
\[
\bigl(w.\operatorname{drop}(i(t+1)+1)\bigr).\operatorname{take}(t)
=\operatorname{natToList}(t,|z_i|).
\]

The hypothesis \(|z_i|<2^t\) permits the existing numeral round trip. In the negative branch, \(-|z_i|=z_i\); in the nonnegative branch, \(|z_i|=z_i\). This proves recovery of every coordinate inside `some`. The extraction theorem's index obligation is supplied by `i.isLt`; the sign block always has positive length, including when \(t=0\).

For the solution-bound corollary, the public `isSolution_iff` supplies the integer squared-norm inequality. For each coordinate,

\[
|z_i|\le z_i^2\le\sum_{j<m}z_j^2\le B<2^t.
\]

Here the first inequality is `Int.natAbs_le_self_sq`, the second is `Finset.single_le_sum` with nonnegative squares, and the final natural-number fit follows through `Int.ofNat_le`. No real square-root estimate, extra norm hypothesis, nonzero-coordinate premise, or sampler property is needed.

At zero columns the round trip returns the unique empty vector. At zero magnitude width the fit hypothesis forces every coordinate to zero. Negative coordinates use the correct sign; zero is encoded with sign false. The unchanged parser also accepts negative-zero strings, which decode to zero. This is compatible with the proved left inverse: no uniqueness theorem for all accepted strings is asserted. Wrong total lengths still return `none`, and parsing still leaves the kernel, nonzeroness, and norm tests to the SIS experiment.

Independent elementary Python models checked 3,836 modular vectors, 1,776 modular matrices, 4,060 signed round trips, all 5,054 words in the selected small exact-length formats, 560 norm-coverage cases, and 39 wrong-length cases. They included modulus one, empty dimensions, zero widths, both signs of zero, and truncation outside coverage. These finite checks corroborate the conventions; they are neither Lean execution nor substitutes for the general proofs.

Reuse and proof prose are satisfactory. New proofs consume public owner equations, numeral results, list lemmas, and polynomial evaluation lemmas. No foreign definition is explicitly unfolded in their `simp`, `rw`, or `unfold` arguments. `blocks` is a local abbreviation of this encoder's coordinate blocks. No handwritten helper declaration, machine host, or copied proved infrastructure was added. The existing sketches describe the implemented routes. I reran the three style checks and reproduced **0 FAIL, 2 WARN over ten mathematical files**. The two warnings concern acronym matching for `DLWEAssumption` and `SISAssumption`; their complete iff readers are present and unchanged. No reader repair or alias is needed.

The evidence census also checks out:

| Inventory | Independently reconciled result |
|---|---|
| Source declarations | 19 definitions, 5 structures, 35 theorems, 2 anonymous instances: 61 total |
| Current owned-module constants | 61 source declarations, 100 structure-generated constants, 5 compiler auxiliaries: 166 total |
| Change from historical constant census | Two additions, no removals: `Encoding.Modular.encodeVector.congr_simp` and `encodeMatrix.congr_simp` |
| Source axiom reports | All 61 agree between the raw printed output and structured inventories |
| Environment-walk axiom reports | All 166 agree with the structured inventory; none is private or of axiom kind |
| Allowed axiom dependencies | Only `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx` or other axiom |

The two generated congruence theorems are disclosed and axiom-checked. Thus the handwritten source interface is invariant; the entire elaborated constant set is not literally identical. The probe correctly enumerates constants belonging to the audited encoding/LWE/SIS modules. It does not claim to enumerate every constant in all imported dependencies.

I reconstructed the three facades' TCSlib import closure and checked its topological order: exactly 55 modules, matching the final sweep. Every sweep source hash matches the extracted source. All final sweep records report exit zero, their raw logs contain no error diagnostics, and the recorded durations total 146.628 seconds. Zero admission warnings occur in the new modules. The inherited warning counts are unchanged: `TimeConstructible` 2, `Build/Loop` 5, `Build/Primitives` 3, `Build/Wrappers` 2, `Composition` 3, `Encoding` 1, and `Simulation` 1, totaling 17.

The separate final probe reports exit zero and agrees with its raw output. The 15 iteration records retain one early failed vector-length attempt, including its diagnostics; the final source corrects the `ofFn` mapping step. That historical failure is not a failure of the final sweep. The check script removes each target olean before invocation and rejects nonzero exit, error diagnostics, or a missing fresh olean.

All eight recorded package-source revisions agree with `lake-manifest.json`. The historical selection and provenance lists agree on 2,334 archive/module pairs, including the newly imported list-lemma owner. Actual archives and the native build environment are not bundled. Physical cache isolation, package extraction, absence of fallback build objects, and fresh native execution remain maintainer execution attestations. I did not independently reproduce them. `TCSlib.lean` is unchanged by this fill and still imports all three facades; neither the supplied evidence nor this audit establishes whole-library root elaboration.

The prior statement report remains historical evidence for its earlier freeze, including its then-current 14 admissions. The current source and probe close those 14 representation admissions for this reviewed fill; they do not retroactively change the prior report. Its continuing obligations are retained as follows.

| ID | Severity | Location | Finding/evidence | Required repair |
|---|---|---|---|---|
| N01 | Note, carried forward | Prior findings/resolutions; `policy.md` §2; proof pack, continuing source obligations | Exact primary-PDF archival, ingestion, and applicable source matching remain open. The prior report's live definition comparison and this representation-proof review do not establish byte-frozen source provenance. This audit did not repeat or complete that workflow. | Preserve the original finding verbatim. Complete the applicable archival/ingestion/source-matching work before claiming source-fidelity or source-policy closure. No representation-proof repair is required. |
| N02 | Note, carried forward; representation-admission portion discharged | `fills/00-encodings/evidence/`, `scripts/lean_check_tree.sh`, root exports | Current supplied evidence consistently records zero new admissions, 17 inherited admission warnings, the 55-module sweep, and standard axioms for all 166 owned-module constants. This auditor did not independently run Lean or validate physical cache isolation. Whole-root elaboration is unclaimed. | Retain those exact limits and perform the relevant landing/integration checks. Preserve the older report as a statement-gate record; do not present this static audit as an independent native rerun or whole-library build certificate. |
| N03 | Note, carried forward | `LWE/Assumption.lean`, `SIS/Assumption.lean`, campaign decisions D1–D7 | Fixed-sample DLWE, finite noise laws, mathematical samplers, and unrestricted SIS numeric profiles remain unchanged and disclosed. Faithful finite representations do not establish efficient honest sampling, machine bridges, sufficient sample schedules, useful SIS profiles, or construction security. | Carry each obligation into its consumer gate, including the actual noise law and sampling transfer, required LWE sample schedule, SIS nontriviality and solution/compression conditions, and representation-machine implementations. No current semantic repair is required. |

**Gate recommendation: PASS with 0 blockers, 0 majors, 0 minors, and 3 retained notes.** Record this as completion of the scoped representation-proof review only. Source archival and user-controlled integration/merge approval remain outstanding; no later primitive gate is approved by this result.

Notation glossary: \(q\) is the modulus; \(m\) is the SIS column count; \(t\) is the magnitude bit width; \(z\) is the integer candidate vector; \(z_i\) is coordinate \(i\); \(w\) is its encoded word; \(B\) is `sqNormBound`; \(i,j\) are coordinate indices. For an integer, \(|\cdot|\) denotes absolute value; for a word, it denotes length. `drop`, `take`, `natToList`, and `decide` denote the operations used in the reviewed source.
