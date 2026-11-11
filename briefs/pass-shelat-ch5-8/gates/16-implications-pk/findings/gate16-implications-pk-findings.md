# Pass–shelat Gate 16: public-key implication findings

**Verdict: CLEAR.** Both catalog statements and their proof compositions pass the audit. Counts: **0 blockers, 0 majors, 1 minor, 0 notes**. The gate meets the pack's closing threshold; the minor is a source-attribution correction.

| Pin | Audited value |
|---|---|
| PR | [Draft #292](https://github.com/Shilun-Allan-Li/tcslib/pull/292) |
| Lean head | `33a616bcc14450b9e3110e4f8801abea1198b2fb` |
| Lean base | `33cb7ae74c8e6ac23ed5bb1875121eadfe0c2046` |
| Campaign records | `6c766470019c318eb00dd1ce937406bedef2e9c3` |
| Exchange | `dcd94a048a40d717083d381ea11f4179acb0d744` |

Audit method: independent retrieval and byte verification of the pinned GitHub inputs; static examination of the statements, proof compositions and relevant callee definitions/proofs; inspection of the supplied build, seal and transitive axiom evidence. Lean was not rerun locally; see the evidence limits below.

## Findings

| # | Severity | File and declaration | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|
| G16-01 | minor | [Implications/PublicKey.lean:27](https://github.com/Shilun-Allan-Li/tcslib/blob/33a616bcc14450b9e3110e4f8801abea1198b2fb/TCSlib/Cryptography/Implications/PublicKey.lean#L27), module docstring | The description identifies the adaptive multi-challenge experiment with PS10 Definition 171.5 without saying it is an extension. | Definition 171.5, book pp. 171–172, has one challenge encryption between two adversary stages. The implemented `AdaptiveINDSecure` permits polynomially many fresh adaptive challenges; `AdaptiveSecurity.lean` correctly calls this an extension, and `INDSecure.adaptive_cpa` proves the lift. | Say “the adaptive multi-challenge extension of the left-or-right game of [PS10, Definition 171.5]”; retain the references to the bitwise/hybrid argument. No statement or proof change is needed. |

## Input integrity

- **13/13 SHA256SUMS entries pass**, using the files retrieved at the exact exchange pin. Their Git blob IDs also match the retrieved bytes.
- `bundle.md` is **93,517 bytes**, SHA-256 `7bc07fa35e696bb98b277e5a54e353df20f851925366b3872c0e86b727e232b2`.
- **10/10 ordered BUNDLE-FILES entries match** their revision-qualified Git files byte-for-byte, with the bundle's separator newlines accounted for. Both the records and Lean revisions are respected.
- GitHub's pinned base/head comparison reports exactly three changed files: `TCSlib.lean`, `Implications.lean`, and `Implications/PublicKey.lean`. Independently comparing the root files confirms its sole change is the Implications import.
- All three `source-head.json` SHA-256 values match the actual Lean files and the corresponding `build.jsonl` source hashes.
- The source PDF matches SHA-256 `7624556077a7a272ba0b3ddb7cd47b96574fb0b4b4947a25467d1f91bb61bda8` and Git blob `695a6b18d3e4c3fd9a7cacfc45b301c94b8c24b3`, as listed at the Lean pin. Its relevant numbered statements and pp. 103, 171–172 were checked. A cached PDF was reused only after both byte-identity checks.

## Statements and endpoint

The declarations at lines 77 and 95 have the advertised, complete premise sets:

| Entry | Explicit premises | Conclusion |
|---|---|---|
| `exists_adaptiveCPA_of_rsa` | `ArithmeticFP`, `RSAAssumption` | `∃ S : FixedLengthPKScheme, S.msgLen = .var ∧ S.AdaptiveINDSecure .cpa` |
| `exists_adaptiveCPA_of_factoring` | `ArithmeticFP`, `BlumDensity`, `FactoringAssumption` | The same conclusion |

`ArithmeticFP` remains a hypothesis about arithmetic algorithms. Factoring is transferred to the Blum setting using the explicitly retained `BlumDensity`; the wrapper does not silently assume Blum factoring or prove prime density.

The definition of `FixedLengthPKScheme` in `Encryption/PublicKey/OracleSecurity.lean:223` supplies all advertised guarantees: `gen` and `enc` are polynomial-time machines with `gen_uniform` and `enc_uniform`; `dec_poly` supplies deterministic polynomial-time decryption; `enc_length` fixes the honest ciphertext width; and `correct` quantifies over every message and both honest coin tapes. In the underlying machine model, `Uniform` requires empty advice at every parameter.

`S.msgLen = .var` makes the message type `Fin n → Bool`, containing every n-bit string. For each positive n it has at least two messages, so an empty-message-only witness cannot satisfy this constraint.

`AdaptiveINDSecure .cpa` quantifies over every `NUPPT` adversary and polynomial total-query and fresh-challenge budgets. `adaptiveIndGame` samples one key pair and uses one fixed hidden bit; each fresh challenge encrypts the selected half of an adaptively supplied message pair with fresh coins. Public-key input is supplied to the adversary. This is the claimed adaptive endpoint, rather than the older batch ensemble predicate.

## Proof composition

1. `rsaTrapdoor_oneWay H hR` supplies RSA trapdoor one-wayness. `rabinBlumTrapdoor_oneWay H hD hF` supplies the Rabin–Blum counterpart. Their concrete assumptions and sampling-error premises are preserved.
2. `shiftParameter_oneWay` shifts the generator, sampler and inverter together. Its proof transports inversion probabilities through `shiftParameter_exists_invProbAt`, using an adversary at the original parameter that runs the shifted adversary at the parameter minus the offset. It also transports sampler closeness. Negligibility is preserved along the constant right shift. Thus the shifted collection is one-way at parameter n; the final adaptive security parameter remains n.
3. The width premises are proved for every generated index and every domain element:

   - RSA: `2 * max (n + 2) 2 = 2 * (n + 2)`, because `2 ≤ n + 2`.
   - Rabin: `2 * max (n + 3) 3 = 2 * (n + 3)`, because `3 ≤ n + 3`.

   The candidate-home width lemmas identify these with the exact `PolyExpr` evaluations required by `exists_glPad_singleBitSecure`. No impossible unshifted `henc` premise is introduced.
4. `TrapdoorCollection.OneWay.exists_glPad_singleBitSecure` supplies a predicate evaluator and a secure single-bit scheme for the shifted, Goldreich–Levin padded collection. The evaluator is obtained by the existing theorem; it is not an extra hypothesis.
5. `SingleBitSecure.exists_adaptive_cpa` chooses a padding bound, constructs the padded bitwise scheme, proves message length `.var`, and applies `bitwise_padded_cpa` followed by `INDSecure.adaptive_cpa`. The wrappers discard only the additional key-generator equality, retaining the message-length and security conjuncts.

These are valid applications of the published APIs. No additional construction, reduction, host or unproved bridge is introduced.

## Axioms, Rule 10 and layering

The supplied `seal-probe.log` reports, for each actual catalog theorem, exactly:

```text
[propext, Classical.choice, Quot.sound]
```

These are transitive theorem dependency reports, not merely a search for local `sorry`. The composition screen reports the same sets. The directly inspected chain includes the candidate one-wayness results, the shift transport, the Goldreich–Levin/single-bit bridge, and the bitwise/adaptive CPA lift; no missing premise or admission was identified there.

Both new proofs use theorem APIs without body-reading tactics. The supplied seal probe repeats both compositions with all twelve listed definitions sealed. Its log has exactly one error diagnostic, at line 33, matching the deliberately failing `rfl` control on `bitwise`; neither composition has an error diagnostic. Its nonzero process status is therefore expected.

The facade imports `Implications.PublicKey`, the root exports the facade, and the implementation imports lower construction/candidate modules. The change adds no reverse import from a lower module. Namespace, Contents list, declaration citations and proof sketches are present. There are no new definitions, admissions or `@[simp]` declarations.

## Evidence limits

The supplied build rows record return code 0 and zero errors, admissions and warnings for `Implications/PublicKey`, the facade and `TCSlib`, in that order. Their source hashes were independently checked as described above.

Lean and Lake are not available in this environment's command path, and no usable toolchain was found in the checked locations. Consequently, the build, seal and `#print axioms` executions were **inspected as supplied evidence, not independently regenerated**. The referenced binary object hashes were not independently checked because those objects are not in the pack. CLEAR reflects the checked source composition and the verified supplied evidence; it is not a claim of a fresh kernel replay.

Notation: n is the scheme's security parameter; S is the existential public-key scheme. Both names are used as in the audited source.
