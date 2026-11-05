# Gate 03c, round 2: closing audit findings

**Verdict: CLOSE for the specified changed surface — 0 blockers, 0 majors, 1 minor, 3 notes.** The next-bit theorem is strengthened correctly; the two previously major restrictions are now disclosed as accepted costs. This does not establish the unrestricted collection theorem or certify the other gates.

Audited the five supplied Lean files at the pack's stated pin `e79397eaf68b156b9db091f464741f6eb75b9c28`, using section A of `repair.diff.txt`, the round 1 findings, review, resolutions, policy, DESIGN and supplied execution evidence. This is a statement/docstring/proof-sketch audit, not a tactic-proof audit or a fresh Lean replay.

Input identification:

- `gate03c-r2-bundle.md`: 19 sections; SHA-256 `c80dbec74422e9c6dbd3695de432e78560a5529a20dc6ff0f56dd5bacc82b16c`.
- Attached Pass–shelat PDF: SHA-256 `7624556077a7a272ba0b3ddb7cd47b96574fb0b4b4947a25467d1f91bb61bda8`.
- The extracted round 1 findings match the recorded SHA-256 `0547776d90b620023b825684a873ebb11f4ec0c3fbf9baa54f02a4da80376a3a`.
- Source passages checked: book pp. 74–78, 80–81, 87, 89–92, 97 and 104 (PDF pages twelve higher). The fraction on book p. 90 was also checked visually.

## Findings

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| R2-1 | minor | `resolutions-03c-r1.md` · “Repair” preamble | The closing record contains inconsistent merge status. | It says #201 “is not yet merged” and that fixes are “on #201's branch only”; `03c-pack-r2.md` identifies its pin as after #201 merged. This is a record discrepancy, not a defect in the supplied Lean statements. | Label the paragraph explicitly as a pre-merge snapshot, or append the merged status and closing pin. |
| R2-2 | note | `Pseudorandom.lean:107–139` · `PRG`; `HardCore.lean:369–477` · `PRG.expand`, `prg_expand` | Exact `2n` and `n²` remain unavailable as `PRG` stretches. The repair declares this restriction rather than removing it. | `2n` fails `expands 0`; `n²` also fails at 1. The declaration, module prose, expansion docstrings and DESIGN §5.25 now state the cost and describe truncation/`DoublingPRG` routes. G3-2 accepts this choice. | None for this gate. Retain the qualification in downstream uses; this audit does not certify the separately located truncation implementations. |
| R2-3 | note | `HardCoreCollection.lean:84–94,344–352` · `Collection.glPad`, `TrapdoorCollection.OneWay.glPad_hardCore` | The collection result still requires exact polynomial encoding length at every generated index. | `henc` is unchanged. The docstrings and DESIGN §5.18 now explain repeated-index obstruction and the reported RSA/Rabin/DL limitations. The trapdoor docstring no longer claims a consequence from trapdoor permutations alone. G3-7(c) accepts disclosure of this cost. | None for this gate. The per-index/bounded-length generalization remains unformalized; do not count it as delivered. |
| R2-4 | note | `resolutions-03c-r1.md` · cross-gate references; `evidence/c2/*` | Several resolutions rely on evidence outside this bundle. | The bundle omits `Collections.lean`'s actual `HardCore` definition, 03b's findings, 03i's cited OWP axiom log, the PRF truncation implementations, `PublicKey.lean`, and the downstream corpus searched by the maintainer. Their cited dispositions can be recorded, but cannot be independently re-attested from these attachments. The local 76-theorem axiom coverage is complete. | No change required to the scoped declarations. Preserve these as cross-gate attestations, not as additional results established by this audit. |

## Round 1 resolution status

The numbering below is the numbering of `resolutions-03c-r1.md`, not the new findings table. “Recorded” accepts an explicitly retained limitation or cross-gate disposition; it does not mean the underlying restriction was removed.

- **1: recorded** — G3-2 retains expansion at every length. The cost is now explicit at `PRG`, both expansion declarations and DESIGN §§2.12/5.25; see R2-2.
- **2: fixed** — `NextBitUnpredictable.pseudorandom` has no `hℓ`; the zero-length lemma and the machine identity at every valid position support the strengthened statement. `stretch_pos` now attributes positivity to expansion, not to Theorem 75.4.
- **3: recorded** — the accepted `henc` cost and the qualified trapdoor conclusion are present in the supplied code and DESIGN. The claimed accompanying `PublicKey.lean` edits are outside the supplied delta; see R2-3/R2-4.
- **4: fixed** — DESIGN §2.12 records the shipped one-bit input and `hℓ`, and `prg_expand` explains the route from a general `PRG`. The optional `PRG.Secure.expand` wrapper is assigned to 03d, not claimed to exist here.
- **5: fixed** — the predictor sketch uses the actual adjoined-bit involution; the mixing sketch agrees. The inventory annotation in section B corrects its old two-to-one map, and the resolution records the local label P2-3 without rewriting the closed run-3 summary.
- **6: fixed** — all eleven previously omitted declarations appear in `evidence/c2/axioms.log` with only standard axioms. The section B diff adds their `Checks.lean` commands.
- **7: fixed** — the family/concrete distinction is accurate, and the revised constant and sample-count explanation agrees with the attached PDF; see the source check below.
- **8: recorded** — 03b owns the definition audit. The supplied `glPad` now supplies canonical decoding, and its compatibility is checked below. The body of `Collection.HardCore` is still absent, so I do not claim to have independently repeated 03b's audit.
- **9: recorded** — the review and resolutions report standard axioms for the OWP route in 03i. Those three declarations/log entries are not in this bundle; no stronger independent conclusion is drawn here.
- **10: fixed** — `HardCore.lean:73–82` now records Shamir's proposal, invariance under permutation iteration, and the distinction between unpredictable blocks and bits. Claim-107.c remains explicitly optional/unformalized.
- **11: recorded** — all eight requested reading lemmas are present and correctly stated; `HardCore` is split into 775 and 353 lines; `@[simp]` on `ensemble_X` is explicitly approved by G3-6. The retained 972-line `NextBit.lean` is disclosed, not represented as satisfying the 600-line target.
- **M1: recorded** — the new deviation names the earlier PRF workaround. Its existence and proof status in that other module remain the maintainer's cross-gate attestation.
- **M2: recorded** — the maintainer reports no downstream exact-stretch hypothesis making a theorem vacuous. No such hypothesis is introduced on this changed surface; the full downstream search was not independently repeated.
- **M3: recorded** — the reported candidate-width obstruction is now disclosed with #3. The obstruction itself is mathematically valid, as demonstrated below.
- **M4: fixed** — removing `hℓ` eliminates the theorem's zero-length exclusion even though G3-2 retains everywhere expansion for `PRG`.
- **M5: fixed** — the PDF directly confirms Lemma 80.5's “any polynomial” wording and the p. 90 bound. The review's shortened quotation omitted the numerator; the repaired docstring includes it correctly.
- **M6: recorded** — for natural-coefficient polynomial stretches, eventual strict expansion implies strict expansion for every `n ≥ 2`. Truncation to `n+1` bits and a finite initial modification preserve the existence of secure PRGs; this remains an informal remark, accurately labelled so.
- **M7: recorded** — same disposition and evidence boundary as #8.
- **M8: recorded** — same disposition and evidence boundary as #9.

**Scheduled cleanup:** the ledger explicitly assigns DL-9–18 to the gate 03 cleanup PR under G3-5/R-03l-1, after #195, and notes DL-19 for that PR. These records do not claim completion. Their implementation is outside this closing round.

## New public declarations: independent restatement

All names below are in `TCSlib.Cryptography`. Each row agrees with its docstring and formal statement.

| Declaration | Restatement and check |
|---|---|
| `prgAdv_eq_zero_of_length_eq_zero` (`NextBit:453`) | A sampler into zero-bit strings, with a finite nonempty seed type, has zero PRG advantage against every finite-coin distinguisher. The nonempty-seed assumption is essential; no nonempty-coin assumption is needed for this equality. |
| `PRG.easy_iff` (`Pseudorandom:156`) | `P.Easy` is equivalent to existence of one deterministic polynomial-time string function computing every `P.G n s` on the seed's list encoding. It adds no hypothesis. |
| `hardCore_iff` (`HardCore:161`) | `HardCore 𝓕 h` is exactly efficient evaluation of `h` from the parameter and input, together with a negligible prediction bound for each nonuniform PPT adversary, uniformly over all parameters. The quantifiers remain `∀ A, ∃ ε, ∀ n`. |
| `PRG.oneBit_stretch` (`HardCore:221`) | The stretch expression of `oneBit G` is syntactically `.add .var (.const 1)`. This is stronger precision than merely equality of its evaluations. |
| `PRG.oneBit_G` (`HardCore:225`) | At each parameter and seed, the generator field of `oneBit G` returns exactly `G n s`. |
| `owpPredictorSnoc_eq` (`HardCore:253`) | The predictor is the existing concrete `owpPredictor` applied to the distinguisher that concatenates the final Boolean to the `n`-bit string, with a dummy `Unit` component. The sign and coins are unchanged. |
| `oneBitStep_eq` (`HardCore:366`) | One step returns `(last output bit, first n output bits)`: the emitted bit first, next seed second. This correctly adapts the source's seed-first output to the concrete iterator. |
| `expandRed_eq` (`HardCore:405`) | `expandRed` is `prgExtRed` with `oneBitStep`, output projection before `D`, and challenge re-encoding `(last T, init T)`. This is an equation for all `l,k`, not a security claim for invalid hybrid indices. |
| `Collection.glBit_eq` (`HardCoreCollection:146`) | The predicate is the Boolean inner product of `r` with `encD_i x` padded/truncated to the length of `encD_i default`. At generated indices, `henc` makes that adjustment length-preserving. |

## Other changed statements, docstrings and source fidelity

| Surface / source item | Audit result |
|---|---|
| `PRG`, `expands`, `stretch_pos`; Def-77.1 | The definition still requires strict expansion at every natural parameter. Its docstrings now accurately distinguish this literal boundary convention from the text's length-doubling uses (book pp. 92, 97). Positivity follows from `0 ≤ n < stretch(n)`. |
| `NextBitUnpredictable.pseudorandom`; Thm-75.4 | It now states the source's implication without global positivity. All existing probability-model deviations remain those already declared. The repaired sketch uses positivity only where a distinguisher has positive advantage. |
| Private `prgAdv_eq_abs_nextBitHybrid` | The advantage equals the absolute difference between the all-uniform and all-sampled endpoints. The order of subtraction is harmless inside the absolute value. |
| Private `exists_nextBitPredMachine` | For fixed `ℓ,D,flip`, one machine works at every `n` and every valid position `i`. It reads `i` from the prefix length; only the sign is additionally advised. There is no impossible choice of an element of `Fin 0`. |
| `uprob_split_bit`, `nextBitProb_nextBitPred_false`, `exists_nextBitPred`; Thm-75.4.2, Alg-76.5 | The revised descriptions retain the extra Boolean in the involution and average the correctly planted and incorrectly planted cases. They yield the stated `1/2 + advantage/ℓ` reduction. No public statement of these existing lemmas changed. |
| `PRG.expand`, `prg_expand`; Lem-80.5 | The source outputs only the successive final bits and discards the final seed, exactly as the construction does. Both declarations now disclose the everywhere-expansion restriction; the one-bit-input signature is accurate and now recorded in DESIGN. |
| `HardCore` module remarks; Constr-77.a, Claim-78.a/b | The recorded Shamir string and the two explanatory claims match book pp. 77–78. They are expressly remarks, not new formal theorems. The formula for the cited concrete witness does reveal its position field and a selected input bit; its separate implementation is not supplied. |
| `HardCoreClaims` module/section prose; Thm-87.3.6/8 | The family/concrete split is correct. For the per-bit estimate, substituting `ε′=ε/2` and counting `2^k−1` nonempty subsets gives the formal denominator. The p. 90 text inconsistently writes `m` while later constructing `m−1` samples; the docstring expressly distinguishes these counts. No claim signature changed. |
| Collection documentation; Thm-87.3.coll and use in Thm-104.4 | The revised trapdoor claim is conditional on `henc`, as the Lean theorem is. The new file imports the collection machinery, and `HardCore.lean` imports the new file. Section B also adds it to the asymptotic facade. |

The constant comparison in the repaired `thm_87_3_6` docstring is, with `m=2^k−1>0` and `ε′=ε/2>0`,

\[
\frac{1-4(\varepsilon')^2}{4m(\varepsilon')^2}
\le \frac{1}{4m(\varepsilon')^2}
=\frac{1}{\varepsilon^2(2^k-1)}
\le\frac{1}{m(\varepsilon')^2}.
\]

Thus the formal estimate is the stated intermediate estimate, not a claim to preserve the source's sharper numerator. The guessing statement separately uses `m=2^k` and probability `2^(−k)`.

## The 17 moved declarations

I reconstructed the old files from section A and checked the diff against the supplied new files. All 17 moved declaration signatures are unchanged; no public declaration was removed. Apart from the new reading lemma and documentation, the collection section's only addition is the canonical-decoding proof field `encD_decD`. The existing computational fields are unchanged.

The following restatements all match their docstrings, subject to the explicit `henc` limitation. All locations are in `HardCoreCollection.lean`.

| Declaration | Restatement |
|---|---|
| `Collection.glPad` | Replace each domain by the product with bit strings of the default element's encoding length; encode pairs, retain the index generator, append independent padding in sampling, and map `(x,r)` to `(f_i(x),r)`. |
| `Collection.glBit` | Take the inner product of the length-adjusted encoding of the original element with its padding bits. |
| `Collection.glPad_gen` | Padding retains exactly the original generator. |
| `Collection.glPad_f` | The padded function outputs the encoded pair of the original function value and unchanged padding. |
| `Collection.glPad_sample_runAtL` | On a raw coin list, use the initial original-sampler coin segment for sampling and append the entire remaining segment. Decodability is guaranteed for the appropriately sized coin tapes, not asserted for arbitrary raw lists. |
| `Collection.glPad_decD_eq` | The padded decoder is `glPadDecode` with the default encoding length. |
| `Collection.OneWay.glPad` | One-wayness of the original collection implies one-wayness of the padded collection, under exact encoding lengths `henc`. |
| `Collection.OneWay.glPad_hardCore` | Under the same conditions, the encoded inner product is hard-core for the padded collection. |
| `goldreich_levin_coll` | Combine those two conclusions into a conjunction. |
| `PermCollection.glPad` | The padded permutation is the product of the original permutation and the identity on padding. |
| `PermCollection.glPad_toCollection` | Forgetting the permutation structure yields exactly `Collection.glPad` of the underlying collection. |
| `PermCollection.OneWay.glPad` | Padding preserves permutation-collection one-wayness, under `henc`. |
| `PermCollection.OneWay.glPad_hardCore` | The same predicate is hard-core for the underlying padded permutation collection. |
| `TrapdoorCollection.glPad` | Retain the padded permutation collection and invert its first component with the original trapdoor inverter while preserving the padding. |
| `TrapdoorCollection.glPad_toPermCollection` | Forgetting the trapdoor structure yields exactly the padded original permutation collection. |
| `TrapdoorCollection.OneWay.glPad` | Padding preserves trapdoor-collection one-wayness, under `henc`. |
| `TrapdoorCollection.OneWay.glPad_hardCore` | A one-way trapdoor collection satisfying `henc` supplies a hard-core predicate after padding. This is the qualified existence route, not one from arbitrary library candidates. |

## Adversarial instantiations

**1. Zero-length output and an empty-seed attack.** Set `ℓ(n)=0`, use any nonempty finite seed type, and take ordinary finite nonempty coins. There is exactly one output string. Hence, for every `D`,

\[
\Pr[D(X_n)=1]=\Pr[D(U_0)=1],\qquad
\operatorname{prgAdv}(X_n,D)=0.
\]

The next-bit condition has no positions to test, and the strengthened theorem's conclusion is correct. If the seed type were empty, the formal sampler acceptance probability would instead be zero; with an always-accepting, coinless distinguisher, the uniform acceptance probability would be one. The attempted counterexample is excluded by `[Nonempty σ]` and `Ensemble.nonempty`, which remain present.

**2. Zero length at only the initial parameter must not hide predictable positive lengths.** Take `ℓ(n)=n` and `X_n=0^n`. For every `n≥1`, the constant-false predictor at position zero succeeds with probability one. The next-bit premise would force `ε(n)≥1/2` for all `n≥1`, contradicting negligibility. Thus the new allowance at `n=0` does not make this non-pseudorandom ensemble pass the premise.

For the sign boundary, take a one-bit output identically false and `D(u)=u`. The advantage is `1/2`. With `flip=false`, the reduction always predicts true: `u=false` produces `¬u=true`, and `u=true` produces `u=true`. With `flip=true`, it always predicts false, achieving

\[
1=\frac12+\frac{1/2}{1}.
\]

The sign bit in the repaired machine statement is therefore necessary and sufficient in this example.

**3. Exact polynomial stretches.** With `stretch(n)=2n`, `expands 0` requires `0<0`. With `stretch(n)=n²`, the requirements at both zero and one fail. In contrast,

\[
2n+1-n=n+1>0,\qquad
n^2+1-n=1+n(n-1)>0
\]

for natural `n` (check zero separately for the second expression). These tests confirm the declared restriction and the advertised one-extra-bit workaround. They do not contradict asymptotic security: the unavoidable deterministic output at seed length zero contributes only a finite exceptional parameter.

**4. Encoding-length plateau.** Use the RSA widths reported in the review: `4,4,4,6,…`. If `henc` held with a natural-coefficient polynomial `m`, write `m(n)=a_0+∑_{j≥1}a_j n^j`. Then

\[
m(0)=m(1)=4
\Longrightarrow\sum_{j\ge1}a_j=0
\Longrightarrow(\forall j\ge1,\ a_j=0)
\Longrightarrow m(3)=4\ne6.
\]

The analogous Rabin plateau gives the same obstruction. More generally, a repeated index at two distinct parameters forces equal values of `m`; a nonconstant natural-coefficient polynomial is strictly increasing, so `m` must be constant. The repair correctly records this obstruction rather than claiming to cure it.

**5. Noncanonical padded encoding.** Fix an index and let `L` be the default element's encoding length. Suppose the padded decoder accepts `w` as `(x,r)`. Its matches require `pairDecode w=some(a,b)`, `F.decD i a=some x`, and `decodeFin L b=some r`. Canonical decoding gives

\[
a=F.\mathrm{encD}\ i\ x,\qquad b=\mathrm{List.ofFn}\ r,
\]
\[
w=\mathrm{pairEncode}\ a\ b
=\mathrm{pairEncode}\,(F.\mathrm{encD}\ i\ x)\,(\mathrm{List.ofFn}\ r).
\]

Thus an alternative accepted representation cannot make the sampler or inverter bypass an evaluator specified only on encodings. Adding `encD_decD` preserves this guarantee through the moved construction.

As a supplementary finite check, exact-rational enumeration over output lengths 0–2, seed cardinalities 1–2 and coin cardinalities 1–2 checked every sampler and Boolean distinguisher: 12 zero-length cases and 5,560 positive-length next-bit inequalities passed. Forty evaluations of the repaired adjoined-bit map satisfied the involution equation. These checks supplement the arguments above; they are not a Lean replay or a proof for arbitrary lengths.

## Execution evidence and limits

- All section A hunks match the supplied current files. Their computed Git blob hashes match the diff's new-file hashes; reversing the four modifications also matches the old hashes. This checks internal consistency, not independent authentication of the repository commit.
- `replay.log` contains 95 module records, all with `rc=0` and `errors=0`; the recorded `sorry` counts total 18, all outside the five files under audit.
- A declaration-name comparison finds exactly 76 public theorems/lemmas and exactly their 76 axiom entries: none missing, none extra. Every entry reports a subset of `propext`, `Classical.choice`, `Quot.sound`, or no axioms; none reports `sorryAx`.
- The five supplied files contain no `sorry`, `admit` or custom `axiom` declaration outside comments. The empty admissions record agrees. The supplied lint reports zero findings in five files.
- The full replay scripts, intermediate overlay logs and external gate evidence are not attached. I checked the supplied evidence for consistency and coverage; I did not rerun Lean or infer that every imported declaration is admission-free.

**Notation.** Symbols follow the bundle: `n` is the security parameter; `ℓ` is output length; `X` is a sampler/ensemble; `σ,ρ` are seed/coin types; `D,A` are distinguisher/predictor; `G` is a generator; `ε,ε′` are probability advantages; `k` counts guessed bits; `m` is the encoding-length polynomial, or the explicitly local sample count in the constant comparison. In the plateau calculation, `a_j` are the natural coefficients of `m`. In the decoder calculation, `i` is an index, `L` its default encoding length, `w` the input string, `a,b` its decoded components, `x` the decoded domain element and `r` its padding.
