# Gate 01 / prong zero — external audit findings

**Audited revision:** [tcslib PR #183](https://github.com/Shilun-Allan-Li/tcslib/pull/183), head `789cf450527ff6b8c779161e555f04093080b88d`; base `06e61e912eedc2bce49b3ccff77bb9c4a7e18579`; supplied records revision `f2653ee20ff0b915fbe40f12fbf90b3af481bc5b`.

**Assessment:** **0 blockers, 0 majors, 7 minors, 3 notes.** I found no false new mathematical theorem or unsound entropy/extractor definition. The pack's numerical closure condition is met, but this is **not an unconditional approval**: the source citations, disclosed scope, reconstruction wording, and public definition interfaces need the corrections below. In particular, the algebraic secret-sharing predicates alone do not constitute a probabilistic, efficient implementation of Definition 152.1.

## 1. Verification and scope

Both supplied checksums match exactly:

| Attachment | Verified SHA-256 |
|---|---|
| `gate01-p0-bundle.md` | `97042aee164fa0e11a0ac1c2bd2f28a5398349a76934f7eee0bd30bb138bf74b` |
| `Pass–Shelat.pdf` | `7624556077a7a272ba0b3ddb7cd47b96574fb0b4b4947a25467d1f91bb61bda8` |

The bundle has **19 sections**. I read its pack and policy, the specified PDF pages, all 11 new definitions and 22 public theorem statements, the private auxiliary statement, the relevant context, the changed secret-sharing docstrings, and the supplied evidence. Definition bodies were inspected without comments before their declaration docstrings; the restatements below reflect those bodies. PDF rendering confirmed the source's formulas, numbering, coefficient typo, and empty §8.3.3 heading.

Independent GitHub checks confirmed the five-file change scope and matched the two new files to the pinned head. Their Git blob hashes are `bf03d3b40e86189e84c63087503cf929d58c20f7` (`Entropy.lean`) and `36b20dae88df037edbaa44cc79ded8419477ea1e` (`Extractors.lean`). Comment-stripped `SecretSharing/Defs.lean` and `Shamir.lean` match the pinned base. All touched-file lines are at most 100 characters. The root `TCSlib.lean` imports the information-theory facade.

**Verification limit:** I did not rerun Lean, reconstruct the olean tree, or certify the tactic scripts. The replay and axiom checks remain maintainer-supplied evidence, consistent with the pack: 18 successful modules and the standard three axioms for the 25 listed theorems. The finite computations in §5 were independently executed with exact rational/modular arithmetic; they are not Lean kernel checks. I inspected the disclosed definitional dependencies and the mathematics of the proof sketches.

Locations below are relative to `TCSlib/InformationTheory/`, except explicitly prefixed `SecretSharing/`, which means `TCSlib/Cryptography/SecretSharing/`.

## 2. Findings

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | minor | `Extractors.lean:46,80–107,134–135,168–171` · references and closeness/strong-extractor docstrings | Several precise source pointers are incorrect; one sentence attributes a statement to an empty heading. | In the published [Vad12], statistical distance versus half the ℓ¹ distance is **Lemma 6.3(7)**, not “Lemma 6.4”; 6.4 is a proposition about simulating randomized algorithms. The strong definition is **Definition 6.16**, whereas 6.13 is the ordinary seeded definition. [PS10] §8.3.3 contains a heading and no lemma statement. | Correct the declaration and module references. Replace “states the leftover hash lemma … without a definition” with “contains only a heading”; attribute the actual statement to the other references. |
| 2 | minor | `Entropy.lean:150–156` · `IsFlatSource` | The declared deviations omit the restriction to natural, rather than real, entropy parameters. | Uniform mass on three points has min-entropy `log₂ 3` and satisfies the literal real-parameter reading of [PS10, Def 183.5], but cannot satisfy `IsFlatSource k` for any natural `k`. The pack notices `k : ℕ`; the declaration's deviation paragraph does not explain it. | State that this predicate covers only integer-bit flat sources, with power-of-two support, and explain the design choice. Keep `flat` for arbitrary support sizes; add a real-parameter predicate only if needed downstream. |
| 3 | minor | `SecretSharing/Defs.lean:96–99` · `Scheme.Correct` | The new sentence identifying threshold `Correct` with [PS10, Def 152.1(2)] omits locality. | With two parties and threshold 1, give party 0 the constant share 0, party 1 the secret, and let reconstruction always read party 1. Raw `Correct` holds even for `{0}`, although party 0 cannot reconstruct. See §5.7. | Say **“Together with `LocalReconstruct`, this gives the reconstruction requirement …”**. This is minor because the nearby `Scheme` deviation and `LocalReconstruct` docstring already disclose the issue, and Shamir separately proves locality. |
| 4 | minor | `SecretSharing/Shamir.lean:87–98` · `scheme` source comparison | The degree description and restriction claim need the positive-threshold qualification, and the interpolation citation silently corrects another source error. | At `k = 0`, `q = 0`, secret 1, `poly` is constant 1 of degree 0, not degree `< 0`; `correct` properly requires `0 < k`. Also [PS10, Lem 153.2] says degree exactly `n`; interpolation guarantees degree **at most** `n`. Data `(0,0),(1,0)` already refute exact degree 1. | Qualify the protocol comparison by `1 ≤ k ≤ n < p` (or distinguish vacuous cases explicitly). Say degree **at most** `k−1`, and disclose that Lemma 153.2's exact-degree wording is also corrected. The existing coefficient-typo correction is appropriate. |
| 5 | minor | `Entropy.lean` and `Extractors.lean` · public definition interfaces | Zero style-lint findings do not establish the policy's “definitions land with their lemmas” requirement. | No public equation/complete characterization is provided for `shannonEntropy`, `probTrue`, `IsFlatSource`, `IsExtractor`, `IsStrongExtractor`, or membership in `seededSources`. A named consequence such as `IsExtractor.mono` does not expose the predicate for construction and elimination without reading its body. | Publish the equations/iff lemmas listed in §6. The existing order characterization for `maxProb`, entropy-bound equivalence, and `flat_apply` do provide useful semantic interfaces. |
| 6 | minor | `Entropy.lean:73,158,187` · `shannonEntropy_nonneg`, `IsFlatSource.isSource`, `isSource_uniform` | Some recognizable mathematical results have no declaration-level source location. | Their docstrings lack `[Tag, location]`, although they are entropy/source facts rather than representation plumbing. This falls under `policy.md` §2 even when their proofs are short. | Cite the relevant [PS10] definitions and describe them as elementary consequences: Def 182.3 for nonnegativity and Defs 183.4–183.5 for the source facts. No invented textbook theorem number is needed. |
| 7 | minor | `Extractors.lean:71–73` · `FinDist.probTrue_sub_probTrue` | The docstring calls a signed difference an “advantage,” whereas the surrounding closeness definition uses absolute advantage. | For opposite Boolean point masses and the test accepting the second mass, the displayed sum is `−1`; absolute distinguishing advantage is `1`. The formal equality itself is correct. | Say “The **signed difference in acceptance probabilities** is the sum …”, or put an absolute value on both sides in an additional theorem. |
| 8 | note | `SecretSharing/Defs.lean` · `Scheme`, `PerfectPrivacy`; `Shamir.scheme` | Coin bijections have a probabilistic interpretation only with an appropriate sampling law. | For **finite, nonempty, uniformly sampled** coins, the bijection gives identical view laws. Arbitrary fields/coin types do not supply such a law; empty coins make raw correctness vacuous, and biased coins need not be preserved. See §§4.1, 5.8. | Retain the algebraic generality, but use the explicit finite/uniform qualification whenever claiming [PS10]'s probabilistic privacy. Do not infer a sampler or efficiency from these predicates. No theorem change is required for the finite-field Shamir application. |
| 9 | note | `Entropy.lean:117–120` · `minEntropy` | The definition handles zero-probability outcomes correctly, but its informal minimum formula requires the usual extended-surprise convention. | For masses `(1/2,1/2,0)`, the definition returns 1. A literal minimum using Lean's totalized real reciprocal/logarithm at zero would instead contain a spurious 0. | Optionally write the minimum over positive-mass points, or explicitly assign surprise `+∞` to zero-mass points. Do **not** change the actual maximum-based definition. |
| 10 | note | `Extractors.lean` · `EpsClose`; duplication evidence | The disclosed sampler-based `StatClose` overlap is real, but no copied proof requiring a duplication major was established. | I checked `Sampling.lean` at the supplied ch. 2–4 revision: its tests concern uniform-seed samplers, potentially with infinite output types. This is a different carrier from arbitrary real-weighted finite distributions. Name-based searches do not certify absence of all semantic overlap. | Preserve the integration obligation for a sampler-to-`FinDist` bridge, with nonempty seed spaces, and reuse closeness results after integration. Do not describe the evidence as an exhaustive conceptual deduplication proof. |

Finding 1 was checked against the author's [published December 2012 Vadhan PDF](https://people.seas.harvard.edu/~salil/pseudorandomness/pseudorandomness-published-Dec12.pdf), printed pp. 169, 176, 178–179. The [HILL paper](https://www.cs.bu.edu/fac/lnd/pdf/hill.pdf), Lemma 4.8, is a legitimate leftover-hash reference: its formulation uses Rényi entropy and pairwise-independent hashing. The audited min-entropy/collision-universal formulation is mathematically valid, as the supplied finite-distribution bridge also shows; it should not be advertised as a literal transcription of HILL's hypotheses.

## 3. Per-definition restatements

### 3.1 All eleven new definitions

These are readings of the definitions, not paraphrases inferred from their names. `FinDist α` means nonnegative real masses on a finite type summing to one; the existence of such a distribution already implies that `α` is nonempty.

| Definition | Mathematical restatement from its body | Comparison with source and docstring |
|---|---|---|
| `FinDist.shannonEntropy` | Sum `−p(a) ln(p(a))/ln 2` over all outcomes, with the product at zero evaluated as zero. | Correct base-two instance of Def 182.3. The base restriction is disclosed. |
| `FinDist.maxProb` | The attained maximum of the atom masses over the finite alphabet; nonemptiness is derived from normalization. | Correct auxiliary quantity for Def 183.4. No dummy maximum over an empty alphabet is used. |
| `FinDist.minEntropy` | The negative base-two logarithm of that maximum mass. | Correct Def 183.4 under its usual zero-mass convention; see §4.6 and finding 9. |
| `FinDist.IsSource k p` | The real number `k` is at most `minEntropy p`. | Exactly the entropy-threshold condition in Def 183.5. Negative thresholds are allowed and harmless. |
| `FinDist.IsFlatSource k p` | For natural `k`, there exists a subset of cardinality exactly `2^k`; every member has probability `2^(−k)` and every other point probability zero. | Correct integer-parameter flat-source notion. Being a `k`-source follows rather than needing to be a separate conjunct. The parameter restriction needs disclosure: finding 2. |
| `FinDist.flat s hs` | The distribution assigning `1/\|s\|` to members of the specified nonempty subset and zero outside it. | Correct uniform-on-support constructor. Unlike `IsFlatSource`, it permits support size 3 or any other positive integer. |
| `FinDist.probTrue p D` | The sum of `p(a)` over exactly those outcomes on which Boolean test `D` returns true. | Exactly the acceptance probability used in Def 181.1. No efficiency restriction is imposed. |
| `EpsClose ε p q` | Every Boolean-valued function has absolute acceptance-probability difference at most the real number `ε`. | Correct finite-alphabet realization of Def 181.1, including negative-error behavior. |
| `IsExtractor C ε Ext` | For every distribution in `C`, its pushforward by the fixed function `Ext` is `ε`-close to uniform on the nonempty finite output type. | Correct Def 181.2, with the declared finite-alphabet generalization. The formal source definition itself does not include a running-time bound. |
| `IsStrongExtractor C ε f` | For every `X ∈ C`, sample a uniform seed independently of `X`, apply `f`, and require the **joint seed/output law** to be `ε`-close to uniform on `S × β`. | Correct strong condition, generalized to a class `C`. Independence follows from the actual `hashPair` definition. Attribution needs finding 1's correction. |
| `seededSources C` | Exactly the distributions on `S × α` that equal `uniform S × X` for some `X ∈ C`. | Correctly captures an independent uniform seed supplied beside the weak sample. It does not include all distributions with a uniform seed marginal. |

### 3.2 Definitions underlying the changed secret-sharing citations

The following code predates this PR; this audit assesses the new claims connecting it to [PS10].

| Definition | Mathematical restatement | Source comparison |
|---|---|---|
| `AccessStructure` | An upward-closed predicate on finite subsets of a party type. | Generalizes the threshold family; neither a finite total party set nor a nontrivial threshold is built in. |
| `AccessStructure.threshold k` | Authorize precisely the finite sets containing at least `k` parties. | Standard threshold condition. For `k=0` every set is authorized; if `k` exceeds the total party count none is. |
| `Scheme` | Two functions: a deterministic sharing map given explicit coins, and a reconstruction map given a finite set and a **full** share assignment. | Raw scheme data, without a coin distribution, finiteness, efficiency, locality, or security bundled in. Its separate locality/efficiency discussion is necessary. |
| `Scheme.Correct` | For each authorized set, every secret and every coin value, reconstructing from the resulting full share assignment returns that secret. | Correct algebraic equation, but source reconstruction from available shares needs `LocalReconstruct`; finding 3. |
| `Scheme.LocalReconstruct` | Changing shares outside the designated set does not change reconstruction. | Supplies the missing input-access constraint. It must actually be assumed or proved, not merely named. |
| `Scheme.PerfectPrivacy` | For every unauthorized finite set and every ordered pair of secrets, some bijection on coins preserves all shares in that set while switching the secret. | Distributional perfect privacy for finite nonempty uniform coins; otherwise an algebraic transport condition. |
| `Shamir.Party` | The subtype of nonzero field elements. | Excludes evaluation at zero, which would reveal the secret. The source's parties embed into this type when `n < p`. |
| `Shamir.label` | The underlying field element of a party. | Injective by construction. |
| `Shamir.poly` | Given secret and a polynomial `q` of degree `< k−1`, form `C secret + X*q`; subtraction in `k−1` is natural subtraction. | The corrected Shamir polynomial, of degree `< k` **when `k>0`**. |
| `Shamir.scheme` | Share by evaluating that polynomial at the nonzero labels; reconstruct by interpolating the designated shares and evaluating at zero. | The intended corrected protocol on restricting parties and using finite uniform coefficient coins. No efficiency claim follows from this noncomputable algebraic definition. |

## 4. Answers to the nine questions

### 4.1 Definition 152.1 versus the scheme predicates

**Privacy:** equality of view distributions is a valid strengthening of statistical closeness, not an equivalent definition of all statistically private schemes. The source provides no explicit error function or security parameter here, so its words do not determine a quantitative positive-error requirement; zero distance satisfies any nonnegative such requirement. It would be unjustified to claim that the source explicitly requires perfect privacy.

For a finite nonempty coin space and uniform coins, fix an unauthorized set and two secrets. Write `V(r)` and `V′(r)` for their restricted share views. The definition supplies a bijection `e` with `V′(e(r))=V(r)`. For every event `T` of views,

\[
e\bigl(\{r:V(r)\in T\}\bigr)=\{r:V'(r)\in T\},
\qquad
\Pr[V\in T]
=\frac{|\{r:V(r)\in T\}|}{|\mathrm{Rand}|}
=\Pr[V'\in T].
\]

The denominator is positive. Conversely, equal laws under finite uniform coins give equal finite fiber sizes; choosing a bijection within each fiber and combining them produces the required coin bijection. Thus the bijection formulation itself is equivalent to perfect privacy in this setting; the strengthening is from approximate to perfect privacy. It says nothing about a nonuniform law unless that law is preserved by the chosen bijections.

**Correctness:** threshold `Correct` directly includes the case of exactly `k` parties and additionally requires the given reconstruction function to work on larger sets. Starting from a source algorithm for exactly `k`, one can implement larger-set reconstruction by choosing a `k`-element subset; this is a benign extension of the model, although not a logical consequence about an arbitrary pre-existing reconstruction function. `LocalReconstruct` is needed to conclude that the authorized set can actually perform reconstruction. Shamir supplies it.

The omitted p.p.t. condition is a substantive but explicitly declared scope restriction: information-theoretic security and efficient implementability are different obligations. This PR establishes neither a complexity bound nor an implemented sampler.

### 4.2 Restricting Shamir to the source's parties

Take prime `p`, `1 ≤ k ≤ n < p`, and `F = ZMod p`. Embed `i ∈ Fin n` by the field label `i+1`. Then

\[
1\le i+1\le n<p
\quad\Longrightarrow\quad
(i+1)\bmod p\ne0.
\]

If two such labels agree modulo `p`, their integer representatives lie in `{1,…,p−1}` and hence agree as integers; therefore the embedding is injective. Finite-set images preserve cardinality, so

\[
k\le |A|\iff k\le |\operatorname{image}(A)|,
\qquad
\neg(k\le |B|)\iff |B|<k.
\]

`Shamir.correct` applies since `k>0`, and `perfectPrivacy` applies to each restricted unauthorized set. Reconstruction of a restricted assignment can extend the assignment arbitrarily outside the embedded set: `localReconstruct` makes the result independent of the extension. The image contains exactly the source's evaluation nodes `1,…,n`.

The coin space `degreeLT F (k−1)` is in bijection with the `k−1` coefficients; uniform polynomial coins therefore mean independent uniform coefficients. Also `k≤n<p` implies the hypothesis `k≤|F|` of `natCard_coins_view`. With `b=|B|<k`,

\[
\#\{\text{coins producing a fixed view}\}=p^{k-1-b},
\qquad
\Pr[\text{that view}]=\frac{p^{k-1-b}}{p^{k-1}}=p^{-b}.
\]

Thus the restricted shares are uniform over all views and independent of the field-valued secret. **The intended, corrected source protocol really is a special case.** The literal misprinted polynomial in Protocol 154.4 is not. Secrets are field elements here; arbitrary strings would need a separate encoding.

### 4.3 Boolean tests and randomized distinguishers

On a finite encoded alphabet, arbitrary functions `α → Bool` are exactly the deterministic tests with no resource bound: each function has a finite truth table. There is no computability or efficiency restriction hidden in the type.

For completeness, put `d(a)=p(a)−q(a)` and

\[
t=\sum_{d(a)>0}d(a)=-\sum_{d(a)<0}d(a)
=\tfrac12\sum_a|d(a)|.
\]

The equalities use `Σ d=0`. A randomized test is described by its acceptance probabilities `u(a)∈[0,1]`. Term by term,

\[
-t=\sum_{d(a)<0}d(a)
\le\sum_a d(a)u(a)
\le\sum_{d(a)>0}d(a)=t.
\]

Consequently its absolute advantage is at most `t`, and the deterministic test accepting exactly `d(a)>0` attains `t`. Allowing randomized tests changes nothing. The same test must be used in both experiments, with its randomization independent of which experiment supplied the sample.

### 4.4 Boundary values of `epsClose_iff_statDist_le`

- **`ε<0`:** the always-false test has advantage zero, so `EpsClose ε p q` would imply `0≤ε`, a contradiction. Statistical distance is nonnegative, so its upper-bound condition is also false.
- **`ε=0`:** the equivalence says statistical distance is zero. Every summand `|p(a)−q(a)|` is nonnegative; their sum is zero exactly when every mass agrees, hence exactly when `p=q` by `FinDist.ext`.
- **One-point alphabet:** normalization forces the unique atom to have mass 1. Every pair of distributions is equal, and either side is equivalent to `0≤ε`.
- **Empty alphabet:** there is no `FinDist` on it, since its total mass would be `0=1`. Statements quantified over such distributions have no instances; no malformed uniform distribution is constructed.

### 4.5 Degenerate extractor classes

If `C=∅`, `IsExtractor C ε Ext` holds for every function and every real error, including negative errors. This is precisely the same universal-quantifier vacuity as Def 181.2.

For any distributions,

\[
\operatorname{statDist}(p,q)
=\tfrac12\sum_a|p(a)-q(a)|
\le\tfrac12\sum_a(p(a)+q(a))=1.
\]

Thus `ε≥1` makes every function an extractor. If the output type has one element, every pushforward is uniform, and the exact condition is

\[
\operatorname{IsExtractor}(C,\varepsilon,\mathrm{Ext})
\iff C=\varnothing\ \lor\ 0\le\varepsilon.
\]

The singleton case corresponds to outputting zero bits. Empty output types are already excluded. These are harmless boundary cases; adding nonemptiness or a nontrivial error/output-size requirement to the general definition would unnecessarily narrow the source. Such hypotheses belong in claims of useful extraction. In particular, an extractor for an empty entropy class is not evidence that randomness was extracted.

### 4.6 Min-entropy and its bound equivalence

Let `m=maxProb p`. Normalization and nonnegativity give `0<m≤1`, and finiteness gives an outcome attaining `m`. For every positive-mass outcome,

\[
p(a)\le m
\Longrightarrow
\log_2\!\frac1{p(a)}\ge\log_2\!\frac1m=-\log_2m.
\]

Equality holds at a maximizer. Zero-mass outcomes have surprise `+∞` in this formula and cannot decrease the minimum. Equivalently one minimizes only over positive-mass outcomes. This proves agreement with Def 183.4 without ever applying a real logarithm to a zero maximum.

For every **real** `k`, monotonicity of base-two exponentiation gives

\[
k\le-\log_2m
\iff\log_2m\le-k
\iff m\le2^{-k}
\iff\forall a,\ p(a)\le2^{-k}.
\]

This is exactly `le_minEntropy_iff`. In particular every distribution is a `k`-source when `k≤0`. If the alphabet has `N` elements, `1=Σp≤Nm` implies

\[
0\le H_\infty(p)\le\log_2N.
\]

Hence the class of `k`-sources is empty when `k>log₂ N`. These conclusions are not defeated by Lean's totalized `log 0`: the maximum is proved strictly positive.

### 4.7 Real source parameters and natural flat parameters

Real `k` is natural for the inequality in Def 183.5. Natural `k` for flatness is a useful **restriction**, not a full real-parameter reformulation. The source does not explicitly impose that restriction.

For example, on a four-point alphabet let the masses be `(1/3,1/3,1/3,0)`. Its entropy is `log₂ 3`, and it is uniform on `2^(log₂ 3)=3` points. There is no natural `k` with `2^k=3`, so the new flat predicate cannot classify it as flat. Nevertheless `flat` constructs it and `IsSource (log₂ 3)` can express its entropy guarantee. Nothing is lost for power-of-two support sizes. When `2^k` is not an integer, an exactly `2^k`-point flat source would not exist even under a real-parameter definition.

Omitting the source's additional `IsSource` conjunct is benign: uniform mass on `2^k` points has **exactly** min-entropy `k`, so the included lower-bound theorem proves the required implication.

### 4.8 Leftover hash and the seeded-source bridge

The error and joint form are correct. For `X` a `k`-source,

\[
\sum_xX(x)^2\le2^{-k}\sum_xX(x)=2^{-k}.
\]

Write `R=hashPair f X`, `L=|S|`, `M=|β|`. The supplied context gives

\[
\sum_zR(z)^2\le L^{-1}\!\left(\sum_xX(x)^2+M^{-1}\right),
\]
\[
\operatorname{statDist}(R,U_{S\times\beta})
\le\tfrac12\sqrt{LM\sum_zR(z)^2-1}
\le\tfrac12\sqrt{M2^{-k}}.
\]

All cardinal denominators are positive because the seed and output types are nonempty. Collision universality suffices; pairwise-independent outputs are not required. The new theorem is exactly a wrapper around the established bound and the min-entropy/closeness equivalences. For `M=2^m`, its error is `2^((m−k)/2−1)`, including the expected factor `1/2`.

The source's §8.3.3 supplies no formula to check; the result is the standard strong leftover-hash statement supplied by the other cited sources and justified above. Its parameters and finite-alphabet formulation should be described as such, not as text present under the [PS10] heading.

For every `X∈C`, the function `(s,x)↦(s,f(s,x))` pushes `uniform S × X` to `hashPair f X`. Thus `isExtractor_seeded` is a faithful Def 181.2 interpretation. The converse also holds, by applying the deterministic extractor to each such product source; publishing an iff would expose the exact correspondence.

This is extraction from a **restricted product class**, with the seed retained in the output. It does not assert seedless extraction from every high-min-entropy distribution on `S×α`, security for correlated seed/source pairs, or closeness for every fixed seed. The independent uniform seed is substantive.

### 4.9 Shannon conventions

The pinned Mathlib definition is `negMulLog x = −x * log x`, with `negMulLog 0 = 0`. Hence

\[
H(p)=\sum_a\frac{-p(a)\ln p(a)}{\ln2}
=\sum_{p(a)>0}p(a)\log_2\!\frac1{p(a)}.
\]

This is the standard continuous convention at zero. It does **not** assign zero surprise to impossible outcomes in the min-entropy minimum; Shannon entropy multiplies by the probability, while min-entropy does not. The notation `H(X)` consistently refers to the distribution, correcting the source's occasional `H(x)`. For uniform `n`-bit strings, including `n=0`, the calculation is `2^n·2^(−n)·n=n`.

## 5. Adversarial instantiations

The following test concrete objects against the definitions. Cases 1–8 give more than the requested three attempts.

### 5.1 Point masses, zero atoms, and error boundaries

On `Bool`, take masses `(1,0)`. Both entropies are zero, it is a `0`-flat source, and it is a `k`-source exactly for `k≤0`. Against the opposite point mass, the distance is `(1+1)/2=1`, attained by a singleton test. Against itself, closeness holds exactly for nonnegative errors.

On a three-point alphabet, masses `(1/2,1/2,0)` have maximum `1/2`, min-entropy 1 and Shannon entropy `2·(1/2)·1=1`. This specifically tests whether the impossible outcome corrupts the logarithm/minimum. It does not.

### 5.2 Three-point flat support

The four-point distribution `(1/3,1/3,1/3,0)` witnesses finding 2. Its positive support has cardinality 3. Any witness for `IsFlatSource k` would have to equal this positive support, since its specified mass is strictly positive exactly on the witness set; thus it would force `2^k=3`, impossible for natural `k`.

### 5.3 A constant extractor and an empty class

Let the output be `Bool` and `Ext` always return false. For any source its distance from uniform is

\[
\tfrac12\bigl(|1-\tfrac12|+|0-\tfrac12|\bigr)=\tfrac12.
\]

For a nonempty class this is an extractor exactly when `ε≥1/2`; for the empty class it is an extractor even at `ε=−1`. On a two-point input alphabet, choosing the class of `2`-sources produces precisely such an empty class. No claimed extraction from an actual `2`-source follows.

### 5.4 Copying the seed does not fool the strong definition

Take `S=β=Bool` and `f(s,x)=s`. The output marginal is uniform, but the joint law is supported on `(0,0),(1,1)`, each with probability `1/2`. Its distance from uniform on four pairs is

\[
\tfrac12\cdot4\cdot\tfrac14=\tfrac12.
\]

Thus it fails `IsStrongExtractor C 0 f` whenever `C` is nonempty. The strong definition has not collapsed to ordinary seeded extraction.

### 5.5 Uniform marginals do not replace independence

Let the source and seed be bits, and `f(s,x)=s XOR x`. For an independent uniform source and uniform seed, the joint seed/output law is uniform, with distance zero. For the correlated input `x=s`, both input marginals remain uniform, but the output is always zero and the joint distance is `1/2`. The correlated law is not in `seededSources {uniform Bool}`, as required.

As a separate nonvacuous leftover-hash check, use all 16 maps from four points to two points, with the uniform four-point source. Every pair of distinct inputs collides under exactly 8 seeds. The joint statistical distance is exactly `3/16`, and

\[
(3/16)^2=9/256\le1/8
=\left(\tfrac12\sqrt{2\cdot2^{-2}}\right)^2.
\]

### 5.6 Restricted Shamir, including threshold zero

For `F=ZMod 5`, `n=3`, `k=2`, write the polynomial as `secret+qX`. At parties 1 and 2,

\[
2(\mathrm{secret}+q)-(\mathrm{secret}+2q)=\mathrm{secret}.
\]

At each individual party `b∈{1,2,3}`, the map `q↦secret+bq` is a bijection of the field, so every possible share has probability `1/5`. I checked all 25 secret/coin pairs and all four authorized subsets (100 reconstructions), all one-party fibers, and all 375 secret-switch/coin/party translation equations.

At `k=0`, instead, the coin polynomial is zero. Empty-set interpolation returns zero, so secret 1 is not correctly reconstructed from the empty authorized set. The theorem properly refuses this instantiation because it requires `0<k`; the scheme docstring should do the same. Privacy at threshold zero is vacuous because no set is unauthorized.

### 5.7 Reconstruction that reads another party's share

Take parties `Fin 2`, secrets and shares `Bool`, coins `Unit`, threshold 1. Define

\[
\operatorname{share}(s,(),0)=\mathrm{false},\quad
\operatorname{share}(s,(),1)=s,\quad
\operatorname{reconstruct}(A,f)=f(1).
\]

For every nonempty `A`, raw `Correct` holds. `PerfectPrivacy` also holds: the only unauthorized set is empty. But party 0's view is identical for both secrets, so it cannot reconstruct. Taking assignments `(false,false)` and `(false,true)` shows `LocalReconstruct` fails for `{0}`. This uses finite nonempty types and is not an empty-type trick. It confirms why locality must accompany the source-identification claim.

### 5.8 Empty or nonuniform coins

Let coins be `Empty`, sharing be the unique function from an empty argument, and reconstruction be a constant. Raw `Correct` is vacuous, `PerfectPrivacy` uses the unique empty-type equivalence, and constant reconstruction is local. There is nevertheless no probability distribution on the coin space. This is acceptable as raw syntax, but not an instantiated source protocol.

Even with nonempty coins, use `F=ZMod 3`, threshold 2, and externally choose `q=0` with probability one. A single party then receives the secret itself. The algebraic `perfectPrivacy` theorem still holds, but that external coin law is not uniform or preserved by its translations. This is not a counterexample to finite-uniform Shamir privacy; it demonstrates the necessary sampling hypothesis.

**Additional exact computation:** on a three-point alphabet I enumerated all 15 probability vectors with denominator 4, all 225 ordered pairs, all 8 Boolean tests, and errors `−1,0,1/4,1/2,1`. Event advantage equaled half ℓ¹ distance throughout. For every pair, all 64 acceptance-probability vectors with coordinates in `{0,1/3,1/2,1}` also satisfied the randomized-test bound.

## 6. Proposed machine-checkable sanity theorems and interfaces

These are proposed statements, **not claimed to have been elaborated in this audit**. They use the same finite/nonempty/decidable instances as the existing definitions, with classical decidability where needed.

First publish the interfaces required by finding 5:

| Suggested name | Required statement |
|---|---|
| `shannonEntropy_eq` | `shannonEntropy p = ∑ a, Real.negMulLog (p a) / Real.log 2` |
| `probTrue_eq` | `p.probTrue D = ∑ a ∈ Finset.univ.filter (fun a => D a = true), p a` |
| `isFlatSource_iff` | The existing existential support/cardinality/mass formula, as a public iff. |
| `isExtractor_iff` | `IsExtractor C ε Ext ↔ ∀ X ∈ C, EpsClose ε (X.map Ext) (uniform β)` |
| `isStrongExtractor_iff` | `IsStrongExtractor C ε f ↔ ∀ X ∈ C, EpsClose ε (hashPair f X) (uniform (S × β))` |
| `mem_seededSources_iff` | `Y ∈ seededSources (S := S) C ↔ ∃ X ∈ C, Y = FinDist.prod (uniform S) X` |

Then prioritize the following semantic checks:

1. `EpsClose ε p q → 0 ≤ ε`; `EpsClose 0 p q ↔ p = q`; and `EpsClose ε p p ↔ 0 ≤ ε`.
2. `0 ≤ minEntropy p`, `minEntropy p ≤ Real.logb 2 (Fintype.card α)`, and `minEntropy (uniform α) = Real.logb 2 (Fintype.card α)`.
3. `IsSource k p` for `k≤0`; no such source when `log₂ |α|<k`; and `IsFlatSource k p → minEntropy p = (k : ℝ)`.
4. For nonempty `s`, both entropies of `flat s hs` equal `log₂ |s|`, including non-power-of-two sizes. For a singleton support both entropies are zero.
5. `IsExtractor (∅ : Set (FinDist α)) ε Ext`; `IsExtractor C ε Ext` when `1≤ε`; the singleton-output iff in §4.5; and monotonicity in the error parameter.
6. `IsStrongExtractor C ε f ↔ IsExtractor (seededSources (S := S) C) ε (fun z => (z.1, f z.1 z.2))`.
7. A published `hashPair` pushforward equation, `statDist` defining equation, and `hasMinEntropy_iff`, so the three disclosed cross-file definitional dependencies can be replaced by public interfaces.
8. A finite-nonempty-uniform coin theorem turning `Scheme.PerfectPrivacy` into equality of restricted-view pushforward distributions; an injective party-restriction theorem transporting **locality, correctness, and privacy** together.

For item 8, the view's type should be functions on the finite subtype of coalition members, not an unrestricted global share assignment. The existing `card_view_eq` is a useful ingredient; its bare `Nat.card` equality should not be treated as a probability theorem over infinite types.

## 7. Per-theorem statement/docstring audit

### 7.1 `Entropy.lean` — thirteen public theorems

| Theorem | Assessment |
|---|---|
| `shannonEntropy_nonneg` | Precisely the claimed nonnegativity, because each atom lies in `[0,1]` and `ln 2>0`. Attribution omission: finding 6. |
| `shannonEntropy_uniform` | Correctly asserts `log₂ \|α\|` with the necessary nonempty type assumption. The equal-term sketch proves the declared finite-alphabet extension of the source's bit-string example. |
| `shannonEntropy_uniform_bits` | Exactly the source example for `Fin n → Bool`, including the zero-bit singleton case. |
| `le_maxProb` | Exactly the pointwise upper bound claimed; the alphabet is already nonempty through the distribution. |
| `maxProb_le_iff` | Exactly characterizes an upper bound on the maximum by upper bounds on all atoms. It does not require any sign condition on the proposed upper bound. |
| `maxProb_pos` | Correctly gives strict positivity, not merely nonnegativity. Normalization excludes the all-zero case. |
| `le_minEntropy_iff` | Matches the source's equivalent pointwise bound for every real threshold. Its logarithm sketch correctly uses positivity of the maximum; the final definitional use of `HasMinEntropy` is the disclosed interface issue, not a mathematical error. |
| `isSource_iff_hasMinEntropy` | Exactly the promised bridge; neither direction drops an entropy assumption. |
| `IsSource.mono` | Correct direction: lowering the required entropy preserves membership. |
| `IsFlatSource.isSource` | Correct implication for natural `k`, viewed as real on the right. It proves the source's omitted conjunct; it does not yet state the stronger exact-entropy equality. |
| `flat_apply` | Exactly the advertised probability formula, with a nonempty support hypothesis. The `@[simp]` designation is visible to this gate. |
| `isFlatSource_flat` | Correctly conditional on a set of size `2^k`; positivity of that size supplies nonemptiness. It is not a claim that such a set exists in every alphabet for every `k`. |
| `isSource_uniform` | Correctly gives the stated entropy lower bound, including a singleton alphabet. The prose mentions the bit-string specialization, which follows by cardinal arithmetic; the formal theorem itself is general. |

### 7.2 `Extractors.lean` — nine public theorems and the private helper

| Theorem | Assessment |
|---|---|
| `FinDist.probTrue_sub_probTrue` | Correct signed-sum identity. The docstring's word “advantage” needs finding 7's correction. |
| `abs_probTrue_sub_le_statDist` | Exactly bounds every Boolean test's absolute advantage. Splitting the accepted set and its complement gives the factor `1/2`; no positivity assumption on an error parameter is involved. |
| `statDist_le_of_epsClose` | Correct converse bound. Its headline mentions attainment, while its formal statement is an implication; the proof sketch actually identifies the attaining test, so there is no mathematical gap, though a separate witness theorem would expose more. |
| `epsClose_iff_statDist_le` | Exact equivalence with no missing `ε≥0` hypothesis; both sides are false for negative errors. Finding 1 concerns its citation, not its statement. |
| `EpsClose.symm` | Exactly the claimed symmetry, valid for all real errors. |
| `EpsClose.trans` | Exactly the additive triangle bound. Negative-error hypotheses cannot be instantiated, so no extra sign assumption is needed. |
| `IsExtractor.mono` | Correctly restricts the source class, leaving the function and error fixed. It is not error monotonicity, which would be a separate lemma. |
| `IsStrongExtractor.isExtractor_seeded` | Exactly the claimed implication, with the seed retained in both input and output. The conclusion's joint uniform target and independent product sources match the definition of `hashPair`. |
| `isStrongExtractor_of_isUniversal` | The exact stated strong error bound for the full class of real-parameter `k`-sources. Its sketch faithfully composes the existing min-entropy bridge, leftover-hash bound, and distance equivalence; it promises no efficient evaluator or short seed. |
| private `sum_sub_eq_zero` | Correct conservation of mass: subtract the two normalization equations. It is appropriate technical glue. |

The two distance sketches explicitly split signed/absolute sums as described. Their `rfl` access to `statDist`, the seeded bridge's definitional use of `hashPair`, and the min-entropy bridge's use of `HasMinEntropy` agree with the pack's disclosures. They are interface-policy departures, not hidden probabilistic assumptions or unsound proof steps.

### 7.3 Changed secret-sharing theorem citations and supporting statements

| Theorem | Assessment |
|---|---|
| `Shamir.correct` | Correct reconstruction for every authorized finite set under `0<k`; the interpolation-uniqueness sketch has the required strict degree bound and distinct nodes. This proves the corrected source's correctness half after restriction/locality, without proving efficiency. |
| `Shamir.perfectPrivacy` | Correct coin-bijection statement for every field and every natural threshold. On unauthorized sets, `\|B\|<k` supplies the degree budget for the interpolating translation; the equation in its sketch has the correct sign. Distributional privacy additionally uses the coin-law condition in §4.1. |
| `Shamir.localReconstruct` | Correctly guarantees that only shares at interpolation nodes matter. This is essential to the source comparison and is actually available. |
| `Shamir.natCard_coins_view` | The finite-field formula is correct under its stated `0<k`, `k≤\|F\|`, and `\|B\|<k` hypotheses. The proof sketch's counting reduction is legitimate; uniformity of the resulting law additionally divides by the finite nonzero number of uniformly sampled coins. |
| `Scheme.PerfectPrivacy.card_view_eq` | Correct counting consequence of a fiber-preserving bijection. Over arbitrary infinite types `Nat.card` is not a probability or a full infinite cardinal, so the informal security conclusion needs the finite-uniform reading. This code/docstring predates the PR. |

The facade imports both new modules and accurately lists their contents. The other eight supplied lint findings are baseline issues; no new mathematical claim is hidden in the facade change. The pin-specific source comparison and comment-stripped checks support the docstring-only attestation. The broad negative claim about duplication remains limited by the searches actually recorded; no new duplication major is asserted here.

[PS10, Fact 153.3] supplies the valid field root bound behind interpolation uniqueness: a nonzero polynomial of degree at most `n` cannot have `n+1` distinct roots. Subtracting two proposed interpolants therefore proves uniqueness within that degree bound. The missing word “at most” in Lemma 153.2 is a source defect; it is not a defect in the formal interpolant or its uniqueness theorem.

## 8. Source record and notation

Primary source: the hash-verified attached [PS10], *A Course in Cryptography*, 3rd ed., January 2010, PDF pp. 163–166 and 193–196 (printed pp. 151–154 and 181–184). Additional attribution checks used the author-hosted [Vadhan publication](https://people.seas.harvard.edu/~salil/pseudorandomness/pseudorandomness-published-Dec12.pdf) and [HILL paper](https://www.cs.bu.edu/fac/lnd/pdf/hill.pdf). `negMulLog` was checked in [pinned Mathlib](https://github.com/leanprover-community/mathlib4/blob/029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e/Mathlib/Analysis/SpecialFunctions/Log/NegMulLog.lean). These checks establish the identified locations and conventions, not a new audit of those entire works.

**Notation glossary.** `α,β,S` are the finite input, output, and seed types; `C` is a class of source distributions; `p,q,X` denote distributions except where explicitly used for Shamir's prime or coin polynomial; `D` is a Boolean test and `Ext,f` extraction functions. `ε,δ` are real error bounds and `k` an entropy bound or, in secret sharing, the natural threshold. `H,H∞` mean Shannon and min-entropy in bits; `ln` is the natural logarithm and `log₂` the base-two logarithm. `|A|` or `#A` is cardinality; `U_A` is uniform on a finite nonempty set; `N=|α|`, `L=|S|`, `M=|β|` where used. In §4.3, `d(a)=p(a)−q(a)`, `t` is its total positive mass, and `u(a)` a randomized test's acceptance probability. In §4.6, `m` is maximum atom mass; in the bit-output formula of §4.8, `m` is output bit length and `R` is the joint seed/hash distribution. In secret sharing, `A,B` are reconstructing and adversarial coalitions, `n` the number of retained parties, `p` the prime modulus, `F` the field, `q` the coin polynomial, `e` a coin bijection, and `V,V′` the two restricted-view maps; `T` is a view event. An empty set is `∅`; `XOR` is addition of bits modulo two.
