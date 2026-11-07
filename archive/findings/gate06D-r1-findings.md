# Gate 06D, round 1 — external audit findings

Date: 2026-11-07. Repository: [Shilun-Allan-Li/tcslib](https://github.com/Shilun-Allan-Li/tcslib).

**CLOSE under the issued statement-gate criterion: 0 blockers, 0 majors, 4 minors.** The three Chapter 8 results are mathematically sound with their stated hypotheses and declared readings. The remaining findings concern the executable schedule in a proof sketch, the scope of a summary, the facade descriptions, and a resource clause missing from a theorem's conclusion. This verdict covers Gate 06D; it does not close Gates 06A–C or certify proof completion.

## Pins and integrity

| Item | Audited identity |
|---|---|
| Exact exchange commit | `5928e06c02b382b63b9b384db89d0458b520f351` |
| Frozen Lean head | `3f6db40e1688c4a0bb922c9575dd3bd2157a650b` |
| Records commit | `c81baa7712ab1b43357276ef5df138d02616c9d0` |
| Checked comparison ancestor | `eee107e92a7db11f1f8c98a5c2867304f57ddc54` |
| Source bundle SHA-256 | `3a167712e1748f7a121aa01455e060977a225bb98f5ea144071c087c568a64cd` |
| Source manifest SHA-256 | `8947c1090298d80034c616b1492792707f91016528759d0b8047478a4ef97f90` |
| Records bundle SHA-256 | `291a1edc28fac3d1b32a29109c71e8316f122dbe16891ddb0d313771c2592f2a` |
| Common evidence ZIP SHA-256 | `960ab0c708c9efdd9a5ef01175889afa0b97be0984e35ace25f4001265ee0749` |
| Final evidence index SHA-256 | `0e011edc90d469d1b3dd1156a74f6f7856f756e15e085343486a232ea24aa73b` |
| Supplied PS10 PDF SHA-256 | `7624556077a7a272ba0b3ddb7cd47b96574fb0b4b4947a25467d1f91bb61bda8` |

Both delivered `SHA256SUMS` files verify completely: nine entries in `06D-r1-gate` and five in `06-common-r1-gate`. Independently of the manifests' assertions:

- All **185** source sections match their raw byte lengths and SHA-256 hashes, and their Git blob identities match the frozen-head Git tree.
- All **184** modules' TCSlib import-edge lists match the extracted sources. The additional section is the root-export context.
- All **22** records sections match Git blobs at the records commit. The source manifest embedded in the records is byte-identical to the separately delivered manifest.
- All **3,419** archived evidence entries match `ZIP-CONTENTS.tsv` in length and SHA-256 and match Git blob identities at the records commit. The archive contains 455,288,109 uncompressed bytes.
- Comparing the supplied ancestor and head trees gives 60 changed `TCSlib/**/*.lean` paths plus the changed root export, consistent with the reported 61-path scope.

Read the exchange README, both requested gate READMEs, the issued `06D-pack.md`, PLAN, policy/rulings, inventory, source-access disclosure, Gate 05 closing findings/resolutions, and relevant final evidence. The primary surface is the four Randomness modules and facade: **8 definitions and 18 theorems**. PAC/Samples and the imported machine, probability, PRF/PRG and complexity interfaces were inspected as context.

No GitHub push, campaign-branch change, or source repair was performed.

## Findings

Paths and line numbers refer to the original frozen files, not bundle line numbers.

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| G06D-01 | **minor** | `TCSlib/Cryptography/Randomness/Derandomization.lean:72` · `bpp_subset_dtime_subexp` proof sketch, steps 1 and 4 | The sketch uses the exact schedule `⌈n^(ε/2)⌉` for every positive real `ε`, and calls an expression with real exponent `1/(ε/2)` a polynomial. | The theorem allows noncomputable real exponents. Such an exact seed schedule need not be computable, and a fixed real power is polynomially bounded rather than necessarily a syntactic polynomial. Neither issue invalidates the theorem: an integer-root schedule gives the required bound. The explicit replacement is given below. | Choose a fixed integer `d` with `1/d < min(ε,1)`; use the least integer `s` with `n ≤ s^d`. Use a syntactic polynomial output-length envelope and retain the real expression only as the target time bound. |
| G06D-02 | **minor** | `TCSlib/Cryptography/Randomness/Learning.lean:39` · module summary of `not_weakLearnsUnder_prfConcept` | The summary says no efficient learner weakly PAC-learns with a constant edge, without mentioning confidence. | The actual theorem correctly requires fixed `δ < γ ≤ 1/2`. A constant edge alone does not put KV94's success guarantee `1/q` into that regime. The PAC context correctly warns that amplification changes the learner and resources; no amplified learner or full KV94 weak-learning corollary is constructed in this module. | Add “at fixed failure probability `δ < γ`” to the summary. Explicitly retain the broader KV94 amplification/resource bridge as an additional result, rather than describing it as already provided by (c). |
| G06D-03 | **minor** | `TCSlib/Cryptography/Randomness.lean:30` · `## Contents` | The facade describes Extraction as unbiased extraction from a biased source and Learning as an Occam bound. | Extraction states the **impossibility** of an efficient one-bit extractor for efficient high-min-entropy sources. Learning proves/states PRF-based prediction hardness; it contains no Occam bound. Derandomization contains the BPP time inclusion. | Replace those entries with “no efficient one-bit extractor for efficient sources,” “PRFs give a hard-to-predict concept class,” and “PRGs give the BPP deterministic-time inclusion.” |
| G06D-04 | **minor** | `TCSlib/Cryptography/Randomness/BPPBridge.lean:72` · `verifier_toNUPPT` | The docstring promises a machine with no coins. | The conclusion specifies its advice and its output for every coin string, but does not assert a zero coin schedule. The actual proof chooses `NUPPT.ofPolyTime ... (.const 0) ...`, so the construction has the promised property; consumers of the theorem's statement receive only coin-independent behavior. | Either add `D.coins = .const 0` (or an equivalent public coin-length clause) to the conclusion, or describe the conclusion as coin-independent and identify zero coins as a property of the chosen proof witness. |

These are nonblocking because the statement-level conclusions remain correct, and each repair preserves the mathematical construction. G06D-01 is a correction to the literal executable plan, not a counterexample to the time inclusion.

### Notes requiring scope precision

**N1 — pointwise efficient-source quantifiers.** `effSources k n` quantifies over a sampler **inside the fixed length** `n`. Thus the theorem supplies a possibly different sampler at every length; it does not state one sampler family defeating an extractor at all sufficiently large lengths. This reading is expressly disclosed in Extraction, so it is not a hidden statement change.

It has a further consequence worth documenting: fixed-length sampler membership permits arbitrarily large finite hard-coded tables. At a fixed `n ≥ 1`, either output fibre of any Boolean function has a subset of size `2^(n-1)` on which the output is constant. A uniform machine can hard-code that subset, sample it with `n-1` coins at this one length, and output uniform bits at other lengths. Its description and time constant may depend on the chosen length. Consequently, the **pointwise** impossibility is true even without extractor efficiency. Do not treat that observation, or the present theorem, as a quantified uniform adversarial-sampler theorem. The supplied rejection-sampling proof remains a valid way to prove the stated efficient-extractor version.

**N2 — admissions and historical evidence.** The following are still direct admissions:

- `predictAdv_prfConcept_negligible`;
- `bpp_subset_dtime_subexp`;
- `not_isExtractor_effSources`.

`not_weakLearnsUnder_prfConcept` has a proof body but depends on the first admission. The final axiom records retain exactly those four admitted-dependent Randomness identities. Gate closure here is approval of their statements and sketches within the issued scope.

## Definition-by-definition semantic restatements

The following are independent descriptions of the expressions in the definition bodies; their adjacent docstrings agree, subject to the scope notes above.

| Definition | Body-level restatement and comparison |
|---|---|
| `prfConcept` | Evaluate the keyed function on the point, list its output bits, and take the first bit; return false when the output is empty. This is the source's first-output-bit class for positive lengths, with the stated zero-length default. |
| `encodeSample` | Turn each example into the self-delimiting pair of its input bits and its singleton Boolean label; right-nest the resulting words using the same pairing, ending with the empty word. It preserves order and labels and is unambiguous. |
| `learnerOf` | With the sample and random tape fixed, make a hypothesis that runs `A` on the paired encoded sample and test point; it predicts true exactly when the complete output word equals `[true]`. Every other output predicts false. |
| `polyLenExpr` | The polynomial syntax tree for the coefficient times the `k`th power of one plus the argument. Its value is exactly `a(n+1)^k`. |
| `subexpBound` | The natural-number ceiling of the positive real number `2^(n^ε)`, with both powers interpreted over the reals. It is the intended bound; its being noncomputable as a definition creates no problem for membership in a time class bounded by it. |
| `samplerLaw` | Push the uniform distribution on the machine's scheduled finite coin tape through its activation at parameter `n` with empty argument, then truncate or false-pad its output to exactly `n` bits. Advice is not automatically excluded here. |
| `effSources` | A law belongs precisely when it is the preceding law for some **uniform**, empty-advice PPT machine and has min-entropy at least `k n`. Uniformity is imposed in this definition. |
| `extBit` | Convert an input tuple to its bit list, apply the total string function, and truncate or false-pad its result to one bit. This models every deterministic one-bit function and gives a defined convention for empty or oversized outputs. |

For the already-gated PAC/Samples context, the consumed definitions have the following meanings:

| Definition | Meaning checked from the body |
|---|---|
| `FinDist.expect` | Finite probability-weighted sum. |
| `FinDist.iid` | Product mass over the ordered `m`-tuple, including the empty product at zero samples. |
| `err` | Probability of Boolean disagreement under the specified distribution. |
| `label` | Attach the target's label to each sampled point. |
| `accuracyProb` | Probability over independent examples and uniform learner coins that the resulting hypothesis has error at most the supplied accuracy threshold. |
| `PACLearnsUnder` | For every indexed target, that accuracy probability is at least one minus the failure parameter, at fixed learner and sample count. |
| `PACLearns` | The preceding condition for every input distribution. |
| `WeakLearnsUnder` | The fixed-distribution PAC condition at accuracy `1/2 - γ`. |
| `WeakLearns` | That weak condition for every input distribution. |
| `trialDist` | Independent uniform target index, uniform examples, and uniform learner coins. |
| `predictSuccess` | Trial probability of correct prediction on an independent uniform test point. A collision with a training point is permitted. |
| `predictAdv` | Absolute difference of this success probability from one half. |
| `expectedErr` | Trial-average uniform error of the hypothesis. |

These are fixed-learner, fixed-parameter predicates, not a reintroduced class-level `PACLearnable`. The finite types of points and keys used by Randomness are nonempty even at length zero. A zero-length coin tape also has one possible tape.

## Theorem-by-theorem comparison

Each row concerns the formal statement, separately from whether its eventual fill has been completed.

| Theorem | Statement/docstring comparison |
|---|---|
| `prfConcept_eq` | Exact reading equation for the first-bit/default convention; the `rfl` proof is correct. |
| `encodeSample_eq` | Exact equation for the ordered right fold; the prose and body agree. |
| `learnerOf_eq` | Exact equation for singleton-true output recognition, with one fixed tape defining the hypothesis. |
| `prfConcept_decidable` | Given a polynomial-time evaluator with the stated exact evaluation contract, it produces a polynomial-time singleton-bit membership decider. This is precisely part (a), including at length zero. |
| `predictAdv_prfConcept_negligible` | For a secure PRF, each fixed nonuniform PPT and polynomial example count has negligible absolute prediction advantage. This matches the stated independent-uniform reading of PS10, including the disclosed two-sided strengthening. |
| `not_weakLearnsUnder_prfConcept` | For each fixed learner and sample polynomial, fixed reals `δ < γ ≤ 1/2` eventually rule out the indicated fixed-distribution weak condition. The declaration-level prose is accurate; G06D-02 concerns the broader module summary. |
| `polyLenExpr_eq` | Exact syntax-tree equation; correct. |
| `eval_polyLenExpr` | Evaluation equals the existing BPP coin schedule at every natural argument, including zero coefficient and zero exponent. The simplification equation has the claimed orientation and value. |
| `verifier_toNUPPT` | An efficient Boolean verifier and polynomially bounded advice sequence give an NUPPT with exactly that advice and the stated output on every tape. This supplies the needed behavioral bridge; the missing explicit zero-coins clause is G06D-04. |
| `randProb_eq_uprob` | The rational counting probability, cast to reals, equals uniform probability on the corresponding bit tuples. The claim is valid also with zero random bits. |
| `subexpBound_eq` | Exact natural-ceiling equation; correct. |
| `subexpBound_pos` | Positive at every length for every real exponent: the outer base is positive, and the ceiling of a positive real is positive. The short proof proves the advertised fact. |
| `bpp_subset_dtime_subexp` | Secure PRG existence implies the stated inclusion for every positive real exponent, with `InBPP polyTimeModel` and the existing multi-tape `DTIME`. It is the source's inclusion with rounding; G06D-01 supplies the computable implementation of the sketch's seed schedule. |
| `samplerLaw_apply` | Each word's mass is the sum of uniform tape masses over exactly its preimage under the padded output map. This is the correct pushforward formula. |
| `samplerLaw_prob` | The same identity at the probability-function field, by function extensionality; correct. |
| `effSources_iff` | Exact membership characterization with both uniformity and min-entropy retained. |
| `extBit_eq` | Exact equation for first-bit truncation/false-padding; correct. |
| `not_isExtractor_effSources` | For every polynomial-time string function and every length, the induced one-bit function fails the specified extractor condition. The efficiency hypothesis repairs the source proof's missing premise; the pointwise quantifiers and the small-length behavior are disclosed. |

### Short correctness proofs and representation costs

The in-scope reading equations are either definitional or direct finite pushforward identities. In particular, `samplerLaw_apply` sums each tape with mass `1 / |S.Coins n|`; `samplerLaw_prob` merely applies function extensionality to that equality.

The membership decider in part (a) is
\[
z\longmapsto [\,\operatorname{headD}(\mathrm{false},E(z))\,].
\]
Polynomial-time closure under composition gives its efficiency, and the evaluator contract gives its equality to the desired concept bit. No key is implicitly supplied to the learner.

The pairing body has
\[
|\operatorname{pairEncode}(u,v)|=2|u|+2+|v|.
\]
Consequently,
\[
|\operatorname{encodeSample}(S)|=m(4n+8),\qquad
|\langle\operatorname{encodeSample}(S),x\rangle|
=2m(4n+8)+n+2.
\]
The right fold doubles each individual entry, not the accumulated suffix. Thus polynomially many examples yield polynomial input length. The fixed learner tape defines one hypothesis; an ordinary efficient training-and-evaluation learner can be simulated by recomputing training on that fixed tape.

For the BPP bridge, membership in the verifier's true-set yields a polynomial-time indicator on `⟨x,y⟩`. The input/advice projections reconstruct that pair. Because the verifier is Boolean and total, its true-set already determines both outputs; ignoring the false-set witness loses no behavior. The constructed witness uses zero coins and the original advice bound.

Both probability notions in the bridge are
\[
\frac{\#\{r\in\{0,1\}^{m}:A(\operatorname{List.ofFn}r)\}}{2^m}.
\]
The denominator is positive at every `m`, including `m=0`. No acceptance event, error threshold, or machine model is changed by this equality.

These checks are mathematical/source checks of the short proofs. They are not a new Lean kernel run.

## The three substantive arguments

### 179.1: PRF prediction hardness and PAC confidence

For positive input lengths, in the random-function experiment let the collision event be that the fresh point appears among the training examples. Independence gives
\[
\Pr[\text{collision}]
=1-(1-2^{-n})^{m}
\le m\,2^{-n}.
\]
Off that event, the fresh first output bit is unbiased and independent of the entire training transcript and learner tape. Therefore
\[
|p_{\mathrm{RF}}-\tfrac12|
\le \Pr[\text{collision}]
\le m\,2^{-n},
\]
and
\[
|p_F-\tfrac12|
\le |p_F-p_{\mathrm{RF}}|+m\,2^{-n}.
\]
The oracle distinguisher makes `m+1` queries. Its coins consist of the points and the learner tape; all transcript lengths, advice and computation costs are polynomial. PRF security makes its first term negligible; the polynomial-over-exponential collision term is negligible. The source's proof and the supplied sketch therefore justify the statement. The exceptional first-bit convention at zero length affects only one parameter.

For the PAC consequence, if the learner satisfied the weak condition at `γ,δ`, the accuracy-event split would give
\[
\operatorname{expectedErr}
\le \tfrac12-\gamma+\delta,\qquad
\operatorname{predictSuccess}\ge\tfrac12+\gamma-\delta,
\]
hence
\[
\operatorname{predictAdv}\ge\gamma-\delta>0.
\]
Part (b) eventually gives advantage below that fixed gap. The displayed Lean proof uses the smaller bound `(γ-δ)/2` and a positive-length cutoff, so the contradiction is valid. For ordinary parameters `0 ≤ δ < γ ≤ 1/2` this is substantive. If `δ < 0`, the weak condition itself is impossible on the nonempty class; allowing such reals does not invalidate the theorem.

**KV94 comparison.** The repaired context does not attribute small failure probability to the original weak learner. Starting only with success at least `1/q`, where `q≥1`, and edge `γ`, an independent resource calculation gives the required different learner as follows. Fix a common target-size bound and common resource/edge/success guarantees over the class. For `0<γ≤1/2`, choose
\[
\delta_*=\gamma/4,\quad
R=\left\lceil q\ln(2/\delta_*)\right\rceil,\quad
V=\left\lceil \frac8{\gamma^2}\ln(4R/\delta_*)\right\rceil.
\]
Run the original learner independently `R` times. Validate its resulting hypotheses on one fresh shared holdout of `V` examples and select the smallest empirical error.

1. Failure to obtain any original good hypothesis is at most
   \[
   (1-1/q)^R\le e^{-R/q}\le\delta_*/2.
   \]
2. Conditional on the candidates, the probability that any validation estimate differs from its true error by more than `γ/4` is at most
   \[
   2R e^{-V\gamma^2/8}\le\delta_*/2.
   \]
3. On the complementary event, the selected hypothesis has error at most
   \[
   \tfrac12-\gamma+2(\gamma/4)=\tfrac12-\gamma/2.
   \]

Thus the new learner has edge `γ/2` and failure at most `γ/4`. If one original run uses `m` examples and time `T`, and hypothesis evaluation costs `E`, the new sample count is `Rm+V`, with time bounded by polynomial bookkeeping plus `RT+RVE` during training and evaluation of the selected hypothesis afterward. With polynomial original training/evaluation costs and reciprocal-polynomial original success and edge, these quantities remain polynomial. One can use a polynomial sample envelope and ignore surplus examples.

This is an independently checked mathematical resource argument, **not a construction already formalized in Learning** and not a fresh textual verification of KV94's unavailable pages. For constant original edge it places the changed learner within (c). For a length-dependent inverse-polynomial edge, the analogous nonnegligible prediction contradiction uses (b); (c)'s fixed real parameters alone do not state that extension. G06D-02 prevents the summary from obscuring this distinction.

### 180.1: BPP bridge and a computable seed schedule

The bridges preserve the actual verifier's output and the exact probability measure. Security against nonuniform distinguishers permits selecting a bad input of each relevant length as advice. After reindexing by seed length, the advice must be polynomially bounded in that seed length.

For a completely executable version of the sketch, fix an integer `d≥2` satisfying
\[
0<1/d<\min(\varepsilon,1),
\qquad
s(n)=\min\{t\in\mathbb N:n\le t^d\}.
\]
Integer comparison and integer powers compute this schedule without a real-number oracle. Its bounds are
\[
n\le s(n)^d,\qquad
s(n)\le n^{1/d}+1.
\]
A syntactic polynomial envelope such as
\[
P(s)=a(s^d+1)^k+s+1
\]
both dominates the needed verifier randomness `a(n+1)^k` and expands the seed at every length. The existing PRG truncation/expansion interfaces support taking such an envelope.

For each bad seed length choose one corresponding bad input. Its length is at most `s^d`, so `verifier_toNUPPT` applies with polynomial advice. The distinguisher feeds the appropriate prefix of its input string to the verifier; it does not need to generate a seed from its challenge string. Each seed length corresponds to finitely many input lengths, and `s(n)→∞`, so infinitely many bad input lengths yield infinitely many bad seed lengths.

The exact real schedule in the original sketch cannot generally be used literally: if `s(n)=⌈n^α⌉` were computable for a positive real `α`, evaluating it at `n=2^j` would determine `α` within a rational interval of width at most `2/j` using the integer binary logarithm of the result. Thus it would make `α` computable. This explains G06D-01.

**The apparent strict-majority boundary is not a defect.** Ruling out infinitely many gaps greater than `1/6` gives eventual gap at most `1/6`. The original verifier's success has the form `b/2^m ≥ 2/3`. Equality is impossible because `3` does not divide a power of two, so its success is actually greater than `2/3`. The generator-driven success is consequently greater than `1/2`. Majority over all seeds is valid. Using a threshold such as `1/12` would simplify this detail but is not required for correctness.

The time bound follows for sufficiently large lengths from
\[
2^{s(n)}\operatorname{poly}(n)
\le 2^{\,n^{1/d}+1+C\log_2(n+1)+C'}
\le 2^{n^\varepsilon},
\]
because `1/d<ε`. A finite table handles the remaining inputs. The enumeration, generator evaluation, verifier evaluation and counting machine still require their substantive fill; the statement phase does not supply that machine.

Finally, for `ε>0`,
\[
\operatorname{subexpBound}(\varepsilon,0)=1,\qquad
\operatorname{subexpBound}(\varepsilon,1)=2.
\]
It never encounters the zero-time-bound pathology of this library's `DTIME`. The family is conventionally called subexponential because arbitrarily small positive exponents are available; individual bounds with exponent at least one need not themselves be subexponential.

### 183.6: efficient-source extractor impossibility

Let `q` be the probability that the induced extractor bit is true on a uniform `n`-bit input. If the uniform source already has output distance greater than `1/4`, it is a witness. Otherwise
\[
\tfrac14\le q\le\tfrac34,\qquad
S=\{x:\operatorname{extBit}(x)=1\},\qquad
|S|=q\,2^n\ge 2^{n-2}.
\]

Ten independent trials with an independent uniform fallback have law
\[
X=(1-q)^{10}U_n+\bigl(1-(1-q)^{10}\bigr)\operatorname{flat}(S).
\]
Each component has every atom at most `2^{-(n-2)}`, and therefore so does their mixture. No efficient sampler for `flat(S)` is assumed: it is only an algebraic description of the bounded rejection sampler's law.

The true-output probability is exactly
\[
\Pr[\operatorname{extBit}(X)=1]
=(1-q)^{10}q+1-(1-q)^{10}
=1-(1-q)^{11}.
\]
At the boundary `q=1/4` it is
\[
\frac{4\,017\,157}{4\,194\,304},
\qquad
\operatorname{dist}(\operatorname{extBit}(X),U_1)
=\frac{1\,920\,005}{4\,194\,304}>\tfrac14.
\]
The `11n` coins, ten calls to the polynomial-time extractor, and one uniform fallback form a uniform PPT sampler. For `n≤2`, a deterministic point source suffices because the entropy requirement is nonpositive. The real subtraction `(n:ℝ)-2` is correctly retained.

This verifies the prior efficiency repair and the exact rejection/fallback calculation. It also verifies that `extBit`'s default for an empty output makes such an extractor a constant-bit function, which correctly fails.

## Adversarial instances and executed checks

These are checks of the stated semantics and boundary cases, not substitutes for asymptotic proofs.

| Instance | Exact result and implication |
|---|---|
| Zero-length PRF class; always-false learner | There is one point and one key, and the concept bit is false. Prediction success is 1 and advantage is `1/2`. A single exceptional length is compatible with negligibility. |
| Random Boolean function on `n=1`, one example; memorize seen labels and predict false elsewhere | Success `3/4`, collision probability `1/2`. Omitting the collision term would be false. |
| Same memorizer at `n=2`, two examples | Success `23/32`, collision probability `7/16`, advantage `7/32`. Repeated examples are correctly allowed. |
| No examples in the random-function experiment | Success exactly `1/2` for the tested predictor. The encoding is empty and the game remains defined. |
| Two constant targets; learner outputs a fair random constant; `γ=1/4, δ=1/2` | For each target it has error zero with probability `1/2`, so the weak condition holds, yet prediction advantage is zero. This refutes dropping the confidence-gap premise from the generic implication; it is not a PRF counterexample. |
| Extractor lengths `n=0,1,2` | Point sources meet the nonpositive entropy threshold, and their deterministic one-bit image has distance `1/2` from uniform. |
| Extractor true fibre occupies exactly `1/4` of the domain | The uniform source is exactly at the allowed output-distance boundary. The rejection witness still has the strict distance calculated above. |
| Constant or empty-output extractor | The uniform source alone gives distance `1/2`; the rejection branch need not divide by an empty fibre. |
| BPP randomness coefficient zero; probability bridge with zero bits | The random-tape space is a singleton and both probability readings are a 0-or-1 event probability. It does not become an empty probability space. |

An independent Python check using exact rational arithmetic:

- verified the sample/argument length formulas for all 25 pairs `0≤n,m≤4`;
- exhaustively enumerated random-function labels, samples and test points for `1≤n≤3`, `0≤m≤2` (nine cases), obtaining success `1/2 + (1-(1-2^-n)^m)/2` for the memorizer;
- checked all **278** Boolean truth tables at lengths `0≤n≤3`, constructing a point, uniform, or rejection-mixture witness and verifying normalization, the maximum-atom bound and output distance strictly greater than `1/4`;
- checked the PAC confidence counterexample and the displayed rejection-sampling fractions.

All assertions passed. These finite calculations are corroboration; the preceding arguments handle general lengths.

## Source access and exact comparison limits

| Source/version | What was independently available and compared | Limit |
|---|---|---|
| **PS10**, exact supplied 3rd-edition January-2010 course copy | Retrieved the provided PDF, verified its 1,771,458 bytes and pinned hash, and read Chapter 8, book pp. 179–184 / PDF pp. 191–196. Visually inspected pp. 179, 180, 183 and 184 as well as extracting the text. The learning class, time inclusion, extractor definition and rejection proof agree with the assessment above. | Poppler reported a reconstructable cross-reference issue; the relevant text and rendered pages were readable. This is a comparison with the supplied exact course copy. |
| **SSBD14**, [official author-hosted personal-use copy](https://www.cs.huji.ac.il/~shais/UnderstandingMachineLearning/understanding-machine-learning-theory-algorithms.pdf) | Read §3.1, Definition 3.1 through the web reader: realizability, i.i.d. labelled samples, parameters in `(0,1)`, and a probability guarantee for sufficient samples. The contextual fixed-parameter adaptation is disclosed and consistent. | This 449-page author copy places the definition on PDF p. 43 and warns that its pagination differs from print. The direct download returned HTML rather than a PDF; it was not counted as a verified PDF. No byte identity with Gate 05's reproduction or the printed edition is asserted. |
| **KV94**, §4.1 p. 74 and §4.2 pp. 76–77 | Read the delivered Gate 05 findings/resolutions and independently checked the claimed success/confidence distinction and resource argument above. The [official publisher record](https://doi.org/10.7551/mitpress/3897.001.0001) identifies Chapter 4. | The publisher's [Chapter 4 endpoint](https://doi.org/10.7551/mitpress/3897.003.0005) was unavailable, and the whole-book endpoint returned 403 on opening. **No fresh literal comparison of these exact KV94 pages was possible.** Prior audit assertions remain context. |
| **AB09**, Definitions 1.12 and 7.3 | Inspected the actual frozen `DTIME`, `InBPP` and `polyTimeModel` definitions and verified their use in the bridge and PS10 inclusion. | Full opens of the [official draft](https://theory.cs.princeton.edu/complexity/book.pdf) and [author-hosted Part I](https://www.cs.princeton.edu/~arora/book/part1.pdf) returned 403. Search-index material has draft numbering, so it was not treated as a fresh published-edition comparison of Definition 7.3. |
| **PSV06**, [official author copy](https://www.cs.cornell.edu/~rafael/papers/PSV06a.pdf) | Retrieved PDF; its SHA-256 is exactly `f5087d68df8782e2ca0465ce511c9dd6778dea70052d666a8ff86bd85873a6e6`, as listed in the common source manifest. | Its non-malleability definitions are outside 06D. No new comparison of Definition 3, Definition 4 or Theorem 1 is claimed here; the historical publisher-copy identity was not verified. |
| **PSV07**, [official author copy](https://www.cs.cornell.edu/~rafael/papers/newdefs.pdf) | Retrieved PDF; its SHA-256 is exactly `d0d6f5edd2527265d20213b35e2042e018ef7e357049cdd5d379ae1d0938c98e`. | Definitions 1–4, Corollary 1 and Theorems 3–4 are outside 06D. No new source comparison, author/publisher equivalence, or access to deferred full-version proofs is claimed. |
| **Goldreich**, [chapter 4 draft](https://www.wisdom.weizmann.ac.il/~oded/PSBookFrag/part4N.pdf), [chapter 7 draft](https://www.wisdom.weizmann.ac.il/~oded/PSBookFrag/prot.pdf), [Appendix C draft](https://www.wisdom.weizmann.ac.il/~oded/PSBookFrag/errI.pdf) | Tried all three exact official PDF URLs. All direct downloads returned HTTP 503. The web reader could access chapter 4 as text; chapter 7 and Appendix C were unavailable there. | No exact PDF-hash verification or new comparison of Def. 4.3.1, §4.3.4/draft Lemma 4.3.9, Defs. 7.3.1–7.3.2, Thm. 7.3.3, Constr. 7.3.5/Prop. 7.3.6, or Def. C.1.1 is claimed. These are other prongs' comparisons, not dependencies of the 06D arguments. Draft/published equivalence remains unverified. |

No third-party PDF, full-text extraction or rendered book page is included in this delivery. The unavailable contextual comparisons do not become source-fidelity approval. They also do not prevent independent checking of the three PS10 arguments whose exact supplied source was available.

## Build-evidence assessment and audit limits

The archive's final records report 37 passing and 17 failing full-source seals, 138 diagnostics in 110 unchanged blocks, retained legacy equation reads, and 46 admitted-dependent identities across the common campaign scope. I did not relabel the inherited failures as passes or treat the maintainer's source-review conclusions as independent mathematical evidence.

For the four primary Randomness modules, I inspected the final classifications and their captured probe/log artifacts: all four report return code 0 and zero error diagnostics; the captured probe and log SHA-256 values match their classification records. The direct admission warnings remain present. Earlier invalid BPPBridge attempts were not substituted for these final records.

Lean and Lake are unavailable on the current PATH. I did **not** rerun elaboration, the seal harnesses, lint, controls, or `#print axioms`; the supplied successful runs remain historical run evidence. The source and arithmetic checks in this report were independently performed. The root export visibly imports the topic and PAC facade, but root-export elaboration is not certified. S2 PR #231 is outside this frozen source and this verdict.

The specified prior repairs are adequate for the statements actually issued: extractor efficiency is explicit, the repaired PAC model is used, and (c) has the necessary confidence gap. The full KV94 amplification construction is not silently credited to the original learner.

**Gate 06D: CLOSE — 0 blockers, 0 majors, 4 minors.**

**Notation glossary.** `p_F,p_RF` are prediction-success probabilities with the PRF and a random function. In the amplification calculation, `q` is the reciprocal-success bound, `δ_*` the new failure bound, `R` the number of independent training runs, `V` the holdout size, and `T,E` the original training and hypothesis-evaluation time bounds. In derandomization, `d` is a fixed integer root degree, `s(n)` the integer seed schedule, `P` a polynomial output envelope, `α` a real exponent, `j` a positive integer index, `b` an accepting-tape count, and `C,C'` fixed bookkeeping constants. In extraction, `q` is the uniform true-output probability, `S` its true-output fibre, and `X` the rejection/fallback law. Remaining symbols follow the audited source.
