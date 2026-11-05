# Gate 02 / S2a — external API audit findings

**Audited:** [Shilun-Allan-Li/tcslib#185](https://github.com/Shilun-Allan-Li/tcslib/pull/185), head `597eef43ccd3c8bfafe0c0c16a2444b12adc1644`; campaign records `b4e02c7b4e7c4c5c4830f8ba8932dc97932f95ee`.

**Disposition: do not close this gate as submitted.** I found **1 blocker, 3 majors, 6 minors, and 2 notes**. The probability, state-threading, composition, and numerical advantage statements survived the checks below. The material problems concern the claimed protocol semantics, the proposed extraction of views, the applicability of the bad-event lemma, and coverage of the source's expected-time zero-knowledge simulators. These are separate from whether Lean accepts the proofs.

## Verification and scope

| Input | Observed SHA-256 | Result |
|---|---|---|
| `gate02-s2a-bundle.md` | `eb9c1c44a45363a793325ad5f5aa69c2cb78b5972c4e6e0aa96e0172733adf05` | Exact match; exactly 20 section headers. |
| `Pass–Shelat.pdf` | `7624556077a7a272ba0b3ddb7cd47b96574fb0b4b4947a25467d1f91bb61bda8` | Exact match. |

The audit covers all **33 explicit definitions/types/abbreviations, both monad instances, and all 68 named theorems** in the six modules, together with the facade, design documents, policy, and bundled contextual definitions. Structure fields and inductive constructors are included below. I read definition bodies through comment-stripped views before comparing their prose; I reviewed theorem statements and mathematical proof sketches, not tactic scripts.

I checked PS10 §4.4, PDF pp. 126–128; the relevant chapter 5–7 definitions in PDF pp. 145–187; and, to resolve the simulator issue, Def. 121.2, Algorithm 123.4, and the continuation of Thm. 175.1 on PDF p. 188. Book page numbers are PDF page numbers minus 12. I visually checked the execution rule on PDF p. 127 and the joint-view/output definition on PDF p. 168. This is not an audit of every theorem in chapters 5–8.

The bundled replay records 8/8 successful module checks, and the axiom log lists all 68 theorems with only the advertised standard axioms. I did **not** independently run Lean or reproduce the repository-wide name screen. I did independently check the declaration inventory and run exact-rational, small-instance checks of a transcription of the defining equations; those checks are corroboration, not Lean certificates. The one-line `TCSlib.lean` export is attested but not included in the bundle, so its presence was not independently verified.

All local source locations below use the individual file's line numbers, with its copyright block beginning at line 1. Paths without a directory prefix are under `TCSlib/Cryptography/Games/`.

## Findings

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | blocker | `Protocols.lean:75,83` · `Party.finish`, `Party.exec`; design §6 | The executor implements PS10 §4.4. | PS10 book p. 115 ends the protocol when the active ITM halts. Here `exec 1 (.pure a) B` executes all of `finish (B none)`, including new randomness and arbitrarily many further exchange queries, and reports success. It can manufacture an output of a party which the source execution never activates. See A4–A5. | Provide a source-faithful stopping semantics with observable output/termination state. Alternatively retain this coroutine-completion operator under an explicitly different specification, and supply a separate source execution or a proved equivalence on an explicit restricted class before defining PS10 security through it. Merely citing §4.4 is insufficient. |
| 2 | major | `Protocols.lean:20–23` · module claim about views; design §6 | A party's received messages and coins are recovered from its own oracle-answer log. | The initial message to `B` enters as the argument of `B (some m)`, outside any query made by `B`. If `B` immediately returns, its oracle log is empty even though it received `m`. The advertised recipe would erase an entire secret-bearing message; A6 gives a privacy counterexample. No view definition is implemented yet, so this is a defect in the proposed interface/recipe, not a claim that an existing security theorem is false. | Make the initial receive an explicit logged event, or explicitly seed the receiver's view with it. Specify input/auxiliary-input and coin-tape handling, and preserve the joint distribution with the other party's output. Correct the present claim now; carry the corrected construction and projection laws into S2b. |
| 3 | major | `Hopping.lean:193,240` · `prob_eq_until_bad`, `identical_until_bad`; design §5 | This is the generally usable code-based fundamental lemma for the intended bad-event hops. | The stated theorem is valid, but `hagree` requires equality of the **whole handler computation from a good entry state**, including the reply and state on the branch that first raises `bad`. Standard bad-event hops may already diverge on that branch. A7 is a one-query example with gap = bad probability = 1/2 which this lemma cannot accept. Equality of computations also excludes equal-law implementations with extra unused randomness. | Retain it as a restricted lemma and state the restriction explicitly. Add a stepwise coupling/off-bad-distribution lemma allowing divergence on the first bad transition, or demonstrate a source-relevant factorization that creates a common boundary after setting `bad` and before divergence. Do not identify this restriction with the full BR06 lemma without a deviation note. |
| 4 | major | `Probability.lean:71`, `Protocols.lean`; design §§6–8, especially B4 | The framework and planned strict-machine bridge cover PS10 Thm. 175.1 in its stated generality. | Every `ProbComp` has finite support and a finite bound on the number of draws. Def. 121.2 expressly permits **expected** polynomial-time simulators; Algorithm 123.4 retries without a worst-case bound, and Thm. 175.1's proof uses expected running time. The current syntax cannot execute such a retry loop or represent its unbounded runtime. A10 proves the obstruction. | Specify a separate expected-time execution/semantics layer and its bridge, or explicitly restrict the downstream theorem and justify any claimed equivalence. A finite-output law may sometimes be represented extensionally, but that does not represent the simulator algorithm or certify its expected efficiency. Finite truncation alone does not preserve perfect zero knowledge. |
| 5 | minor | `Protocols.lean:33,79–90` · `Party.exec` fuel documentation; design §6 | `fuel` is the protocol's message count / suffices for at most that many messages. | A protocol with one send followed by a return needs fuel 2: fuel 1 produces `none`. Even two immediate returns need fuel 1. In addition, the `finish` branch does not charge further exchange requests against fuel. See A4–A5. | Describe the actual recursion budget precisely, prove its relation to rounds/messages, and separate it from the uncharged drain. For a run with `r` handoffs before the first return, `r+1` suffices for the present executor; source-faithful execution still requires resolving #1. |
| 6 | minor | `OracleComp.lean:17–18` · module description of `OracleComp` | A general oracle computation is a finite tree. | `rng i` can be `ℕ`. A first query returning `n`, followed by `n` singleton-answer queries, is a legal well-founded tree with infinitely many branches and unbounded finite depths. See A11. | Say “well-founded query tree”; explain that finite response types make each individual computation finite. The finite-tree claim for `ProbComp` is correct. |
| 7 | minor | `Probability.lean:71,78`; `Simulate.lean:137,148`; `CITATION-VCVio.md` | The design-adaptation citation is complete at declaration level and accurately describes source headers. | File-level citations supply project, authors, commit, modules, licence, and tag. However, `ProbComp`, `sampleFin`, `QueryImpl.comp`, and `simulate_comp` lack declaration tags despite identifiable VCVio counterparts. The record's statement that the consulted headers say “VCVio Contributors” is false for the checked modules: they name Devon Tuma and, in several cases, Quang Dao/Alexander Hicks. See Q10. | Tag these adapted constructions/results, preferably with exact paths. Correct the header description; retain the distinction between design adaptation and copied code. Updating the redirected repository URL is useful but not itself a missing-credit finding. |
| 8 | minor | `Advantage.lean:43,93–97`; `Hopping.lean` reference block | Precise source locations identify the cited results. | The attached PS10 hybrid lemma is **Lemma 71.6**, book pp. 71–72, not “Lemma 70.2”; book p. 70 has Figure 70.2. In the inspected Shoup revision, the difference lemma is Lemma 1 in §1.1, not §4. | Correct the PS10 reference and say that `advantage_hybrid` is the telescoping inequality used in that lemma's proof. Pin the Shoup revision and correct its section references. |
| 9 | minor | `Advantage.lean:65–66`; `Hopping.lean:95–98` | The opening prose precisely states each theorem. | `accept_nonneg` says “between zero and one” but proves only the lower bound; the next theorem supplies the upper bound. `expect_mono_of_allOutputs` is a support-restricted **inequality**, while its prose describes dependence on support without stating the inequality. | Change the first to “nonnegative” and the second to “pointwise inequality on all possible outputs implies the corresponding expectation inequality.” |
| 10 | minor | `Advantage.lean:97` · `advantage_hybrid`; contextual `Foundations/Probability.lean:211` | Disclosed generalization/bridge debt covers the relevant duplication. | `advantage_hybrid` is directly the existing `abs_sub_le_sum_hybrids` with `P i = accept (G i)`. This arithmetic overlap is additional to the three advertised definition bridges and needs no probabilistic bridge to identify. | Record this overlap explicitly; when reconciling dependencies, share the elementary real-number lemma in an appropriate common module or document the intentional duplication. No assertion of copied tactic text is made. |
| 11 | note | `Probability.lean` · `sample`, `expect`; planned machine layer | Exact finite uniform sampling supplies mathematical semantics, not automatic fair-bit efficiency. | Uniform sampling from three elements gives probability 1/3. A machine using at most `k` fair random bits has event probabilities with denominator dividing `2^k`, so it cannot implement that law exactly. Arbitrary continuations and `Fintype.equivFin` also carry no computational bound. | No defect in the current mathematical semantics. S2b must distinguish efficiently implemented samplers from abstract ones; use a suitable machine/randomness model, expected-time sampling, or a quantified approximation where needed. |
| 12 | note | Facade; design §8; contextual `QueryTree`, `uprob`, `acceptProb`, `distAdv` | Bridges and efficiency results are deferred. | The disclosed B1/B2 and acceptance/advantage correspondences are mathematically plausible on nonempty finite seed types. Neither `simulate_comp` nor query-cost preservation establishes polynomial-time closure, cryptographic oracle substitution, or protocol/ZK equivalence. | Keep these as explicit outstanding obligations. Their absence alone is not a new S2a finding; the specific incorrect claims and expressiveness gaps above are. |

## Answers to the ten questions

### Q1. Sampling

**Yes, with the usual conditional meaning of fresh randomness.** At a query node with `m+1` answers, the weight of each continuation is `1/(m+1)`. For any root-to-leaf path, its probability is the product of these weights; expectation sums the leaf value times its path probability. A repeated occurrence of the same sampling computation draws again. Sharing a previously returned value instead reuses that value.

When the size of the next sample depends on history, the next answer is uniform **conditional on that history and its chosen range**; this does not assert unconditional independence of arbitrarily encoded adaptive outputs. For a fixed nonempty finite `T`, the cast in `sample` is justified by `|T|>0`, and its inverse enumeration is bijective. Consequently

\[
\mathbb E_{\mathrm{sample}\ T}[g]
=\frac1{|T|}\sum_{t\in T}g(t),\qquad
\Pr_{\mathrm{sample}\ T}[t=a]=\frac1{|T|}.
\]

The singleton case is valid; the empty case is excluded by `[Nonempty T]`. Neither independence nor normalization is being inferred from a zero denominator.

### Q2. Simulation and logging

**State threading and chronological logging are correct.** Each handler returns `(answer,newState)`, and the continuation receives exactly that answer and state. `withLog` calls the underlying handler on the underlying state, then appends one entry at the tail of the old log. Thus a pre-existing log is a prefix, not reversed or overwritten. The handler cannot inspect the additional log through this wrapper.

`simulate_withLog` proves equality of computations after discarding the log, retaining **both** the original output and final underlying state. This is stronger than equality of output probabilities and is the right conservativity law. It records the queries at the wrapped interface, not automatically all target-oracle queries inside each implementation. Protocol views additionally require the initial-receive correction in #2.

### Q3. Composition

**Yes, at the semantic level.** If the inner implementation has state `σ₁` and the outer implementation has state `σ₂`, the left side returns `((a,s₁'),s₂')`. The right side first returns `(a,(s₁',s₂'))` and then explicitly reassociates it to the same value. Both states persist across successive adversary queries; neither is reset per call.

This is the reduction-interpreter equation needed for oracle implementations. It does not itself assert indistinguishability or the efficiency of the composite reduction. The supplied proof sketch correctly explains the induction and reassociation.

### Q4. Costs

**Yes.** The theorem permits a per-source-oracle charge `b i`, not merely a universal charge of one. If every target implementation costs at most `b i`, then a source bound using those charges transfers unchanged. At a query, the accounting is

\[
b(i)+(q-b(i))=q\quad\text{because }b(i)\le q.
\]

Natural subtraction therefore does not hide overspending. For `b i=0`, the corresponding implementation must itself have target cost zero. It cannot secretly make positive-cost target calls. Cost-zero sampling oracles can execute arbitrarily many finite draws without affecting this bound; that is appropriate for a **query** bound, not a running-time or bit-complexity bound. At budget zero, pure computations and zero-cost queries are permitted, positive-cost queries are excluded.

### Q5. Identical until bad

**The conclusions and proof sketches are correct for the actual hypotheses; applicability is narrower than advertised.** `prob_eq_until_bad` equates the two off-bad output-event probabilities and the two final-bad probabilities. Splitting each output event into good and bad parts gives the bound in `identical_until_bad`, with constant one and either game's common bad probability.

There are two distinct restrictions:

1. Equal computations is stronger than equal distributions. Adding even a discarded deterministic sampling query can break the premise while preserving every probability.
2. More significantly, equality is required for the **entire call that starts good**. The implementations cannot answer differently on that call even after discovering a repeated nonce or a forbidden/challenge query and setting the flag. This is the ordinary first-divergence case of the fundamental lemma, illustrated in A7.

Repeated-nonce flags and “ever queried the challenge” flags can be made sticky by updating `bad := bad ∨ newBad`. But that does not repair the first-divergence restriction. A source hop can use the current lemma only if the whole crossing call still agrees, or after a proved restructuring which places a simulation boundary between detecting bad and divergent behavior. The underlying framework can express such extra phases; the general handler-level lemma has not been supplied.

**Stickiness cannot simply be removed** while bounding by final bad probability: A8 gives an explicit gap of one with final bad probability zero. An alternative theorem could instead track “ever bad” in an accumulated flag or trace.

### Q6. Collision bound

**Yes.** The list is produced first, and `sample T` is then invoked freshly inside the continuation. For every possible list `L`,

\[
\Pr[t\in L\mid L]
=\frac{|\operatorname{set}(L)|}{|T|}
\le\frac{L.\mathrm{length}}{|T|}
\le\frac q{|T|}.
\]

Averaging gives exactly the stated real-valued bound. Duplicate entries only weaken the upper bound. `q=0` yields zero; `q>|T|` gives a valid but uninformative bound above one. A list chosen after seeing `t`, such as `[t]`, does not have the theorem's program shape. This is a single fresh-hit estimate, not yet a complete adaptive birthday/CCA1 analysis: those need conditional-history arguments and a union bound across steps. In particular, it does not by itself justify treating an adversarially chosen nonce query as an independent uniform sample.

### Q7. Guessing versus distinguishing

**Yes, for the explicitly chosen absolute-bias convention.** Write `p₁ = accept (G true)` and `p₀ = accept (G false)`. Directly,

\[
\Pr[\mathrm{win}]
=\tfrac12 p_1+\tfrac12(1-p_0),\qquad
\left|\Pr[\mathrm{win}]-\tfrac12\right|
=\tfrac12|p_1-p_0|.
\]

Thus the maximum `guessAdv` is 1/2 while the maximum `advantage` is 1. This is not the convention which already multiplies guessing bias by two. An always-wrong predictor also has absolute bias 1/2; complementing its output makes it always correct, so this does not trivialize a security definition quantified over adversaries.

### Q8. Executions

**Alternating routing is correct until the first return; the full source semantics is not.** When `A` sends `m`, `B (some m)` becomes active, and `A`'s continuation becomes the waiting party. The result swap restores the original output order. Independent coin draws are preserved through `step`.

PS10 stops on the active party's halt. The executor instead activates/drains the other party, synthesizing repeated `none` replies. The `Option` datatype itself is a reasonable way to distinguish a message from an explicit closure notification, but PS10 does not provide this notification-and-drain rule. `finish` can discard arbitrary attempted sends and still produce a successful pair, hiding such behavior from an output-only observer. A consumer must not silently equate that success with source-conformant termination.

For a fixed bound of `r` actual handoffs before the first return, `r+1` fuel avoids the current off-by-one truncation. This is only an accounting observation about this executor; it does not cure its halt semantics or establish agreement with a fixed-round source protocol. A monotonicity/stabilization theorem and an explicit correspondence theorem are missing.

### Q9. Expressiveness for the source

“Expressible” in the successful rows means the concrete experiment at one security parameter; efficient-adversary quantification and negligibility remain the explicitly deferred machine layer.

| Source item | Assessment |
|---|---|
| MAC forgery, Def. 134.2; signatures, Def. 136.2 | **Yes:** sample keys, simulate the randomized/stateful tag or signing oracle with a fresh log, return `(message,tag/signature)`, and test verification together with absence of that **message** among the signing-query inputs; public verification keys can be passed as ordinary adversary input. |
| Collision resistance, Def. 140.1 | **Yes:** sample the public function index, run the adversary returning two domain elements, and accept iff they differ and hash equally; compression and efficient evaluation are separate scheme hypotheses, not consequences of this game. |
| IND-CPA/CCA1/CCA2, Def. 168.1 | **Yes:** two adversary phases can return and retain explicit state, share the key/oracle state, and switch oracle families; CCA2 must implement an actual `c'=c*` check returning an explicitly encoded rejection value, rather than merely log or penalize the query after answering it. |
| Non-malleability, Def. 172.6 | **Yes:** let the second adversary phase return a list of ciphertexts, replace each challenge-equal ciphertext by rejection, decrypt the rest, and run a separate distinguisher on the resulting plaintext/rejection list; `prob` accepts this output type without a global `Fintype (List T)`. |
| Honest-but-curious security, Def. 155.1 | **Not faithfully through the advertised execution/view recipe as it stands:** the generic monad can carry `(view_A,out_B)` and `(view_B,out_A)`, but the executor and initial-message logging must be corrected as in #1–#2 before these are the source's distributions. |
| Sequential composition of zero knowledge, Thm. 175.1 | **Only the bounded concrete interactions/hybrid algebra are directly expressible:** the full source claim additionally needs faithful views, auxiliary-input/history handling, preserved verifier state/coins across sessions, and expected-time simulators; #1–#4 prevent an unqualified affirmative answer. |

For Def. 155.1, comparing only separate marginals is insufficient: the **joint** view/opposite-output distribution must be preserved. For Thm. 175.1, `simulate_comp` is not itself a zero-knowledge composition theorem. One must retain the malicious verifier's session history and random tape rather than replace it by independent fresh verifier executions.

Other nearby definitions introduce no additional obstacle at the experiment level: finite secret sharing (Def. 152.1) can return shares and select a coalition's subtuple, and public-key IND (Def. 171.5) removes the encryption oracle. Def. 165.1 quantifies over general multiparty real/ideal executions: the supplied **two-party** `Party.exec` is not an implementation of that scheduler. The generic oracle syntax could host one, but none is supplied or established by this gate.

### Q10. VCVio citation and policy

**File-level attribution is substantially adequate; declaration-level compliance is incomplete.** I verified the pinned commit and source headers through GitHub. The old `dtumad/VCV-io` repository redirects to [`Verified-zkEVM/VCVio`](https://github.com/Verified-zkEVM/VCVio). The cited commit exists with date 2026-11-04; it is not an invented or floating reference. The pinned licence is Apache 2.0, and the pinned toolchain is Lean 4.35.0.

| Policy element | Check |
|---|---|
| Project and authors | “D. Tuma and the VCVio contributors” identifies the project and principal author adequately. Checked headers name Devon Tuma; `OracleComp`, `ProbComp/Basic`, and handler composition also name Quang Dao; logging additionally names Alexander Hicks. |
| Modules | The pinned `OracleComp/OracleSpec.lean`, `OracleComp.lean`, `OracleQuery.lean`, `SimSemantics/`, and `QueryTracking/LoggingOracle/` exist. The last two are directory-level references; exact files would be more useful for individual tags. |
| Commit/version | `9054989327a7185ff19ef9ff0f119cccea479501` exists, dated 2026-11-04. |
| Licence | The pinned `LICENSE` is Apache License 2.0. |
| Module and design-document tag | All seven audited module/facade files and both design documents carry `[VCVio]` with the specified attribution information. |
| Tagged adapted declarations | `OracleSpec`, `OracleComp`, `OracleSpec.add`, `unifSpec`, `QueryImpl`, `simulate`, `QueryLog`, and `QueryImpl.withLog` have VCVio tags. |
| Untagged identifiable counterparts | At least `ProbComp`, `sampleFin`, `QueryImpl.comp`, and `simulate_comp` need tags; their upstream counterparts are `ProbComp`, `ProbComp.uniformFin`, `QueryImpl.compose`, and `simulateQ_compose`. Routine glue can use the policy's exception, but these are central advertised constructions/results. |
| Design versus transcription | The local specification separates oracle names and query arguments, whereas the pinned upstream specification indexes response types by complete query inputs. This is an adaptation, not an assertion of identical types. Preserving upstream copyright headers is required for copied code; the bundle declares no code transcription, and this audit does not establish that any code was copied. |

The citation record's sentence about “VCVio Contributors” in file headers should be corrected. No blueprint entries were supplied, so blueprint-wide compliance is unverified. Specific verified primary-source links appear at the end.

## Per-definition mathematical restatements

These describe the actual objects defined, rather than algorithms or efficiency guarantees that might later be attached to them. “Matches” concerns the local mathematical prose, subject to the numbered qualifications.

### `OracleComp.lean` — 8 definitions/types

| Declaration | Restatement | Comparison with prose |
|---|---|---|
| `OracleSpec` | For each oracle index `i`, choose a query type `dom i` and an answer type `rng i`. There are no finiteness, inhabitedness, computability, or probability assumptions. | Matches. Its fields `OracleSpec.dom` and `OracleSpec.rng` are exactly those two type families. |
| `OracleComp` | A well-founded tree whose leaves contain outputs and whose query nodes contain an oracle index, a query argument, and one continuation per possible answer. | The constructor docstring matches; the module's unrestricted “finite tree” claim does not (#6). |
| `OracleComp.bind` | Replace each return leaf of the first computation by the continuation selected by that leaf's value, preserving every prior query and branch. | Matches. |
| `OracleComp.call` | Issue exactly one query and immediately return its answer. | Matches. |
| `OracleSpec.add` | Take the disjoint sum of the index types and select the corresponding component's query/answer types. | Matches; equal-looking oracle names in different components remain distinct. |
| `OracleComp.liftLeft` | Recursively relabel every query index `i` as `Sum.inl i`, retaining its argument, branches, and output. | Matches. |
| `OracleComp.liftRight` | Recursively relabel every query index `j` as `Sum.inr j`, retaining its argument, branches, and output. | Matches. |
| `OracleComp.CostBoundedBy` | A return fits every natural budget. A query fits budget `q` iff its own charge is at most `q` and every continuation fits `q` minus that charge. | Matches the worst-case cumulative query-charge interpretation; does not measure evaluation of pure functions. |

`OracleComp.pure` constructs an output leaf; `OracleComp.query` constructs the indexed query/continuation node. Their individual constructor docstrings match. The anonymous `Monad` instance uses those `pure`/`bind` operations; `instLawfulMonad` packages the stated identity and associativity laws. Both instances have the intended interpretation.

### `Probability.lean` — 7 definitions/abbreviations

| Declaration | Restatement | Comparison with prose |
|---|---|---|
| `unifSpec` | Oracle names are natural numbers; every argument type is `Unit`, and oracle `m` has answer type `Fin (m+1)`. | Matches as a sampling interface. Uniformity is imposed by `expect`, not by this bare type specification alone. |
| `ProbComp` | Specialize `OracleComp` to `unifSpec`. These are finite, terminating trees of finite-range sampling choices. | Matches; no general probabilistic looping or nontermination construct. |
| `ProbComp.sampleFin` | Make one call to sampling oracle `m`, returning its `Fin (m+1)` answer. | Uniform under the specified semantics; matches. |
| `ProbComp.sample` | Sample an index from `Fin (\|T\|-1+1)`, cast it to `Fin \|T\|`, and apply the inverse of the chosen enumeration of `T`. | Matches for nonempty finite `T`; enumeration choices cannot bias a bijective uniform sample. |
| `ProbComp.expect` | Evaluate a leaf as `g a`; at a query take the arithmetic mean of the continuation expectations. | Matches exactly. Expectations may be arbitrary real numbers because `g` may be real-valued, even though event probabilities are rational. |
| `ProbComp.prob` | Take expectation of the indicator of the event predicate, using classical decidability. | Matches; arbitrary predicates are permitted mathematically, with no efficient-decision claim. |
| `ProbComp.dist` | On a finite output type, assign to each value its probability of being returned, with proofs of nonnegativity and total mass one. | Matches `FinDist`. This does not assert that every real-valued `FinDist` can be generated by a finite uniform-sampling computation. |

### `Simulate.lean` — 8 definitions/abbreviations

| Declaration | Restatement | Comparison with prose |
|---|---|---|
| `QueryImpl` | A dependent function taking an oracle index, an allowed query, and a state, and returning a target-oracle computation of an answer paired with a new state. | Matches. |
| `simulate` | At a leaf return the leaf value and current state; at a query run its implementation, then recursively interpret the answer-selected continuation from the returned state. | Matches. |
| `QueryImpl.ofComp` | Turn a state-independent answer computation into a stateful handler which returns the original state unchanged. | Matches; “stateless” means state-preserving, not necessarily deterministic. |
| `QueryImpl.passthrough` | Forward a query to the same oracle and preserve the state. | Matches. |
| `QueryImpl.sum` | Dispatch left indices to the first handler and right indices to the second, both operating on the same state type and state value. | Matches; these are shared-state components, not implicitly independent state stores. |
| `QueryImpl.comp` | Run the first handler using its component state, interpret its target queries through the second handler using the other component state, and return the answer with both updated states. | Matches; order is `impl₂.comp impl₁`. Missing attribution tag is #7. |
| `QueryLog` | A list of dependent triples consisting of an index, one of its queries, and one of its answers. | It is a type of potential logs, not a proof that a particular list arose in an execution; the ordering/authenticity comes from the producer. This is a benign reading of the prose. |
| `QueryImpl.withLog` | Apply the original handler to the underlying state and, after it returns, append its source query and answer to the log, preserving the new underlying state. | Matches chronological source-interface logging. |

### `Advantage.lean` — 4 definitions

| Declaration | Restatement | Comparison with prose |
|---|---|---|
| `accept` | The probability that a Boolean computation returns `true`. | Matches. |
| `advantage` | The absolute difference of the acceptance probabilities of two Boolean computations. | Matches the precise declaration docstring; the introductory bullet's “difference” should be read as absolute difference. This is not a supremum over distinguishers. |
| `guessGame` | Draw a uniform Boolean `b`, run the supplied game `G b`, and return whether its Boolean answer equals `b`. | Matches; `G` is the whole experiment parameterized by the hidden bit, not a claim that the adversary is given that bit. |
| `guessAdv` | The absolute difference between the guessing game's acceptance probability and 1/2. | Matches, with range `[0,1/2]`. |

### `Hopping.lean` — 1 definition

| Declaration | Restatement | Comparison with prose |
|---|---|---|
| `OracleComp.AllOutputs` | A predicate holds at every return leaf reachable by any sequence of answers allowed by the specification: check the predicate at a return and universally quantify over the next answer at a query. | Matches syntactic possibility. For arbitrary oracle specifications this may include answers inconsistent with a particular stateful implementation; for `ProbComp`, every reachable leaf has positive probability. |

### `Protocols.lean` — 5 definitions/abbreviations

| Declaration | Restatement | Comparison with prose |
|---|---|---|
| `exchangeSpec` | One oracle accepts an outgoing value and returns either an incoming value or `none`. | Matches as an interface. The bare type does not enforce any meaning for `none`; its source interpretation is disputed in #1. |
| `Party` | An oracle tree with exchange queries and finite uniform-sampling queries, returning an output value. | Matches this coroutine syntax; it is not by itself a representation theorem for arbitrary source ITMs. |
| `Party.step` | Preserve and execute sampling nodes until reaching either a return or the next exchange node; in the latter case expose the outgoing message and its pending continuation without answering it. | Matches. |
| `Party.finish` | Recursively answer every exchange with `none`, discarding its outgoing message, while preserving sampling, until an output is returned. | Matches its local docstring; it is precisely the source-incompatible drain used by `exec` (#1). |
| `Party.exec` | At zero fuel return failure immediately. Otherwise run the active party to a return/exchange; a return drains the waiting party, while an exchange activates the waiting party on that message, consumes one fuel unit, swaps roles, and finally swaps outputs back. | The equations are unambiguous; the claims of source fidelity and message-count semantics require #1 and #5. |

## Per-theorem statement/docstring checks

Each row assesses one named theorem. The total is **16 + 22 + 7 + 10 + 11 + 2 = 68**. “Matches” is a statement-fidelity judgment, not approval of all surrounding design claims.

### `OracleComp.lean` — 16 theorems

| Theorem | Assessment |
|---|---|
| `OracleComp.bind_eq_bind` | Matches: monadic `>>=` is the explicitly defined structural `bind`. |
| `OracleComp.pure_eq_pure` | Matches: overloaded `pure` is the return constructor. |
| `OracleComp.map_eq_bind` | Matches: mapping is sequencing with a return of the mapped value. |
| `OracleComp.pure_bind` | Matches: binding a return immediately applies its continuation. |
| `OracleComp.query_bind` | Matches: binding a query binds each answer-selected continuation. |
| `OracleComp.bind_pure` | Matches the right identity law. |
| `OracleComp.bind_assoc` | Matches associativity with the expected continuation nesting. |
| `OracleComp.call_bind` | Matches: one primitive call followed by `f` is the query node with continuation `f`. |
| `OracleComp.liftLeft_bind` | Matches: left relabelling preserves sequencing. |
| `OracleComp.liftRight_bind` | Matches: right relabelling preserves sequencing. |
| `OracleComp.costBoundedBy_pure` | Matches: a return fits every natural budget, including zero. |
| `OracleComp.costBoundedBy_query` | Matches the exact equivalence between a query's bound and the own-cost/continuation obligations. |
| `OracleComp.CostBoundedBy.mono` | Matches: increasing the budget preserves the bound. |
| `OracleComp.CostBoundedBy.bind` | Matches: a uniform bound on all continuations adds to the first computation's bound; the stated subtraction identity in the sketch uses the available `cost i ≤ q₁`. |
| `OracleComp.costBoundedBy_liftLeft` | Matches: the source cost is the restriction of the union cost to left indices. |
| `OracleComp.costBoundedBy_liftRight` | Matches: the source cost is the restriction of the union cost to right indices. |

### `Probability.lean` — 22 theorems

| Theorem | Assessment |
|---|---|
| `ProbComp.expect_pure` | Matches: a deterministic output evaluates `g` at that output. |
| `ProbComp.expect_query` | Matches: one sampling node is the uniform average over exactly `m+1` answers. |
| `ProbComp.expect_bind` | Matches total expectation, including adaptive continuations; the induction sketch is valid. |
| `ProbComp.expect_map` | Matches pushforward of the observable by function composition. |
| `ProbComp.expect_sampleFin` | Matches the uniform average on `Fin (m+1)`, including `m=0`. |
| `ProbComp.expect_sample` | Matches the uniform average on every nonempty finite type; the bijective-reindexing sketch justifies independence from the enumeration. |
| `ProbComp.expect_add` | Matches additivity for arbitrary real-valued observables. |
| `ProbComp.expect_const_mul` | Matches scalar linearity for every real scalar, not only nonnegative ones. |
| `ProbComp.expect_const` | Matches normalization: a constant observable has that constant expectation. |
| `ProbComp.expect_sum` | Matches exchange of expectation with a finite indexed sum; the index type itself need not be finite. |
| `ProbComp.expect_mono` | Matches monotonicity under a pointwise inequality on the whole output type. |
| `ProbComp.expect_nonneg` | Matches nonnegativity under pointwise nonnegativity. |
| `ProbComp.prob_eq_expect` | Matches the indicator expression for any supplied decidability instance. |
| `ProbComp.prob_pure` | Matches the zero/one probability of a deterministic output's satisfying the predicate. |
| `ProbComp.prob_bind` | Matches total probability, expressed as expectation of the continuation probabilities. |
| `ProbComp.prob_nonneg` | Matches the lower probability bound. |
| `ProbComp.prob_le_one` | Matches the upper probability bound. |
| `ProbComp.prob_mono` | Matches the prose: if `p` implies `q`, the implied event `q` has at least the probability of `p`. |
| `ProbComp.prob_congr` | Matches equality under pointwise equivalence of the event predicates. |
| `ProbComp.prob_or_le` | Matches the two-event union bound; disjointness and independence are not required. |
| `ProbComp.prob_not` | Matches the complement identity, relying correctly on total mass one. |
| `ProbComp.dist_apply` | Matches the atomic-output probability of the associated `FinDist`. |

### `Simulate.lean` — 7 theorems

| Theorem | Assessment |
|---|---|
| `simulate_pure` | Matches: a return leaves the state unchanged. |
| `simulate_query` | Matches: run the handler, then the answer-selected continuation with its updated state. |
| `simulate_bind` | Matches stateful sequencing, explicitly passing the first phase's state into the second; the sketch correctly uses associativity. |
| `simulate_call` | Matches: simulating a single return-answer query is exactly the handler computation. |
| `simulate_comp` | Matches nested simulation up to the stated reassociation of product states; this is a semantic identity, not an efficiency theorem. |
| `simulate_withLog` | Matches conservation of the full output/state computation after discarding the log, for every initial log. |
| `simulate_costBoundedBy` | Matches the general per-oracle target-cost bound, including zero charges; no multiplication factor is missing because it is already encoded in `b`. |

### `Advantage.lean` — 10 theorems

| Theorem | Assessment |
|---|---|
| `accept_nonneg` | The statement proves only nonnegativity, whereas its docstring claims both bounds; correct the docstring (#9). |
| `accept_le_one` | Matches the missing upper bound. |
| `advantage_nonneg` | Matches nonnegativity of the absolute difference. |
| `advantage_comm` | Matches symmetry in the two experiments. |
| `advantage_self` | Matches zero advantage against the identical experiment. |
| `advantage_le_one` | Matches the maximum possible gap between two acceptance probabilities. |
| `advantage_triangle` | Matches the single-hop triangle inequality. |
| `advantage_hybrid` | Matches the sum of `n` adjacent gaps, including zero hops; it is the telescoping form, not the existential adjacent-gap formulation of the misnumbered PS10 citation (#8). |
| `accept_guessGame` | Matches the average of correctness under bit one and bit zero, with the latter expressed by a complement. |
| `guessAdv_eq_half_advantage` | Matches the factor of two for absolute guessing bias; Q7 gives the algebra. |

### `Hopping.lean` — 11 theorems

| Theorem | Assessment |
|---|---|
| `OracleComp.AllOutputs.mono` | Matches weakening the property required of every possible output. |
| `OracleComp.AllOutputs.bind` | Matches propagation through sequencing, requiring the continuation property only at outputs satisfying the intermediate predicate. |
| `ProbComp.prob_split` | Matches the disjoint partition of an event by `F` and its complement. |
| `ProbComp.expect_mono_of_allOutputs` | Correct support-restricted monotonicity; the opening prose should state the inequality, not just support dependence (#9). |
| `ProbComp.prob_eq_one_of_allOutputs` | Matches certainty of a predicate holding at every possible leaf. |
| `ProbComp.prob_eq_zero_of_allOutputs` | Matches probability zero when the predicate fails at every possible leaf. |
| `ProbComp.abs_prob_sub_le_of_agree` | Matches the difference lemma on a shared experiment: the two events may differ only where `F` holds; its pointwise-indicator sketch is sufficient. |
| `ProbComp.prob_mem_le` | Matches a fresh, fixed-range uniform draw after the bounded list; it does not assert the same bound for a list depending on that draw. |
| `simulate_allOutputs_bad` | Matches propagation of a sticky predicate from an initially bad state through every simulated call. |
| `prob_eq_until_bad` | Matches both advertised equalities under whole-handler agreement and stickiness; the induction sketch correctly separates good and bad successor states. Its applicability restriction is #3. |
| `identical_until_bad` | Matches the explicit hypotheses and the bound by the first simulation's final-bad probability. Its description as the full code-based fundamental lemma requires a restriction/deviation note (#3). |

### `Protocols.lean` — 2 theorems

| Theorem | Assessment |
|---|---|
| `Party.exec_zero` | Matches immediate truncation at zero fuel, even when both parties could return without sending. |
| `Party.exec_succ` | Matches the recursive equation, including the drain-on-return behavior; that equation does not establish PS10 fidelity (#1). |

The mathematical sketches for the nontrivial probability, simulation, hybrid, and bad-event lemmas are consistent with their actual statements. In particular, the bad-event sketches do not surreptitiously prove the stronger transition-sensitive theorem: they explicitly rely on whole-handler equality. The facade contains no additional mathematical declarations; it imports the six modules and lists their intended contents. Its broad source-coverage description inherits #1–#4.

## Adversarial instantiations and explicit calculations

The following include attempted counterexamples that fail for good reasons, and counterexamples to advertised interpretations. None is presented as a counterexample to a Lean theorem with all its stated hypotheses satisfied. In the protocol examples, `send(m,k)` abbreviates the exchange query with outgoing message `m` and continuation `k`; `return` means `OracleComp.pure`.

### A1. Repeating the same sampler versus reusing its result — passes

Run `sample Bool` twice, returning the pair `(x,y)`. Total probability gives, for each fixed pair of bits `(a,b)`,

\[
\Pr[(x,y)=(a,b)]
=\sum_{x\in\{0,1\}}\tfrac12\sum_{y\in\{0,1\}}\tfrac12
  \mathbf1_{(x,y)=(a,b)}
=\tfrac14.
\]

Hence `Pr[x=y]=1/4+1/4=1/2`. In contrast, sample once and return `(x,x)`; equality has probability one. The semantics correctly distinguishes fresh execution from reuse, even if the two fresh draws use the same Lean expression. `sampleFin 0` returns its sole answer with probability one.

### A2. A state-sensitive handler with an existing log — passes

Let there be one oracle `i`, with natural-number query and answer, and handler

\[
\mathrm{impl}(i,x,s)=\mathrm{return}(s,s+x).
\]

Start at state 5, ask argument 2, then ask argument 3, and return both answers. The defining equations give

\[
(x,s)=(2,5)\mapsto(5,7),\qquad
(x,s)=(3,7)\mapsto(7,10).
\]

Thus the output is `(5,7)` and the final state is 10. Starting from any log `L`, the final log is

\[
L\mathbin{++}[(i,2,5),(i,3,7)].
\]

It is chronological; the second call sees the updated state; dropping the log leaves exactly the same output/state.

### A3. Composition with two changing states — passes

Let the inner handler, from state `s₁`, ask target oracle `j` on the same argument `x`, then return its answer with state `s₁+1`. Let the outer handler, from `s₂`, answer `x+s₂` and update to `s₂+10`. Run the two source queries 2 and 3 from `(s₁,s₂)=(3,10)`:

\[
\begin{aligned}
\text{first answer}&=2+10=12,&(s_1',s_2')&=(4,20),\\
\text{second answer}&=3+20=23,&(s_1'',s_2'')&=(5,30).
\end{aligned}
\]

Nested simulation returns `(((12,23),5),30)`. Composed simulation returns `((12,23),(5,30))`, and the theorem's final reassociation produces the former. The exact finite-model check confirmed these values.

### A4. Zero and one-message protocols — fuel discrepancy

Take

\[
A=\mathrm{send}(m,\lambda\_\, .\mathrm{return}\ a),\qquad
B=\lambda\_\, .\mathrm{return}\ b.
\]

Unfolding `step` and then `exec` gives

\[
\begin{aligned}
\mathrm{exec}\ 1\ A\ B
  &=\mathrm{map}\ \mathrm{swap}\bigl(\mathrm{exec}\ 0\ (\mathrm{return}\ b)
                                  (\lambda\_\, .\mathrm{return}\ a)\bigr)\\
  &=\mathrm{return}\ \mathrm{none},\\
\mathrm{exec}\ 2\ A\ B
  &=\mathrm{return}\bigl(\mathrm{some}(a,b)\bigr).
\end{aligned}
\]

Here the map swaps a successful pair inside `Option`, leaving `none` unchanged. Also

\[
\mathrm{exec}\ 0\ (\mathrm{return}\ a)\ B=\mathrm{return}\ \mathrm{none},\qquad
\mathrm{exec}\ 1\ (\mathrm{return}\ a)\ B=\mathrm{return}\bigl(\mathrm{some}(a,b)\bigr).
\]

The budget is not an inclusive bound on the number of messages needed to finish. This is #5, independently of source fidelity.

### A5. Arbitrary behavior after the other party halts — source mismatch

Fix an arbitrary natural number `N`. Let `K₀ = return N` and recursively

\[
K_{j+1}=\mathrm{send}(j,\lambda\_\, .K_j).
\]

Induction on `j` using the definition of `finish` gives `finish Kⱼ = return N`. Therefore

\[
\mathrm{exec}\ 1\ (\mathrm{return}\ a)\ (\lambda\_\, .K_N)
=\mathrm{return}\bigl(\mathrm{some}(a,N)\bigr).
\]

All `N` attempted sends are silently answered with `none`, and the second party's computation reaches its chosen output. The first party has already returned before any of this occurs. PS10's active-party-halt rule instead ends the execution at that first return; it does not activate the waiting machine to do these actions. The exact check used `N=100`. Fresh sampling placed inside `K_N` would likewise execute after the first party's halt. This establishes #1, not merely a naming concern about fuel.

### A6. A secret-bearing first message disappears from the proposed receiver log

Let Alice's private input be a bit `x`; let her party send `x` and eventually return 0. Let `B` receive its initial argument and immediately return 0 without issuing any oracle query. The proposed log of `B`'s **own** oracle calls is `[]` for both `x=0` and `x=1`. Its input and coins can also be fixed identically.

However, the actual received-message sequence of `B` is `[x]`. Thus, with `D` reading that received bit,

\[
\Pr[D(\mathrm{view}_B\mid x=0)=1]=0,\qquad
\Pr[D(\mathrm{view}_B\mid x=1)=1]=1.
\]

For the constant function `f(x,y)=0`, a simulator given only `(y,0)` cannot depend on `x`. If its acceptance probability is `p`, the two gaps are `|p|` and `|1-p|`, and

\[
|p|+|1-p|=1,\qquad \max(|p|,|1-p|)\ge\tfrac12.
\]

The true view therefore leaks Alice's input, while the empty-log substitute and constant outputs are trivially simulatable. This is a counterexample to the **announced view recipe**, not an existing implemented `View` definition. Recording the initial message fixes this specific loss; it must not be inferred from `simulate_withLog`.

### A7. First divergence occurs inside the call setting bad — current premise fails

Use one unit-query, Boolean-answer oracle and Boolean state, initially `false`; define `bad s` as `s=true`. From a good state, draw a fresh uniform bit `b` and set

\[
\begin{aligned}
\mathrm{impl}_0((),\mathrm{false}) &: \mathrm{return}(\mathrm{false},b),\\
\mathrm{impl}_1((),\mathrm{false}) &: \mathrm{return}(b,b).
\end{aligned}
\]

From a bad state, let both handlers retain state `true` (their answers can be arbitrary). Under the shared fresh bit, the good successor branch `b=false` is identical, and the first possible divergence is exactly the branch `b=true` which sets bad. Both flags are sticky. For an adversary making one call and returning the answer,

\[
\Pr_0[\mathrm{answer}=\mathrm{true}]=0,\qquad
\Pr_1[\mathrm{answer}=\mathrm{true}]=\tfrac12,\qquad
\Pr_0[\mathrm{bad}]=\Pr_1[\mathrm{bad}]=\tfrac12.
\]

This is the standard bad-event bound with equality. Nevertheless, `hagree` is false at the initial good state: the two whole computations even have different answer distributions. Moving `bad := true` before the divergent return **inside the handler** does not change that fact. A boundary-sensitive lemma or an additional factoring construction is needed.

There is a separate weaker-premise issue: `return (false,s)` and `sampleFin 0 >>= fun _ => return (false,s)` have the same law but cannot be equal computations, since one has a return constructor at its root and the other a query constructor. This does not refute the theorem; it shows why equality-in-law or coupling interfaces would be more reusable.

### A8. Dropping stickiness makes the final-state bound false

Use states `0,1,2`, initially 0, and `bad(s) ↔ s=1`. Provide two query kinds. The first kind, `raise`, is implemented identically in both games and returns `(false,1)`. At state 1, the second kind, `differ`, returns `(false,2)` in game 0 and `(true,2)` in game 1. At every good state, define the two implementations identically.

The adversary asks `raise`, then `differ`, and outputs the second answer. Thus whole-handler agreement on good entry states holds, but

\[
\left|\Pr_0[\mathrm{true}]-\Pr_1[\mathrm{true}]\right|=1,
\qquad \Pr_0[\text{final bad}]=0.
\]

Both executions visited bad and then cleared it. This proves why the existing theorem needs stickiness, or a replacement “ever bad” observable. The finite-model check confirmed the two values.

### A9. Duplicate lists and dependent lists — collision statement survives

For `T=Fin 3` and the fixed list `[0,0]`, a fresh sample belongs to the list with probability

\[
\tfrac13+0+0=\tfrac13\le\tfrac23=\frac{\mathrm{length}([0,0])}{3}.
\]

The list is counted with multiplicity in the bound, but membership is not. For the different program “draw `t`, then return `([t],t)`”, membership has probability one, exceeding `1/3`; this **does not instantiate the theorem**, which samples `t` after producing the list and does not let the earlier list depend on it. The independence restriction is substantive and correctly encoded.

### A10. Expected-time retrying is not a finite `ProbComp`

First, structural induction establishes two facts for every `c : ProbComp α`:

\[
\begin{aligned}
\operatorname{supp}(\mathrm{return}\ a)&=\{a\},\\
\operatorname{supp}(\mathrm{query}\ m\ ()\ k)
 &=\bigcup_{j:\mathrm{Fin}(m+1)}\operatorname{supp}(k(j)).
\end{aligned}
\]

The union is finite, since there are finitely many children and each child's support is finite by induction. Similarly, define the maximum draw depth by

\[
h(\mathrm{return}\ a)=0,\qquad
h(\mathrm{query}\ m\ ()\ k)=1+\max_{j:\mathrm{Fin}(m+1)}h(k(j)).
\]

This is finite for every such tree. Now flip fair bits until the first `true`, returning the number `N` of preceding `false` bits. Then

\[
\Pr[N=j]=2^{-(j+1)}>0\quad(j\ge0),\qquad
\mathbb E[N+1]=\sum_{j\ge0}\Pr[N\ge j]=\sum_{j\ge0}2^{-j}=2.
\]

This expected-constant-time algorithm has infinite support and cannot be a `ProbComp ℕ`. Even if a particular simulator's **returned view** has finite support, its unbounded retrying execution and expected-time certification are not represented by the current syntax. Replacing it extensionally by a finite sampler is a further construction/efficiency obligation, not a consequence of the output type being finite. PS10 explicitly uses this expected-time distinction in Def. 121.2 and Thm. 175.1.

### A11. Generic oracle trees need not be finite

Let oracle `first` return a natural number, and let oracle `tick` have a singleton answer. Define `C₀ = return ()`, `Cⱼ₊₁ = call tick () >>= fun _ => Cⱼ`, and

\[
C=\mathrm{query}\ \mathrm{first}\ ()\ (\lambda n.C_n).
\]

This is permitted by `OracleComp`: every subtree `Cₙ` is already defined by natural-number recursion. The branch selecting `n` contains `n+1` queries, so no single natural bound works for every branch. The root also has infinitely many branches. There is no infinite execution path, but the tree is not finite. This does not contradict A10, since `first` is not an oracle of `unifSpec`.

### A12. Cost-zero calls and exact three-way sampling — boundary checks

If every query has charge zero, then every `OracleComp` is `CostBoundedBy` zero, by structural induction: `0≤0` and `0-0=0` at every query. This is intentional and does not prove fast execution. A target handler beginning with a charge-one query cannot satisfy the zero-cost premise, because it would require `1≤0`.

Separately, `sampleFin 2` assigns each of three outcomes probability `1/3`. Any bounded fair-bit machine using at most `k` bits can be padded to exactly `k` bits, so every event has probability `a/2^k` for an integer `a`. Equality with `1/3` would require `3a=2^k`, which is impossible. This justifies note #11 and identifies a concrete bridge obligation without disputing the uniform-sampling definition.

## Missing sanity results and closure obligations

These are proposed statements/obligations, not claims of completed Lean proofs.

1. **Sampling laws:** atomic uniform probability, invariance under a finite equivalence, independent-product sampling, and `dist (sample T) = FinDist.uniform T`. The calculations in A1 should be immediate corollaries.
2. **Basic probability/support laws:** `prob c True = 1`, `prob c False = 0`, a `prob_map` equation, finite support, and for `ProbComp`, `AllOutputs P c ↔ prob c P = 1` (all possible leaves have positive weight).
3. **Interpreter laws:** passthrough simulation equals the original computation paired with unchanged state; simulation commutes with mapping; left/right lifts are handled by the matching component of `QueryImpl.sum`; composition is associative up to explicit state reassociation.
4. **Log laws:** the initial log is a prefix; each wrapped call appends exactly one correctly typed input/answer entry; an all-source-query bound `q` bounds the number of new entries by `q`. A selected-oracle version should count only that component's entries.
5. **First-bad-transition lemma:** use a one-step joint sampling computation whose marginals are the two handlers, whose successor bad flags agree, and whose answer/state pairs agree whenever those flags are good; propagate it through simulation with stickiness and prove the standard constant-one bound. Alternatively use equality of the restricted off-bad successor laws. Both permit A7.
6. **Adaptive collision theorem:** derive a birthday/union bound by conditioning on the prior history and using the fresh-sample hypothesis at each step. Record which list/history is independent of which draw, especially for challenge nonces versus adversarial decryption queries.
7. **Source execution laws:** no activation or new randomness after the source stop event; correct role/output order; a trace records every delivered message, including the initial receive; terminal/abort status is not silently converted into a pair of completed outputs.
8. **Fuel laws:** exact zero/one-message examples; monotonicity of success probabilities and nonincrease of timeout probability; stabilization once a sufficient bound is reached; a proved relation to the source's round bound. State precisely whether discarded post-closure sends are charged or forbidden.
9. **View laws:** projecting a traced execution recovers the intended execution, each view has its initial input/auxiliary input and initial message, and the joint `(view_A,out_B)` and `(view_B,out_A)` laws agree with the source. The secret-first-message example A6 must fail a claimed privacy test.
10. **Expected-time and machine bridges:** explicitly separate source-faithful bounded real executions, expected-time simulators, and abstract finite uniform samplers. Prove the reduction-efficiency and ZK-composition statements in the appropriate model; a query bound or equality of output laws is not a substitute.
11. **Disclosed reuse bridges:** B1 should preserve evaluation, simulation, and bounds, not just syntax; B2 should preserve probabilities on nonempty finite seed types; the acceptance/advantage bridges should preserve constants. `uprob` on an empty seed type is not a normalized distribution and should not be silently included in B2.

For closing this API gate, #1 requires a source-semantics repair or an explicit source-preserving restriction/bridge. #2–#4 require corrected claims and concrete compatible designs, with the necessary source-facing results identified before downstream statements are frozen. Merely retaining the successful elaboration log does not address these issues. S2b work which is already openly deferred need not be retroactively claimed complete.

## Primary sources checked

The PS10 page/item references above are to the hash-verified supplied PDF. The code and policy references are to the hash-verified bundle, not a moving PR head.

- [VCVio pinned commit](https://github.com/Verified-zkEVM/VCVio/commit/9054989327a7185ff19ef9ff0f119cccea479501), [licence](https://github.com/Verified-zkEVM/VCVio/blob/9054989327a7185ff19ef9ff0f119cccea479501/LICENSE), and [toolchain](https://github.com/Verified-zkEVM/VCVio/blob/9054989327a7185ff19ef9ff0f119cccea479501/lean-toolchain).
- VCVio [oracle specifications](https://github.com/Verified-zkEVM/VCVio/blob/9054989327a7185ff19ef9ff0f119cccea479501/VCVio/OracleComp/OracleSpec.lean), [oracle computations](https://github.com/Verified-zkEVM/VCVio/blob/9054989327a7185ff19ef9ff0f119cccea479501/VCVio/OracleComp/OracleComp.lean), and [single-query functor](https://github.com/Verified-zkEVM/VCVio/blob/9054989327a7185ff19ef9ff0f119cccea479501/VCVio/OracleComp/OracleQuery.lean).
- VCVio [probabilistic computation constructors](https://github.com/Verified-zkEVM/VCVio/blob/9054989327a7185ff19ef9ff0f119cccea479501/VCVio/OracleComp/ProbComp/Basic.lean), [handler composition](https://github.com/Verified-zkEVM/VCVio/blob/9054989327a7185ff19ef9ff0f119cccea479501/VCVio/OracleComp/SimSemantics/QueryImpl/Compose.lean), and [logging](https://github.com/Verified-zkEVM/VCVio/blob/9054989327a7185ff19ef9ff0f119cccea479501/VCVio/OracleComp/QueryTracking/LoggingOracle/Core.lean).
- Shoup, [*Sequences of Games*](https://www.shoup.net/papers/games.pdf), revision dated 18 January 2006, §1.1, Lemma 1, for the difference lemma and its equal-off-bad/equal-bad-mass formulation. The ePrint series identifier is 2004/332; the revision should be specified when citing section numbers.
- Bellare–Rogaway, [author's publication record](https://web.cs.ucdavis.edu/~rogaway/papers/games.html) and [ePrint 2004/331](https://eprint.iacr.org/2004/331), Lemma 2, for the code-based fundamental lemma. The author record confirms the EUROCRYPT 2006 provenance; the first-bad-transition limitation in this audit is also established independently by A7.

## Notation glossary

| Notation | Meaning |
|---|---|
| `return a`, `send(m,k)` | Respectively `OracleComp.pure a` and a party's exchange query carrying `m` with continuation `k`. |
| $\Pr_c[P]$, $\mathbb E_c[g]$ | `ProbComp.prob c P` and `ProbComp.expect c g`; subscripts 0 and 1 identify the two explicitly specified games. |
| `\|T\|`, `set(L)`, `L ++ L'` | Cardinality of a finite type; distinct elements occurring in a list; list concatenation. |
| $\mathbf1_P$ | Indicator of proposition `P`, equal to one when it holds and zero otherwise. |
| `supp(c)`, `h(c)` | Possible return values of a computation; the maximum number of sampling queries on a branch, used in A10. |
| `p₀,p₁` in Q7; `p` in A6 | The two branch acceptance probabilities; the fixed simulator's acceptance probability. |
| `A,B,D`, `a,b,m,x,y,L,s,s₁,s₂` | Locally specified parties/distinguisher; outputs, messages, bits/inputs, list, and handler states, with roles stated in each example. |
| `impl₀,impl₁`, `bad` | The two local handler definitions and their stated bad-state predicate. |
| `N,j,Kⱼ` in A5; `N` in A10; `Cⱼ,C` in A11 | Number of discarded sends, recursion index, and drain-example parties; the geometric count of failures; the finite chains and infinitely branching oracle tree. |
| `q,r,k,b(i)` | A query budget; a handoff bound; a draw index/continuation or fair-bit budget as specified locally; the per-oracle charge in `simulate_costBoundedBy`. |



