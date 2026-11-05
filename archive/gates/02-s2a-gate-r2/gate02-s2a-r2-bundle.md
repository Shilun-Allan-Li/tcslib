## ===== briefs/pass-shelat-ch5-8/gates/02-s2a/pack-r2.md =====

# Gate 02 (Pass–shelat ch. 5–8, S2a), round 2: external API audit pack

**What is audited:** PR [Shilun-Allan-Li/tcslib#185](https://github.com/Shilun-Allan-Li/tcslib/pull/185)
into `cryptography/pass-shelat-ch2-4`, at its head `586510c1416afa21881b9a42b5a8d0578c9bd749`.
- **Round 1** audited `597eef43ccd3c8bfafe0c0c16a2444b12adc1644` and found **1 blocker, 3 majors,
  6 minors and 2 notes** (`gate02-s2a-findings.md`, in the bundle, verbatim).
- **The repairs:** two commits on #185's branch, after `597eef43`:
  - `14e5988633b949811f774a15583d4967397bf292`, the round 1 repairs;
  - `586510c1416afa21881b9a42b5a8d0578c9bd749`, completing finding 8's citation repair.

  Their full diff is `evidence-r2/repair.diff.txt`. Each finding's resolution is in
  `resolutions-r1.md`.
- **The deliverable:** **`gate02-s2a-r2-findings.md`**.

The bundle holds this pack, then every file named below under a `## ===== <path> =====` header.
**The source is attached separately:** [PS10] R. Pass, a. shelat, *A Course in Cryptography*,
3rd ed., January 2010 (PDF). Book page = PDF page − 12; item numbers carry the book page.

## Brief for the auditor

Round 2 does two things.
1. **It verifies the round 1 resolutions.** For each of the 12 findings and the review's 3 extra
   items (M1, M2, M4), say whether the resolution is adequate:
   - **fixed** — the defect is gone, and the fix introduces no new one;
   - **recorded** — the finding is accepted as a declared deviation or as scheduled work, and the
     record is accurate;
   - **not resolved** — say why.
2. **It audits the changed surface afresh,** as round 1 audited the whole: definitions,
   statements, docstrings and proof sketches. The proofs are machine-checked; do not review tactic
   scripts. Most of `Protocols.lean` is new (the execution was redesigned after finding 1), and
   the identical-until-bad lemmas of `Hopping.lean` have a new hypothesis (finding 3).

For **every new or changed definition**, restate it in your own mathematical English before
reading its docstring, and report any daylight. For **every new or changed theorem**, say in
1–3 sentences whether its statement is what the docstring claims. Attempt at least **three
adversarial instantiations** of the new execution, and at least two of the new hypothesis of
`identical_until_bad`. Look for regressions: anything round 1 accepted that the repairs broke. Do
not give a blanket approval.

## Scope

| Item | Where |
|---|---|
| Under audit (new or changed declarations; the rest for regressions) | `TCSlib/Cryptography/Games/{OracleComp,Probability,Simulate,Advantage,Hopping,Protocols}.lean`, `TCSlib/Cryptography/Games.lean` |
| Round 1 record | `gate02-s2a-findings.md` (round 1's findings), `resolutions-r1.md`, `pack-errata.md` (E1–E3), `pack.md` (round 1's pack and questions) |
| Design documents (context; they state the intent) | `briefs/pass-shelat-ch5-8/design/S2-game-framework.md`, `briefs/pass-shelat-ch5-8/design/CITATION-VCVio.md` |
| Campaign inventory (pack erratum E1) | `briefs/pass-shelat-ch5-8/inventory-ch5-8.md`; the rows of the source items asked about are Def-134.2, Def-136.2, Def-140.1, Def-155.1, Def-168.1, Thm-168.2, Def-172.6 and Thm-175.1 |
| Context, not under audit | `TCSlib/InformationTheory/FinDist.lean` (on `main`); the ch. 2–4 layer: `Foundations/Probability.lean` (now imported by `Games/Advantage.lean`, pack erratum E2), `Foundations/Experiments.lean`, `Pseudorandom/Functions/OracleAdversary.lean`, and `ZeroKnowledge/Interaction.lean` (its foundation decision D8, which the new execution follows) |
| Source | [PS10] §4.4 (book pp. 114–116); ch. 5–7 definitions (book pp. 133–175) |
| Standards | `policy.md` |
| Out of scope | tactic proofs; the S2b layer (bridges to the ch. 2–4 layer, the machine model), not in this PR |

## Attestations (maintainer execution claims; evidence under `evidence-r2/` in the bundle)

1. **Elaboration.** `scripts/lean_check_tree.sh`, one module at a time into a fresh olean tree,
   over the 9 modules of the closure (`InformationTheory/FinDist`,
   `Cryptography/Foundations/Probability`, the six modules, the facade): 9/9 pass, 0 errors,
   0 warnings, 0 `sorry` (`replay-head.log`, `replay-order.txt`).
2. **Axioms.** `#print axioms` for all 75 theorems: only `propext`, `Classical.choice` and
   `Quot.sound` (`axioms.log`).
3. **Lint.** `scripts/style_lint.py` and `scripts/campaign_style_lint.py`: 0 findings on the 7
   files; no line over 100 characters (`style-lint.log`).
4. **Imports.** `Mathlib.Data.Nat.Notation`, `TCSlib.InformationTheory.FinDist`,
   `TCSlib.Cryptography.Foundations.Probability` (finding 10's reuse; it imports only Mathlib),
   and the framework's own modules.
5. **Names** (`name-screen.log`). No new clash. The new public names are listed in the log;
   `Party.finish` is removed.
6. **Generalizations of existing code,** unchanged from round 1, attestation 6, with one addition:
   the hybrid argument now reuses the concrete layer's lemmas (finding 10).

## Changes since round 1 (declared; verify them)

- **Execution (findings 1, 2 and 5; ruling 2026-11-05).**
  - `ExecOutcome`: both outputs (`done`), the message budget ran out (`outOfFuel`), or a party sent
    after its counterpart returned (`sentAfterEnd`).
  - When the active party returns, the waiting party's pending send is answered `none`. It may then
    draw coins and must return without sending (`Party.close`, `Party.endWith`). This is D8's
    reading of [PS10, §4.4], with one declared difference: a party may return early.
  - `fuel` is the message budget, and a return costs no fuel.
  - **Views:** `Party.execT` records, for each party, the messages delivered to it and its coins
    (`Party.Obs`). `execT_outcome` proves that its outcome is `exec`'s. Inputs and auxiliary
    inputs are the parties' Lean parameters.
- **Identical until bad (finding 3).**
  - `prob_eq_until_bad` and `identical_until_bad` take a semantic hypothesis: from a good state,
    the two implementations give the same law to good successors (equal expectations of every
    function that vanishes on bad states). Stickiness is still required.
  - `hagree_of_eq` derives this hypothesis from equality on good states.
  - `identical_until_bad_init` starts from a sampled initial state that is good with probability 1.
  - A deviation note against [BR06].
- **Hybrid argument (finding 10, ruled):** `advantage_hybrid` and the new
  `exists_advantage_hybrid_gap` are one-line instances of the concrete layer's
  `abs_sub_le_sum_hybrids` and `exists_hybrid_gap`.
- **Docstrings and citations** (findings 6–9, M1, M2): see `resolutions-r1.md`. The [Sho04] and
  [BR06] section and lemma numbers are dropped, since the revisions could not be inspected from the
  maintainer's session.
- **Recorded, no code change:** finding 4 (Thm 175.1 with strict or truncated simulators, ruled),
  finding 11 (non-dyadic sampling and fair bits) and finding 12 (bridges and efficiency, S2b).

## Specific questions

1. **Resolutions.** Is each round 1 finding fixed or accurately recorded (see the brief)?
2. **The execution.**
   - Does `Party.exec` implement the alternating execution of [PS10, §4.4] under D8's reading,
     with early returns as the only difference? Compare it with `TCSlib.Cryptography.exec` and
     `Protocol` in `ZeroKnowledge/Interaction.lean`.
   - Can a party's misbehaviour (sending after the end, running past the budget) be hidden by
     the outcome?
   - Is the fuel accounting right at the boundaries: `fuel = 0`, an immediate return, and the
     last allowed message?
3. **Views.** Is a party's view in [PS10, §4.4] (its input, auxiliary input, coins and received
   messages) recoverable from `Party.Obs` and the party's parameters? Is the order of received
   messages and coins right, including the coins drawn by `close`? Is `execT_outcome` the right
   consistency statement, or is a sanity theorem missing (for example, about the length of the
   received lists)?
4. **The new hypothesis of identical until bad.**
   - Is it implied by the round 1 syntactic hypothesis (`hagree_of_eq`)?
   - Is it met by the bad-event hops it is meant for: the repeated-nonce hop in Thm 168.2, and
     CCA2's decryption oracle answering the challenge?
   - Is the conclusion still the standard one?
   - Does `identical_until_bad_init` cover a sampled key?
5. **Hybrid reuse.** Do `advantage_hybrid` and `exists_advantage_hybrid_gap` state what their
   docstrings claim, and is [PS10, Lemma 71.6] the right tag?
6. **Expressiveness, re-checked.** With the new execution and views, can Def 155.1 (both views,
   jointly with the other party's output) and the sequential composition of Thm 175.1 (under the
   ruled deviation) be expressed? Report any that cannot as findings.

## Findings format (auditor fills)

Two tables.

**Table 1, resolutions:**

| Round 1 # | Verdict (fixed / recorded / not resolved) | Evidence |
|---|---|---|

**Table 2, new findings:**

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | blocker / major / minor / note | | | | |

Severity guide:
- **blocker:** a downstream phase would build on a wrong definition or statement;
- **major:** fixable but materially misleading as it stands, or debt that needs explicit human
  acknowledgment;
- **minor:** an edge case, or a naming or attribution defect;
- **note:** an observation; no change required.

A round 1 finding judged "not resolved" counts at its round 1 severity. The gate closes at
**0 blockers and 0 majors**.

## ===== briefs/pass-shelat-ch5-8/gates/02-s2a/gate02-s2a-findings.md =====

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




## ===== briefs/pass-shelat-ch5-8/gates/02-s2a/resolutions-r1.md =====

# Gate 02 (S2a, #185): round 1 resolutions

- **Round 1:** findings `gate02-s2a-findings.md`, verbatim, SHA-256
  `fed1bc4afbc4d829aa71c4dcc455ef514709836dfd7f686a45fbdd4138113709`; head
  `597eef43ccd3c8bfafe0c0c16a2444b12adc1644`. Counts: **1 blocker, 3 majors, 6 minors, 2 notes.**
  The gate does not close.
- **Review:** `review/subagent-review.md` found 11 true and 1 partly true (#1), none false, and no
  severity change. Its exact-rational model of the counterexamples is
  `review/scripts/model.py.txt`.
- **Rulings (user, 2026-11-05):** #1 D8's execution semantics, with early returns; #4 strict or
  truncated simulators (a declared deviation); #10 reuse of the concrete layer's hybrid lemmas.
- **Repairs:** two commits on #185's branch, after `597eef43`:
  - `14e5988633b949811f774a15583d4967397bf292`, the round 1 repairs;
  - `586510c1416afa21881b9a42b5a8d0578c9bd749`, completing #8. The maintainer's check of each
    "Fixed" row against the code found the [Sho04] and [BR06] numbers still in `Hopping.lean`'s
    reference block.

  Round 2 audits the head `586510c1416afa21881b9a42b5a8d0578c9bd749`.
- **Verified at `586510c1`** (`evidence-r2/`):
  - a clean replay of the 9-module closure: 9/9 pass, 0 errors, 0 warnings;
  - `#print axioms` for all 75 theorems: only `propext`, `Classical.choice` and `Quot.sound`;
  - both style lints: 0 findings; no line over 100 characters;
  - the name screen: no new clash.

  The full repair diff is `evidence-r2/repair.diff.txt`.

| # | Severity | Resolution |
|---|---|---|
| 1 | blocker | **Fixed (API change).** `ExecOutcome` (`done` / `outOfFuel` / `sentAfterEnd`). `Party.close` replaces `finish`: the waiting party's pending send is answered `none`, it may draw coins, and a send is reported. `endWith`; `exec`, where a return costs no fuel. A deviation note (D8; early returns allowed). Three `rfl` sanity examples (fuel counts messages; a send after the end is reported). `finish` is removed. To be confirmed with Frederick under F-2. |
| 2 | major | **Fixed.** The views docstring is corrected. New `Party.Obs`, `stepT`, `closeT`, `endWithT` and `execT`, the traced execution recording each party's received messages (the second mover's first message first) and coins. `execT_outcome` proves it has `exec`'s outcome. |
| 3 | major | **Fixed (generalization).** `prob_eq_until_bad`/`identical_until_bad` take the semantic hypothesis (from a good state, the same law to good successors). `hagree_of_eq` recovers the syntactic form; `identical_until_bad_init` handles a sampled initial state (the review's missed item 3). A deviation note against [BR06]. |
| 4 | major | **Recorded (ruled).** Strict or truncated simulators for Thm 175.1, carrying D8 into ch. 7: `PerfectZKAbort` composes to statistical ZK with error `Q·2^-k`. Recorded in the plan's decision log and the S2 design note; the inventory row already carried the debt (pack erratum E1). No framework change. |
| 5 | minor | **Fixed** with #1: fuel is the message budget. |
| 6 | minor | **Fixed:** "a well-founded tree …; finite with finite answer types". |
| 7 | minor | **Fixed:** VCVio tags on `ProbComp`, `sampleFin`, `QueryImpl.comp` and `simulate_comp`; the reference block lists `ProbComp/Basic` and `QueryImpl/Compose`; `CITATION-VCVio.md` names the authors per module. |
| 8 | minor | **Fixed:** [PS10, Lemma 71.6]. [Sho04] and [BR06] section and lemma numbers are dropped (unverifiable from this session; completed in `586510c1`). |
| 9 | minor | **Fixed:** the `accept_nonneg` and `expect_mono_of_allOutputs` docstrings. |
| 10 | minor | **Fixed (ruled reuse):** `advantage_hybrid` is the concrete layer's `abs_sub_le_sum_hybrids`, and the new `exists_advantage_hybrid_gap` is its `exists_hybrid_gap` ([PS10, Lemma 71.6]). It imports `Foundations/Probability.lean`, which uses only Mathlib (pack erratum E2). |
| 11 | note | **Recorded:** exact non-dyadic sampling is not fair-bit-efficient. The machine bridge (S2b) restricts to dyadic sampling, or uses the concrete layer's truncated rejection sampler. |
| 12 | note | **Recorded:** the bridges and efficiency are S2b, scheduled. |
| M1 (review) | minor | **Fixed:** the collision bound's docstring is scoped to one fresh draw. The adaptive repeated-nonce lemma is scheduled with the statement phase. |
| M2 (review) | minor | **Fixed:** source tags on `prob_mem_le` and the guess-the-bit declarations. |
| M4 (review) | note | **Fixed:** the S2 design note is synchronized with the code. |

## ===== briefs/pass-shelat-ch5-8/gates/02-s2a/pack-errata.md =====

# Gate 02: pack errata

The pack is shipped and is not edited; corrections are recorded here and carried into round 2.

| # | Pack location | Erratum | Found |
|---|---|---|---|
| E1 | Scope, context | The inventory row of Thm 175.1 (`inventory-ch5-8.md`), which already recorded the expected-polynomial-time debt (finding 4), was not in the bundle. Round 2 includes the inventory rows of the source items it asks about. | 2026-11-05, review sub-agent |
| E2 | Attestation 4 ("No ch. 2–4 module is imported") | True at round 1's head. After the round-1 repairs, `Games/Advantage.lean` imports `TCSlib.Cryptography.Foundations.Probability` (finding 10, ruled: reuse `abs_sub_le_sum_hybrids` and `exists_hybrid_gap`); that module imports only Mathlib. | 2026-11-05, maintainer |
| E3 | Attestation 6 (generalizations disclosed) | `advantage_hybrid` was a statement-level duplicate of `abs_sub_le_sum_hybrids`, not disclosed (finding 10). Resolved by reuse. | 2026-11-05, auditor |

## ===== briefs/pass-shelat-ch5-8/gates/02-s2a/pack.md =====

# Gate 02 (Pass–shelat ch. 5–8, S2a): external API audit pack

**What is audited:** PR [Shilun-Allan-Li/tcslib#185](https://github.com/Shilun-Allan-Li/tcslib/pull/185)
into `cryptography/pass-shelat-ch2-4`, at its head `597eef43ccd3c8bfafe0c0c16a2444b12adc1644`.
- **The change:** the core of a new framework for security games and two-party protocols,
  `TCSlib/Cryptography/Games/` (six modules and a facade, 1,325 lines), plus one import line in
  `TCSlib.lean`.
- **Gate type:** an **API gate** (user's ruling, 2026-11-04). The definitions are new, every
  lemma is proved, and there is no `sorry`. The statements of the six chapters' prongs will be
  written against this API, so its definitions are what matter most.
- **The deliverable:** **`gate02-s2a-findings.md`**.

The bundle holds this pack, then every file named below under a `## ===== <path> =====` header.
**The source is attached separately:** [PS10] R. Pass, a. shelat, *A Course in Cryptography*,
3rd ed., January 2010 (PDF). Book page = PDF page − 12; item numbers carry the book page. You need
it for question 9: §4.4 (book pp. 114–116), and the definitions of ch. 5–7 (book pp. 133–175).

## Brief for the auditor

You are auditing the **trusted surface** of a Lean 4 framework: definitions, theorem statements,
docstrings and proof sketches. The proofs are machine-checked; do not review tactic scripts. Hunt
for:
1. **Wrong semantics:** a definition that does not compute what its docstring says. For example,
   probabilities that are not those of uniform sampling, a simulation that threads state wrongly, a
   log in the wrong order, or an execution that misroutes messages.
2. **Trivialization:** hypotheses that are vacuous or too strong to be met by the games they are
   meant for, or definitions satisfiable for degenerate reasons.
3. **Wrong strength:** a theorem weaker or stronger than its docstring claims; boundary cases.
4. **Unfitness for purpose:** this API must express the security games and protocols of [PS10]
   ch. 5–8 (question 9). A definition that cannot express one of them is a finding.
5. **Debt and duplication:** see the attestations; the framework generalizes three existing
   pieces, with bridges scheduled for the next PR (S2b).
6. **Attribution:** `policy.md` §2 (in the bundle), including its *design adaptation* rule. The
   framework adapts VCVio's design, and the citation block is
   `briefs/pass-shelat-ch5-8/design/CITATION-VCVio.md` (in the bundle).

For **every definition**, restate it in your own mathematical English before reading its
docstring, and report any daylight. For **every theorem**, say in 1–3 sentences whether its
statement is what the docstring claims. Attempt at least **three adversarial instantiations**.
Propose missing sanity theorems. Do not give a blanket approval.

## Scope

| Item | Where |
|---|---|
| Under audit (all declarations) | `TCSlib/Cryptography/Games/{OracleComp,Probability,Simulate,Advantage,Hopping,Protocols}.lean`, `TCSlib/Cryptography/Games.lean` |
| Design documents (context; they state the intent) | `briefs/pass-shelat-ch5-8/design/S2-game-framework.md`, `briefs/pass-shelat-ch5-8/design/CITATION-VCVio.md` |
| Context, not under audit | `TCSlib/InformationTheory/FinDist.lean` (on `main`); the concrete layer of the ch. 2–4 branch that the framework generalizes: `TCSlib/Cryptography/Pseudorandom/Functions/OracleAdversary.lean` (`QueryTree`), `TCSlib/Cryptography/Foundations/Probability.lean` (`uprob`), `TCSlib/Cryptography/Foundations/Experiments.lean` (`distAdv`, `acceptProb`) |
| Source | [PS10] §4.4; ch. 5–7 definitions (PDF attached) |
| Standards | `policy.md` |
| Out of scope | tactic proofs; the S2b layer (bridges to the ch. 2–4 layer, the machine model), which is not written yet |

## Attestations (maintainer execution claims; evidence under `evidence/` in the bundle)

1. **Elaboration.** `scripts/lean_check_tree.sh`, one module at a time into a fresh olean tree,
   over the 8 modules of the closure (`InformationTheory/FinDist`, the six modules, the facade):
   8/8 pass, 0 errors, 0 warnings, 0 `sorry` (`replay-head.log`).
2. **Axioms.** `#print axioms` for all 68 theorems: only `propext`, `Classical.choice` and
   `Quot.sound` (`axioms.log`).
3. **Lint.** `scripts/style_lint.py`: 0 findings on the 7 files; no line over 100 characters
   (`style-lint.log`).
4. **Imports.** `Mathlib.Data.Nat.Notation`, `TCSlib.InformationTheory.FinDist` and the
   framework's own modules. No ch. 2–4 module is imported.
5. **Names** (`name-screen.log`).
   - No short name of `TCSlib.Cryptography.Games` is declared elsewhere in `TCSlib.Cryptography`.
     The one clash found, `distAdv`, was renamed `advantage` before this head.
   - The pinned Mathlib has no `OracleComp`, `OracleSpec`, `ProbComp` or `QueryImpl`.
6. **Generalizations of existing code, disclosed as planned debt.** Each is resolved by a bridge
   in S2b (design note §8). None is a copy: the framework's definitions are new and more general.
   - B1: `Games.OracleComp` with one oracle and `Games.simulate` generalize the concrete layer's
     `QueryTree` and `QueryTree.simulate`.
   - B2: `Games.ProbComp.prob` over finite samples generalizes `uprob` over finite seed types, as
     the user's ruling R-1 decided (sampling as an oracle). A route probe proved the concrete
     layer's `invProb f A` equal to the probability of a one-line game (design note, probe
     P-S2-1).
   - `Games.advantage` and `Games.accept` correspond to `distAdv` and `acceptProb` over
     samplers.

## Known deviations and design choices (declared; verify they are benign)

- **Universe 0.** The framework lives in `Type`; [PS10]'s objects are all finite strings or
  finite structures.
- **Probability.** A real-valued finite sum over each sampling step: sampling oracle `m` is uniform
  on `Fin (m + 1)`, and other finite types are sampled through `Fintype.equivFin`. There are no
  measures (VCVio's semantics is measure-valued; this one is not).
- **Query bounds.** `CostBoundedBy cost c q`: total cost along every run at most `q`, oracle `i`
  costing `cost i`. "At most `q` queries to oracle `i`" is cost 1 on `i` and 0 elsewhere.
- **Identical until bad.**
  - The two implementations must be *equal as computations* on good states, and keep bad states
    bad (every possible new state of a bad state is bad).
  - The bound is the first simulation's probability of ending bad.
  - The lemma also proves the two simulations' bad probabilities equal.
- **Protocols.**
  - A party's exchange query is answered with `Option In`, where `none` means the other party has
    returned.
  - The first mover is the first argument of `Party.exec`.
  - Execution stops with `none` when the fuel runs out.
  - Views are not yet defined as objects; they come from logging, in S2b.

## Specific questions

1. **Sampling.** Is `ProbComp.expect` exactly the expectation under uniform, independent answers
   at every sampling step? Is `ProbComp.sample T` uniform for every nonempty finite `T`?
2. **Simulation and logging.** Is `simulate`'s threading of state right, and does
   `QueryImpl.withLog` log in chronological order? Is `simulate_withLog` the right "logging is
   harmless" statement?
3. **Composition.** Does `simulate_comp` say what a reduction needs: running a reduction against
   implemented oracles is one implementation of its adversary's oracles?
4. **Costs.** Does `simulate_costBoundedBy` capture "the reduction asks at most `q` queries if its
   adversary does and each answer costs at most one query"? Any boundary problem with cost-0
   oracles?
5. **Identical until bad.** Are the hypotheses usable for the bad-event hops of [PS10]'s proofs
   (for example the repeated-nonce event in Thm 168.2, or a forger querying the challenge)? Is
   requiring *equal computations* on good states too strong, or the stickiness hypothesis
   unnecessary? Is the conclusion the standard one?
6. **The collision bound** (`prob_mem_le`). Does the statement capture independence of the fresh
   sample from the list, and the right bound `q/|T|`?
7. **Guessing versus distinguishing** (`guessAdv_eq_half_advantage`). Is it the standard factor
   of two?
8. **Executions.**
   - Does `Party.exec` implement [PS10] §4.4's alternating execution?
   - Is the `Option` reply sound, or can it hide a party's misbehaviour?
   - Does the fuel bound lose anything for protocols with a fixed number of rounds?
9. **Expressiveness for [PS10] ch. 5–8.** Check whether each of the following can be expressed
   with this API, in a sentence each:
   - MAC and signature forgery (Defs 134.2, 136.2), with "`m` was not queried" read from the
     log;
   - collision resistance (Def 140.1);
   - IND-CPA/CCA1/CCA2 (Def 168.1), with CCA2's refusal to decrypt the challenge;
   - non-malleability (Def 172.6);
   - honest-but-curious two-party security (Def 155.1), with views and outputs;
   - sequential composition of zero knowledge (Thm 175.1).

   Report any that cannot be expressed as findings.
10. **The VCVio citation.** Is it adequate under `policy.md`'s design-adaptation rule?
    - Check the project, authors, modules, commit, licence, and a tag usable at declaration
      level.
    - Are the declarations that follow a VCVio construction tagged
      (`[VCVio, OracleComp/OracleSpec]`, `[VCVio, SimSemantics]`, …)?

## Findings format (auditor fills)

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | blocker / major / minor / note | | | | |

Severity guide:
- **blocker:** a downstream phase would build on a wrong definition or statement;
- **major:** fixable but materially misleading as it stands, or debt that needs explicit human
  acknowledgment;
- **minor:** an edge case, or a naming or attribution defect;
- **note:** an observation; no change required.

The gate closes at **0 blockers and 0 majors**.

## ===== policy.md =====

# TCSlib Contribution Policy

Standards for all Lean contributions to this repository, whether written by humans or by
agents. This document covers three things: **modularity** (how code is organized),
**attribution** (how every result is traced to a source), and **proof sketches** (how every
formal proof is accompanied by readable mathematics).

It complements, and does not replace:

- `workflow.md` — the campaign formalization process (phases, audit gates, fill epochs)
  that produces code meeting these standards.
- `.github/copilot-instructions.md` — build workflows, import rules, CI integration points.
- `AGENTS.md` / `.claude/CLAUDE.md` — the sorry-ladder proof workflow and agent roster.
- `blueprint/BLUEPRINT_PIPELINE.md` — how blueprint entries are generated and validated.

Where this document names an existing mechanism (blueprint macros, hygiene scripts), the
policy is to *use that mechanism*, not to invent a parallel one.

## 1. Modularity

**Layout.** Content lives at `TCSlib/<Area>/<Topic>/<Piece>.lean`, one coherent concept or
lemma cluster per file, with a facade file `TCSlib/<Area>/<Topic>.lean` that imports every
child and carries a `/-! -/` module docstring with a `## Contents` list (one line per child).
See `TCSlib/Complexity/NPReductions.lean` for the reference example.

**File size.** Target 150–600 lines per math file. A file approaching 1000 lines should be
split unless there is a positive reason not to (e.g. a single long proof that cannot be
usefully decomposed).

**Exports.** Every new topic facade must be imported from `TCSlib.lean`. CI only builds what
is reachable from `TCSlib.lean`; an unexported file is invisible to CI, docs, and the
blueprint.

**Imports.** Precise module imports only. A bare `import Mathlib` fails CI. Import only what
the file uses.

**Namespaces.** Namespaces are area-local: pick one namespace root per topic and use it
consistently within that topic. Do not leak auxiliary definitions into the root namespace;
mark internal helpers `private` or put them in a dedicated inner namespace.
*Model registry exception*: a model-defining **type** (a machine, circuit, formula, or
decision-tree model) may live at the root namespace, Mathlib-style, provided it is
registered in the catalog facade `TCSlib/ComputationalModels.lean`; its operations and
lemmas still live in the type's own namespace. Anything else at root is a leak.

**Layering.** Keep definition files separate from heavyweight theorem files, so that
downstream work can import a model or a class definition without pulling in every proof about
it. When a development has both a "raw/general" layer and a "bundled" layer (e.g. a machine
model that is parametric in its types, plus a bundled version carrying finiteness instances),
headline definitions and theorems are stated against the bundled layer; the raw layer is
internal plumbing.

**Helpers.** Foundational helper lemmas that serve a whole area belong in that area's
`Basic.lean`, not in the file that first needed them.

**File header.** Every math file begins with the Mathlib-style copyright block, its imports,
the repo-standard options

```
set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false
```

then a module docstring containing `# Title`, `## Main definitions`, `## Main results`, and
`## References` (see §2).

## 2. Attribution

Every mathematical statement in the library must be traceable to a source, at the level of
precision of a textbook theorem number or a paper section.

**File-level.** Every math file's module docstring contains a `## References` section giving
full citations with short tags, e.g.

```
## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
```

**Declaration-level.** Every definition, theorem, and lemma that corresponds to a result in
a source carries the tag with a precise location in its docstring: `[AB09, Claim 1.6]`,
`[AB09, §1.7]`, `[GRS25, Thm 4.2.1]`. Purely technical glue lemmas with no textbook
counterpart may omit the tag; anything a reader would recognize as "a result" may not.

**Deviations.** If the formal statement deviates from the source — different constants,
strengthened or weakened hypotheses, a reformulation — the docstring must say so and briefly
say why (e.g. "stated with explicit constant 5k rather than O(·), following the proof").

**Statement prose.** Every public declaration's docstring begins with a natural-language
statement of what it asserts (for a definition: what it is), precise enough that a reader
could judge the formalization's fidelity without parsing the Lean. The `[Tag, location]`
citation and any deviation note attach to that statement; the proof sketch (§3) follows it.
A bare label ("Unfolding lemma", "Helper for X") is not a statement. Instances are exempt,
as are vendored files (which follow upstream style). `private` declarations should carry
docstrings too, but at reviewer discretion rather than as a hard requirement. The blueprint
remains the cross-referenced informal layer for dependency structure (see **Blueprint**);
the docstring statement is what external audits compare blind restatements against, so it
is part of the trusted surface.

**Blueprint.** When an ingested reference exists under `blueprint/src/references/`, blueprint
entries use `\statementsource{<ref>}{<anchor>}` and `\proofsource{<ref>}{<anchor>}` to cite
it, subject to the existing rule that these are written only after an approved proofmatch
run. When starting a new chapter or paper, ingest it as a reference pair
(`<name>.raw.md` + `<name>.md`) so these citations are possible.

**Vendored code.** Lean code adapted from another project keeps the original copyright
header and license notice, and its file docstring names the source project, the commit it
was taken from, and a summary of local modifications.

**Design adaptation.** When a construction, proof architecture, or module design is
adapted from — or materially inspired by — another project's code, the debt is cited even
when no code is transcribed. The module docstring's `## References` section names the
source project, author, module or archive entry, the commit or version consulted, and its
license, with a short tag usable at declaration level; the precedent is
`TuringMachine/Composition.lean`'s `[Balbach22]` for the Isabelle AFP `Cook_Levin`
composition-combinator architecture. Design documents and blueprint entries built on the
adapted design carry the same citation. Examining external code purely for comparison,
with nothing taken, creates no citation duty, but on a campaign it belongs in the
campaign's records (plan decision log or backlog) so the provenance question is answerable
later. (Maintainer guideline, binding, 2026-10-06.)

## 3. Proof sketches

Every nontrivial formal proof is accompanied by a human-readable English proof sketch, kept
next to the Lean it describes.

**What counts as nontrivial.** Rule of thumb: any proof longer than ~20 lines of tactics, or
that would rate difficulty ≥ 3 on the blueprint scale. One-line `simp`/`omega`/`exact`
proofs need no sketch.

**Where sketches live.** In the Lean file itself:

- For most theorems: a `**Proof sketch.**` paragraph at the end of the theorem's docstring,
  written in mathematical English (not Lean identifiers), naming the key intermediate steps.
- For long proofs: additionally, short comments at the major `have`/section boundaries tying
  the tactics back to the sketch's steps.

The named intermediate steps of a sketch should be visible in the formalization as `have`s
or standalone lemmas — if the sketch says "first reduce to the one-tape case", there should
be a lemma that is that reduction.

**Where sketches do not live.** Not in the blueprint. Blueprint statement entries state
claims only; `scripts/dataset_hygiene.py --strict` hard-fails on proof content there. The
blueprint records *what* is true and its dependency structure; the Lean docstrings record
*why* it is true.

**Sketches and the sorry ladder.** When landing a sorry-skeleton, write the sketch at
skeleton time — the sketch *is* the plan, and each `sorry` should correspond to a named step
of it. A skeleton whose sketch cannot be written is not ready to land.

**Synchronization.** When a proof strategy changes, the sketch changes in the same commit.
A sketch that describes a proof the code no longer performs is worse than no sketch.

## Review checklist

Before merging new Lean content, check:

1. Files follow the Area/Topic layout with a facade, and `TCSlib.lean` exports are updated.
2. Imports are precise; no bare `import Mathlib`.
3. Every file has a `## References` section; every source-derived declaration has a
   `[Tag, location]` in its docstring; deviations from sources are noted.
4. Every nontrivial proof (or sorry-stub standing in for one) has a proof sketch.
5. Every public declaration (instances and vendored files excepted) has a docstring
   opening with a natural-language statement of what it asserts
   (`python3 scripts/style_lint.py` checks presence mechanically; statement quality is
   review judgment).
6. `zsh scripts/lean_check.sh <file>` reports zero errors for each touched file.
7. If blueprint content was touched: `python3 scripts/blueprint_validate.py --strict` and
   `python3 scripts/dataset_hygiene.py --strict` pass.

## ===== briefs/pass-shelat-ch5-8/design/S2-game-framework.md =====

# S2 design note: one framework for security games and two-party protocols

Status: **draft, 2026-11-04.** It implements the user's rulings of 2026-11-04:
- S2 is home-built at TCSlib's pins, adapting VCVio's design, and **VCVio is cited**;
- two-party protocols are carried by the same framework ("protocols unified");
- D-2: a common base, with `OracleEnsemble` restated over it, by agreement with Frederick.

Open decisions for the user are marked **R-n**; points needing Frederick's agreement are marked
**F-n**.

## Citation (policy.md §2, design adaptation)

```
* [VCVio] D. Tuma and the VCVio contributors, *VCVio: machine-checked cryptographic proofs in
  Lean*, https://github.com/dtumad/VCV-io, commit 9054989327a7185ff19ef9ff0f119cccea479501
  (2026-11-04), Apache License 2.0. Design adapted (no code transcribed): oracle specifications
  indexed by a type of oracle names (`VCVio/OracleComp/OracleSpec.lean`), oracle computations as
  a free monad over them (`OracleComp.lean`, `OracleQuery.lean`), probabilistic computations as
  computations over the uniform-selection oracles (`OracleComp/ProbComp/Basic.lean`), and
  simulation of oracles by stateful handlers with query logging and composition (`SimSemantics/`,
  `SimSemantics/QueryImpl/Compose.lean`, `QueryTracking/LoggingOracle`).
```

The source of every mathematical notion stays [PS10] (with [KL] and [Gol04] where [PS10] is
silent). The game-playing method is from [BR06] M. Bellare, P. Rogaway, "The security of triple
encryption and a framework for code-based game-playing proofs", EUROCRYPT 2006 (the fundamental
lemma), and [Sho04] V. Shoup, "Sequences of games", ePrint 2004/332. The rule for when each tag
is used is in `CITATION-VCVio.md`.

## Why (the finding behind the ruling)

Ch. 2–4 expresses each security notion by hand:
- the fixed functionals `invProb`, `predProb`, `acceptProb`, `distAdv` over uniform seeds;
- one deterministic oracle `I → O` with a Boolean output (`QueryTree`, `OracleAdversary`);
- a custom NUPPT decoder per notion (`inverter`, `distinguisherL`, `toOracleAdversary`).

Ch. 5–8 needs several things that model cannot express directly:
- **randomized, stateful oracles:** CPA's `Enc_k` draws fresh coins per query;
- **oracle families:** CCA's `Enc` and `Dec`;
- **non-Boolean adversary outputs:** forgeries, collisions, message pairs;
- **phases with adversary state:** CPA/CCA, non-malleability;
- **transcript predicates:** "`m` was not queried", "the challenge was not decrypted";
- **two-party executions with views:** Def 155.1, OT, Yao, ZK composition.

## Design

**Synchronized with the code after gate 02 (2026-11-05).** The framework lives in namespace
`TCSlib.Cryptography.Games`, with `OracleSpec` inside `OracleComp.lean`. Query bounds are
`OracleComp.CostBoundedBy cost c q`. Executions follow D8's reading (`Party.exec`, `ExecOutcome`;
fuel counts messages). Views are recorded by the executor (`Party.execT`), not read from a
party's log. Identical-until-bad has a semantic hypothesis (same law to good successors). The
sketches below are the pre-gate draft; where they differ, the code and this paragraph rule.
**Thm 175.1 (ruled 2026-11-05):** strict or truncated simulators, a declared deviation carrying D8
into ch. 7 (`PerfectZKAbort` composes to statistical ZK with error `Q·2^-k`).

### 1. Oracle specifications and computations (after [VCVio, OracleComp/OracleSpec])

```lean
/-- A family of oracles named by `ι`: oracle `i` takes a query in `dom i` and answers in `rng i`. -/
structure OracleSpec (ι : Type) where
  dom : ι → Type
  rng : ι → Type

/-- Computations with access to the oracles of `spec`, returning an `α`: a free monad. -/
inductive OracleComp {ι : Type} (spec : OracleSpec ι) (α : Type) : Type
  | pure : α → OracleComp spec α
  | query (i : ι) : spec.dom i → (spec.rng i → OracleComp spec α) → OracleComp spec α
```

- `Monad` and `LawfulMonad` instances, with bind by structural recursion.
- Disjoint union of specs, `spec₁ + spec₂` (index `ι₁ ⊕ ι₂`), and the lifts `liftLeft`/`liftRight`.
- Garg's `QueryTree I O α` is the one-oracle case: there is a bijection
  `QueryTree I O α ≃ OracleComp (singleSpec I O) α` that commutes with `eval` and `simulate`
  (bridge B1).
- The whole framework lives in `Type` (universe 0), as `QueryTree`'s uses do. VCVio's universe
  polymorphism is not needed for [PS10].

### 2. Probability (TCSlib's: finite, uniform, real-valued)

Sampling is the oracle `unifSpec : OracleSpec ℕ` with `dom _ = Unit` and `rng m = Fin (m + 1)`
(after VCVio's uniform-selection oracle). Other finite types are sampled through an equivalence
with `Fin`: `$ᵗ T` for `[Fintype T] [Nonempty T]` (`Fintype.equivFin`). Write
`ProbComp α := OracleComp unifSpec α`.

**Semantics, by structural recursion, real-valued, with finite branching (no PMF, no `ℝ≥0∞`):**

```lean
noncomputable def ProbComp.prob (c : ProbComp α) (p : α → Prop) : ℝ   -- written Pr[p | c]
--   Pr[p | pure a]          = if p a then 1 else 0
--   Pr[p | query m () k]    = (m + 1)⁻¹ * ∑ j : Fin (m + 1), Pr[p | k j]
```

For finite `α` this gives a `FinDist α` (`ProbComp.dist`), which connects to `main`'s `statDist`,
`EpsClose` and extractors (#183).

**Bridge to `uprob` (B2):** a computation that samples `x ← $ᵗ σ`, `r ← $ᵗ ρ` and then decides
`P x r` has `Pr = uprob (fun z : σ × ρ => P z.1 z.2)`. So Garg's `invProb`, `predProb`,
`acceptProb` and `distAdv` are exactly the probabilities of four one-line games, and every
ch. 2–4 result stated through them transfers.

- **R-1 (ruled 2026-11-04: (a), the sampling oracle):**
  - (a) sampling as an oracle in the monad, as above (recommended): games read as programs, as in
    [PS10]'s experiments, and the semantics is a finite sum;
  - (b) all randomness as external finite seeds (`ρ → OracleComp spec α`, handlers reading coin
    tables): closest to today's code, but every game must declare and thread its product of
    seeds by hand.

  Both are finite, uniform and real-valued; the bridge B2 makes (a) agree with today's `uprob`.

### 3. Oracle implementations, simulation, logging (after [VCVio, SimSemantics, QueryTracking])

```lean
/-- Implement the oracles of `spec` by computations over `spec'`, with state `σ`. -/
def QueryImpl (spec : OracleSpec ι) (σ : Type) (spec' : OracleSpec ι') :=
  ∀ i, spec.dom i → σ → OracleComp spec' (spec.rng i × σ)

def simulate (impl : QueryImpl spec σ spec') : OracleComp spec α → σ → OracleComp spec' (α × σ)
```

- **Stateful, randomized oracles** are handlers into `spec' = unifSpec` (or `unifSpec + …`). For
  example, `Enc_k` draws its coins with `$ᵗ` on each query; the state holds the key, counters and
  flags.
- **Logging** is a handler transformer `withLog impl`, which appends `⟨i, x, y⟩` to a
  `QueryLog spec` in the state. Win conditions and oracle restrictions are predicates on the log:
  - "`m` was never queried to `Tag`";
  - CCA2's refusal to decrypt the challenge is a handler that answers `⊥` on it.
- **Reductions** are `simulate` with a handler that answers the adversary's oracles by querying
  the reduction's own oracles. This generalizes `QueryTree.simulate` (`eval_simulate`) to
  families and to state.
- **Query bounds** are a structural predicate `IsQueryBound c (qb : ι → ℕ)`, preserved by
  `simulate` with a per-query cost, generalizing `QueryTree.BoundedBy`.

### 4. Games and advantages (concrete level, one security parameter value)

- A **search game** is a `ProbComp Bool` built from the adversary: forgery, collision, inversion.
  Its advantage is `Pr[= true]`.
- A **distinguishing pair** is `G₀ G₁ : ProbComp Bool`, with advantage `|Pr[G₀] − Pr[G₁]|`.
- A **guess-the-bit game** has advantage `|Pr[b' = b] − ½|`, with the standard lemma relating it
  to the distinguishing form (factor 2).

[PS10]'s definitions are then short programs over these. Examples:
- **MAC forgery** (Def 134.2): `k ← Gen; (m, σ) ← simulate (withLog (tagImpl k)) A; return
  (Ver k m σ ∧ m ∉ log)`.
- **IND-CCA2** (Def 168.1): phase 1 with `(encImpl k + decImpl k)`, then the challenge, then
  phase 2 with `decImpl` refusing `c*`. The adversary's state between phases is the value it
  returns.

### 5. Game hopping (the generic lemmas, proved once)

1. `Pr` respects bind (total probability), `map` and relabelling of finite samples.
2. **Hybrids:** advantages add along a chain of games (the triangle inequality), with the standard
   `k`-step form used by the hybrid lemma.
3. **Identical until bad** [BR06]: two games written over the same code that differ only after a
   flag is set satisfy `|Pr[G₀] − Pr[G₁]| ≤ Pr[bad]`. Here this is a lemma about two handlers that
   agree while a state flag is clear.
4. **Oracle substitution:** if two oracle implementations are indistinguishable to every
   `q`-query adversary, then a game using one is close to the game using the other. The proof is
   by `simulate`. This is the step "replace the PRF by a random function" used in
   Thms 135.4, 168.2, 170.4 and 179.1.
5. **Lazy sampling** of a random function: a handler that samples on first query and caches gives
   the same distribution as a function table sampled up front. Garg's `LazySampling.lean` proves
   this for `QueryTree`; it is re-derived through B1/B2, not re-proved, where possible.
6. **Collision and union bounds** over `q` queries: for example, the `r` collisions of Thm 168.2.

### 6. Two-party protocols in the same framework ("protocols unified")

```lean
/-- A party that sends messages of type `Out`, receives messages of type `In`, and draws coins. -/
abbrev Party (Out In α : Type) := OracleComp (exchangeSpec Out In + unifSpec) α
--   exchangeSpec Out In has one oracle: query = outgoing message,
--   answer = the other party's next message, or `none` once the other party has returned
```

- **Execution** `exec (fuel : ℕ) (A : Party M₁ M₂ α) (B : Option M₁ → Party M₂ M₁ β) :
  ProbComp (Option (α × β))` (probed in P-S2-4; the transcript comes from logging handlers) is the
  coroutine interleaving: A's exchange query is answered by running B until
  B's next exchange query, and so on. The fuel is the protocol's message count, as in
  Frederick's fixed alternation.
- **A party's view** is (its input, its coins, the messages it received), read off the log of its
  `exchangeSpec` queries and its `unifSpec` answers. Def 155.1's joint distribution
  `{(view_A, out_B)}` is then a `ProbComp` directly.
- **Simulation-based security** (Def 155.1, ZK) compares two such `ProbComp`s, or two ensembles
  of them asymptotically, through the same distinguishing advantage.
- **OT inside Yao** (the composition step [PS10] omits): a party whose sub-protocol is run by a
  handler. Sequential composition is `simulate` of the outer party's calls to an inner
  protocol's ideal functionality, so the hybrid "real OT → simulated OT" is the oracle
  substitution lemma (§5.4) applied to a protocol.
- **Bridge B4 to Frederick's model:** every `Strategy` with a fixed alternation of `rounds`
  moves induces a `Party` (a loop that keeps the history and calls `next`). `exec` of the
  induced parties gives his `Protocol.exec`, `View`, `outP`/`outV` and transcript. His ZK
  definitions (`ZK`, `PerfectZK`, `PerfectZKAbort`) then transfer, and Thm 175.1 (sequential
  composition) is stated in the framework with a proved equivalence to his `ZK`. **F-2:** whether
  his ZK layer is later restated over `Party`, or only bridged (our recommendation: bridged now,
  restated at integration, by him).

### 7. The machine layer (asymptotic security)

- **Codecs.** A `SpecCodec spec` gives, per security parameter, string encodings of oracle
  names, queries, answers and the output, with `decode (encode a) = some a` and polynomial length
  bounds. It reuses Frederick's `pairEncode`, `decodeFin` and `encodeHist`.
- **The generic decoder.** `NUPPT.toComp (A : NUPPT) (codec) (n q : ℕ) : (A.Coins n) →
  OracleComp spec α` iterates `A`'s next-query activation on the encoded history, decoding a query
  or a final output, with budget `q`. It generalizes his `toOracleAdversary`, which is its
  one-oracle, Boolean-output instance (**bridge B3, which is also the D-2 restatement of
  `OracleEnsemble.Indist`**).
- **Security, uniformly:** `Secure G := ∀ (A : NUPPT) (q : PolyExpr), Negligible fun n =>
  adv (G n) (A.toComp codec n (q.eval n))`. The same shape covers search, distinguishing and
  guess-bit games, with fixed or adversary-chosen messages.
- **The efficiency lemma (the machine-level crux, proved once).** If a reduction is a NUPPT
  adversary run under a handler whose per-query work is a `PolyTimeComputable` function of the
  encoded state and query, with a polynomial query bound and polynomial state size, then the
  composite is `NUPPT.toComp` of a single NUPPT. It is built from Frederick's closure calculus
  (`Complexity/Randomized/Closure`). Every reduction of prongs A–D then needs only its handler's
  poly-time computability, never a machine construction of its own.

### 8. Bridges to existing code (all in our files; nothing of his edited without agreement)

**Status (2026-11-04, S2b branch `cryptography/pass-shelat-ch5-8-s2b`, stacked on #185):**
- **B1 proved** (`Games/Bridges/QueryTree.lean`): a bijection `QueryTree I O α ≃ OracleComp (singleSpec I O) α`, under which evaluation, Garg's `simulate` and `BoundedBy` (as `CostBoundedBy` with unit costs) are preserved.
- **B2 proved** (`Games/Bridges/Experiments.lean`): `Pr[x ← $ α : p x] = uprob p` (through the published `uprob_eq_card_filter`), sequential sampling equals product sampling, and `invProb`, `predProb`, `acceptProb` and `distAdv` as one-line games. It reads the four definitions' bodies (F-3).
- **B3 decoder drafted** (`Games/Machines.lean`): `Move`, `MachineCodec`, `buildComp`, `NUPPT.toComp` with its query bound, and `toComp_singleCodec`, which shows that `toOracleAdversary` is the one-oracle instance. The efficiency lemma is not started.
- **B4, B5 not started:** B4 waits for gate 02's findings on `Protocols`; B5's asymptotic part needs B3.

| Bridge | Relates | Purpose |
|---|---|---|
| B1 | `QueryTree I O α` ≃ one-oracle `OracleComp`; `eval`, `simulate`, `BoundedBy` | reuse Garg's PRF/GGM/lazy-sampling results |
| B2 | `uprob`-functionals (`invProb`, `predProb`, `acceptProb`, `distAdv`) = `Pr` of one-line games | reuse every ch. 2–4 concrete result |
| B3 | `NUPPT.toOracleAdversary` = one-oracle instance of `NUPPT.toComp`; `OracleEnsemble.Indist` = a one-oracle distinguishing `Secure` | D-2's restatement (**F-1**) |
| B4 | `Strategy`/`Protocol.exec`/`View` = induced `Party`s and `exec` | reuse his ZK layer (**F-2**) |
| B5 | `PrivateKeyScheme.SingleMessageSecure`/`MultiMessageSecure`, `PublicKeyScheme.Secure` = games with fixed message vectors | Thm 168.2, Claim 172.a |

### 9. Layout (new directory, on `cryptography/pass-shelat-ch2-4` per D-0)

`TCSlib/Cryptography/Games/`:
- `OracleSpec.lean`, `OracleComp.lean` (monad, sums of specs, query bounds);
- `Probability.lean` (`unifSpec`, `$ᵗ`, `Pr`, `dist`);
- `Simulate.lean` (handlers, `simulate`, logging);
- `Advantage.lean` (game shapes);
- `Hopping.lean` (§5);
- `Protocols.lean` (`Party`, `exec`, views);
- `Machines.lean` (codecs, `NUPPT.toComp`, the efficiency lemma);
- `Bridges/` (B1–B5);
- the facade `Games.lean`.

The namespace is `TCSlib.Cryptography`, with the framework's types `OracleSpec`, `OracleComp`,
`ProbComp`, `QueryImpl` and `Party`. Each module docstring's `## References` carries [VCVio] (the
block above), plus [BR06]/[Sho04] for `Hopping.lean`, and [PS10] for the protocol layer's §4.4
and §6.2.

**Size estimate:** 3–5k lines, including the protocol layer and the machine layer (the plan's
1–2k for S2 assumed the narrower design). The machine layer (§7) is the largest risk.

## Route probes before the statement phase (pre-ship, run in Lean)

| Probe | Shows |
|---|---|
| P-S2-1 | the monad, `Pr`, and B2 on `invProb` (one ch. 2–4 functional, transferred). **Passed 2026-11-04** (`probes/P-S2-1-monad-prob-bridge.lean.txt`): the free monad, `unifSpec` sampling, the finite-sum `expect`/`prob`, total expectation (`expect_bind`), `expect_sample`, and `invProb f A = Pr[game]`, with standard axioms. It reads `invProb` and `uexp` by their bodies, for want of published equations (F-3) |
| P-S2-2 | Thm 135.4's concrete reduction: a forger, run under a handler that answers `Tag` with a PRF-or-random oracle, gives a distinguisher with advantage `≥ ε − 2^{-n}` |
| P-S2-3 | the CPA game for Alg 99.1 with a stateful, fresh-coin `Enc` oracle, and one hop of Thm 168.2's proof. **Passed in part, 2026-11-04** (`probes/P-S2-3-handlers-log-cpa.lean.txt`). Done: sums of specs and of handlers, `simulate` with state, logging, `simulate_withLog` (logging is conservative; proved), the fresh-coin `encImpl`, the IND-CPA experiment as a program (phases, adversary state, challenge), `cpaAdv`, and the bad event of Thm 168.2 as a log predicate. **Not yet:** the hop itself, which needs the oracle-substitution and identical-until-bad lemmas (§5) and is scheduled for the statement-phase probes |
| P-S2-4 | one OT execution (Prot 160.4) through `exec`, with the receiver's view read from the log. **Passed in part, 2026-11-04** (`probes/P-S2-4-protocol-exec.lean.txt`): `Party` over `exchangeSpec` + `unifSpec`, `step`/`finish`, `exec` with fuel and role swap, a toy protocol executing by `rfl`. Design fix found: an exchange answers `Option In`, where `none` means the other party has returned, so a waiting party can finish. **Not yet:** OT itself and views from logs |
| P-S2-5 | B3: his `toOracleAdversary` as an instance of `NUPPT.toComp`, at the level of definitions |

## Coordination with Frederick (adds to the S1 note)

- **F-1 (D-2):** `OracleEnsemble` and `toOracleAdversary` restated over `Games`, or bridged by
  B3; who does it, and when relative to his external gate.
- **F-2 (protocols unified):** his `Strategy`/`View`/`ZK` bridged by B4 now, and restated at
  integration.
- **F-3:** the framework adapts his `encodeHist`/`pairEncode` codecs and cites his closure
  calculus; any machine lemma we need in his `Closure.lean` is requested, not added.
  It also requests published equations for `invProb`, `predProb`, `acceptProb` and `uexp`
  (`Foundations/`): bridge B2 reads them by their bodies today (P-S2-1).

## Decisions for the user (ruled 2026-11-04: R-1 (a) the sampling oracle; R-2 reuse via bridges)

- **R-1:** sampling as an oracle inside the monad (recommended), or external finite seeds (§2).
- **R-2:** the generic lemmas of §5, re-derived through B1/B2 from Garg's concrete layer where
  possible (recommended), or proved fresh in the framework (simpler proofs, more duplication;
  each duplicate goes to the ledger).

## ===== briefs/pass-shelat-ch5-8/design/CITATION-VCVio.md =====

# Citation for the S2 game framework's design source

Ruled 2026-11-04 (user): S2 is home-built at TCSlib's pins, **adapting VCVio's design**, and VCVio
**must be cited**. `policy.md` (§2, *Design adaptation*) requires the citation even though no code
is transcribed: in the `## References` of every module that uses the adapted design, with a short
tag usable at declaration level, and in every design document and blueprint entry built on it.

## The reference block (use verbatim in module docstrings)

```
* [VCVio] D. Tuma and the VCVio contributors, *VCVio: machine-checked cryptographic proofs in
  Lean*, https://github.com/dtumad/VCV-io, commit 9054989327a7185ff19ef9ff0f119cccea479501
  (2026-11-04), Apache License 2.0. Design adapted (no code transcribed): oracle specifications
  indexed by a type of oracle names (`VCVio/OracleComp/OracleSpec.lean`), oracle computations as
  a free monad over them (`OracleComp.lean`, `OracleQuery.lean`), probabilistic computations as
  computations over the uniform-selection oracles (`OracleComp/ProbComp/Basic.lean`), and
  simulation of oracles by stateful handlers with query logging and composition (`SimSemantics/`,
  `SimSemantics/QueryImpl/Compose.lean`, `QueryTracking/LoggingOracle`).
```

## Declaration level

A declaration whose shape follows a VCVio construction carries `[VCVio, <module>]` in its
docstring, for example `[VCVio, OracleComp/OracleSpec]`, after the source citation ([PS10], [KL],
[Gol04]) that the mathematics comes from.

## What is and is not taken

- **Taken (design):** the three ideas above.
- **Not taken:**
  - no code, and no proof;
  - not VCVio's probability semantics: TCSlib keeps real-valued probabilities over finite uniform
    seeds (`uprob`) and `FinDist`;
  - not its notion of polynomial time: TCSlib keeps the Turing-machine `Complexity.NUPPT`;
  - not its program logic or tactics.
- **Why not a dependency:** VCVio pins Lean 4.35.0 with Mathlib v4.35.0, while TCSlib pins Lean
  4.25.0. Its polynomial time is a backend-relative cost model, and its probability semantics is
  measure-valued (the decision log of `PassShelatChapter5-8Plan.md`, 2026-11-04).

## Authors seen in the consulted modules (from their headers)

Checked at the pinned commit (gate 02, finding 7):
- `OracleComp.lean`, `ProbComp/Basic.lean`, `SimSemantics/QueryImpl/Compose.lean`: Devon Tuma,
  Quang Dao;
- `OracleSpec.lean`, `OracleQuery.lean`: Devon Tuma;
- `QueryTracking/LoggingOracle/Core.lean`: Devon Tuma, Quang Dao, Alexander Hicks.

The repository has since moved to `https://github.com/Verified-zkEVM/VCVio`; the old URL
redirects, and the citation keeps it, with the pinned commit.

## ===== briefs/pass-shelat-ch5-8/inventory-ch5-8.md =====

# Inventory — [PS10] Chapters 5–8 (§5.1–§8.3)

Draft of 2026-11-04, by the maintainer agent of the Arora–Barak ch. 3–4 campaign, for planning only.
Nothing under `TCSlib/` was touched. Source: [PS10] R. Pass, a. shelat, *A Course in
Cryptography*, 3rd edition, January 2010 (book pp. 133–184, PDF pp. 145–196 of
`https://www.cs.cornell.edu/courses/cs4830/2010fa/lecnotes.pdf`). Items are described in our own
words. No text of the notes is copied here.

The companion documents are the plan (`PassShelatChapter5-8Plan.md`, repository root), the spine
design (`SPINE-DESIGN.md`) and the workflow handover (`WORKFLOW.md`, both in this folder).

## Conventions

- **IDs** follow the ch. 2–4 inventories: `Kind-page.seq` for numbered items, and
  `Kind-page.a`, `.b`, … for unnumbered items on that page. Kinds:
  - `Def`, `Thm`, `Lem`, `Prop`, `Claim`, `Fact`, `Rem`;
  - `Prot`/`Alg`/`Constr` for protocols, algorithms and constructions.
- **"His"** means a declaration of the ch. 2–4 layer on `cryptography/pass-shelat-ch2-4`
  (Frederick Dehmel's), in namespace `TCSlib.Cryptography` unless written out. **"main"** means
  `origin/main`.
- **Scope:**
  - **core:** mandatory for the campaign;
  - **optional:** feasible and useful, not needed downstream;
  - **deferred:** research-level, informal in the source, or needing a notion ch. 2–4 left out;
  - **out:** no formal content.
- **diff** is 1 (one-liner, or a citation) to 5 (research-level), as in the ch. 2–4 inventories.
- **Prong** is the parallel workstream of the plan:
  - **P0** needs nothing from ch. 2–4;
  - **A** authentication; **B** secure computation; **C** composability; **D** randomness;
  - **S** the shared spine.

## Headline findings (read first)

1. **ch. 5–8 depend on ch. 2–4's definitions, almost never on its proofs.** His 63 open
   sorries block no statement here. They show up only in our axiom prints, through the few
   results we cite (the DL candidate in Thm 142.3, his §3.9 scheme's analysis in Thm 168.2).
2. **No prong depends on another at statement level.** The source proves Thm 170.4 (CCA2)
   directly from PRFs, not through ch. 5's MAC theorem, so prong C does not wait for A. What
   prongs share is infrastructure, which the spine builds once:
   - the oracle-game layer: A's forgery games and C's CPA/CCA games;
   - the two-party execution layer: B's secure computation and C's ZK composition.
3. **The source is thin in places.** These are recorded in the notes column:
   - §5.7–5.9 are exercises or empty;
   - Shamir security (Prop 154.5) and the OT receiver's simulator (in Prop 161.5) are left as
     exercises;
   - Thm 165.2 is cited from [GMW87] without proof;
   - §7.2.3–7.3 are bullet outlines;
   - Prot 176.2 needs proofs of knowledge, which [PS10] §4.8 leaves as a stub and ch. 2–4 did
     not formalize.

   Where a core item needs a proof the notes do not give, the fill cites a second source, per
   `policy.md`'s attribution rules: [Gol04] O. Goldreich, *Foundations of Cryptography*, vol. 2;
   or [KL] J. Katz, Y. Lindell, *Introduction to Modern Cryptography*.
4. **main already has pieces ch. 8 needs:**
   - `TCSlib/InformationTheory/` has `FinDist`, `HasMinEntropy`, `statDist`, universal hashing
     and `leftover_hash`;
   - `TCSlib/Complexity/CircuitComplexity/DAGCircuit` has `runWith`, a circuit evaluation over
     any value type, which is the shape Yao's garbled evaluation needs;
   - ch7's randomized classes and `ClassP/DTIME` are there for Thm 180.1.

## Chapter 5 — Authentication (book pp. 133–149)

| ID | kind | § | item | depends on | prong | scope | diff | notes |
|---|---|---|---|---|---|---|---|---|
| Def-134.1 | definition | 5.2 | MAC `(Gen, Tag, Ver)`: PPT `Gen`, `Tag`; deterministic poly-time `Ver`; perfect correctness | `Complexity.NUPPT`/`PPT`, `PolyTimeComputable` | A | core | 2 | |
| Def-134.2 | definition | 5.2 | MAC security: a non-uniform PPT forger with a `Tag_k` oracle outputs `(m, σ)`, `m` unqueried, accepted, with negligible probability | S (search-game layer), `Negligible` | A | core | 3 | the first search game of the campaign; the spine designs it |
| Prot-134.3 | construction | 5.2 | PRF MAC: `Tag_k(m) = f_k(m)` | his `PRF` | A | core | 1 | |
| Thm-135.4 | theorem | 5.2 | a PRF gives a secure MAC on `{0,1}^n` | his `PRF` (`OracleEnsemble.Indist`), the random-function guess bound | A | core | 3 | source: proof sketch. The reduction runs the forger against the oracle and tests its forgery; the advantage is at least `ε − 2^{-n}` |
| Def-135.1 | definition | 5.3 | digital signature scheme `(Gen, Sign, Ver)`, perfect correctness | as Def-134.1 | A | core | 2 | |
| Def-136.2 | definition | 5.3 | signature security against a chosen-message forger with a `Sign_sk` oracle | S, `Negligible` | A | core | 3 | `Ver` is public, so no verification oracle is needed |
| Def-136.a | definition | 5.3 | one-time security: at most one signing query | Def-136.2 | A | core | 2 | |
| Prot-137.1 | construction | 5.4 | Lamport one-time signature on `{0,1}^n` from `f` | his `FunFamily` | A | core | 2 | |
| Thm-137.2 | theorem | 5.4 | Lamport is one-time secure if `f` is one-way | his `StrongOneWay`, `Closure` (the NUPPT calculus) | A | core | 3 | the reduction guesses the position and bit `(i, c)`, aborts on a conflicting query, and succeeds with `ε/(2n)` |
| Def-140.1 | definition | 5.5.1 | CRH family: PPT `Gen`, compression (range smaller than domain), efficient evaluation, collision resistance against non-uniform PPT | S (search games), `Negligible` | A | core | 2 | a family is needed against non-uniform adversaries (source remark) |
| Claim-141.a | claim | 5.5.2 | collision probability of `h` on a random pair is at least one over the range size (Cauchy–Schwarz) | — | A | optional | 2 | |
| Claim-142.a | claim | 5.5.2 | birthday bound: on the order of the square root of the range size, in samples find a collision | — | A | optional | 3 | expectation only in the source |
| Prot-142.2 | construction | 5.5.2 | DL hash `h_{p,g,y}(x, b) = y^b g^x mod p` | his `Candidates.ExpGroupGen`, `ArithmeticFP` | A | core | 2 | conditional, like his candidates (the arithmetic hypothesis bundle) |
| Thm-142.3 | theorem | 5.5.2 | under DL, Prot-142.2 is a CRH compressing by one bit | his `Candidates.DLAssumption` | A | core | 3 | source: the domain is "an `n`-bit `x`" but the proof needs exponents below `p − 1`. State it over `ZMod (p − 1) × Bool` |
| Constr-143.a | construction | 5.5.2 | factoring-based CRH `y^b x^2 mod N`, restricted domain | his factoring candidate | A | deferred | 3 | footnote only |
| Constr-143.b | construction | 5.5.3 | from one-bit to polynomial compression | Thm-142.3 | A | optional | 4 | sketch only: the naive iteration is insecure, and no construction is given. Needs [KL] (Merkle–Damgård) |
| Thm-144.1 | theorem | 5.6 | CRH plus OWF give a one-time signature for long messages (hash-and-sign) | Def-140.1, Thm-137.2, Def-136.a | A | core | 3 | source: CRH from `{0,1}^*`. **Decision D-3:** state it for messages of length `≤ p(n)` with a CRH `{0,1}^{p(n)} → {0,1}^n`, or take the unbounded form with Constr-143.b |
| Prot-144.2 | construction | 5.6 | hash-then-sign scheme | Thm-144.1 | A | core | 1 | |
| Constr-146.a | construction | 5.7 | chain-based many-message signature, stateful | Def-136.2 | A | optional | 4 | source: security "left as an exercise" |
| Constr-146.b | construction | 5.7.1 | tree-based (depth `n`) many-message signature | Constr-146.a | A | optional | 4 | idem |
| Constr-148.a | construction | 5.7.1 | stateless tree signatures from PRFs | his `PRF`, Constr-146.b | A | optional | 4 | idem |
| Claim-148.b | claim | 5.8 | textbook trapdoor signatures are forgeable (RSA multiplicativity) | his RSA candidate | A | optional | 2 | |
| Rem-149.a | remark | 5.8 | hash-and-sign in the random oracle model | — | A | out | — | ROM not modeled |
| §5.9 | section | 5.9 | zero-knowledge authentication | — | — | out | — | empty in the source |

## Chapter 6 — Computing on secret inputs (book pp. 151–165)

| ID | kind | § | item | depends on | prong | scope | diff | notes |
|---|---|---|---|---|---|---|---|---|
| Prot-151.a | protocol | 6.1 | additive (sum) sharing for the average of salaries | — | P0 | optional | 2 | |
| Claim-152.a | claim | 6.1 | any `n − 2` transcripts are independent of the other two inputs | Prot-151.a | P0 | optional | 2 | |
| Def-152.1 | definition | 6.1.1 | `(k, n)` secret sharing: `Share`, `Recon`, privacy for `< k` shares | `statDist` (main) | P0 | core | 2 | source: "statistically close". Shamir is exact; define both, and prove the exact one |
| Lem-153.2 | lemma | 6.1.2 | Lagrange interpolation, uniqueness | Mathlib `Lagrange` | P0 | core | 1 | cite Mathlib |
| Fact-153.3 | fact | 6.1.2 | a nonzero degree-`n` polynomial has at most `n` roots | Mathlib `Polynomial.card_roots'` | P0 | core | 1 | cite |
| Prot-154.4 | protocol | 6.1.3 | Shamir sharing over `ZMod p`, `p > n` | Lem-153.2 | P0 | core | 2 | **source typo:** it draws `n − 1` coefficients up to `a_n tⁿ`. Threshold `k` needs degree `k − 1` with `k − 1` random coefficients |
| Prop-154.5 | proposition | 6.1.3 | Shamir is a secure `k`-out-of-`n` scheme | Prot-154.4, Def-152.1 | P0 | core | 3 | source: an exercise. Proof: any `k − 1` shares are uniform (a bijection with the coefficients); reconstruction by Lem-153.2 |
| Def-155.1 | definition | 6.2 | two-party honest-but-curious secure computation: simulators `S_A`, `S_B`; each party's view jointly with the other's output ≈c the ideal | his `Protocol`, `Strategy`, `View` (ZK `Interaction`), `Ensemble.Indist`; S (execution layer) | B | core | 4 | the output clause makes the definition imply correctness (source remark) |
| Alg-157.2 | construction | 6.2.2 | special encryption: `Enc_k(m) = (r, 0^n‖m ⊕ f_k(r))` with a length-doubling PRF; a wrong key decrypts to `⊥` | his `PRF`, `PrivateKeyScheme` | B | core | 2 | **source typo:** `x` for `m` |
| Claim-157.a | claim | 6.2.2 | Alg-157.2 is multi-message secure, and decryption under an independent key gives `⊥` except with negligible probability | his `MultiMessageSecure`, `PRF` | B | core | 3 | source: "easy to modify 99.1" |
| Constr-158.a | construction | 6.2.1–3 | garbled circuit: two keys per wire, each gate a randomly permuted table of doubly-encrypted output keys | `DAGCircuit` (main; fan-in two via `FaninTwo`), Alg-157.2 | B | core | 4 | evaluate through `DAGCircuit.runWith` with keys as values |
| Claim-159.a | claim | 6.2.3 | garbled evaluation: exactly one row decrypts per gate, w.h.p.; the output keys encode `C(x, y)` | Constr-158.a, Claim-157.a | B | core | 3 | |
| Def-160.a | definition | 6.2.4 | 1-out-of-2 OT functionality `OT(a₁, a₂, b) = (⊥, a_b)` | Def-155.1 | B | core | 1 | |
| Prot-160.4 | protocol | 6.2.4 | OT from a trapdoor permutation family and a hard-core predicate | his `TrapdoorCollection`, `Collection.HardCore` | B | core | 3 | **source typo:** the sender sends `(z₁, z₂)`, not `(z₁, …, z₄)` |
| Prop-161.5 | proposition | 6.2.4 | Prot-160.4 is honest-but-curious secure | Def-155.1, his hard-core theorem for TDP collections | B | core | 4 | source gives `S_A` only; `S_B` is "an exercise" and needs the hard-core predicate's unpredictability |
| Prot-162.6 | protocol | 6.2.5 | Yao: A garbles, the parties run one OT per input bit of B, B evaluates and sends the output | Constr-158.a, Prot-160.4 | B | core | 3 | |
| Thm-163.7 | theorem | 6.2.5 | Yao is honest-but-curious secure | Prop-161.5, Claim-159.a, Claim-157.a | B | core | 5 | source: a hybrid over the garbled circuit and the OT simulators. It needs a composition step (OT simulators inside a larger protocol) that the notes do not state. Use [Gol04] §7.3 |
| Def-165.1 | definition | 6.3 | multi-party secure computation, real vs ideal, with corrupted subsets | Def-155.1 | B | optional | 4 | informal in the source |
| Thm-165.2 | theorem | 6.3 | [GMW87]: TDPs give honest-majority MPC for any poly-time `f` | Def-165.1 | B | deferred | 5 | cited without proof; statement-only at most |
| Claim-165.a | claim | 6.3 | fairness is impossible for two parties | — | B | deferred | 5 | a remark ([Cleve86]) |

## Chapter 7 — Composability (book pp. 167–178)

| ID | kind | § | item | depends on | prong | scope | diff | notes |
|---|---|---|---|---|---|---|---|---|
| Def-168.1 | definition | 7.1.1 | IND-CPA/CCA1/CCA2 for private-key schemes: oracle pairs `(O₁; O₂)`, and under CCA2 the decryption oracle refuses the challenge | S (game layer), his `PrivateKeyScheme` | C | core | 3 | |
| Thm-168.2 | theorem | 7.1.2 | his §3.9 construction (Alg-99.1, `r‖m ⊕ f_k(r)`) is CPA- and CCA1-secure | his multi-message scheme (`MultiMessage`), `PRF` | C | core | 4 | source: sketch. The bad events are `r` colliding with an oracle query, and a pre-challenge decryption query on the challenge `r` |
| Claim-169.a | claim | 7.1.3 | Alg-99.1 is not CCA2-secure (mauling the challenge ciphertext) | Thm-168.2's scheme | C | core | 2 | source: "`c + 1`". Formalize as XOR with a fixed nonzero `δ`, giving an explicit adversary with advantage ≈ 1 |
| Alg-169.3 | construction | 7.1.3 | `π′`: encrypt with `f_{k₁}`, then tag `c₁` with `f_{k₂}` | his `PRF` | C | core | 2 | **source typo:** the tag is `f_{k₂}(c₁)` (the proof writes `g`) |
| Thm-170.4 | theorem | 7.1.3 | `π′` is CCA2-secure | Thm-168.2 (CPA), his `PRF` | C | core | 4 | **proved from PRFs directly, not via Thm 135.4**, so C does not depend on prong A |
| Def-171.5 | definition | 7.1.4 | IND-CPA/CCA1/CCA2 for public-key schemes (no encryption oracle) | S, his `PublicKeyScheme` | C | core | 2 | |
| Claim-172.a | claim | 7.1.4 | his Alg-104.3 (TDP bit encryption) is CPA-secure | his `BitPublicKeyScheme` security (Thm-104.4) | C | core | 2 | close to his own theorem; CPA adds nothing when the adversary holds `pk` |
| Def-172.6 | definition | 7.1.5 | non-malleability: the decryptions of the adversary's ciphertexts (`⊥` for copies of the challenge) are indistinguishable for `m₀`, `m₁` | Def-171.5 | C | core | 3 | source mixes private- and public-key notation; take the public-key reading |
| Def-173.7 | definition | 7.1.6 | relation-based non-malleability with a simulator and auxiliary input | Def-172.6 | C | core | 3 | |
| Thm-174.8 | theorem | 7.1.6 | the two notions of non-malleability are equivalent | Def-172.6, Def-173.7 | C | core | 4 | source: the (⇐) direction uses the hybrid lemma (his `Ensemble.Indist`) |
| Thm-175.9 | theorem | 7.1.7 | CCA2 secrecy ⇔ CCA2 non-malleability | Def-168.1, Def-172.6 | C | optional | 4 | source: sketch. CCA2 non-malleability is not defined explicitly: add the decryption oracle to Def-172.6 |
| Thm-175.1 | theorem | 7.2.1 | sequential composition: `Q(n)` independent runs of a ZK proof are ZK | his `ZK`/`PerfectZK`, auxiliary input (present in his `Defs`) | C | core | 4 | source assumes **expected** poly-time simulators. His are strict PPT (his D8) or truncated with abort (`PerfectZKAbort`), so the composition must carry the truncation error |
| Prot-176.2 | protocol | 7.2.2 | a ZK protocol that is not concurrently secure | ZK proofs of knowledge | C | deferred | 5 | needs proofs of knowledge ([PS10] §4.8 is a stub; not in ch. 2–4) |
| §7.2.3–7.3 | sections | 7.2.3–7.3 | witness indistinguishability, a concurrent identification protocol, non-malleable commitments | — | — | out | — | bullet outlines only |

## Chapter 8 — More on randomness and pseudorandomness (book pp. 179–184)

| ID | kind | § | item | depends on | prong | scope | diff | notes |
|---|---|---|---|---|---|---|---|---|
| Def-179.a | definition | 8.1 | the learning game: random concept `C_i`, labelled samples, predict a fresh point | his `NUPPT` | D | core | 2 | **Decision D-5:** a crypto-style prediction game here (recommended), or PAC learning in `TCSlib/LearningTheory` (which has online and mistake-bound learning, not PAC) |
| Thm-179.1 | theorem | 8.1 | PRFs give a PPT-decidable concept class no non-uniform PPT learner predicts with probability `1/2 + ε` | his `PRF`, Def-179.a | D | core | 3 | source: proof sketch. The learner's samples are answered by oracle queries at random points. A fresh point must avoid the sampled ones |
| Thm-180.1 | theorem | 8.2 | PRGs give BPP ⊆ `DTIME(2^{n^ε})` for every `ε > 0` | his `PRG` with polynomial stretch (his expansion theorem); main's BPP (ch7 `Randomized/Classes`) and `ClassP/DTIME`; S (model bridge) | D | core | 5 | machine-level: seed enumeration in deterministic time. The NUPPT model and ch7's BPP model must meet (Decision D-6). Non-uniform distinguishers, with `x` fixed in the advice, fit his definitions |
| Rem-181.a | remark | 8.2 | subexponentially secure PRGs give BPP ⊆ quasi-polynomial time | Thm-180.1 | D | deferred | 4 | |
| Def-181.1 | definition | 8.3.1 | `ε`-closeness | main's `statDist` | P0 | core | 1 | cite |
| Def-181.2 | definition | 8.3.1 | `m`-bit `ε`-extractor for a class `C` of sources (deterministic) | Def-181.1 | P0 | core | 1 | |
| Claim-182.a | claim | 8.3.2 | von Neumann's procedure extracts unbiased bits from i.i.d. biased coins | — | P0 | optional | 3 | source: "repeat" (Las Vegas). Formalize per accepted pair, or with a bounded number of trials and its failure probability |
| Claim-182.b | claim | 8.3.2 | the XOR of many independent biased coins is `ε`-close to uniform | — | P0 | optional | 2 | piling-up lemma |
| Def-182.3 | definition | 8.3.2 | Shannon entropy | Mathlib (`Real.negMulLog`), main's `FinDist` | P0 | core | 1 | |
| Claim-183.a | claim | 8.3.2 | high Shannon entropy does not allow extraction (the `0ⁿ` w.p. 0.99 source) | Def-182.3 | P0 | optional | 1 | |
| Def-183.4 | definition | 8.3.2 | min-entropy | main's `HasMinEntropy` | P0 | core | 1 | cite; add the min-entropy value if needed |
| Def-183.5 | definition | 8.3.2 | `k`-source, `k`-flat source | Def-183.4 | P0 | core | 1 | |
| Thm-183.6 | theorem | 8.3.2 | no 1-bit `1/4`-extractor for efficiently computable `(n − 2)`-sources | Def-181.2, Def-183.5, his `Ensemble.Samplable` (PPT samplers) | D | core | 3 | **source gap:** the proof needs `Ext` poly-time ("`X` is computable since `Ext` is"), so restrict to efficient `Ext`. The statistical core is P0; the efficiency part needs his sampler model |
| §8.3.3 | section | 8.3.3 | leftover hash lemma | main's `leftover_hash` | P0 | core | 2 | heading only in the source. Cite main, and add the bridge "a universal family is a strong extractor for `k`-sources" in Def-181.2's terms |

## Counts

Counted from the rows above by script (the scope column of each chapter's table).

| Chapter | core | optional | deferred | out |
|---|---|---|---|---|
| 5 | 14 | 7 | 1 | 2 |
| 6 | 15 | 3 | 2 | 0 |
| 7 | 11 | 1 | 1 | 1 |
| 8 | 10 | 3 | 1 | 0 |
| **total** | **50** | **14** | **5** | **3** |

Core items by prong:
- **P0:** 11 (Shamir 5, extractor basics 6);
- **A:** 14;
- **B:** 10;
- **C:** 11;
- **D:** 4 (Def-179.a, Thm-179.1, Thm-180.1, Thm-183.6).

Prong D is small in items, but Thm-180.1 is machine-level and the hardest single item after
Thm-163.7.

## ===== TCSlib/Cryptography/Games.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.OracleComp
import TCSlib.Cryptography.Games.Probability
import TCSlib.Cryptography.Games.Simulate
import TCSlib.Cryptography.Games.Advantage
import TCSlib.Cryptography.Games.Hopping
import TCSlib.Cryptography.Games.Protocols

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Security games and protocols as oracle computations

One framework for the security games and the two-party protocols of [PS10] chapters 5–8:
- oracle computations, a free monad over an indexed family of oracles;
- uniform sampling as an oracle, with a real-valued, finite-sum probability;
- stateful oracle implementations with query logging, and simulation;
- the shapes of security advantages;
- the game-hopping lemmas;
- two-party executions.

It lives in the namespace `TCSlib.Cryptography.Games`. Its connections to the ch. 2–4 layer are
the next layer (S2b): the concrete layer's `QueryTree` and `uprob`, the machine model `NUPPT`, and
the interaction model `Strategy`.

## Contents

* `TCSlib.Cryptography.Games.OracleComp`: oracle specifications, oracle computations, unions,
  query costs.
* `TCSlib.Cryptography.Games.Probability`: the sampling oracle, expectations, probabilities,
  output distributions.
* `TCSlib.Cryptography.Games.Simulate`: oracle implementations, simulation, logging, composition.
* `TCSlib.Cryptography.Games.Advantage`: acceptance, distinguishing and guess-the-bit
  advantages, the hybrid argument.
* `TCSlib.Cryptography.Games.Hopping`: the difference lemma, identical until bad, the collision
  bound.
* `TCSlib.Cryptography.Games.Protocols`: parties, the message exchange, executions with D8's
  reading of the end, and traced executions recording views.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
* [VCVio] D. Tuma and the VCVio contributors, *VCVio: machine-checked cryptographic proofs in
  Lean*, https://github.com/dtumad/VCV-io, commit 9054989327a7185ff19ef9ff0f119cccea479501
  (2026-11-04), Apache License 2.0. Design adapted (no code transcribed): oracle specifications
  indexed by a type of oracle names (`VCVio/OracleComp/OracleSpec.lean`), oracle computations as
  a free monad over them (`OracleComp.lean`, `OracleQuery.lean`), probabilistic computations as
  computations over the uniform-selection oracles (`OracleComp/ProbComp/Basic.lean`), and
  simulation of oracles by stateful handlers with query logging and composition (`SimSemantics/`,
  `SimSemantics/QueryImpl/Compose.lean`, `QueryTracking/LoggingOracle`).
* [BR06] M. Bellare, P. Rogaway, *The security of triple encryption and a framework for
  code-based game-playing proofs*, EUROCRYPT 2006.
* [Sho04] V. Shoup, *Sequences of games: a tool for taming complexity in security proofs*, IACR
  ePrint 2004/332.
-/

## ===== TCSlib/Cryptography/Games/OracleComp.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Data.Nat.Notation

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Oracle computations

The syntax of security games and protocols. An *oracle specification* names a family of oracles,
each with a type of queries and a type of answers. An *oracle computation* over it asks one
oracle a query, looks at the answer, chooses what to do next, and eventually returns a value. It
is the free monad over the specification: a well-founded tree (every run makes finitely many
queries) whose inner nodes are queries, with one subtree per possible answer. With finite answer
types, as for probabilistic computations, the tree is finite.

Everything else in the framework is built on this file:
- uniform sampling is one more oracle (`TCSlib.Cryptography.Games.Probability`);
- running a computation against implementations of its oracles is `simulate`
  (`TCSlib.Cryptography.Games.Simulate`);
- a two-party protocol is a pair of computations whose oracle is the message exchange
  (`TCSlib.Cryptography.Games.Protocols`).

With one oracle, an oracle computation is a `TCSlib.Cryptography.QueryTree` of the concrete
layer ([Gar26]); the bridge between the two is in the S2b layer.

## Main definitions

* `Games.OracleSpec ι`: a family of oracles named by `ι`.
* `Games.OracleComp spec α`: computations with access to the oracles of `spec`, returning an `α`;
  a `Monad` and a `LawfulMonad`.
* `Games.OracleComp.call i x`: ask oracle `i` the query `x` and return the answer.
* `Games.OracleSpec.add`: the disjoint union of two oracle families;
  `OracleComp.liftLeft`/`liftRight` run a computation over one part in the union.
* `Games.OracleComp.CostBoundedBy cost c q`: every run of `c` spends at most `q`, oracle `i`
  costing `cost i` per query (for example, 1 for the oracle under attack and 0 for coin draws).

## Main results

* `Games.OracleComp.instLawfulMonad`: the monad laws.
* `Games.OracleComp.CostBoundedBy.bind`: costs add under sequencing.
* `Games.OracleComp.costBoundedBy_liftLeft`, `costBoundedBy_liftRight`: lifting into a union of
  specifications keeps the cost.

## References

* [VCVio] D. Tuma and the VCVio contributors, *VCVio: machine-checked cryptographic proofs in
  Lean*, https://github.com/dtumad/VCV-io, commit 9054989327a7185ff19ef9ff0f119cccea479501
  (2026-11-04), Apache License 2.0. Design adapted (no code transcribed): oracle specifications
  indexed by a type of oracle names (`VCVio/OracleComp/OracleSpec.lean`), oracle computations as
  a free monad over them (`OracleComp.lean`, `OracleQuery.lean`), probabilistic computations as
  computations over the uniform-selection oracles (`OracleComp/ProbComp/Basic.lean`), and
  simulation of oracles by stateful handlers with query logging and composition (`SimSemantics/`,
  `SimSemantics/QueryImpl/Compose.lean`, `QueryTracking/LoggingOracle`).
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley, draft of
  22 January 2026, Definition 3.9 (oracle adversaries).
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §3.8.1 (oracle machines).
-/

namespace TCSlib.Cryptography.Games

/-- A **family of oracles** named by `ι`: oracle `i` accepts queries in `dom i` and answers in
`rng i`. [VCVio, OracleComp/OracleSpec] -/
structure OracleSpec (ι : Type) where
  /-- The queries oracle `i` accepts. -/
  dom : ι → Type
  /-- The answers oracle `i` gives. -/
  rng : ι → Type

/-- **Oracle computations** over `spec` returning an `α`: either return a value, or ask oracle
`i` the query `x` and continue with `k` applied to the answer. This is the free monad over
`spec`; an oracle adversary of [Gar26, Definition 3.9] or [PS10, §3.8.1] with fixed coins is the
one-oracle case. [VCVio, OracleComp/OracleComp] -/
inductive OracleComp {ι : Type} (spec : OracleSpec ι) (α : Type) : Type where
  /-- Return `a` without further queries. -/
  | pure : α → OracleComp spec α
  /-- Ask oracle `i` the query `x`, and continue with `k` on the answer. -/
  | query (i : ι) (x : spec.dom i) (k : spec.rng i → OracleComp spec α) : OracleComp spec α

namespace OracleComp

variable {ι ι₁ ι₂ : Type} {spec : OracleSpec ι} {α β γ : Type}

/-- Sequencing: run `c`, then `f` on its result. Queries of `c` come first. -/
def bind : OracleComp spec α → (α → OracleComp spec β) → OracleComp spec β
  | .pure a, f => f a
  | .query i x k, f => .query i x (fun y => bind (k y) f)

instance : Monad (OracleComp spec) where
  pure := .pure
  bind := bind

/-- `>>=` is `OracleComp.bind`. -/
theorem bind_eq_bind (c : OracleComp spec α) (f : α → OracleComp spec β) :
    (c >>= f) = c.bind f := rfl

/-- `pure` is the constructor `OracleComp.pure`. -/
theorem pure_eq_pure (a : α) : (Pure.pure a : OracleComp spec α) = .pure a := rfl

/-- `<$>` is sequencing with a return. -/
theorem map_eq_bind (h : α → β) (c : OracleComp spec α) :
    (h <$> c) = c.bind (fun a => .pure (h a)) := rfl

/-- Returning first, then continuing, is continuing. -/
@[simp] theorem pure_bind (a : α) (f : α → OracleComp spec β) : (OracleComp.pure a).bind f = f a :=
  rfl

/-- A query followed by `f` is the query whose continuation is followed by `f`. -/
@[simp] theorem query_bind (i : ι) (x : spec.dom i) (k : spec.rng i → OracleComp spec α)
    (f : α → OracleComp spec β) :
    (OracleComp.query i x k).bind f = .query i x (fun y => (k y).bind f) := rfl

/-- Continuing with a return changes nothing. -/
@[simp] theorem bind_pure (c : OracleComp spec α) : c.bind .pure = c := by
  induction c with
  | pure a => rfl
  | query i x k ih => simp only [query_bind, ih]

/-- Sequencing is associative. -/
theorem bind_assoc (c : OracleComp spec α) (f : α → OracleComp spec β)
    (g : β → OracleComp spec γ) : (c.bind f).bind g = c.bind (fun a => (f a).bind g) := by
  induction c with
  | pure a => rfl
  | query i x k ih => simp only [query_bind, ih]

/-- The monad laws. -/
instance instLawfulMonad : LawfulMonad (OracleComp spec) :=
  LawfulMonad.mk' _
    (id_map := fun c => bind_pure c)
    (pure_bind := fun _ _ => rfl)
    (bind_assoc := fun c f g => bind_assoc c f g)

/-- Ask oracle `i` the query `x` and return the answer. -/
def call (i : ι) (x : spec.dom i) : OracleComp spec (spec.rng i) :=
  .query i x .pure

/-- Asking and then continuing with `f` is the query with continuation `f`. -/
@[simp] theorem call_bind (i : ι) (x : spec.dom i) (f : spec.rng i → OracleComp spec α) :
    (call i x).bind f = .query i x f := rfl

/-! ### Unions of oracle families -/

end OracleComp

/-- The **disjoint union** of two oracle families: oracle `.inl i` is oracle `i` of `s₁`, and
oracle `.inr j` is oracle `j` of `s₂`. [VCVio, OracleComp/OracleSpec] -/
def OracleSpec.add {ι₁ ι₂ : Type} (s₁ : OracleSpec ι₁) (s₂ : OracleSpec ι₂) :
    OracleSpec (ι₁ ⊕ ι₂) :=
  ⟨Sum.elim s₁.dom s₂.dom, Sum.elim s₁.rng s₂.rng⟩

namespace OracleComp

variable {ι ι₁ ι₂ : Type} {α β : Type}

/-- Run a computation over `s₁` inside the union `s₁.add s₂`, asking only oracles of `s₁`. -/
def liftLeft {s₁ : OracleSpec ι₁} {s₂ : OracleSpec ι₂} :
    OracleComp s₁ α → OracleComp (s₁.add s₂) α
  | .pure a => .pure a
  | .query i x k => .query (.inl i) x (fun y => liftLeft (k y))

/-- Run a computation over `s₂` inside the union `s₁.add s₂`, asking only oracles of `s₂`. -/
def liftRight {s₁ : OracleSpec ι₁} {s₂ : OracleSpec ι₂} :
    OracleComp s₂ α → OracleComp (s₁.add s₂) α
  | .pure a => .pure a
  | .query j x k => .query (.inr j) x (fun y => liftRight (k y))

/-- Lifting commutes with sequencing. -/
theorem liftLeft_bind {s₁ : OracleSpec ι₁} {s₂ : OracleSpec ι₂} (c : OracleComp s₁ α)
    (f : α → OracleComp s₁ β) :
    (liftLeft (s₂ := s₂) (c.bind f)) = (liftLeft c).bind (fun a => liftLeft (f a)) := by
  induction c with
  | pure a => rfl
  | query i x k ih => simp only [query_bind, liftLeft, ih]

/-- Lifting commutes with sequencing. -/
theorem liftRight_bind {s₁ : OracleSpec ι₁} {s₂ : OracleSpec ι₂} (c : OracleComp s₂ α)
    (f : α → OracleComp s₂ β) :
    (liftRight (s₁ := s₁) (c.bind f)) = (liftRight c).bind (fun a => liftRight (f a)) := by
  induction c with
  | pure a => rfl
  | query j x k ih => simp only [query_bind, liftRight, ih]

/-! ### Query costs -/

variable {spec : OracleSpec ι₁}

/-- `c` is **cost-bounded by `q`**: along every run, the total cost of its queries, oracle `i`
costing `cost i` per query, is at most `q`. With `cost` equal to 1 on the oracle under attack and
0 elsewhere, this is "at most `q` queries to that oracle", the query bound of
[Gar26, Definition 3.9]. -/
def CostBoundedBy (cost : ι₁ → ℕ) : OracleComp spec α → ℕ → Prop
  | .pure _, _ => True
  | .query i _ k, q => cost i ≤ q ∧ ∀ y, CostBoundedBy cost (k y) (q - cost i)

/-- A return costs nothing. -/
@[simp] theorem costBoundedBy_pure (cost : ι₁ → ℕ) (a : α) (q : ℕ) :
    CostBoundedBy cost (OracleComp.pure (spec := spec) a) q :=
  trivial

/-- A query is within budget `q` exactly when its cost fits and every continuation fits in what
is left. -/
@[simp] theorem costBoundedBy_query (cost : ι₁ → ℕ) (i : ι₁) (x : spec.dom i)
    (k : spec.rng i → OracleComp spec α) (q : ℕ) :
    CostBoundedBy cost (OracleComp.query i x k) q ↔
      cost i ≤ q ∧ ∀ y, CostBoundedBy cost (k y) (q - cost i) :=
  Iff.rfl

/-- A larger budget is still a bound. -/
theorem CostBoundedBy.mono {cost : ι₁ → ℕ} {c : OracleComp spec α} {q q' : ℕ}
    (h : CostBoundedBy cost c q) (hq : q ≤ q') : CostBoundedBy cost c q' := by
  induction c generalizing q q' with
  | pure a => trivial
  | query i x k ih =>
    obtain ⟨hi, hk⟩ := h
    exact ⟨Nat.le_trans hi hq, fun y => ih y (hk y) (Nat.sub_le_sub_right hq _)⟩

/-- **Costs add under sequencing:** if `c` fits in `q₁` and every continuation `f a` fits in
`q₂`, then `c` followed by `f` fits in `q₁ + q₂`.

**Proof sketch.** Induction on `c`. At a query of cost `cost i ≤ q₁`, the continuation fits in
`q₁ - cost i` by hypothesis, so by induction it fits in `(q₁ - cost i) + q₂`, which is
`(q₁ + q₂) - cost i`. -/
theorem CostBoundedBy.bind {cost : ι₁ → ℕ} {c : OracleComp spec α} {f : α → OracleComp spec β}
    {q₁ q₂ : ℕ} (hc : CostBoundedBy cost c q₁) (hf : ∀ a, CostBoundedBy cost (f a) q₂) :
    CostBoundedBy cost (c.bind f) (q₁ + q₂) := by
  induction c generalizing q₁ with
  | pure a => exact (hf a).mono (Nat.le_add_left _ _)
  | query i x k ih =>
    obtain ⟨hi, hk⟩ := hc
    refine ⟨Nat.le_trans hi (Nat.le_add_right _ _), fun y => ?_⟩
    rw [Nat.sub_add_comm hi]
    exact ih y (hk y)

/-- Lifting into a union keeps the cost, when the union's cost agrees with the original on the
left part. -/
theorem costBoundedBy_liftLeft {s₂ : OracleSpec ι₂} {cost : ι₁ ⊕ ι₂ → ℕ} {c : OracleComp spec α}
    {q : ℕ} (h : CostBoundedBy (fun i => cost (.inl i)) c q) :
    CostBoundedBy cost (liftLeft (s₂ := s₂) c) q := by
  induction c generalizing q with
  | pure a => trivial
  | query i x k ih => exact ⟨h.1, fun y => ih y (h.2 y)⟩

/-- Lifting into a union keeps the cost, when the union's cost agrees with the original on the
right part. -/
theorem costBoundedBy_liftRight {s₁ : OracleSpec ι₂} {cost : ι₂ ⊕ ι₁ → ℕ}
    {c : OracleComp spec α} {q : ℕ} (h : CostBoundedBy (fun j => cost (.inr j)) c q) :
    CostBoundedBy cost (liftRight (s₁ := s₁) c) q := by
  induction c generalizing q with
  | pure a => trivial
  | query j x k ih => exact ⟨h.1, fun y => ih y (h.2 y)⟩

end OracleComp

end TCSlib.Cryptography.Games

## ===== TCSlib/Cryptography/Games/Probability.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.OracleComp
import TCSlib.InformationTheory.FinDist

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Probabilistic computations

Randomness enters the framework as one more oracle: oracle `m` of `unifSpec` answers a uniformly
random element of `Fin (m + 1)`, and a uniform element of any nonempty finite type is obtained
through an enumeration. A *probabilistic computation* (`ProbComp`) is an oracle computation whose
only oracle is this one. Security games, once their adversary is plugged in and their oracles
implemented, are probabilistic computations.

The semantics is elementary and real-valued. The expectation of `g` over the output of a
computation is defined by recursion on the computation: a return contributes `g a`, and a sampling
step averages over its `m + 1` equally likely answers. There are no measures and no extended
reals: every computation is a finite tree with finite branching, so every probability is a finite
sum of rationals. The probability of an event is the expectation of its indicator. For a
computation with a finite output type, its output distribution is a `FinDist` of the library's
information-theory layer, so statistical distance and closeness (`EpsClose`) apply directly.

## Main definitions

* `Games.unifSpec`: the uniform-sampling oracles; `Games.ProbComp`: computations over them.
* `Games.ProbComp.sampleFin m`, `Games.ProbComp.sample T`: a uniform element of `Fin (m + 1)`, and
  of a nonempty finite type `T`.
* `Games.ProbComp.expect c g`: the expectation of `g` over the output of `c`.
* `Games.ProbComp.prob c p`: the probability that the output of `c` satisfies `p`.
* `Games.ProbComp.dist c`: the output distribution of `c`, for a finite output type.

## Main results

* `ProbComp.expect_bind`: **total expectation**; sequencing averages the continuations.
* `ProbComp.expect_sample`: sampling a finite type is the uniform average.
* `ProbComp.expect_add`, `expect_const_mul`, `expect_sum`, `expect_mono`: linearity and
  monotonicity.
* `ProbComp.prob_nonneg`, `prob_le_one`, `prob_mono`, `prob_or_le` (the union bound),
  `prob_not`, `prob_bind`.

## References

* [VCVio] D. Tuma and the VCVio contributors, *VCVio: machine-checked cryptographic proofs in
  Lean*, https://github.com/dtumad/VCV-io, commit 9054989327a7185ff19ef9ff0f119cccea479501
  (2026-11-04), Apache License 2.0. Design adapted (no code transcribed): oracle specifications
  indexed by a type of oracle names (`VCVio/OracleComp/OracleSpec.lean`), oracle computations as
  a free monad over them (`OracleComp.lean`, `OracleQuery.lean`), probabilistic computations as
  computations over the uniform-selection oracles (`OracleComp/ProbComp/Basic.lean`), and
  simulation of oracles by stateful handlers with query logging and composition (`SimSemantics/`,
  `SimSemantics/QueryImpl/Compose.lean`, `QueryTracking/LoggingOracle`).
  Uniform sampling as an oracle follows VCVio's uniform-selection oracle; the real-valued
  finite-sum semantics here is not VCVio's (which is measure-valued).
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §2.1 (probabilistic algorithms; the uniform distribution over coin strings).
-/

namespace TCSlib.Cryptography.Games

open Finset TCSlib.InformationTheory

/-- The **uniform-sampling oracles**: oracle `m` takes no query and answers a uniformly random
element of `Fin (m + 1)`. [VCVio, OracleComp/ProbComp] -/
abbrev unifSpec : OracleSpec ℕ := ⟨fun _ => Unit, fun m => Fin (m + 1)⟩

/-- **Probabilistic computations**: oracle computations whose only oracles draw uniform samples.
[VCVio, OracleComp/ProbComp/Basic] -/
abbrev ProbComp := OracleComp unifSpec

namespace ProbComp

variable {α β : Type}

/-- A uniformly random element of `Fin (m + 1)`. [VCVio, OracleComp/ProbComp/Basic (uniformFin)] -/
def sampleFin (m : ℕ) : ProbComp (Fin (m + 1)) := .query m () .pure

/-- A uniformly random element of the nonempty finite type `T`, through its enumeration
`Fintype.equivFin`. -/
noncomputable def sample (T : Type) [Fintype T] [Nonempty T] : ProbComp T :=
  (fun j : Fin (Fintype.card T - 1 + 1) =>
    (Fintype.equivFin T).symm (Fin.cast (Nat.sub_add_cancel Fintype.card_pos) j)) <$>
      sampleFin (Fintype.card T - 1)

/-- The **expectation** of `g` over the output of `c`: `g a` for a return, and the average over
the `m + 1` equally likely answers at a sampling step. -/
noncomputable def expect : ProbComp α → (α → ℝ) → ℝ
  | .pure a, g => g a
  | .query m _ k, g => ((m : ℝ) + 1)⁻¹ * ∑ j : Fin (m + 1), expect (k j) g

/-- The **probability** that the output of `c` satisfies `p`: the expectation of the indicator
of `p`. -/
noncomputable def prob (c : ProbComp α) (p : α → Prop) : ℝ := by
  classical exact expect c (fun a => if p a then 1 else 0)

/-- A return is its own expectation. -/
@[simp] theorem expect_pure (a : α) (g : α → ℝ) : expect (.pure a) g = g a := rfl

/-- A sampling step averages over its answers. -/
theorem expect_query (m : ℕ) (x : Unit) (k : Fin (m + 1) → ProbComp α) (g : α → ℝ) :
    expect (.query m x k) g = ((m : ℝ) + 1)⁻¹ * ∑ j : Fin (m + 1), expect (k j) g := rfl

/-- **Total expectation:** the expectation over `c` followed by `f` is the expectation over `c`
of the expectation over `f a`.

**Proof sketch.** Induction on `c`: a return is immediate, and at a sampling step both sides
average the same continuations. -/
theorem expect_bind (c : ProbComp α) (f : α → ProbComp β) (g : β → ℝ) :
    expect (c.bind f) g = expect c (fun a => expect (f a) g) := by
  induction c with
  | pure a => rfl
  | query m x k ih => simp only [OracleComp.query_bind, expect_query, ih]

/-- The expectation over a mapped computation is the expectation of the composite. -/
theorem expect_map (h : α → β) (c : ProbComp α) (g : β → ℝ) :
    expect (h <$> c) g = expect c (fun a => g (h a)) := by
  rw [OracleComp.map_eq_bind, expect_bind]; rfl

/-- Sampling `Fin (m + 1)` is the uniform average over it. -/
theorem expect_sampleFin (m : ℕ) (g : Fin (m + 1) → ℝ) :
    expect (sampleFin m) g = ((m : ℝ) + 1)⁻¹ * ∑ j, g j := rfl

/-- Sampling a nonempty finite type is the uniform average over it.

**Proof sketch.** The sample is the image of a uniform element of `Fin |T|` under the bijection
`Fintype.equivFin`, and a sum is invariant under reindexing by a bijection. -/
theorem expect_sample (T : Type) [Fintype T] [Nonempty T] (g : T → ℝ) :
    expect (sample T) g = (Fintype.card T : ℝ)⁻¹ * ∑ t, g t := by
  have hc : Fintype.card T - 1 + 1 = Fintype.card T := Nat.sub_add_cancel Fintype.card_pos
  rw [sample, expect_map, expect_sampleFin]
  congr 1
  · congr 1
    exact_mod_cast hc
  · exact Fintype.sum_equiv ((finCongr hc).trans (Fintype.equivFin T).symm) _ _
      (fun j => by simp)

/-- Expectation is additive. -/
theorem expect_add (c : ProbComp α) (f g : α → ℝ) :
    expect c (fun a => f a + g a) = expect c f + expect c g := by
  induction c with
  | pure a => rfl
  | query m x k ih => simp only [expect_query, ih, sum_add_distrib, mul_add]

/-- Expectation commutes with scaling by a constant. -/
theorem expect_const_mul (c : ProbComp α) (r : ℝ) (f : α → ℝ) :
    expect c (fun a => r * f a) = r * expect c f := by
  induction c with
  | pure a => rfl
  | query m x k ih =>
    simp only [expect_query, ih, ← mul_sum]
    ring

/-- The expectation of a constant is that constant. -/
theorem expect_const (c : ProbComp α) (r : ℝ) : expect c (fun _ => r) = r := by
  induction c with
  | pure a => rfl
  | query m x k ih =>
    simp only [expect_query, ih, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]
    have : (m : ℝ) + 1 ≠ 0 := by positivity
    push_cast
    field_simp

/-- Expectation commutes with finite sums. -/
theorem expect_sum {ι : Type} (c : ProbComp α) (s : Finset ι) (f : ι → α → ℝ) :
    expect c (fun a => ∑ i ∈ s, f i a) = ∑ i ∈ s, expect c (f i) := by
  induction c with
  | pure a => rfl
  | query m x k ih =>
    simp only [expect_query, ih, mul_sum]
    exact sum_comm

/-- Expectation is monotone. -/
theorem expect_mono (c : ProbComp α) {f g : α → ℝ} (h : ∀ a, f a ≤ g a) :
    expect c f ≤ expect c g := by
  induction c with
  | pure a => exact h a
  | query m x k ih =>
    simp only [expect_query]
    exact mul_le_mul_of_nonneg_left (sum_le_sum fun j _ => ih j) (by positivity)

/-- The expectation of a nonnegative function is nonnegative. -/
theorem expect_nonneg (c : ProbComp α) {f : α → ℝ} (h : ∀ a, 0 ≤ f a) : 0 ≤ expect c f := by
  simpa [expect_const] using expect_mono c (f := fun _ => 0) h

/-! ### Probabilities of events -/

/-- The probability of `p` is the expectation of its indicator (any decidability instance). -/
theorem prob_eq_expect (c : ProbComp α) (p : α → Prop) [DecidablePred p] :
    prob c p = expect c (fun a => if p a then 1 else 0) := by
  unfold prob
  congr 1
  funext a
  congr 1

/-- A return satisfies `p` with probability one or zero. -/
theorem prob_pure (a : α) (p : α → Prop) [Decidable (p a)] :
    prob (.pure a) p = if p a then 1 else 0 := by
  classical
  rw [prob_eq_expect, expect_pure]
  congr 1

/-- **Total probability:** the probability over `c` followed by `f` is the expectation over `c`
of the probability over `f a`. -/
theorem prob_bind (c : ProbComp α) (f : α → ProbComp β) (p : β → Prop) :
    prob (c.bind f) p = expect c (fun a => prob (f a) p) := by
  classical
  simp only [prob_eq_expect, expect_bind]

/-- Probabilities are nonnegative. -/
theorem prob_nonneg (c : ProbComp α) (p : α → Prop) : 0 ≤ prob c p := by
  classical
  rw [prob_eq_expect]
  exact expect_nonneg c fun a => by split_ifs <;> norm_num

/-- Probabilities are at most one. -/
theorem prob_le_one (c : ProbComp α) (p : α → Prop) : prob c p ≤ 1 := by
  classical
  rw [prob_eq_expect]
  calc expect c (fun a => if p a then (1 : ℝ) else 0) ≤ expect c (fun _ => 1) :=
        expect_mono c fun a => by split_ifs <;> norm_num
    _ = 1 := expect_const c 1

/-- An event implied by another has at least its probability. -/
theorem prob_mono (c : ProbComp α) {p q : α → Prop} (h : ∀ a, p a → q a) :
    prob c p ≤ prob c q := by
  classical
  rw [prob_eq_expect, prob_eq_expect]
  exact expect_mono c fun a => by
    by_cases hp : p a
    · simp [hp, h a hp]
    · simp only [hp, if_false]; split_ifs <;> norm_num

/-- Events that agree on every output have the same probability. -/
theorem prob_congr (c : ProbComp α) {p q : α → Prop} (h : ∀ a, p a ↔ q a) :
    prob c p = prob c q :=
  le_antisymm (prob_mono c fun a => (h a).1) (prob_mono c fun a => (h a).2)

/-- **The union bound** for two events. -/
theorem prob_or_le (c : ProbComp α) (p q : α → Prop) :
    prob c (fun a => p a ∨ q a) ≤ prob c p + prob c q := by
  classical
  rw [prob_eq_expect, prob_eq_expect, prob_eq_expect, ← expect_add]
  exact expect_mono c fun a => by
    by_cases hp : p a <;> by_cases hq : q a <;> simp [hp, hq]

/-- The complement of an event has one minus its probability. -/
theorem prob_not (c : ProbComp α) (p : α → Prop) :
    prob c (fun a => ¬ p a) = 1 - prob c p := by
  classical
  rw [prob_eq_expect, prob_eq_expect, eq_sub_iff_add_eq, ← expect_add]
  calc expect c (fun a => (if ¬ p a then (1 : ℝ) else 0) + if p a then 1 else 0)
      = expect c (fun _ => 1) := by
        congr 1; funext a; by_cases hp : p a <;> simp [hp]
    _ = 1 := expect_const c 1

/-! ### Output distributions -/

/-- The **output distribution** of a computation with a finite output type: the probability of
each outcome. -/
noncomputable def dist [Fintype α] [DecidableEq α] (c : ProbComp α) : FinDist α where
  prob a := prob c (· = a)
  nonneg a := prob_nonneg c _
  sum_prob := by
    simp only [prob_eq_expect]
    rw [← expect_sum]
    calc expect c (fun x => ∑ a, if x = a then (1 : ℝ) else 0) = expect c (fun _ => 1) := by
          congr 1; funext x; simp
      _ = 1 := expect_const c 1

/-- The output distribution gives each outcome its probability. -/
theorem dist_apply [Fintype α] [DecidableEq α] (c : ProbComp α) (a : α) :
    dist c a = prob c (· = a) := rfl

end ProbComp

end TCSlib.Cryptography.Games

## ===== TCSlib/Cryptography/Games/Simulate.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.OracleComp

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Implementing oracles: simulation and logging

An oracle computation only *asks* its oracles. A security game decides how they answer: with a
keyed function, with fresh coins on every query (a randomized encryption oracle), refusing some
queries (a CCA2 decryption oracle that will not decrypt the challenge), or by asking other
oracles (a reduction that answers its adversary's queries with queries of its own). All of these
are *implementations*: for each oracle and query, a computation over a target specification that
returns the answer and updates a state. `simulate` runs a computation with every query answered
by an implementation, threading the state.

Logging is an implementation transformer: it answers as before and also appends every query and
its answer to a log kept in the state. Win conditions such as "the forged message was never
queried" are predicates on that log. Logging never changes the computation
(`simulate_withLog`).

## Main definitions

* `Games.QueryImpl spec σ spec'`: implementations of the oracles of `spec` by computations over
  `spec'`, with state `σ`.
* `Games.simulate impl c s`: run `c` from state `s`, answering its queries with `impl`.
* `Games.QueryImpl.ofComp`, `QueryImpl.passthrough`, `QueryImpl.sum`: stateless implementations,
  forwarding queries unchanged, and implementing two oracle families side by side.
* `Games.QueryLog spec`, `Games.QueryImpl.withLog`: the record of a run's queries and answers, and
  the logging transformer.
* `Games.QueryImpl.comp`: answering one implementation's queries with another.

## Main results

* `Games.simulate_bind`: simulation commutes with sequencing.
* `Games.simulate_withLog`: forgetting the log of a logged simulation gives the plain simulation.
* `Games.simulate_comp`: simulation composes; a reduction run against an implementation of its
  oracles is a single implementation of its adversary's oracles.
* `Games.simulate_costBoundedBy`: if each query of `c` to oracle `i` is answered by a computation
  of cost at most `b i`, and `c` is cost-bounded by `q` when oracle `i` costs `b i`, then the
  simulation is cost-bounded by `q`.

## References

* [VCVio] D. Tuma and the VCVio contributors, *VCVio: machine-checked cryptographic proofs in
  Lean*, https://github.com/dtumad/VCV-io, commit 9054989327a7185ff19ef9ff0f119cccea479501
  (2026-11-04), Apache License 2.0. Design adapted (no code transcribed): oracle specifications
  indexed by a type of oracle names (`VCVio/OracleComp/OracleSpec.lean`), oracle computations as
  a free monad over them (`OracleComp.lean`, `OracleQuery.lean`), probabilistic computations as
  computations over the uniform-selection oracles (`OracleComp/ProbComp/Basic.lean`), and
  simulation of oracles by stateful handlers with query logging and composition (`SimSemantics/`,
  `SimSemantics/QueryImpl/Compose.lean`, `QueryTracking/LoggingOracle`).
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley, draft of
  22 January 2026, Definition 3.9 (answering an adversary's queries in a reduction).
-/

namespace TCSlib.Cryptography.Games

variable {ι ι' ι₁ ι₂ : Type} {α β σ : Type}

/-- An **implementation** of the oracles of `spec` by computations over `spec'`, with state `σ`:
on oracle `i`, query `x` and state `s`, a computation returning the answer and the new state.
[VCVio, SimSemantics] -/
def QueryImpl {ι ι' : Type} (spec : OracleSpec ι) (σ : Type) (spec' : OracleSpec ι') : Type :=
  ∀ i, spec.dom i → σ → OracleComp spec' (spec.rng i × σ)

/-- **Simulation:** run `c` from state `s`, answering each of its queries with `impl` and
threading the state; return `c`'s result and the final state. [VCVio, SimSemantics] -/
def simulate {spec : OracleSpec ι} {spec' : OracleSpec ι'} (impl : QueryImpl spec σ spec') :
    OracleComp spec α → σ → OracleComp spec' (α × σ)
  | .pure a, s => .pure (a, s)
  | .query i x k, s => (impl i x s).bind (fun ys => simulate impl (k ys.1) ys.2)

section Simulate

variable {spec : OracleSpec ι} {spec' : OracleSpec ι'} (impl : QueryImpl spec σ spec')

/-- Simulating a return returns it with the state unchanged. -/
@[simp] theorem simulate_pure (a : α) (s : σ) :
    simulate impl (OracleComp.pure a) s = .pure (a, s) := rfl

/-- Simulating a query runs the implementation, then simulates the continuation. -/
@[simp] theorem simulate_query (i : ι) (x : spec.dom i) (k : spec.rng i → OracleComp spec α)
    (s : σ) :
    simulate impl (OracleComp.query i x k) s =
      (impl i x s).bind (fun ys => simulate impl (k ys.1) ys.2) := rfl

/-- **Simulation commutes with sequencing:** simulating `c` followed by `f` is simulating `c`,
then simulating `f` on its result from the state it reached.

**Proof sketch.** Induction on `c`; at a query, both sides run the implementation first, and the
monad's associativity lines up the continuations. -/
theorem simulate_bind (c : OracleComp spec α) (f : α → OracleComp spec β) (s : σ) :
    simulate impl (c.bind f) s = (simulate impl c s).bind (fun p => simulate impl (f p.1) p.2) := by
  induction c generalizing s with
  | pure a => rfl
  | query i x k ih => simp only [OracleComp.query_bind, simulate_query, OracleComp.bind_assoc, ih]

/-- Simulating a single call is running the implementation. -/
theorem simulate_call (i : ι) (x : spec.dom i) (s : σ) :
    simulate impl (OracleComp.call i x) s = impl i x s := by
  simp only [OracleComp.call, simulate_query, simulate_pure]
  exact OracleComp.bind_pure _

end Simulate

namespace QueryImpl

/-- A **stateless** implementation: oracle `i` answers query `x` by running `f i x`. -/
def ofComp {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    (f : ∀ i, spec.dom i → OracleComp spec' (spec.rng i)) : QueryImpl spec σ spec' :=
  fun i x s => (f i x).bind (fun y => .pure (y, s))

/-- **Forwarding:** every query is passed unchanged to the same oracle of the target. -/
def passthrough {spec : OracleSpec ι} : QueryImpl spec σ spec :=
  ofComp (fun i x => OracleComp.call i x)

/-- Implement two oracle families **side by side**, sharing one state: `.inl i` is answered by
`impl₁`, and `.inr j` by `impl₂`. -/
def sum {s₁ : OracleSpec ι₁} {s₂ : OracleSpec ι₂} {spec' : OracleSpec ι'}
    (impl₁ : QueryImpl s₁ σ spec') (impl₂ : QueryImpl s₂ σ spec') :
    QueryImpl (s₁.add s₂) σ spec'
  | .inl i => impl₁ i
  | .inr j => impl₂ j

end QueryImpl

/-! ### Composing implementations -/

/-- **Composition:** answer the queries of `spec` with `impl₁`, whose own queries (to `spec'`)
are answered by `impl₂`; the state is the pair of the two states. This is how a reduction that
answers its adversary's queries by querying its own oracles becomes, after its oracles are
implemented, a single implementation of the adversary's oracles.
[VCVio, SimSemantics/QueryImpl/Compose (QueryImpl.compose)] -/
def QueryImpl.comp {ι'' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    {spec'' : OracleSpec ι''} {σ₁ σ₂ : Type} (impl₂ : QueryImpl spec' σ₂ spec'')
    (impl₁ : QueryImpl spec σ₁ spec') : QueryImpl spec (σ₁ × σ₂) spec'' :=
  fun i x s => (simulate impl₂ (impl₁ i x s.1) s.2).bind (fun p => .pure (p.1.1, (p.1.2, p.2)))

/-- **Simulation composes:** simulating with `impl₂` a simulation by `impl₁` is simulating once
with the composed implementation, up to regrouping the states.
[VCVio, SimSemantics/QueryImpl/Compose (simulateQ_compose)]

**Proof sketch.** Induction on the computation. At a query, both sides first run `impl₁`'s answer
under `impl₂` (`simulate_bind` on the left, the definition of `comp` on the right), and the
continuations agree by induction after associativity. -/
theorem simulate_comp {ι'' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    {spec'' : OracleSpec ι''} {σ₁ σ₂ : Type} (impl₂ : QueryImpl spec' σ₂ spec'')
    (impl₁ : QueryImpl spec σ₁ spec') (c : OracleComp spec α) (s₁ : σ₁) (s₂ : σ₂) :
    simulate impl₂ (simulate impl₁ c s₁) s₂ =
      (simulate (impl₂.comp impl₁) c (s₁, s₂)).bind (fun p => .pure ((p.1, p.2.1), p.2.2)) := by
  induction c generalizing s₁ s₂ with
  | pure a => rfl
  | query i x k ih =>
    simp only [simulate_query, simulate_bind, QueryImpl.comp, OracleComp.bind_assoc,
      OracleComp.pure_bind]
    congr 1
    funext p
    exact ih p.1.1 p.1.2 p.2

/-! ### Logging -/

/-- The **log** of a run: the list of its queries, each with the oracle asked, the query and the
answer, in order. [VCVio, QueryTracking/LoggingOracle] -/
abbrev QueryLog {ι : Type} (spec : OracleSpec ι) : Type :=
  List (Σ i, spec.dom i × spec.rng i)

/-- **Logging:** answer as `impl` does, and append each query and its answer to the log kept
beside the state. [VCVio, QueryTracking/LoggingOracle] -/
def QueryImpl.withLog {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    (impl : QueryImpl spec σ spec') : QueryImpl spec (σ × QueryLog spec) spec' :=
  fun i x s => (impl i x s.1).bind (fun ys => .pure (ys.1, (ys.2, s.2 ++ [⟨i, x, ys.1⟩])))

/-- **Logging is conservative:** forgetting the log of a logged simulation gives the plain
simulation, whatever the initial log.

**Proof sketch.** Induction on the computation: at a query, the logged implementation is the
plain one followed by a return that only extends the log, and the continuations agree by
induction. -/
theorem simulate_withLog {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    (impl : QueryImpl spec σ spec') (c : OracleComp spec α) (s : σ) (log : QueryLog spec) :
    (simulate impl.withLog c (s, log)).bind (fun p => .pure (p.1, p.2.1)) =
      simulate impl c s := by
  induction c generalizing s log with
  | pure a => rfl
  | query i x k ih =>
    simp only [simulate_query, QueryImpl.withLog, OracleComp.bind_assoc, OracleComp.pure_bind]
    congr 1
    funext ys
    exact ih ys.1 ys.2 _

/-! ### Costs under simulation -/

/-- **Costs under simulation:** if every call to oracle `i` is answered by a computation of cost
at most `b i` (target costs `cost'`), and `c` is cost-bounded by `q` when oracle `i` costs
`b i`, then the simulation of `c` is cost-bounded by `q`. With `b i = 1` for every oracle the
reduction asks once per query, the reduction makes no more target queries than its adversary
makes queries.

**Proof sketch.** Induction on `c`. At a query to oracle `i` with budget `q ≥ b i`, the
implementation fits in `b i`, and the simulated continuation fits in `q - b i` by induction, so
the sequence fits in `b i + (q - b i) = q` (`CostBoundedBy.bind`). -/
theorem simulate_costBoundedBy {spec : OracleSpec ι} {spec' : OracleSpec ι'}
    {impl : QueryImpl spec σ spec'} {cost' : ι' → ℕ} {b : ι → ℕ}
    (himpl : ∀ i x s, OracleComp.CostBoundedBy cost' (impl i x s) (b i))
    {c : OracleComp spec α} {q : ℕ} (hc : OracleComp.CostBoundedBy b c q) (s : σ) :
    OracleComp.CostBoundedBy cost' (simulate impl c s) q := by
  induction c generalizing q s with
  | pure a => trivial
  | query i x k ih =>
    obtain ⟨hi, hk⟩ := hc
    have h := OracleComp.CostBoundedBy.bind (himpl i x s) (fun ys => ih ys.1 (hk ys.1) ys.2)
    rwa [Nat.add_sub_cancel' hi] at h

end TCSlib.Cryptography.Games

## ===== TCSlib/Cryptography/Games/Advantage.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.Probability
import TCSlib.Cryptography.Foundations.Probability

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Advantages of game-playing adversaries

Security definitions come in three shapes, each measured at one value of the security parameter:
- a **search game** (forge a tag, find a collision, invert a function): its advantage is the
  probability that the game, run with the adversary, outputs `true`;
- a **distinguishing pair** (real versus random, left versus right): its advantage is the
  difference of the two games' acceptance probabilities;
- a **guess-the-bit game**: a bit `b` is drawn, the game runs on `b`, and the adversary wins if it
  outputs `b`. Its advantage is the distance of the winning probability from `½`, which is half
  the distinguishing advantage of the two games (`guessAdv_eq_half_advantage`).

Games are `ProbComp Bool`s built from the adversary; these shapes are what asymptotic security
definitions wrap with "negligible for every efficient adversary".

## Main definitions

* `Games.accept G`: the probability that `G` outputs `true`.
* `Games.advantage G₀ G₁`: `|Pr[G₀ = 1] − Pr[G₁ = 1]|`.
* `Games.guessGame G`, `Games.guessAdv G`: the guess-the-bit game over `G : Bool → ProbComp Bool`
  and its advantage `|Pr[win] − ½|`.

## Main results

* `advantage_triangle`, `advantage_hybrid`, `exists_advantage_hybrid_gap`: the hybrid argument;
  the advantage between the ends of a chain of games is at most the sum of the advantages between
  neighbours, so some neighbouring pair carries a `1/n` share of it ([PS10, Lemma 71.6]).
* `guessAdv_eq_half_advantage`: the guess-the-bit advantage is half the distinguishing advantage
  between the games for `b = 1` and `b = 0`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §3.1 (computational indistinguishability), Lemma 71.6 (the hybrid lemma) and Definition 168.1
  (the challenge bit of the indistinguishability games).
* [Sho04] V. Shoup, *Sequences of games: a tool for taming complexity in security proofs*,
  IACR ePrint 2004/332.
* [VCVio] D. Tuma and the VCVio contributors, *VCVio: machine-checked cryptographic proofs in
  Lean*, https://github.com/dtumad/VCV-io, commit 9054989327a7185ff19ef9ff0f119cccea479501
  (2026-11-04), Apache License 2.0. Design adapted (no code transcribed): oracle specifications
  indexed by a type of oracle names (`VCVio/OracleComp/OracleSpec.lean`), oracle computations as
  a free monad over them (`OracleComp.lean`, `OracleQuery.lean`), probabilistic computations as
  computations over the uniform-selection oracles (`OracleComp/ProbComp/Basic.lean`), and
  simulation of oracles by stateful handlers with query logging and composition (`SimSemantics/`,
  `SimSemantics/QueryImpl/Compose.lean`, `QueryTracking/LoggingOracle`).
-/

namespace TCSlib.Cryptography.Games

open Finset ProbComp

/-- The probability that the game `G` outputs `true`. -/
noncomputable def accept (G : ProbComp Bool) : ℝ := prob G (· = true)

/-- The **distinguishing advantage** between two games: `|Pr[G₀ = 1] − Pr[G₁ = 1]|`.
[PS10, §3.1] -/
noncomputable def advantage (G₀ G₁ : ProbComp Bool) : ℝ := |accept G₀ - accept G₁|

/-- An acceptance probability is nonnegative. -/
theorem accept_nonneg (G : ProbComp Bool) : 0 ≤ accept G := prob_nonneg G _

/-- An acceptance probability is at most one. -/
theorem accept_le_one (G : ProbComp Bool) : accept G ≤ 1 := prob_le_one G _

/-- The distinguishing advantage is nonnegative. -/
theorem advantage_nonneg (G₀ G₁ : ProbComp Bool) : 0 ≤ advantage G₀ G₁ := abs_nonneg _

/-- The distinguishing advantage is symmetric. -/
theorem advantage_comm (G₀ G₁ : ProbComp Bool) : advantage G₀ G₁ = advantage G₁ G₀ :=
  abs_sub_comm _ _

/-- A game has no advantage against itself. -/
@[simp] theorem advantage_self (G : ProbComp Bool) : advantage G G = 0 := by simp [advantage]

/-- The distinguishing advantage is at most one. -/
theorem advantage_le_one (G₀ G₁ : ProbComp Bool) : advantage G₀ G₁ ≤ 1 := by
  unfold advantage
  rw [abs_le]
  constructor <;> linarith [accept_nonneg G₀, accept_nonneg G₁, accept_le_one G₀, accept_le_one G₁]

/-- **One game hop:** the advantage between `G₀` and `G₂` is at most the sum of the advantages
through `G₁`. -/
theorem advantage_triangle (G₀ G₁ G₂ : ProbComp Bool) :
    advantage G₀ G₂ ≤ advantage G₀ G₁ + advantage G₁ G₂ :=
  abs_sub_le _ _ _

/-- **The hybrid argument:** along a chain of games `G 0, …, G n`, the advantage between the ends
is at most the sum of the advantages between neighbours: the telescoping inequality in the proof of
[PS10, Lemma 71.6]. It is the concrete layer's `abs_sub_le_sum_hybrids` for the acceptance
probabilities. -/
theorem advantage_hybrid (G : ℕ → ProbComp Bool) (n : ℕ) :
    advantage (G 0) (G n) ≤ ∑ i ∈ range n, advantage (G i) (G (i + 1)) :=
  abs_sub_le_sum_hybrids (fun i => accept (G i)) n

/-- **The hybrid lemma:** along a chain of `n > 0` games, some neighbouring pair has advantage at
least a `1/n` share of the advantage between the ends. [PS10, Lemma 71.6] It is the concrete
layer's `exists_hybrid_gap` for the acceptance probabilities. -/
theorem exists_advantage_hybrid_gap (G : ℕ → ProbComp Bool) {n : ℕ} (hn : 0 < n) :
    ∃ i < n, advantage (G 0) (G n) / n ≤ advantage (G i) (G (i + 1)) :=
  exists_hybrid_gap (fun i => accept (G i)) hn

/-! ### Guess-the-bit games -/

/-- The **guess-the-bit game** over `G`: draw a uniform bit `b`, run `G b`, and win if its output
is `b`. The challenge bit of the indistinguishability games of [PS10, Def 168.1]. -/
noncomputable def guessGame (G : Bool → ProbComp Bool) : ProbComp Bool :=
  (sample Bool).bind fun b => (G b).bind fun b' => .pure (decide (b' = b))

/-- The **guess-the-bit advantage**: how far the winning probability is from `½`. -/
noncomputable def guessAdv (G : Bool → ProbComp Bool) : ℝ := |accept (guessGame G) - 1 / 2|

/-- The winning probability of the guess-the-bit game is the average of `Pr[G 1 = 1]` and
`Pr[G 0 = 0]`.

**Proof sketch.** Total probability over the uniform bit (two equally likely values), and
`Pr[G 0 = 0] = 1 − Pr[G 0 = 1]`. -/
theorem accept_guessGame (G : Bool → ProbComp Bool) :
    accept (guessGame G) = (accept (G true) + (1 - accept (G false))) / 2 := by
  classical
  have hnot : prob (G false) (· = false) = 1 - accept (G false) := by
    rw [accept, ← prob_not]
    exact prob_congr _ fun b => by cases b <;> simp
  unfold accept guessGame
  rw [prob_bind, expect_sample]
  simp only [Fintype.univ_bool, mem_singleton, Bool.true_eq_false, not_false_eq_true,
    sum_insert, sum_singleton, Fintype.card_bool, prob_bind]
  have h1 : expect (G true) (fun b' => prob (OracleComp.pure (decide (b' = true))) (· = true)) =
      prob (G true) (· = true) := by
    rw [prob_eq_expect]; congr 1; funext b'; cases b' <;> simp [prob_pure]
  have h0 : expect (G false) (fun b' => prob (OracleComp.pure (decide (b' = false))) (· = true)) =
      prob (G false) (· = false) := by
    rw [prob_eq_expect]; congr 1; funext b'; cases b' <;> simp [prob_pure]
  rw [h1, h0, hnot]
  simp only [accept]
  push_cast
  ring

/-- **Guessing versus distinguishing:** the guess-the-bit advantage is half the distinguishing
advantage between `G 1` and `G 0`. The standard relation between the two forms of
indistinguishability; [PS10] uses both (§3.1 and Def 168.1) without stating it. -/
theorem guessAdv_eq_half_advantage (G : Bool → ProbComp Bool) :
    guessAdv G = advantage (G true) (G false) / 2 := by
  unfold guessAdv advantage
  rw [accept_guessGame]
  rw [show (accept (G true) + (1 - accept (G false))) / 2 - 1 / 2 =
      (accept (G true) - accept (G false)) / 2 by ring, abs_div, abs_two]

end TCSlib.Cryptography.Games

## ===== TCSlib/Cryptography/Games/Hopping.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.Simulate
import TCSlib.Cryptography.Games.Advantage

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Game hopping

The steps of a game-based security proof, proved once:
- **the difference lemma**: two events that agree unless a "bad" event happens differ in
  probability by at most the probability of the bad event;
- **identical until bad**: two oracle implementations that give the same law to good successors
  until a flag in their state is raised, and never lower it, give simulations whose outputs differ
  in probability by at most the probability that the flag is raised;
- **a collision bound**: one fresh uniform sample lands in a list of at most `q` values fixed
  before it with probability at most `q / |T|`. The adaptive repeated-nonce event of
  [PS10, Thm 168.2] (later nonces hitting an earlier one) is a union of such steps; its lemma is
  scheduled with the statement phase.

The hybrid argument itself is `advantage_hybrid` (`TCSlib.Cryptography.Games.Advantage`).

## Main definitions

* `Games.OracleComp.AllOutputs P c`: every possible output of `c` satisfies `P`.

## Main results

* `ProbComp.prob_eq_one_of_allOutputs`, `ProbComp.expect_mono_of_allOutputs`: reasoning on the
  possible outputs only.
* `ProbComp.abs_prob_sub_le_of_agree`: the difference lemma [Sho04].
* `ProbComp.prob_mem_le`: the collision bound.
* `Games.prob_eq_until_bad`, `Games.identical_until_bad`, `Games.identical_until_bad_init`: the
  code-based fundamental lemma [BR06], in semantic form, from a fixed or a sampled initial
  state; `Games.hagree_of_eq` recovers the syntactic hypothesis.

## References

* [BR06] M. Bellare, P. Rogaway, *The security of triple encryption and a framework for
  code-based game-playing proofs*, EUROCRYPT 2006 (the fundamental lemma of game playing).
* [Sho04] V. Shoup, *Sequences of games: a tool for taming complexity in security proofs*,
  IACR ePrint 2004/332 (the difference lemma). Section and lemma numbers are not cited: they vary
  between revisions, and the revision could not be inspected.
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Thm 168.2 (proof sketch: the bad events of the CPA analysis).
* [VCVio] D. Tuma and the VCVio contributors, *VCVio: machine-checked cryptographic proofs in
  Lean*, https://github.com/dtumad/VCV-io, commit 9054989327a7185ff19ef9ff0f119cccea479501
  (2026-11-04), Apache License 2.0. Design adapted (no code transcribed): oracle specifications
  indexed by a type of oracle names (`VCVio/OracleComp/OracleSpec.lean`), oracle computations as
  a free monad over them (`OracleComp.lean`, `OracleQuery.lean`), probabilistic computations as
  computations over the uniform-selection oracles (`OracleComp/ProbComp/Basic.lean`), and
  simulation of oracles by stateful handlers with query logging and composition (`SimSemantics/`,
  `SimSemantics/QueryImpl/Compose.lean`, `QueryTracking/LoggingOracle`).
-/

namespace TCSlib.Cryptography.Games

open Finset

variable {ι : Type} {α β σ : Type}

/-- **Every possible output** of `c` satisfies `P`: a return satisfies it, and every
continuation of a query does, whatever the answer. -/
def OracleComp.AllOutputs {spec : OracleSpec ι} (P : α → Prop) : OracleComp spec α → Prop
  | .pure a => P a
  | .query _ _ k => ∀ y, AllOutputs P (k y)

/-- `AllOutputs` is monotone in the predicate. -/
theorem OracleComp.AllOutputs.mono {spec : OracleSpec ι} {P Q : α → Prop} (hPQ : ∀ a, P a → Q a)
    {c : OracleComp spec α} (h : c.AllOutputs P) : c.AllOutputs Q := by
  induction c with
  | pure a => exact hPQ a h
  | query i x k ih => exact fun y => ih y (h y)

/-- Every possible output of `c` followed by `f` satisfies `Q` when every possible output `a`
of `c` satisfies `P` and every possible output of `f a` with `P a` satisfies `Q`. -/
theorem OracleComp.AllOutputs.bind {spec : OracleSpec ι} {P : α → Prop} {Q : β → Prop}
    {c : OracleComp spec α} {f : α → OracleComp spec β} (hc : c.AllOutputs P)
    (hf : ∀ a, P a → (f a).AllOutputs Q) : (c.bind f).AllOutputs Q := by
  induction c with
  | pure a => exact hf a hc
  | query i x k ih => exact fun y => ih y (hc y)

namespace ProbComp

/-- An event splits by a second event: `Pr[A] = Pr[A ∧ ¬F] + Pr[A ∧ F]`. -/
theorem prob_split (c : ProbComp α) (A F : α → Prop) :
    prob c A = prob c (fun a => A a ∧ ¬ F a) + prob c (fun a => A a ∧ F a) := by
  classical
  rw [prob_eq_expect, prob_eq_expect, prob_eq_expect, ← expect_add]
  congr 1
  funext a
  by_cases hA : A a <;> by_cases hF : F a <;> simp [hA, hF]

/-- If every possible output of `c` satisfies `P`, and `f ≤ g` at every output satisfying `P`,
then the expectation of `f` over `c` is at most that of `g`. -/
theorem expect_mono_of_allOutputs {c : ProbComp α} {P : α → Prop} (hc : c.AllOutputs P)
    {f g : α → ℝ} (h : ∀ a, P a → f a ≤ g a) : expect c f ≤ expect c g := by
  induction c with
  | pure a => exact h a hc
  | query m x k ih =>
    simp only [expect_query]
    exact mul_le_mul_of_nonneg_left (sum_le_sum fun j _ => ih j (hc j)) (by positivity)

/-- An event holding at every possible output has probability one. -/
theorem prob_eq_one_of_allOutputs {c : ProbComp α} {p : α → Prop} (hc : c.AllOutputs p) :
    prob c p = 1 := by
  classical
  refine le_antisymm (prob_le_one c p) ?_
  rw [prob_eq_expect]
  calc (1 : ℝ) = expect c (fun _ => 1) := (expect_const c 1).symm
    _ ≤ _ := expect_mono_of_allOutputs hc fun a ha => by simp [ha]

/-- An event failing at every possible output has probability zero. -/
theorem prob_eq_zero_of_allOutputs {c : ProbComp α} {p : α → Prop}
    (hc : c.AllOutputs fun a => ¬ p a) : prob c p = 0 := by
  have h := prob_not c p
  rw [prob_eq_one_of_allOutputs hc] at h
  linarith

/-- **The difference lemma:** if the events `A` and `B` agree at every output where `F` fails,
their probabilities differ by at most the probability of `F`. [Sho04] (the difference lemma)

**Proof sketch.** Pointwise, the indicators of `A` and `B` differ by at most the indicator of
`F`; take expectations in both directions (linearity and monotonicity). -/
theorem abs_prob_sub_le_of_agree (c : ProbComp α) {A B F : α → Prop}
    (h : ∀ a, ¬ F a → (A a ↔ B a)) : |prob c A - prob c B| ≤ prob c F := by
  classical
  have key : ∀ (A B : α → Prop), (∀ a, ¬ F a → (A a ↔ B a)) →
      prob c A ≤ prob c B + prob c F := by
    intro A B hAB
    rw [prob_eq_expect, prob_eq_expect, prob_eq_expect, ← expect_add]
    exact expect_mono c fun a => by
      by_cases hF : F a
      · by_cases hA : A a <;> by_cases hB : B a <;> simp [hA, hB, hF]
      · have := hAB a hF
        by_cases hA : A a
        · simp [hA, this.1 hA, hF]
        · simp [hA, hF]; split_ifs <;> norm_num
  rw [abs_le]
  constructor
  · linarith [key B A fun a ha => (h a ha).symm]
  · linarith [key A B h]

/-- **The collision bound:** if every possible output list has length at most `q`, one fresh
uniform element of `T`, drawn after the list, lies in it with probability at most `q / |T|`.
A standard union-bound fact behind the bad events of [PS10, Thm 168.2]'s proof sketch; the
adaptive repeated-nonce event is a union of such steps.

**Proof sketch.** By total probability over the list, it suffices that a fixed list `L` of length
at most `q` is hit with probability `#{t ∈ L} / |T| ≤ q / |T|`; average over the possible lists
with `expect_mono_of_allOutputs`. -/
theorem prob_mem_le {T : Type} [Fintype T] [Nonempty T] [DecidableEq T] (c : ProbComp (List T))
    {q : ℕ} (hc : c.AllOutputs fun L => L.length ≤ q) :
    prob (c.bind fun L => (sample T).bind fun t => .pure (L, t)) (fun p => p.2 ∈ p.1) ≤
      q / Fintype.card T := by
  have hT : (0 : ℝ) < Fintype.card T := by exact_mod_cast Fintype.card_pos
  rw [prob_bind]
  calc expect c (fun L => prob ((sample T).bind fun t => .pure (L, t)) (fun p => p.2 ∈ p.1))
      ≤ expect c (fun _ => (q : ℝ) / Fintype.card T) := by
        refine expect_mono_of_allOutputs hc fun L hL => ?_
        rw [prob_bind, expect_sample]
        have hsum : ∑ t : T, prob (OracleComp.pure (L, t)) (fun p : List T × T => p.2 ∈ p.1) =
            (L.toFinset.card : ℝ) := by
          simp only [prob_pure, Finset.sum_boole]
          congr 2
          ext t
          simp
        rw [hsum, inv_mul_eq_div]
        refine div_le_div_of_nonneg_right ?_ hT.le
        exact_mod_cast (List.toFinset_card_le L).trans hL
    _ = q / Fintype.card T := expect_const c _

end ProbComp

/-- From a bad state, every possible final state of the simulation is bad, when the
implementation never leaves a bad state. -/
theorem simulate_allOutputs_bad {spec : OracleSpec ι} {impl : QueryImpl spec σ unifSpec}
    (bad : σ → Prop) (hstick : ∀ i x s, bad s → (impl i x s).AllOutputs fun ys => bad ys.2)
    (c : OracleComp spec α) {s : σ} (hs : bad s) :
    (simulate impl c s).AllOutputs fun r => bad r.2 := by
  induction c generalizing s with
  | pure a => exact hs
  | query i x k ih =>
    rw [simulate_query]
    exact OracleComp.AllOutputs.bind (hstick i x s hs) fun ys hys => ih ys.1 hys

/-- Splitting an expectation on a predicate: on `b` the function is `1`, elsewhere `f`. -/
private theorem expect_ite_one_split {γ : Type} (c : ProbComp γ) (b : γ → Prop) [DecidablePred b]
    (f : γ → ℝ) :
    ProbComp.expect c (fun y => if b y then 1 else f y) =
      (1 - ProbComp.expect c (fun y => if b y then 0 else 1)) +
        ProbComp.expect c (fun y => if b y then 0 else f y) := by
  have h : (fun y => if b y then (1 : ℝ) else f y) =
      fun y => (1 + (-1) * (if b y then (0 : ℝ) else 1)) + (if b y then 0 else f y) := by
    funext y
    by_cases hy : b y <;> simp [hy]
  rw [h, ProbComp.expect_add c (fun y => 1 + (-1) * (if b y then (0 : ℝ) else 1))
      (fun y => if b y then 0 else f y),
    ProbComp.expect_add c (fun _ => (1 : ℝ)) (fun y => (-1) * (if b y then (0 : ℝ) else 1)),
    ProbComp.expect_const, ProbComp.expect_const_mul]
  ring

/-- **Equal until bad:** let two implementations give, from every good state, the same law to good
successors (they may differ arbitrarily on bad successors, including in the call that makes the
state bad), and let each keep bad states bad. Then, from a good state, the two simulations give
the same probability to "`Q` holds and the final state is good", and the same probability to "the
final state is bad".

**Proof sketch.** Induction on the computation. At a query from a good state, write `F_b` for the
continuation's probability of the event. On a bad successor `F_b` is `0` (for "good at the end")
or `1` (for "bad at the end") on both sides (`simulate_allOutputs_bad`). So each expectation only
depends on `F_b` at good successors, where `F₀ = F₁` by induction; and the two implementations give
good successors the same law (`hagree`, once with `g := F₁` and once with `g := 1`). -/
theorem prob_eq_until_bad {spec : OracleSpec ι} {impl₀ impl₁ : QueryImpl spec σ unifSpec}
    (bad : σ → Prop) [DecidablePred bad]
    (hagree : ∀ i x s, ¬ bad s → ∀ g : spec.rng i × σ → ℝ,
      ProbComp.expect (impl₀ i x s) (fun ys => if bad ys.2 then 0 else g ys) =
        ProbComp.expect (impl₁ i x s) (fun ys => if bad ys.2 then 0 else g ys))
    (hstick₀ : ∀ i x s, bad s → (impl₀ i x s).AllOutputs fun ys => bad ys.2)
    (hstick₁ : ∀ i x s, bad s → (impl₁ i x s).AllOutputs fun ys => bad ys.2)
    (c : OracleComp spec α) (Q : α → Prop) {s : σ} (hs : ¬ bad s) :
    ProbComp.prob (simulate impl₀ c s) (fun r => Q r.1 ∧ ¬ bad r.2) =
        ProbComp.prob (simulate impl₁ c s) (fun r => Q r.1 ∧ ¬ bad r.2) ∧
      ProbComp.prob (simulate impl₀ c s) (fun r => bad r.2) =
        ProbComp.prob (simulate impl₁ c s) (fun r => bad r.2) := by
  induction c generalizing s with
  | pure a => exact ⟨rfl, rfl⟩
  | query i x k ih =>
    simp only [simulate_query, ProbComp.prob_bind]
    constructor
    · -- "`Q` and good at the end"
      have h0 : ∀ ys : spec.rng i × σ,
          ProbComp.prob (simulate impl₀ (k ys.1) ys.2) (fun r => Q r.1 ∧ ¬ bad r.2) =
            if bad ys.2 then 0 else
              ProbComp.prob (simulate impl₁ (k ys.1) ys.2) (fun r => Q r.1 ∧ ¬ bad r.2) := by
        intro ys
        by_cases hb : bad ys.2
        · rw [if_pos hb]
          exact ProbComp.prob_eq_zero_of_allOutputs
            ((simulate_allOutputs_bad bad hstick₀ _ hb).mono fun r hr h => h.2 hr)
        · rw [if_neg hb]
          exact (ih ys.1 hb).1
      have h1 : ∀ ys : spec.rng i × σ,
          ProbComp.prob (simulate impl₁ (k ys.1) ys.2) (fun r => Q r.1 ∧ ¬ bad r.2) =
            if bad ys.2 then 0 else
              ProbComp.prob (simulate impl₁ (k ys.1) ys.2) (fun r => Q r.1 ∧ ¬ bad r.2) := by
        intro ys
        by_cases hb : bad ys.2
        · rw [if_pos hb]
          exact ProbComp.prob_eq_zero_of_allOutputs
            ((simulate_allOutputs_bad bad hstick₁ _ hb).mono fun r hr h => h.2 hr)
        · rw [if_neg hb]
      rw [funext h0, hagree i x s hs, ← funext h1]
    · -- "bad at the end"
      have h0 : ∀ ys : spec.rng i × σ,
          ProbComp.prob (simulate impl₀ (k ys.1) ys.2) (fun r => bad r.2) =
            if bad ys.2 then 1 else
              ProbComp.prob (simulate impl₁ (k ys.1) ys.2) (fun r => bad r.2) := by
        intro ys
        by_cases hb : bad ys.2
        · rw [if_pos hb]
          exact ProbComp.prob_eq_one_of_allOutputs (simulate_allOutputs_bad bad hstick₀ _ hb)
        · rw [if_neg hb]
          exact (ih ys.1 hb).2
      have h1 : ∀ ys : spec.rng i × σ,
          ProbComp.prob (simulate impl₁ (k ys.1) ys.2) (fun r => bad r.2) =
            if bad ys.2 then 1 else
              ProbComp.prob (simulate impl₁ (k ys.1) ys.2) (fun r => bad r.2) := by
        intro ys
        by_cases hb : bad ys.2
        · rw [if_pos hb]
          exact ProbComp.prob_eq_one_of_allOutputs (simulate_allOutputs_bad bad hstick₁ _ hb)
        · rw [if_neg hb]
      rw [funext h0, expect_ite_one_split, hagree i x s hs (fun _ => 1), hagree i x s hs,
        ← expect_ite_one_split, ← funext h1]

/-- **Identical until bad** (the code-based fundamental lemma): let two implementations of the
same oracles give, from every good state, the same law to good successors, and let each keep `bad`
once it holds (every possible new state of a bad state is bad). Then, from a good state, for any
computation `c` and event `p` on its output, the probabilities of `p` under the two simulations
differ by at most the probability that the first simulation ends in a bad state.
[BR06] (the fundamental lemma); [Sho04]

**Deviation:** [BR06] assumes the two games' code is syntactically identical up to `bad ← true`.
Here the hypothesis is semantic: from a good state the two implementations give the same law to
good successors, and may differ arbitrarily on bad ones, including in the call that raises the
flag. Stickiness is required; without it the bound fails.

**Proof sketch.**
1. *Sticky:* from a bad state, every possible final state of either simulation is bad
   (`simulate_allOutputs_bad`).
2. *Equal until bad:* `prob_eq_until_bad`.
3. Write each probability of `p` as "`p` and good" plus at most "bad", and conclude with the
   difference lemma's arithmetic. -/
theorem identical_until_bad {spec : OracleSpec ι}
    {impl₀ impl₁ : QueryImpl spec σ unifSpec} (bad : σ → Prop) [DecidablePred bad]
    (hagree : ∀ i x s, ¬ bad s → ∀ g : spec.rng i × σ → ℝ,
      ProbComp.expect (impl₀ i x s) (fun ys => if bad ys.2 then 0 else g ys) =
        ProbComp.expect (impl₁ i x s) (fun ys => if bad ys.2 then 0 else g ys))
    (hstick₀ : ∀ i x s, bad s → (impl₀ i x s).AllOutputs fun ys => bad ys.2)
    (hstick₁ : ∀ i x s, bad s → (impl₁ i x s).AllOutputs fun ys => bad ys.2)
    (c : OracleComp spec α) (p : α → Prop) {s : σ} (hs : ¬ bad s) :
    |ProbComp.prob (simulate impl₀ c s) (fun r => p r.1) -
        ProbComp.prob (simulate impl₁ c s) (fun r => p r.1)| ≤
      ProbComp.prob (simulate impl₀ c s) (fun r => bad r.2) := by
  obtain ⟨h1, h2⟩ := prob_eq_until_bad bad hagree hstick₀ hstick₁ c p hs
  rw [ProbComp.prob_split (simulate impl₀ c s) (fun r => p r.1) (fun r => bad r.2),
    ProbComp.prob_split (simulate impl₁ c s) (fun r => p r.1) (fun r => bad r.2), h1]
  have a0 := ProbComp.prob_nonneg (simulate impl₀ c s) (fun r => p r.1 ∧ bad r.2)
  have a1 := ProbComp.prob_nonneg (simulate impl₁ c s) (fun r => p r.1 ∧ bad r.2)
  have b0 := ProbComp.prob_mono (simulate impl₀ c s) (p := fun r => p r.1 ∧ bad r.2)
    (q := fun r => bad r.2) fun r h => h.2
  have b1 := ProbComp.prob_mono (simulate impl₁ c s) (p := fun r => p r.1 ∧ bad r.2)
    (q := fun r => bad r.2) fun r h => h.2
  rw [abs_le]
  constructor <;> linarith

/-- Equal implementations on good states give the same law to good successors: the hypothesis of
`identical_until_bad` in its syntactic form. -/
theorem hagree_of_eq {spec : OracleSpec ι} {impl₀ impl₁ : QueryImpl spec σ unifSpec}
    (bad : σ → Prop) [DecidablePred bad] (h : ∀ i x s, ¬ bad s → impl₀ i x s = impl₁ i x s) :
    ∀ i x s, ¬ bad s → ∀ g : spec.rng i × σ → ℝ,
      ProbComp.expect (impl₀ i x s) (fun ys => if bad ys.2 then 0 else g ys) =
        ProbComp.expect (impl₁ i x s) (fun ys => if bad ys.2 then 0 else g ys) :=
  fun i x s hs _ => by rw [h i x s hs]

/-- **Identical until bad, from a sampled initial state:** if every possible initial state is
good, the bound of `identical_until_bad` holds for the games that first sample the state.

**Proof sketch.** Total probability over the initial state, the pointwise bound at every possible
(good) initial state (`identical_until_bad`), and monotonicity and linearity of expectation. -/
theorem identical_until_bad_init {spec : OracleSpec ι}
    {impl₀ impl₁ : QueryImpl spec σ unifSpec} (bad : σ → Prop) [DecidablePred bad]
    (hagree : ∀ i x s, ¬ bad s → ∀ g : spec.rng i × σ → ℝ,
      ProbComp.expect (impl₀ i x s) (fun ys => if bad ys.2 then 0 else g ys) =
        ProbComp.expect (impl₁ i x s) (fun ys => if bad ys.2 then 0 else g ys))
    (hstick₀ : ∀ i x s, bad s → (impl₀ i x s).AllOutputs fun ys => bad ys.2)
    (hstick₁ : ∀ i x s, bad s → (impl₁ i x s).AllOutputs fun ys => bad ys.2)
    (c : OracleComp spec α) (p : α → Prop) (init : ProbComp σ)
    (hinit : init.AllOutputs fun s => ¬ bad s) :
    |ProbComp.prob (init.bind fun s => simulate impl₀ c s) (fun r => p r.1) -
        ProbComp.prob (init.bind fun s => simulate impl₁ c s) (fun r => p r.1)| ≤
      ProbComp.prob (init.bind fun s => simulate impl₀ c s) (fun r => bad r.2) := by
  rw [ProbComp.prob_bind, ProbComp.prob_bind, ProbComp.prob_bind]
  have key := fun s (hs : ¬ bad s) =>
    abs_le.1 (identical_until_bad bad hagree hstick₀ hstick₁ c p hs)
  have u := ProbComp.expect_mono_of_allOutputs hinit
    (f := fun s => ProbComp.prob (simulate impl₀ c s) (fun r => p r.1))
    (g := fun s => ProbComp.prob (simulate impl₁ c s) (fun r => p r.1) +
      ProbComp.prob (simulate impl₀ c s) (fun r => bad r.2))
    (fun s hs => by linarith [(key s hs).2])
  have v := ProbComp.expect_mono_of_allOutputs hinit
    (f := fun s => ProbComp.prob (simulate impl₁ c s) (fun r => p r.1))
    (g := fun s => ProbComp.prob (simulate impl₀ c s) (fun r => p r.1) +
      ProbComp.prob (simulate impl₀ c s) (fun r => bad r.2))
    (fun s hs => by linarith [(key s hs).1])
  rw [ProbComp.expect_add] at u v
  rw [abs_le]
  constructor <;> linarith

end TCSlib.Cryptography.Games

## ===== TCSlib/Cryptography/Games/Protocols.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.Probability

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Two-party protocols as oracle computations

A party of a two-party protocol is an oracle computation with two kinds of oracles: the message
exchange (send a message, receive the other party's next message) and its own coins. Running the
protocol interleaves the two parties as coroutines: the active party runs until it sends a
message, the other party resumes with that message and runs until it replies, and so on, for at
most `fuel` messages.

**When a party returns.** [PS10, §4.4] ends the protocol when the active machine halts, and gives
a machine an output only on halting, so the waiting party has none. Yet Definitions 116.1 and
155.1 use both parties' outputs. As in the ch. 2–4 layer's reading (its foundation decision D8,
`TCSlib.Cryptography.ZeroKnowledge.Interaction`), the waiting party is activated **once more**:
its pending send is answered `none` ("the other party has finished"), it may draw coins, and it
must then return without sending. A send after the end is reported (`ExecOutcome.sentAfterEnd`),
never hidden. Either party may return early.

**Views.** A party's view (its input and auxiliary input, which are Lean parameters of the party,
its coins, and the messages delivered to it, starting with the second mover's first message) is
recorded by the executor: `Party.execT` returns, beside the outcome, each party's received
messages and coin draws (`Party.Obs`), and its outcome is that of `Party.exec`
(`Party.execT_outcome`). A party's own oracle log would miss the second mover's first message,
which reaches it as an argument.

The bridge to the next-message strategies of the ch. 2–4 layer (`TCSlib.Cryptography.Strategy`,
`TCSlib.Cryptography.exec`) is part of the S2b layer.

## Main definitions

* `Games.exchangeSpec Out In`: the message-exchange oracle (send an `Out`, receive an `In` or
  `none`).
* `Games.Party Out In α`: a party sending `Out`, receiving `In`, drawing its own coins and returning
  an `α`.
* `Games.ExecOutcome`: both outputs, out of fuel, or a send after the end.
* `Games.Party.step`, `Games.Party.close`: run a party to its next send or return; close a party
  whose counterpart has returned.
* `Games.Party.exec fuel A B`: execute a protocol in which `A` moves first, with at most `fuel`
  messages.
* `Games.Party.Obs`, `Games.Party.execT`: the traced execution, recording each party's received
  messages and coins.

## Main results

* `Games.Party.exec_zero`, `Party.exec_succ`: the execution equations.
* `Games.Party.execT_outcome`: the traced execution has the outcome of the execution.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §4.4 (interactive machines, executions, views), Definitions 116.1 and 155.1.
* [VCVio] D. Tuma and the VCVio contributors, *VCVio: machine-checked cryptographic proofs in
  Lean*, https://github.com/dtumad/VCV-io, commit 9054989327a7185ff19ef9ff0f119cccea479501
  (2026-11-04), Apache License 2.0. Design adapted (no code transcribed): oracle specifications
  indexed by a type of oracle names (`VCVio/OracleComp/OracleSpec.lean`), oracle computations as
  a free monad over them (`OracleComp.lean`, `OracleQuery.lean`), probabilistic computations as
  computations over the uniform-selection oracles (`OracleComp/ProbComp/Basic.lean`), and
  simulation of oracles by stateful handlers with query logging and composition (`SimSemantics/`,
  `SimSemantics/QueryImpl/Compose.lean`, `QueryTracking/LoggingOracle`).
-/

namespace TCSlib.Cryptography.Games

/-- The **message-exchange oracle**: the query is the message sent, and the answer is the other
party's next message, or `none` if the other party has returned. [PS10, §4.4] -/
abbrev exchangeSpec (Out In : Type) : OracleSpec Unit := ⟨fun _ => Out, fun _ => Option In⟩

/-- A **party** of a two-party protocol: sends messages of type `Out`, receives messages of type
`In`, draws its own coins, and returns an `α`. [PS10, §4.4] -/
abbrev Party (Out In α : Type) : Type := OracleComp ((exchangeSpec Out In).add unifSpec) α

/-- The **outcome of an execution**: both outputs; the message budget ran out; or a party sent a
message after its counterpart had returned. -/
inductive ExecOutcome (α β : Type) : Type where
  /-- Both parties returned: the first mover's output and the second mover's. -/
  | done (a : α) (b : β)
  /-- The message budget ran out before both parties returned. -/
  | outOfFuel
  /-- A party sent a message after its counterpart had returned. -/
  | sentAfterEnd

/-- Exchange the roles in an outcome. -/
def ExecOutcome.swap {α β : Type} : ExecOutcome α β → ExecOutcome β α
  | .done a b => .done b a
  | .outOfFuel => .outOfFuel
  | .sentAfterEnd => .sentAfterEnd

namespace Party

variable {Out In α β : Type}

/-- Run a party until it returns or sends a message, passing its coin draws through. The result is
either its output, or the message it sends together with how it continues on the reply. -/
def step : Party Out In α → ProbComp (α ⊕ (Out × (Option In → Party Out In α)))
  | .pure a => .pure (.inl a)
  | .query (.inl ()) m k => .pure (.inr (m, k))
  | .query (.inr j) x k => .query j x (fun y => step (k y))

/-- **Close** a party whose counterpart has returned (its pending send already answered `none`):
it may still draw coins, and returns `some` of its output, or `none` if it sends a message. -/
def close : Party Out In α → ProbComp (Option α)
  | .pure a => .pure (some a)
  | .query (.inl ()) _ _ => .pure none
  | .query (.inr j) x k => .query j x (fun y => close (k y))

/-- The end of an execution in which the active party returned `a`: the waiting party `B` is
activated once more, with `none`, and closed. -/
def endWith {M₁ M₂ α β : Type} (a : α) (B : Option M₁ → Party M₂ M₁ β) :
    ProbComp (ExecOutcome α β) :=
  (close (B none)).bind fun ob => .pure (Option.elim ob .sentAfterEnd (ExecOutcome.done a))

/-- **Execution** of a two-party protocol with at most `fuel` messages. `A` moves first, and `B`
waits for `A`'s first message. After each message the roles swap. A return costs no fuel; when the
active party returns, the waiting party is activated once more and closed (`endWith`).

**Deviation from [PS10, §4.4]:** the source ends the protocol when the active machine halts and
defines outputs only on halting, so the waiting party would have none, while Definitions 116.1
and 155.1 use both outputs. As in the ch. 2–4 layer's D8, the waiting party is activated once
more; it may draw coins, but a send is reported as `sentAfterEnd`. Unlike D8, which fixes the
number of messages, a party may return early. -/
def exec : ℕ → ∀ {M₁ M₂ α β : Type},
    Party M₁ M₂ α → (Option M₁ → Party M₂ M₁ β) → ProbComp (ExecOutcome α β)
  | 0, _, _, _, _, A, B =>
    (step A).bind (Sum.elim (fun a => endWith a B) (fun _ => .pure .outOfFuel))
  | fuel + 1, _, _, _, _, A, B =>
    (step A).bind (Sum.elim (fun a => endWith a B)
      (fun mk => (exec fuel (B (some mk.1)) mk.2).bind fun r => .pure r.swap))

/-- With no fuel, the execution ends at the first mover's first send. -/
theorem exec_zero {M₁ M₂ : Type} (A : Party M₁ M₂ α) (B : Option M₁ → Party M₂ M₁ β) :
    exec 0 A B = (step A).bind (Sum.elim (fun a => endWith a B) (fun _ => .pure .outOfFuel)) :=
  rfl

/-- One message of the execution: `A` runs until it returns (then `B` is closed) or sends `m`
(then `B` resumes with `m` as the first mover, against `A`'s continuation). -/
theorem exec_succ {M₁ M₂ : Type} (fuel : ℕ) (A : Party M₁ M₂ α)
    (B : Option M₁ → Party M₂ M₁ β) :
    exec (fuel + 1) A B =
      (step A).bind (Sum.elim (fun a => endWith a B)
        (fun mk => (exec fuel (B (some mk.1)) mk.2).bind fun r => .pure r.swap)) :=
  rfl

/-! ### Sanity checks: fuel counts messages; a send after the end is reported -/

example (a b : Bool) :
    exec 0 (M₁ := Unit) (M₂ := Unit) (.pure a) (fun _ => .pure b) = .pure (.done a b) := rfl

example (m : Unit) (a b : Bool) :
    exec 1 (M₂ := Unit) (.query (.inl ()) m fun _ => .pure a) (fun _ => .pure b) =
      .pure (.done a b) := rfl

example (m : Unit) (a b : Bool) :
    exec 1 (M₁ := Unit) (.pure a) (fun _ => .query (.inl ()) m fun _ => .pure b) =
      .pure .sentAfterEnd := rfl

/-! ### The traced execution -/

/-- What one party **observes** during an execution: the messages delivered to it, in order, and
the coins it drew, each as a sampling oracle `m` with its answer in `Fin (m + 1)`. -/
structure Obs (In : Type) : Type where
  /-- The messages delivered to the party, in order. -/
  received : List In
  /-- The party's coin draws, in order. -/
  coins : List (Σ m : ℕ, Fin (m + 1))

/-- `step`, also returning the coins drawn along the way. -/
def stepT : Party Out In α →
    ProbComp ((α ⊕ (Out × (Option In → Party Out In α))) × List (Σ m : ℕ, Fin (m + 1)))
  | .pure a => .pure (.inl a, [])
  | .query (.inl ()) m k => .pure (.inr (m, k), [])
  | .query (.inr j) x k => .query j x fun y =>
      (stepT (k y)).bind fun p => .pure (p.1, ⟨j, y⟩ :: p.2)

/-- `close`, also returning the coins drawn along the way. -/
def closeT : Party Out In α → ProbComp (Option α × List (Σ m : ℕ, Fin (m + 1)))
  | .pure a => .pure (some a, [])
  | .query (.inl ()) _ _ => .pure (none, [])
  | .query (.inr j) x k => .query j x fun y =>
      (closeT (k y)).bind fun p => .pure (p.1, ⟨j, y⟩ :: p.2)

/-- The traced end of an execution: `endWith`, also returning the waiting party's coins. -/
def endWithT {M₁ M₂ α β : Type} (a : α) (B : Option M₁ → Party M₂ M₁ β) :
    ProbComp (ExecOutcome α β × List (Σ m : ℕ, Fin (m + 1))) :=
  (closeT (B none)).bind fun p => .pure (Option.elim p.1 .sentAfterEnd (ExecOutcome.done a), p.2)

/-- The **traced execution**: `exec`, also returning what each party observed. The first component
of the result is the outcome, the second the first mover's observations, and the third the second
mover's. When the active party sends `m`, `m` is the first message the other party receives in the
rest of the run. [PS10, §4.4] (views) -/
def execT : ℕ → ∀ {M₁ M₂ α β : Type},
    Party M₁ M₂ α → (Option M₁ → Party M₂ M₁ β) →
      ProbComp (ExecOutcome α β × Obs M₂ × Obs M₁)
  | 0, _, _, _, _, A, B =>
    (stepT A).bind fun p => Sum.elim
      (fun a => (endWithT a B).bind fun q => .pure (q.1, ⟨[], p.2⟩, ⟨[], q.2⟩))
      (fun _ => .pure (.outOfFuel, ⟨[], p.2⟩, ⟨[], []⟩)) p.1
  | fuel + 1, _, _, _, _, A, B =>
    (stepT A).bind fun p => Sum.elim
      (fun a => (endWithT a B).bind fun q => .pure (q.1, ⟨[], p.2⟩, ⟨[], q.2⟩))
      (fun mk => (execT fuel (B (some mk.1)) mk.2).bind fun r =>
        .pure (r.1.swap, ⟨r.2.2.received, p.2 ++ r.2.2.coins⟩,
          ⟨mk.1 :: r.2.1.received, r.2.1.coins⟩)) p.1

/-- `stepT` projects to `step`. -/
theorem stepT_fst (A : Party Out In α) : (stepT A).bind (fun p => .pure p.1) = step A := by
  induction A with
  | pure a => rfl
  | query i x k ih =>
    cases i with
    | inl u => cases u; rfl
    | inr j =>
      simp only [stepT, step, OracleComp.query_bind, OracleComp.bind_assoc, OracleComp.pure_bind]
      congr 1
      funext y
      exact ih y

/-- `closeT` projects to `close`. -/
theorem closeT_fst (A : Party Out In α) : (closeT A).bind (fun p => .pure p.1) = close A := by
  induction A with
  | pure a => rfl
  | query i x k ih =>
    cases i with
    | inl u => cases u; rfl
    | inr j =>
      simp only [closeT, close, OracleComp.query_bind, OracleComp.bind_assoc, OracleComp.pure_bind]
      congr 1
      funext y
      exact ih y

/-- `endWithT` projects to `endWith`. -/
theorem endWithT_fst {M₁ M₂ : Type} (a : α) (B : Option M₁ → Party M₂ M₁ β) :
    (endWithT a B).bind (fun q => .pure q.1) = endWith a B := by
  simp only [endWithT, endWith, OracleComp.bind_assoc, OracleComp.pure_bind]
  rw [← closeT_fst (B none), OracleComp.bind_assoc]
  simp only [OracleComp.pure_bind]

/-- **The traced execution has the execution's outcome.**

**Proof sketch.** Induction on the fuel, generalizing the parties and their types. Each level of
`execT` runs `stepT`, which projects to `step` (`stepT_fst`); the branch on the first component
then matches `exec`'s, with `endWithT` projecting to `endWith` and the recursive call to the
recursive call. -/
theorem execT_outcome : ∀ (fuel : ℕ) {M₁ M₂ α β : Type} (A : Party M₁ M₂ α)
    (B : Option M₁ → Party M₂ M₁ β),
    (execT fuel A B).bind (fun r => .pure r.1) = exec fuel A B
  | 0, _, _, _, _, A, B => by
    simp only [execT, exec, OracleComp.bind_assoc]
    rw [← stepT_fst A, OracleComp.bind_assoc]
    simp only [OracleComp.pure_bind]
    congr 1
    funext p
    rcases p with ⟨_ | _, c⟩
    · simp only [Sum.elim_inl, OracleComp.bind_assoc, OracleComp.pure_bind]
      rw [← endWithT_fst]
    · rfl
  | fuel + 1, _, _, _, _, A, B => by
    simp only [execT, exec, OracleComp.bind_assoc]
    rw [← stepT_fst A, OracleComp.bind_assoc]
    simp only [OracleComp.pure_bind]
    congr 1
    funext p
    rcases p with ⟨_ | mk, c⟩
    · simp only [Sum.elim_inl, OracleComp.bind_assoc, OracleComp.pure_bind]
      rw [← endWithT_fst]
    · simp only [Sum.elim_inr, OracleComp.bind_assoc, OracleComp.pure_bind]
      rw [← execT_outcome fuel (B (some mk.1)) mk.2, OracleComp.bind_assoc]
      simp only [OracleComp.pure_bind]

end Party

end TCSlib.Cryptography.Games

## ===== TCSlib/InformationTheory/FinDist.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Chebyshev

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Distributions on a finite type

A lightweight, real-valued model of a probability distribution on a finite type: a nonnegative
function summing to one. This is deliberately not `PMF`, whose `ℝ≥0∞` values make subtraction
truncated and Cauchy–Schwarz awkward — and the arguments this file supports (collision
probability, the `ℓ¹`–`ℓ²` bound, the leftover hash lemma) are all differences of real numbers.

## Main definitions

* `TCSlib.InformationTheory.FinDist α`: a distribution on a finite type.
* `FinDist.uniform`, `FinDist.map`, `FinDist.prod`: the uniform distribution, pushforward along a
  function, and the product (independent pair) of two distributions.
* `FinDist.collision`: the collision probability `∑ p a ^ 2`, i.e. the chance that two
  independent samples agree.
* `FinDist.HasMinEntropy p k`: every outcome has probability at most `2 ^ (-k)`.

## Main results

* `FinDist.collision_le_of_hasMinEntropy`: min-entropy `k` bounds the collision probability by
  `2 ^ (-k)`.
* `FinDist.collision_uniform`, `FinDist.inv_card_le_collision`: the uniform distribution
  minimizes collision probability.

## References

* [Vad12] S. Vadhan, *Pseudorandomness*, FnTTCS 7(1–3), 2012, §6.
* [Sho09] V. Shoup, *A Computational Introduction to Number Theory and Algebra*, 2nd ed., §8.
-/

namespace TCSlib.InformationTheory

open Finset

/-- A probability distribution on a finite type: nonnegative weights summing to one. -/
structure FinDist (α : Type*) [Fintype α] where
  /-- The probability assigned to each outcome. -/
  prob : α → ℝ
  /-- Probabilities are nonnegative. -/
  nonneg : ∀ a, 0 ≤ prob a
  /-- Probabilities sum to one. -/
  sum_prob : ∑ a, prob a = 1

namespace FinDist

variable {α β : Type*} [Fintype α] [Fintype β]

instance : CoeFun (FinDist α) (fun _ => α → ℝ) := ⟨FinDist.prob⟩

@[simp] theorem coe_mk (f : α → ℝ) (h₁ : ∀ a, 0 ≤ f a) (h₂ : ∑ a, f a = 1) (a : α) :
    (⟨f, h₁, h₂⟩ : FinDist α) a = f a := rfl

@[ext] theorem ext {p q : FinDist α} (h : ∀ a, p a = q a) : p = q := by
  cases p; cases q; simpa using funext h

theorem le_one (p : FinDist α) (a : α) : p a ≤ 1 := by
  rw [← p.sum_prob]
  exact single_le_sum (fun b _ => p.nonneg b) (mem_univ a)

theorem card_pos (p : FinDist α) : 0 < Fintype.card α := by
  by_contra hcon
  have hzero : Fintype.card α = 0 := by omega
  haveI : IsEmpty α := Fintype.card_eq_zero_iff.1 hzero
  have hsum := p.sum_prob
  rw [Finset.univ_eq_empty, Finset.sum_empty] at hsum
  norm_num at hsum

instance (p : FinDist α) : Nonempty α := Fintype.card_pos_iff.1 p.card_pos

/-- The uniform distribution on a nonempty finite type. -/
noncomputable def uniform (α : Type*) [Fintype α] [Nonempty α] : FinDist α where
  prob _ := (Fintype.card α : ℝ)⁻¹
  nonneg _ := by positivity
  sum_prob := by
    have hc : (Fintype.card α : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
    rw [Finset.sum_const, card_univ, nsmul_eq_mul]
    field_simp

@[simp] theorem uniform_apply [Nonempty α] (a : α) :
    uniform α a = (Fintype.card α : ℝ)⁻¹ := rfl

/-- The pushforward of a distribution along a function. -/
def map [DecidableEq β] (f : α → β) (p : FinDist α) : FinDist β where
  prob b := ∑ a ∈ univ.filter (fun a => f a = b), p a
  nonneg _ := sum_nonneg fun a _ => p.nonneg a
  sum_prob := by
    rw [← p.sum_prob]
    exact sum_fiberwise_eq_sum_filter univ univ f p.prob ▸ (sum_fiberwise _ _ _)

@[simp] theorem map_apply [DecidableEq β] (f : α → β) (p : FinDist α) (b : β) :
    map f p b = ∑ a ∈ univ.filter (fun a => f a = b), p a := rfl

/-- The product of two distributions: an independent pair. -/
def prod (p : FinDist α) (q : FinDist β) : FinDist (α × β) where
  prob x := p x.1 * q x.2
  nonneg x := mul_nonneg (p.nonneg _) (q.nonneg _)
  sum_prob := by
    rw [Fintype.sum_prod_type]
    simp [← Finset.mul_sum, p.sum_prob, q.sum_prob]

@[simp] theorem prod_apply (p : FinDist α) (q : FinDist β) (x : α × β) :
    prod p q x = p x.1 * q x.2 := rfl

/-- The collision probability of `p`: the probability that two independent samples from `p`
are equal. [Vad12, §6.1] -/
def collision (p : FinDist α) : ℝ := ∑ a, p a ^ 2

theorem collision_nonneg (p : FinDist α) : 0 ≤ collision p :=
  sum_nonneg fun _ _ => sq_nonneg _

@[simp] theorem collision_uniform [Nonempty α] :
    collision (uniform α) = (Fintype.card α : ℝ)⁻¹ := by
  have hc : (Fintype.card α : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  simp only [collision, uniform_apply, Finset.sum_const, card_univ, nsmul_eq_mul]
  field_simp

/-- Uniform is the distribution of least collision probability. -/
theorem inv_card_le_collision (p : FinDist α) : (Fintype.card α : ℝ)⁻¹ ≤ collision p := by
  have hc : (0 : ℝ) < Fintype.card α := by exact_mod_cast p.card_pos
  have h := sq_sum_le_card_mul_sum_sq (s := (univ : Finset α)) (f := p.prob)
  rw [p.sum_prob, card_univ] at h
  have h2 : (1 : ℝ) ≤ (Fintype.card α : ℝ) * collision p := by
    simpa [collision] using h
  rw [inv_le_iff_one_le_mul₀ hc]
  linarith [mul_comm (Fintype.card α : ℝ) (collision p)]

/-- `p` has min-entropy at least `k` when no outcome has probability more than `2 ^ (-k)`.
Stated as this bound rather than as `-logb 2 (⨆ a, p a)` so that no logarithms appear in the
hypotheses of the results that use it. [Vad12, §6.2] -/
def HasMinEntropy (p : FinDist α) (k : ℝ) : Prop := ∀ a, p a ≤ (2 : ℝ) ^ (-k)

/-- Min-entropy `k` bounds the collision probability by `2 ^ (-k)`: the chance of a collision is
at most the chance of hitting any single most-likely point.

**Proof sketch.** `∑ p a ^ 2 ≤ (max p) · ∑ p a = max p ≤ 2 ^ (-k)`. -/
theorem collision_le_of_hasMinEntropy {p : FinDist α} {k : ℝ} (h : HasMinEntropy p k) :
    collision p ≤ (2 : ℝ) ^ (-k) := by
  calc collision p = ∑ a, p a * p a := by simp [collision, sq]
    _ ≤ ∑ a, (2 : ℝ) ^ (-k) * p a :=
        sum_le_sum fun a _ => mul_le_mul_of_nonneg_right (h a) (p.nonneg a)
    _ = (2 : ℝ) ^ (-k) := by rw [← Finset.mul_sum, p.sum_prob, mul_one]

end FinDist

end TCSlib.InformationTheory

## ===== TCSlib/Cryptography/Foundations/Probability.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Real.Basic
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Linarith

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Uniform probability on finite types

Every probability in the concrete layer of the cryptography development is the
probability of an event under the uniform distribution on a finite type: inputs, keys
and coin strings are uniform, and an experiment's sample space is the product of their
types. So probabilities are exact counts, `uprob p = |{a | p a}| / |α|`, and
expectations are averages. Distributions that are not uniform arise as pushforwards
of uniform coins.

## Main definitions

* `uprob p`: the probability that a uniformly random element satisfies `p`.
* `uexp f`: the average of a real function over a finite type.

## Main results

* `uprob_nonneg`, `uprob_le_one`, `uprob_not`, `uprob_mono`, `uprob_or_le`,
  `uprob_exists_le`: basic laws and the union bound.
* `uprob_prod`: probability over a product is the average of the probabilities of
  the sections.
* `uprob_comp_equiv`: probability is invariant under relabelling by a bijection.
* `half_le_uprob_good`: the averaging argument — if an event has probability at least
  `ε`, then at least an `ε / 2` fraction of first coordinates have a section of
  probability at least `ε / 2`.
* `abs_sub_le_sum_hybrids`, `exists_hybrid_gap`: the hybrid argument for a chain of
  probabilities.

## References

* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §2.3 (Lemma 2.1) and §3.2 (proof of Lemma 3.3).
-/

namespace TCSlib.Cryptography

open Finset

variable {α β : Type*} [Fintype α] [Fintype β]

/-- The probability that a uniformly random element of the finite type `α` satisfies `p`,
the number of elements satisfying `p` divided by the number of elements. -/
noncomputable def uprob (p : α → Prop) : ℝ :=
  (Nat.card {a // p a} : ℝ) / Fintype.card α

/-- The average of a real function over the finite type `α`, its expectation under the
uniform distribution. -/
noncomputable def uexp (f : α → ℝ) : ℝ :=
  (∑ a, f a) / Fintype.card α

/-- With decidable `p`, the probability counts the elements of the filter. -/
theorem uprob_eq_card_filter (p : α → Prop) [DecidablePred p] :
    uprob p = ((univ.filter p).card : ℝ) / Fintype.card α := by
  rw [uprob, Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- The probability of an event is the average of its indicator. -/
theorem uprob_eq_uexp (p : α → Prop) [DecidablePred p] :
    uprob p = uexp (fun a => if p a then (1 : ℝ) else 0) := by
  rw [uprob_eq_card_filter, uexp, Finset.sum_boole]

/-- Probabilities are nonnegative. -/
theorem uprob_nonneg (p : α → Prop) : 0 ≤ uprob p := by
  unfold uprob; positivity

/-- Probabilities are at most one. -/
theorem uprob_le_one (p : α → Prop) : uprob p ≤ 1 := by
  classical
  rw [uprob_eq_card_filter]
  exact div_le_one_of_le₀ (by exact_mod_cast card_le_univ _) (by positivity)

/-- The certain event has probability one on a nonempty type. -/
theorem uprob_true [Nonempty α] : uprob (fun _ : α => True) = 1 := by
  classical
  rw [uprob_eq_card_filter, filter_true, card_univ]
  exact div_self (Nat.cast_ne_zero.2 Fintype.card_ne_zero)

/-- The impossible event has probability zero. -/
theorem uprob_false : uprob (fun _ : α => False) = 0 := by
  classical
  rw [uprob_eq_card_filter, filter_false, card_empty, Nat.cast_zero, zero_div]

/-- The complement of an event has probability one minus its probability.

**Proof sketch.** The elements satisfying `p` and those satisfying `¬ p` partition `α`, so
their counts add up to `|α|`. -/
theorem uprob_not [Nonempty α] (p : α → Prop) : uprob (fun a => ¬ p a) = 1 - uprob p := by
  classical
  have hc : (Fintype.card α : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have h := filter_card_add_filter_neg_card_eq_card (s := univ) p
  rw [card_univ] at h
  rw [uprob_eq_card_filter, uprob_eq_card_filter, eq_sub_iff_add_eq, ← add_div,
    div_eq_one_iff_eq hc]
  exact_mod_cast (by omega : (univ.filter fun a => ¬ p a).card + (univ.filter p).card =
    Fintype.card α)

/-- An event implied by another has at least its probability. -/
theorem uprob_mono {p q : α → Prop} (h : ∀ a, p a → q a) : uprob p ≤ uprob q := by
  classical
  rw [uprob_eq_card_filter, uprob_eq_card_filter]
  gcongr with a
  exact h a

/-- Union bound for two events. -/
theorem uprob_or_le (p q : α → Prop) : uprob (fun a => p a ∨ q a) ≤ uprob p + uprob q := by
  classical
  rw [uprob_eq_card_filter, uprob_eq_card_filter, uprob_eq_card_filter, ← add_div, filter_or]
  gcongr
  exact_mod_cast card_union_le _ _

/-- Union bound for finitely many events.

**Proof sketch.** The set where some `p i` holds is the union over `i ∈ s` of the sets
where `p i` holds, and the size of a union is at most the sum of the sizes. -/
theorem uprob_exists_le {ι : Type*} (s : Finset ι) (p : ι → α → Prop) :
    uprob (fun a => ∃ i ∈ s, p i a) ≤ ∑ i ∈ s, uprob (p i) := by
  classical
  rw [uprob_eq_card_filter]
  simp_rw [uprob_eq_card_filter, ← sum_div]
  gcongr
  have : (univ.filter fun a => ∃ i ∈ s, p i a) = s.biUnion (fun i => univ.filter (p i)) := by
    ext a; simp
  rw [this]
  exact_mod_cast card_biUnion_le

/-- Probability over a product is the average over the first coordinate of the
probability of the section: Fubini for uniform distributions.

**Proof sketch.** Count the pairs satisfying `p` by first coordinate:
`|{z | p z}| / (|α| |β|) = (∑ a, |{b | p (a, b)}| / |β|) / |α|`. -/
theorem uprob_prod (p : α × β → Prop) :
    uprob p = uexp (fun a => uprob (fun b => p (a, b))) := by
  classical
  simp_rw [uexp, uprob_eq_card_filter, ← sum_div, div_div, Fintype.card_prod, Nat.cast_mul,
    mul_comm (Fintype.card β : ℝ)]
  congr 1
  simp_rw [card_filter]
  push_cast
  exact Fintype.sum_prod_type _

/-- Relabelling the sample space by a bijection preserves probabilities. In particular a
permutation of a uniform input is uniform. -/
theorem uprob_comp_equiv (e : α ≃ β) (p : β → Prop) : uprob (fun a => p (e a)) = uprob p := by
  rw [uprob, uprob, Nat.card_congr (e.subtypeEquiv (fun _ => Iff.rfl)),
    Fintype.card_congr e]

/-- An event depending only on the first coordinate has the same probability on the
product.

**Proof sketch.** By `uprob_prod`, the section at `a` is the certain or the impossible
event according to `p a`, so its probability is the indicator of `p a`, whose average
is `uprob p`. -/
theorem uprob_fst [Nonempty β] (p : α → Prop) : uprob (fun z : α × β => p z.1) = uprob p := by
  classical
  rw [uprob_prod, uprob_eq_uexp]
  congr 1
  funext a
  by_cases h : p a <;> simp [h, uprob_true, uprob_false]

/-- The averaging argument: if an event on `α × β` has probability at least `ε`, then
the first coordinates whose section has probability at least `ε / 2` have probability
at least `ε / 2`. [Gar26, Lemma 2.1].

**Proof sketch.** For `ε < 0` the claim is trivial, and for empty `α` both sides vanish.
Otherwise every section has probability at most `[a is good] + ε / 2`: a good `a` has
section probability at most `1`, a bad one below `ε / 2`. Averaging over `a` with Fubini
(`uprob_prod`) gives `ε ≤ uprob p ≤ Pr[good] + ε / 2`. -/
theorem half_le_uprob_good (p : α × β → Prop) {ε : ℝ} (h : ε ≤ uprob p) :
    ε / 2 ≤ uprob (fun a => ε / 2 ≤ uprob (fun b => p (a, b))) := by
  classical
  rcases lt_or_ge ε 0 with hε | hε
  · linarith [uprob_nonneg (fun a => ε / 2 ≤ uprob (fun b => p (a, b)))]
  rcases isEmpty_or_nonempty α with hα | hα
  · have : uprob p = 0 := by
      rw [uprob, Fintype.card_eq_zero, Nat.cast_zero, div_zero]
    linarith [uprob_nonneg (fun a => ε / 2 ≤ uprob (fun b => p (a, b)))]
  have hc : (0 : ℝ) < Fintype.card α := Nat.cast_pos.2 Fintype.card_pos
  rw [uprob_prod, uexp] at h
  rw [uprob_eq_uexp, uexp]
  have hpt : ∀ a, uprob (fun b => p (a, b)) ≤
      (if ε / 2 ≤ uprob (fun b => p (a, b)) then (1 : ℝ) else 0) + ε / 2 := by
    intro a
    split_ifs with hg
    · linarith [uprob_le_one (fun b => p (a, b))]
    · linarith
  have hsum := sum_le_sum (fun a (_ : a ∈ univ) => hpt a)
  rw [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul] at hsum
  rw [le_div_iff₀ hc] at h ⊢
  linarith

/-- The hybrid argument, telescoping form: the gap between the ends of a chain is at
most the sum of the gaps between neighbours. [Gar26, proof of Lemma 3.3].

**Proof sketch.** Induction on `t` with the triangle inequality
`|P 0 - P (t+1)| ≤ |P 0 - P t| + |P t - P (t+1)|`. -/
theorem abs_sub_le_sum_hybrids (P : ℕ → ℝ) (t : ℕ) :
    |P 0 - P t| ≤ ∑ i ∈ range t, |P i - P (i + 1)| := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [sum_range_succ]
    exact (abs_sub_le _ _ _).trans (add_le_add_right ih _)

/-- The hybrid argument: in a chain of `t ≥ 1` steps some neighbouring pair is at least
a `1 / t` fraction of the end-to-end gap apart. [Gar26, proof of Lemma 3.3].

**Proof sketch.** Otherwise the telescoping bound gives a sum below `t · (gap / t)`. -/
theorem exists_hybrid_gap (P : ℕ → ℝ) {t : ℕ} (ht : 0 < t) :
    ∃ k < t, |P 0 - P t| / t ≤ |P k - P (k + 1)| := by
  by_contra hcon
  push_neg at hcon
  have hlt : ∑ i ∈ range t, |P i - P (i + 1)| < ∑ _i ∈ range t, |P 0 - P t| / t :=
    sum_lt_sum_of_nonempty (nonempty_range_iff.2 ht.ne') fun i hi => hcon i (mem_range.1 hi)
  have htR : (t : ℝ) ≠ 0 := Nat.cast_ne_zero.2 ht.ne'
  rw [sum_const, card_range, nsmul_eq_mul, mul_div_cancel₀ _ htR] at hlt
  linarith [abs_sub_le_sum_hybrids P t]

end TCSlib.Cryptography

## ===== TCSlib/Cryptography/Foundations/Experiments.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Foundations.Probability
import TCSlib.InformationTheory.StatisticalDistance

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Concrete security experiments

The concrete layer fixes one value of the security parameter and quantifies over all
adversaries, given as functions of their input and of a uniformly random coin string
from a finite type `ρ`. No running time is imposed here; efficiency is the job of the
asymptotic layer. The experiments are:

* inversion: on `f x` for uniform `x`, output some preimage of `f x`;
* prediction: on `f x`, output the bit `B x`;
* distinguishing: tell apart samples `X s` and `Y t` from uniform seeds `s` and `t`.

Samplers `X : σ → γ` from a finite seed type `σ` describe exactly the distributions
that are pushforwards of uniform coins, which covers every efficiently samplable
ensemble at a fixed parameter.

## Main definitions

* `invProb f A`: the probability that `A` inverts `f`.
* `predProb f B A`: the probability that `A` predicts `B` from `f`.
* `acceptProb X D`: the probability that `D` accepts a sample of `X`.
* `distAdv X Y D`: the distinguishing advantage of `D` between `X` and `Y`.

## Main results

* `acceptProb_comp_equiv`: relabelling the seeds by a bijection preserves acceptance.
* `abs_sum_sub_le_statDist`: a test set distinguishes two distributions by at most
  their statistical distance.
* `distAdv_le_statDist`: the distinguishing advantage of any distinguisher is at most
  the statistical distance of the sampled distributions.

## References

* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, Definition 2.1 (inversion), Definition 2.3 (prediction),
  Definitions 3.2–3.4 and Lemma 3.1 (distinguishing).
-/

namespace TCSlib.Cryptography

open Finset TCSlib.InformationTheory

variable {α β ρ σ τ γ : Type*} [Fintype α] [Fintype ρ] [Fintype σ] [Fintype τ]

/-- The probability that the adversary `A`, given `f x` for uniform `x` and uniform coins
`r`, outputs a preimage of `f x`. [Gar26, Definition 2.1, Equation (2.1)], at one value of
the security parameter; the input `1^n` is implicit in the fixed types. -/
noncomputable def invProb (f : α → β) (A : β → ρ → α) : ℝ :=
  uprob fun z : α × ρ => f (A (f z.1) z.2) = f z.1

/-- The probability that the adversary `A`, given `f x` for uniform `x` and uniform coins
`r`, outputs the bit `B x`. [Gar26, Definition 2.3], at one value of the security
parameter. -/
noncomputable def predProb (f : α → β) (B : α → Bool) (A : β → ρ → Bool) : ℝ :=
  uprob fun z : α × ρ => A (f z.1) z.2 = B z.1

/-- The probability that the distinguisher `D` with uniform coins accepts a sample `X s`
for a uniform seed `s`. [Gar26, Definitions 3.2 and 3.4], the quantities `p(n)` and
`q(n)`. -/
noncomputable def acceptProb (X : σ → γ) (D : γ → ρ → Bool) : ℝ :=
  uprob fun z : σ × ρ => D (X z.1) z.2 = true

/-- The distinguishing advantage of `D` between the sampled distributions `X` and `Y`,
`|Pr[D(X) = 1] - Pr[D(Y) = 1]|`. [Gar26, Definitions 3.2 and 3.4], the quantity
`Δ_A(n)`. -/
noncomputable def distAdv (X : σ → γ) (Y : τ → γ) (D : γ → ρ → Bool) : ℝ :=
  |acceptProb X D - acceptProb Y D|

/-- Relabelling the seed space of a sampler by a bijection does not change the probability
that a distinguisher accepts: a bijective image of a uniform seed is uniform. -/
theorem acceptProb_comp_equiv (e : σ ≃ τ) (X : τ → γ) (D : γ → ρ → Bool) :
    acceptProb (fun s => X (e s)) D = acceptProb X D :=
  uprob_comp_equiv (e.prodCongr (Equiv.refl ρ)) (fun z : τ × ρ => D (X z.1) z.2 = true)

/-- The probability that a uniform seed `s` has `X s` in an event `q` is the mass of `q` under
the pushforward of the uniform distribution along `X`. Technical glue between `uprob` and
`FinDist.map`.

**Proof sketch.** Both sides equal `∑ s, [q (X s)] / |σ|`: on the right, group the seeds
by their image under `X`. -/
theorem uprob_comp_eq_sum_map [Nonempty σ] [Fintype γ] [DecidableEq γ] (X : σ → γ)
    (q : γ → Prop) [DecidablePred q] :
    uprob (fun s => q (X s)) = ∑ g ∈ univ.filter q, (FinDist.uniform σ).map X g := by
  rw [uprob_eq_card_filter, sum_filter]
  have h := Finset.sum_fiberwise' univ X
    (fun g => if q g then (Fintype.card σ : ℝ)⁻¹ else 0)
  have h2 : ∑ s, (if q (X s) then (Fintype.card σ : ℝ)⁻¹ else 0) =
      ((univ.filter fun s => q (X s)).card : ℝ) / Fintype.card σ := by
    rw [← sum_filter, sum_const, nsmul_eq_mul, div_eq_mul_inv]
  rw [← h2, ← h]
  refine sum_congr rfl fun g _ => ?_
  split_ifs <;> simp [FinDist.map_apply]

/-- The acceptance probability of `D` on samples of `X` is the average over the coins `r` of
the mass, under the distribution of `X`, of the set of samples that `D` accepts with coins
`r`. Technical glue for `distAdv_le_statDist`.

**Proof sketch.** Swap the two coordinates of the sample space, apply Fubini
(`uprob_prod`) to average over the coins first, and rewrite each section with
`uprob_comp_eq_sum_map`. -/
theorem acceptProb_eq_uexp_sum_map [Nonempty σ] [Fintype γ] [DecidableEq γ] (X : σ → γ)
    (D : γ → ρ → Bool) :
    acceptProb X D = uexp (fun r : ρ => ∑ g ∈ univ.filter (fun g => D g r = true),
        (FinDist.uniform σ).map X g) := by
  rw [acceptProb, ← uprob_comp_equiv (Equiv.prodComm ρ σ), uprob_prod]
  congr 1
  funext r
  exact uprob_comp_eq_sum_map X (fun g => D g r = true)

/-- For any set `T` of outcomes, `|p(T) - q(T)|` is at most the statistical distance of `p`
and `q`. This is the deterministic case of [Gar26, Lemma 3.1].

**Proof sketch.** The differences `d = p - q` sum to zero, so the sum of `d` over the
complement of `T` is `-d(T)`. Splitting `∑ |d|` over `T` and its complement and applying
the triangle inequality to each part gives `∑ |d| ≥ 2 |d(T)|`. -/
theorem abs_sum_sub_le_statDist [Fintype γ] (p q : FinDist γ) (T : Finset γ) :
    |∑ g ∈ T, (p g - q g)| ≤ statDist p q := by
  classical
  have h0 : ∑ g, (p g - q g) = 0 := by
    rw [sum_sub_distrib, p.sum_prob, q.sum_prob, sub_self]
  have hsplit := sum_add_sum_compl T (fun g => p g - q g)
  have habs := sum_add_sum_compl T (fun g => |p g - q g|)
  have h1 := abs_sum_le_sum_abs (fun g => p g - q g) T
  have h2 := abs_sum_le_sum_abs (fun g => p g - q g) Tᶜ
  have hneg : ∑ g ∈ Tᶜ, (p g - q g) = -∑ g ∈ T, (p g - q g) := by linarith
  rw [hneg, abs_neg] at h2
  rw [statDist]
  linarith

/-- The distinguishing advantage of any distinguisher, deterministic or with coins, is at
most the statistical distance of the two sampled distributions. [Gar26, Lemma 3.1].

**Proof sketch.** Average over the coins (`acceptProb_eq_uexp_sum_map`): for fixed coins
`r` the distinguisher is a test set `T_r`, whose advantage is `|X(T_r) - Y(T_r)|`. By
`abs_sum_sub_le_statDist` each of these is at most the statistical distance, and the
absolute value of an average is at most the average of the absolute values. -/
theorem distAdv_le_statDist [Nonempty σ] [Nonempty τ] [Nonempty ρ] [Fintype γ]
    [DecidableEq γ] (X : σ → γ) (Y : τ → γ) (D : γ → ρ → Bool) :
    distAdv X Y D ≤
      statDist ((FinDist.uniform σ).map X) ((FinDist.uniform τ).map Y) := by
  have hρ : (0 : ℝ) < Fintype.card ρ := Nat.cast_pos.2 Fintype.card_pos
  rw [distAdv, acceptProb_eq_uexp_sum_map X, acceptProb_eq_uexp_sum_map Y, uexp, uexp,
    ← sub_div, ← sum_sub_distrib, abs_div, abs_of_pos hρ, div_le_iff₀ hρ]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  rw [mul_comm, ← nsmul_eq_mul, ← card_univ, ← sum_const]
  refine sum_le_sum fun r _ => ?_
  rw [← sum_sub_distrib]
  exact abs_sum_sub_le_statDist _ _ _

end TCSlib.Cryptography

## ===== TCSlib/Cryptography/Pseudorandom/Functions/OracleAdversary.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Foundations.Experiments

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Adaptive oracle adversaries as query trees

An oracle adversary asks its oracle a question, looks at the answer, chooses the next
question, and finally outputs a value. At one fixed value of the security parameter such
an adversary (for a fixed coin string) is exactly a finite tree: a leaf carries the output,
and an inner node carries a query `x : I` and one subtree for each possible answer `o : O`.
The coins are a uniform element of a finite type `ρ`, so a randomized oracle adversary is a
function `ρ → QueryTree I O α`.

Running the adversary against an oracle `f : I → O` follows the path chosen by the
answers `f x`. The adversary makes at most `q` queries when every root-to-leaf path has at
most `q` inner nodes. The cost of a query in [Gar26, Definition 3.9] ("each call to that
function costs 1 unit of time") is accounted by this bound; running time otherwise is the
business of the asymptotic layer.

Answering the queries of one adversary by a computation that itself asks queries to a
second oracle (`simulate`) is the basic reduction step: the simulated tree makes the same
number of queries.

## Main definitions

* `QueryTree I O α`: adaptive query trees with queries in `I`, answers in `O` and outputs
  in `α`.
* `QueryTree.eval f t`: the output of `t` run against the oracle `f`.
* `QueryTree.BoundedBy t q`: every path of `t` makes at most `q` queries.
* `QueryTree.simulate π ans t`: answer each query `x` of `t` by asking `π x` to a new oracle
  and post-processing the answer with `ans x`.
* `OracleAdversary ρ I O`: randomized Boolean oracle adversaries with coins in `ρ`.
* `oracleDist A`: the adversary viewed as a distinguisher for oracles.

## Main results

* `QueryTree.eval_simulate`: running the simulated tree against `g` is running the
  original tree against the oracle `x ↦ ans x (g (π x))`.
* `QueryTree.BoundedBy.simulate`: simulation preserves the query bound.
* `QueryTree.BoundedBy.mono`: query bounds are monotone.

## References

* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, Definition 3.9 (oracle adversaries).
-/

namespace TCSlib.Cryptography

universe u v w u' v'

/-- An adaptive oracle algorithm with queries in `I`, answers in `O` and output in `α`,
as a decision tree: `ret a` stops and outputs `a`, and `query x k` asks the oracle at `x`
and continues with the subtree `k o` for the answer `o`. This is the concrete form of an
oracle adversary with fixed coins [Gar26, Definition 3.9]. -/
inductive QueryTree (I : Type u) (O : Type v) (α : Type w) : Type (max u v w)
  /-- Stop and output `a`. -/
  | ret : α → QueryTree I O α
  /-- Ask the oracle at `x` and continue with `k` applied to the answer. -/
  | query : I → (O → QueryTree I O α) → QueryTree I O α

namespace QueryTree

variable {I : Type u} {O : Type v} {α : Type w} {I' : Type u'} {O' : Type v'}

/-- The output of the query tree `t` when every query `x` is answered by `f x`. -/
def eval (f : I → O) : QueryTree I O α → α
  | ret a => a
  | query x k => eval f (k (f x))

/-- A leaf outputs its value. -/
@[simp] theorem eval_ret (f : I → O) (a : α) : (ret a : QueryTree I O α).eval f = a := rfl

/-- A query node continues with the subtree for the oracle's answer. -/
@[simp] theorem eval_query (f : I → O) (x : I) (k : O → QueryTree I O α) :
    (query x k).eval f = (k (f x)).eval f := rfl

/-- The query tree `t` makes at most `q` oracle queries along every path: a leaf is
bounded by every `q`, and `query x k` is bounded by `q + 1` when every continuation `k o`
is bounded by `q`. -/
def BoundedBy : QueryTree I O α → ℕ → Prop
  | ret _, _ => True
  | query _ _, 0 => False
  | query _ k, q + 1 => ∀ o, BoundedBy (k o) q

/-- A leaf makes no queries. -/
@[simp] theorem boundedBy_ret (a : α) (q : ℕ) : (ret a : QueryTree I O α).BoundedBy q :=
  trivial

/-- A query node makes at least one query. -/
@[simp] theorem boundedBy_query_zero (x : I) (k : O → QueryTree I O α) :
    ¬ (query x k).BoundedBy 0 := id

/-- A query node makes at most `q + 1` queries iff every continuation makes at most
`q`. -/
@[simp] theorem boundedBy_query_succ (x : I) (k : O → QueryTree I O α) (q : ℕ) :
    (query x k).BoundedBy (q + 1) ↔ ∀ o, (k o).BoundedBy q := Iff.rfl

/-- A tree making at most `q` queries makes at most `q'` queries for every `q' ≥ q`. -/
theorem BoundedBy.mono {t : QueryTree I O α} {q q' : ℕ} (h : t.BoundedBy q)
    (hq : q ≤ q') : t.BoundedBy q' := by
  induction t generalizing q q' with
  | ret a => trivial
  | query x k ih =>
    cases q with
    | zero => exact absurd h (boundedBy_query_zero x k)
    | succ q =>
      obtain ⟨q', rfl⟩ : ∃ q'', q' = q'' + 1 := ⟨q' - 1, by omega⟩
      exact fun o => ih o (h o) (by omega)

/-- Simulation of oracle queries: each query `x` of `t` is replaced by the query `π x` to a
new oracle with answers in `O'`, whose answer `o'` is turned into the answer `ans x o'` for
`t`. The simulated tree asks exactly one new query per original query. -/
def simulate (π : I → I') (ans : I → O' → O) : QueryTree I O α → QueryTree I' O' α
  | ret a => ret a
  | query x k => query (π x) (fun o' => simulate π ans (k (ans x o')))

/-- Running the simulated tree against `g` is running the original tree against the
oracle that answers `x` by `ans x (g (π x))`. -/
@[simp] theorem eval_simulate (π : I → I') (ans : I → O' → O) (g : I' → O')
    (t : QueryTree I O α) :
    (t.simulate π ans).eval g = t.eval (fun x => ans x (g (π x))) := by
  induction t with
  | ret a => rfl
  | query x k ih => exact ih _

/-- Simulation does not increase the number of queries. -/
theorem BoundedBy.simulate {t : QueryTree I O α} {q : ℕ} (h : t.BoundedBy q)
    (π : I → I') (ans : I → O' → O) : (t.simulate π ans).BoundedBy q := by
  induction t generalizing q with
  | ret a => trivial
  | query x k ih =>
    cases q with
    | zero => exact absurd h (boundedBy_query_zero x k)
    | succ q => exact fun o' => ih _ (h _)

end QueryTree

/-- A randomized Boolean oracle adversary with coins in `ρ`: for every coin string a query
tree with queries in `I`, answers in `O` and a one-bit output. [Gar26, Definition 3.9]
at one value of the security parameter; the input `1^n` is implicit in the fixed types,
and the coins are uniform over the finite type `ρ`. -/
abbrev OracleAdversary (ρ : Type*) (I : Type u) (O : Type v) := ρ → QueryTree I O Bool

/-- The randomized oracle adversary `A` makes at most `q` queries on every coin string and
every path. -/
def OracleAdversary.BoundedBy {ρ : Type*} {I : Type u} {O : Type v}
    (A : OracleAdversary ρ I O) (q : ℕ) : Prop :=
  ∀ r, (A r).BoundedBy q

/-- The oracle adversary `A` as a distinguisher for oracles: on the oracle `f` and coins
`r` it outputs the result of running `A r` against `f`. With a sampler for the oracle,
`acceptProb` of this distinguisher is the probability `Pr[A^f = 1]` of
[Gar26, Definition 3.9]. -/
def oracleDist {ρ : Type*} {I : Type u} {O : Type v} (A : OracleAdversary ρ I O) :
    (I → O) → ρ → Bool :=
  fun f r => (A r).eval f

end TCSlib.Cryptography

## ===== TCSlib/Cryptography/ZeroKnowledge/Interaction.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.Randomized.PPT
import TCSlib.Complexity.ClassNP.PolyTimePairing
import TCSlib.Cryptography.Foundations.Probability

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Interactive protocols: strategies, executions, views

The interaction model of [PS10, §4.4] in the form frozen by the campaign's foundation
decision D8 (`briefs/pass-shelat/DESIGN.md` §2.15). An interactive machine is a *next-message
strategy* `next x z r received`: given the common input `x`, the auxiliary input `z`, the
random tape `r` and the messages received so far, it returns the next message to send; its
value on the complete history is the party's output. A protocol is a pair of strategies with
an explicit polynomial number of messages (`rounds : PolyExpr`) and a first mover. The
execution `A_{r₁}(x, z₁) ↔ B_{r₂}(x, z₂)` is the fixed alternation of `rounds.eval |x|` moves
(`exec`), and the four derived objects of the text — the view of each party, the transcript,
and the outputs — are projections of it.

**Deviation (D8, recorded once here for the whole chapter):** no tapes, states or idle
transitions are modelled; "entering the idle state" is returning from `next`; the number of
messages is fixed by the protocol (a party that would halt is modelled as sending `[]`), and the
verifier's verdict is `V.next` on the complete history, so it is always defined. The text's
"a round ends when the active machine halts — in which case the protocol ends" makes the
literal `Pr[out_V = 0]` of [PS10, Definition 116.1] unsatisfiable against a prover that halts
at once; the fixed-alternation reading is the one under which that clause is satisfiable.
Verdict convention (run-3 audit P9-3): when the verifier is the last mover, the verdict
activation has exactly the arguments of the activation that produced its last message, so its
last message *is* its verdict (`Protocol.outV_eq_getLast_of_moverIsV`); the chapter's protocols
are stated with the prover moving last, and the `n`-fold protocols read the verifier's last
message as the verdict.
`Strategy.Efficient` ([PS10, §4.4], time complexity of an interactive machine) is one
activation of a uniform `Complexity.NUPPT` at parameter `|x|` on `⟨⟨x, z⟩, messages⟩` with the
whole random tape; the time is polynomial in the total input length rather than in `|x|`
alone (the text's `t(|x|)` "regardless of messages" would leave the simulator's call to `V*`
on long auxiliary inputs ill-defined; see D8). Consequently `Efficient` alone does not bound a
party's work in `|x|` against a counterparty that sends long messages; the message-prefix cap
`Strategy.ReadsPrefix m` — the strategy depends only on the first `m(|x|)` bits of each received
message, as a time-`t(|x|)` machine of the text necessarily does — restores the text's bound,
and the class `IP` (`InteractiveProofs.lean`) requires it of the verifier (run-3 audit P9-1).

## Main definitions

* `TCSlib.Cryptography.Strategy` — a next-message strategy with an explicit coin polynomial
  [PS10, §4.4] (Def-114.a); `Strategy.ofNUPPT`, `Strategy.Efficient` (Def-116.b, the machine
  half), `Strategy.ReadsPrefix` (Def-116.b, the message-prefix cap of the text's bound in `|x|`).
* `TCSlib.Cryptography.exec` — the messages received by each party after `k` moves
  [PS10, §4.4] (Def-115.a).
* `TCSlib.Cryptography.View`, `TCSlib.Cryptography.View.encode` — a party's view
  `(x, z, r, received)` and its string encoding (Def-115.b).
* `TCSlib.Cryptography.Protocol` — two strategies, the number of messages and the first mover
  (Def-114.b); `Protocol.transcriptWith`, `Protocol.transcript` (Def-115.c), `Protocol.outV`,
  `Protocol.outP`, `Strategy.out` (Def-115.d), `Protocol.viewV`, `Protocol.viewP`,
  `Protocol.execution` (Def-115.a/b), `Protocol.withV`.

## Main results

* `TCSlib.Cryptography.exec_length` — after `k` moves exactly `k` messages have been sent.
* `TCSlib.Cryptography.Strategy.ofNUPPT_efficient` — every uniform machine is an efficient
  strategy (non-vacuity of Def-116.b).
* `TCSlib.Cryptography.Strategy.ReadsPrefix.mono`,
  `TCSlib.Cryptography.Strategy.ReadsPrefix.next_congr` — the message-prefix cap is monotone
  in the cap and makes the next message a function of the truncated history.
* `TCSlib.Cryptography.Protocol.outV_eq_getLast_of_moverIsV` — when the verifier is the last
  mover, its last message is its verdict (the verdict convention of D8).
* `TCSlib.Cryptography.Protocol.uprob_outV_eq_uexp`,
  `TCSlib.Cryptography.Protocol.exists_proverCoins_le` — random executions are samplers on the
  product of the two coin spaces (Def-116.a), and a prover's coins may be fixed without
  decreasing any event's probability (the "without loss of generality deterministic `P*`"
  remark of the soundness clause).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§4.4 Interactive protocols, pp. 114–116.)
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Cambridge
  University Press, 2009. (Chapter 8, interactive proofs.)
-/

namespace TCSlib.Cryptography

open Complexity Turing Finset

/-! ### Strategies -/

/-- A next-message strategy [PS10, §4.4] (Def-114.a): `next x z r received` is the message a
party sends on common input `x`, auxiliary input `z` and random tape `r` after having
*received* the listed messages; on the complete history its value is the party's output. The
random tape has the explicit polynomial length `coins.eval |x|`.

**Deviation (D8):** no tapes, states or idle transitions; the output function of the text is
the next-message function on the complete history. -/
structure Strategy where
  /-- The next-message function `(x, z, r, received) ↦ message`. -/
  next : List Bool → List Bool → List Bool → List (List Bool) → List Bool
  /-- The length of the random tape as a polynomial in `|x|`. -/
  coins : PolyExpr

namespace Strategy

/-- The number of random bits of a strategy at common-input length `n`. -/
def coinLen (S : Strategy) (n : ℕ) : ℕ := S.coins.eval n

/-- The random tape of a strategy at common-input length `n`: `coinLen n` uniform bits. -/
abbrev Coins (S : Strategy) (n : ℕ) : Type := Fin (S.coinLen n) → Bool

/-- The string encoding of a list of messages: right-nested `pairEncode` pairs ending in `[]`
(the encoding of the received-messages component of a view, Inf-4.1). -/
def encodeMsgs (h : List (List Bool)) : List Bool := h.foldr pairEncode []

/-- The encoding of the empty history is the empty string. -/
@[simp] theorem encodeMsgs_nil : encodeMsgs [] = [] := rfl

/-- The encoding of `m :: h` is the pair `⟨m, encodeMsgs h⟩`. -/
@[simp] theorem encodeMsgs_cons (m : List Bool) (h : List (List Bool)) :
    encodeMsgs (m :: h) = pairEncode m (encodeMsgs h) := rfl

/-- The first projection of an encoded history is its first message (`[]` when empty). -/
theorem pairFstD_encodeMsgs (h : List (List Bool)) : pairFstD (encodeMsgs h) = h.headD [] := by
  cases h with
  | nil => rfl
  | cons m h => simp

/-- The strategy computed by a machine `A`: one activation at parameter `|x|` on
`⟨⟨x, z⟩, messages⟩` with the whole random tape (`A.runAtL`); the coin polynomial is `A.coins`
[PS10, §4.4, the interactive machine as a Turing machine with a random tape]. -/
def ofNUPPT (A : NUPPT) : Strategy where
  next x z r hist := A.runAtL x.length (pairEncode (pairEncode x z) (encodeMsgs hist)) r
  coins := A.coins

/-- The next-message function of `ofNUPPT A` unfolds to one activation of `A`. -/
theorem ofNUPPT_next (A : NUPPT) (x z r : List Bool) (hist : List (List Bool)) :
    (ofNUPPT A).next x z r hist =
      A.runAtL x.length (pairEncode (pairEncode x z) (encodeMsgs hist)) r := rfl

/-- A PPT strategy [PS10, §4.4, time complexity of an interactive machine] (Def-116.b): the
next-message function is computed by a uniform `NUPPT` with the same coin polynomial, one
activation per message at parameter `|x|` on `⟨⟨x, z⟩, messages⟩` with the whole random tape.

**Deviation (D8):** per-activation time polynomial in the total input length `|x| + |z| +
|messages|` instead of the text's `t(|x|)` "regardless of the messages". The number of
activations is bounded by the protocol's `rounds`, but the messages of an unbounded
counterparty may be arbitrarily long, so `Efficient` alone does not bound a party's work in
`|x|` (run-3 audit P9-1). The text's bound is recovered by adding the message-prefix cap
`ReadsPrefix m`: an efficient strategy that reads only `m(|x|)` bits of each message runs in
time polynomial in `|x| + |z|`, and the class `IP` requires the cap of the verifier. -/
def Efficient (S : Strategy) : Prop :=
  ∃ A : NUPPT, A.Uniform ∧ S.coins = A.coins ∧
    ∀ x z r hist, S.next x z r hist = (ofNUPPT A).next x z r hist

/-- Non-vacuity of `Strategy.Efficient`: the strategy of a uniform machine is efficient. -/
theorem ofNUPPT_efficient (A : NUPPT) (hA : A.Uniform) : (ofNUPPT A).Efficient :=
  ⟨A, hA, rfl, fun _ _ _ _ => rfl⟩

/-- An efficient strategy has the coin polynomial of some uniform machine computing it. -/
theorem Efficient.exists_uniform {S : Strategy} (h : S.Efficient) :
    ∃ A : NUPPT, A.Uniform ∧ S.coins = A.coins := by
  obtain ⟨A, hA, hc, -⟩ := h
  exact ⟨A, hA, hc⟩

/-- A strategy reads at most an `m(|x|)`-bit prefix of each received message [PS10, §4.4, time
complexity: an interactive machine of time complexity `t(|x|)` reads at most `t(|x|)` cells of
its communication tape per activation, "independently of the content of the messages it
receives"] (Def-116.b, the message half of the text's bound in `|x|`): the next-message
function is unchanged when every received message is truncated to its first `m.eval |x|` bits.
Together with `Efficient` this is the text's PPT interactive machine — the activation is
computed in time polynomial in `|x| + |z| + rounds · m(|x|)` by truncating the messages first —
whereas `Efficient` alone is polynomial in the total message length (D8).

**Repair (run-3 audit P9-1):** added; the class `IP` requires it of the verifier. -/
def ReadsPrefix (S : Strategy) (m : PolyExpr) : Prop :=
  ∀ x z r hist, S.next x z r hist = S.next x z r (hist.map (List.take (m.eval x.length)))

/-- Under a message-prefix cap the next message depends only on the truncated history. -/
theorem ReadsPrefix.next_congr {S : Strategy} {m : PolyExpr} (h : S.ReadsPrefix m)
    {x z r : List Bool} {hist hist' : List (List Bool)}
    (he : hist.map (List.take (m.eval x.length)) = hist'.map (List.take (m.eval x.length))) :
    S.next x z r hist = S.next x z r hist' := by
  rw [h x z r hist, h x z r hist', he]

/-- The message-prefix cap is monotone: a cap `m` implies every pointwise larger cap `m'`
(`List.take_take`: truncating to `m'(|x|)` and then to `m(|x|) ≤ m'(|x|)` bits is truncating to
`m(|x|)` bits). -/
theorem ReadsPrefix.mono {S : Strategy} {m m' : PolyExpr} (h : S.ReadsPrefix m)
    (hle : ∀ n, m.eval n ≤ m'.eval n) : S.ReadsPrefix m' := by
  intro x z r hist
  refine h.next_congr ?_
  rw [List.map_map]
  refine List.map_congr_left fun msg _ => ?_
  simp only [Function.comp_apply, List.take_take, min_eq_left (hle _)]

end Strategy

/-! ### Executions -/

/-- Which party moves at move `k` (0-indexed): the verifier moves at the even positions when
it moves first, at the odd ones otherwise. -/
def moverIsV (vFirst : Bool) (k : ℕ) : Bool :=
  if vFirst then decide (k % 2 = 0) else decide (k % 2 = 1)

/-- With the verifier first, it moves at the even positions. -/
@[simp] theorem moverIsV_true (k : ℕ) : moverIsV true k = decide (k % 2 = 0) := rfl

/-- With the prover first, the verifier moves at the odd positions. -/
@[simp] theorem moverIsV_false (k : ℕ) : moverIsV false k = decide (k % 2 = 1) := rfl

/-- The messages received by `P` and by `V` after `k` moves of the execution
`P_{rP}(x, zP) ↔ V_{rV}(x, zV)` [PS10, §4.4, the execution `A_{r₁}(x, z₁) ↔ B_{r₂}(x, z₂)`]
(Def-115.a): at move `k` the active party applies its next-message function to the messages
it has received so far and the message is appended to the other party's received list. -/
def exec (P V : Strategy) (vFirst : Bool) (x zP zV rP rV : List Bool) :
    ℕ → List (List Bool) × List (List Bool)
  | 0 => ([], [])
  | k + 1 =>
    let e := exec P V vFirst x zP zV rP rV k
    if moverIsV vFirst k then (e.1 ++ [V.next x zV rV e.2], e.2)
    else (e.1, e.2 ++ [P.next x zP rP e.1])

/-- Before the first move nothing has been received. -/
@[simp] theorem exec_zero (P V : Strategy) (vFirst : Bool) (x zP zV rP rV : List Bool) :
    exec P V vFirst x zP zV rP rV 0 = ([], []) := rfl

/-- One more move: the active party's message is appended to the other party's list. -/
theorem exec_succ (P V : Strategy) (vFirst : Bool) (x zP zV rP rV : List Bool) (k : ℕ) :
    exec P V vFirst x zP zV rP rV (k + 1) =
      (let e := exec P V vFirst x zP zV rP rV k
       if moverIsV vFirst k then (e.1 ++ [V.next x zV rV e.2], e.2)
       else (e.1, e.2 ++ [P.next x zP rP e.1])) := rfl

/-- After `k` moves exactly `k` messages have been sent in total. -/
theorem exec_length (P V : Strategy) (vFirst : Bool) (x zP zV rP rV : List Bool) (k : ℕ) :
    (exec P V vFirst x zP zV rP rV k).1.length + (exec P V vFirst x zP zV rP rV k).2.length = k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [exec_succ]
    split_ifs <;> simp only [List.length_append, List.length_singleton] <;> omega

/-! ### Views -/

/-- A party's view [PS10, §4.4] (Def-115.b): the common input, its auxiliary input, its random
tape and the messages it received. -/
structure View where
  /-- The common input. -/
  x : List Bool
  /-- The party's auxiliary input. -/
  z : List Bool
  /-- The party's random tape. -/
  r : List Bool
  /-- The messages the party received, in order. -/
  received : List (List Bool)

/-- The string encoding of a view, `⟨⟨x, z⟩, ⟨r, messages⟩⟩` (the sample handed to
distinguishers and produced by simulators in the zero-knowledge definitions). -/
def View.encode (v : View) : List Bool :=
  pairEncode (pairEncode v.x v.z) (pairEncode v.r (Strategy.encodeMsgs v.received))

/-- The output of a party on a view [PS10, §4.4, `out(v)`] (Def-115.d): its next-message
function on the complete history. -/
def Strategy.out (S : Strategy) (v : View) : List Bool := S.next v.x v.z v.r v.received

/-! ### Protocols -/

/-- A protocol [PS10, §4.4] (Def-114.b): a prover strategy, a verifier strategy, the number of
messages exchanged (an explicit polynomial in `|x|`) and the first mover (`true` = verifier
first, as in the graph non-isomorphism protocol; `false` = prover first, as in the graph
isomorphism and 3-colouring protocols). The verifier's verdict is its next-message function
on the complete history.

**Deviation (D8):** fixed number of messages `rounds.eval |x|`; a halting party sends `[]`.
If the verifier is the last mover (prover first with an even number of messages, or verifier
first with an odd number), its last message coincides with its verdict — both are `V.next` on
the same history (`outV_eq_getLast_of_moverIsV`) — so a verifier whose final message differs
from its verdict is not expressible; protocols are therefore stated so that the prover moves
last, or the verifier's last message is read as the verdict (the `n`-fold protocols)
(run-3 audit P9-3). -/
structure Protocol where
  /-- The prover's strategy. -/
  P : Strategy
  /-- The verifier's strategy. -/
  V : Strategy
  /-- The number of messages exchanged, as a polynomial in `|x|`. -/
  rounds : PolyExpr
  /-- Whether the verifier sends the first message. -/
  verifierFirst : Bool

namespace Protocol

/-- The joint coin space of an execution of `π` with the prover strategy `P'` on `x`: the
prover's and the verifier's random tapes at parameter `|x|` [PS10, §4.4, random executions]
(Def-116.a). -/
abbrev ExecCoins (π : Protocol) (P' : Strategy) (x : List Bool) : Type :=
  P'.Coins x.length × π.V.Coins x.length

/-- The protocol with the verifier replaced by `V'` (the cheating verifier `V*` of the
zero-knowledge definitions), same prover, round count and first mover. -/
def withV (π : Protocol) (V' : Strategy) : Protocol := { π with V := V' }

/-- The verifier of `π.withV V'` is `V'`. -/
@[simp] theorem withV_V (π : Protocol) (V' : Strategy) : (π.withV V').V = V' := rfl

/-- The prover of `π.withV V'` is the prover of `π`. -/
@[simp] theorem withV_P (π : Protocol) (V' : Strategy) : (π.withV V').P = π.P := rfl

/-- The round count of `π.withV V'` is that of `π`. -/
@[simp] theorem withV_rounds (π : Protocol) (V' : Strategy) : (π.withV V').rounds = π.rounds := rfl

/-- The first mover of `π.withV V'` is that of `π`. -/
@[simp] theorem withV_verifierFirst (π : Protocol) (V' : Strategy) :
    (π.withV V').verifierFirst = π.verifierFirst := rfl

/-- Replacing the verifier by itself changes nothing. -/
@[simp] theorem withV_self (π : Protocol) : π.withV π.V = π := by
  cases π
  rfl

/-- The transcript (messages received by `P'`, messages received by `V`) of the execution
`P'_{r₁}(x, y) ↔ V_{r₂}(x, z)` with all `rounds.eval |x|` moves [PS10, §4.4] (Def-115.c). -/
def transcriptWith (π : Protocol) (P' : Strategy) (x y z : List Bool) (r : π.ExecCoins P' x) :
    List (List Bool) × List (List Bool) :=
  exec P' π.V π.verifierFirst x y z (List.ofFn r.1) (List.ofFn r.2) (π.rounds.eval x.length)

/-- The transcript of the honest execution `P(x, y) ↔ V(x, z)` (Def-115.c). -/
def transcript (π : Protocol) (x y z : List Bool) (r : π.ExecCoins π.P x) :
    List (List Bool) × List (List Bool) :=
  π.transcriptWith π.P x y z r

/-- The verifier's output in `P'_{r₁}(x, y) ↔ V_{r₂}(x, z)` [PS10, §4.4, `out_V`] (Def-115.d):
`V.next` on the complete history.

**Deviation (D8, run-3 audit P9-3):** when the verifier is the last mover this is also the
last message it sent (`outV_eq_getLast_of_moverIsV`); see `Protocol`. -/
def outV (π : Protocol) (P' : Strategy) (x y z : List Bool) (r : π.ExecCoins P' x) : List Bool :=
  π.V.next x z (List.ofFn r.2) (π.transcriptWith P' x y z r).2

/-- The honest prover's output in `P_{r₁}(x, y) ↔ V_{r₂}(x, z)` (Def-115.d). -/
def outP (π : Protocol) (x y z : List Bool) (r : π.ExecCoins π.P x) : List Bool :=
  π.P.next x y (List.ofFn r.1) (π.transcriptWith π.P x y z r).1

/-- The honest verifier's view of `P_{r₁}(x, y) ↔ V_{r₂}(x, z)` [PS10, §4.4, `view_V`]
(Def-115.b). -/
def viewV (π : Protocol) (x y z : List Bool) (r : π.ExecCoins π.P x) : View :=
  ⟨x, z, List.ofFn r.2, (π.transcriptWith π.P x y z r).2⟩

/-- The honest prover's view of `P_{r₁}(x, y) ↔ V_{r₂}(x, z)` [PS10, §4.4, `view_P`]
(Def-115.b). -/
def viewP (π : Protocol) (x y z : List Bool) (r : π.ExecCoins π.P x) : View :=
  ⟨x, y, List.ofFn r.1, (π.transcriptWith π.P x y z r).1⟩

/-- The execution `P_{r₁}(x, y) ↔ V_{r₂}(x, z)` as the pair of views (the joint view)
[PS10, §4.4] (Def-115.a). -/
def execution (π : Protocol) (x y z : List Bool) (r : π.ExecCoins π.P x) : View × View :=
  (π.viewP x y z r, π.viewV x y z r)

/-- The verifier's output is its output function on its view (Def-115.d). -/
theorem outV_eq_out (π : Protocol) (x y z : List Bool) (r : π.ExecCoins π.P x) :
    π.outV π.P x y z r = π.V.out (π.viewV x y z r) := rfl

/-- The prover's output is its output function on its view (Def-115.d). -/
theorem outP_eq_out (π : Protocol) (x y z : List Bool) (r : π.ExecCoins π.P x) :
    π.outP x y z r = π.P.out (π.viewP x y z r) := rfl

/-- The transcript is the pair of received-message components of the two views. -/
theorem transcript_eq (π : Protocol) (x y z : List Bool) (r : π.ExecCoins π.P x) :
    π.transcript x y z r = ((π.viewP x y z r).received, (π.viewV x y z r).received) := rfl

/-- The verifier's output against `P'` only depends on `P'` through the transcript. -/
theorem outV_withV (π : Protocol) (V' P' : Strategy) (x y z : List Bool)
    (r : (π.withV V').ExecCoins P' x) :
    (π.withV V').outV P' x y z r =
      V'.next x z (List.ofFn r.2)
        (exec P' V' π.verifierFirst x y z (List.ofFn r.1) (List.ofFn r.2)
          (π.rounds.eval x.length)).2 := rfl

/-- The verdict convention of D8 made explicit (run-3 audit P9-3): if the verifier makes the
last of the `k + 1` moves (`moverIsV verifierFirst k`), the last message it sent — the last
message `P'` received — is its verdict, because both are `V.next` on the messages `V` received
in the first `k` moves (`exec_succ`, `List.getLast?_concat`). -/
theorem outV_eq_getLast_of_moverIsV (π : Protocol) (P' : Strategy) (x y z : List Bool)
    (r : π.ExecCoins P' x) {k : ℕ} (hk : π.rounds.eval x.length = k + 1)
    (hV : moverIsV π.verifierFirst k = true) :
    (π.transcriptWith P' x y z r).1.getLast? = some (π.outV P' x y z r) := by
  unfold outV transcriptWith
  rw [hk, exec_succ]
  simp [hV]

/-! ### Random executions -/

/-- A random execution is a sampler on the product of the two coin spaces [PS10, §4.4]
(Def-116.a): the probability of any event of the verifier's output is the average over the
prover's coins of its conditional probability over the verifier's coins (`uprob_prod`). -/
theorem uprob_outV_eq_uexp (π : Protocol) (P' : Strategy) (x y z : List Bool)
    (p : List Bool → Prop) :
    uprob (fun r : π.ExecCoins P' x => p (π.outV P' x y z r)) =
      uexp (fun r₁ : P'.Coins x.length =>
        uprob (fun r₂ : π.V.Coins x.length => p (π.outV P' x y z (r₁, r₂)))) :=
  uprob_prod _

/-- A cheating prover may be taken deterministic: for every event of the verifier's output
there is a fixed prover random tape under which the event is at least as likely as on average
(the "without loss of generality `P*` is deterministic" remark behind the soundness clause of
[PS10, Definition 116.1]). -/
theorem exists_proverCoins_le (π : Protocol) (P' : Strategy) (x y z : List Bool)
    (p : List Bool → Prop) :
    ∃ r₁ : P'.Coins x.length,
      uprob (fun r : π.ExecCoins P' x => p (π.outV P' x y z r)) ≤
        uprob (fun r₂ : π.V.Coins x.length => p (π.outV P' x y z (r₁, r₂))) := by
  rw [uprob_outV_eq_uexp]
  set f : P'.Coins x.length → ℝ :=
    fun r₁ => uprob (fun r₂ : π.V.Coins x.length => p (π.outV P' x y z (r₁, r₂)))
  have hcard : (0 : ℝ) < Fintype.card (P'.Coins x.length) := by
    exact_mod_cast Fintype.card_pos
  have hsum : ∑ _a : P'.Coins x.length, uexp f ≤ ∑ a, f a := by
    rw [sum_const, card_univ, nsmul_eq_mul, uexp, mul_div_cancel₀ _ hcard.ne']
  obtain ⟨a, -, ha⟩ := exists_le_of_sum_le univ_nonempty hsum
  exact ⟨a, ha⟩

end Protocol

end TCSlib.Cryptography

## ===== briefs/pass-shelat-ch5-8/gates/02-s2a/evidence-r2/replay-head.log =====

# clean replay of S2a at 586510c1416afa21881b9a42b5a8d0578c9bd749, 2026-11-05T01:52:31Z
=== TCSlib/InformationTheory/FinDist rc=0
=== TCSlib/Cryptography/Foundations/Probability rc=0
=== TCSlib/Cryptography/Games/OracleComp rc=0
=== TCSlib/Cryptography/Games/Probability rc=0
=== TCSlib/Cryptography/Games/Simulate rc=0
=== TCSlib/Cryptography/Games/Advantage rc=0
=== TCSlib/Cryptography/Games/Hopping rc=0
=== TCSlib/Cryptography/Games/Protocols rc=0
=== TCSlib/Cryptography/Games rc=0
=== axioms rc=0 printed=75 sorryAx=0

## ===== briefs/pass-shelat-ch5-8/gates/02-s2a/evidence-r2/replay-order.txt =====

TCSlib/InformationTheory/FinDist
TCSlib/Cryptography/Foundations/Probability
TCSlib/Cryptography/Games/OracleComp
TCSlib/Cryptography/Games/Probability
TCSlib/Cryptography/Games/Simulate
TCSlib/Cryptography/Games/Advantage
TCSlib/Cryptography/Games/Hopping
TCSlib/Cryptography/Games/Protocols
TCSlib/Cryptography/Games

## ===== briefs/pass-shelat-ch5-8/gates/02-s2a/evidence-r2/axioms.log =====

# #print axioms over every theorem of the six Games modules, at 586510c1416afa21881b9a42b5a8d0578c9bd749 (probe: TCSlib.Cryptography.Games imported, 75 theorems)
'TCSlib.Cryptography.Games.OracleComp.bind_eq_bind' does not depend on any axioms
'TCSlib.Cryptography.Games.OracleComp.pure_eq_pure' does not depend on any axioms
'TCSlib.Cryptography.Games.OracleComp.map_eq_bind' does not depend on any axioms
'TCSlib.Cryptography.Games.OracleComp.pure_bind' does not depend on any axioms
'TCSlib.Cryptography.Games.OracleComp.query_bind' does not depend on any axioms
'TCSlib.Cryptography.Games.OracleComp.bind_pure' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Games.OracleComp.bind_assoc' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Games.OracleComp.call_bind' does not depend on any axioms
'TCSlib.Cryptography.Games.OracleComp.liftLeft_bind' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Games.OracleComp.liftRight_bind' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Games.OracleComp.costBoundedBy_pure' does not depend on any axioms
'TCSlib.Cryptography.Games.OracleComp.costBoundedBy_query' does not depend on any axioms
'TCSlib.Cryptography.Games.OracleComp.CostBoundedBy.mono' does not depend on any axioms
'TCSlib.Cryptography.Games.OracleComp.CostBoundedBy.bind' depends on axioms: [propext]
'TCSlib.Cryptography.Games.OracleComp.costBoundedBy_liftLeft' does not depend on any axioms
'TCSlib.Cryptography.Games.OracleComp.costBoundedBy_liftRight' does not depend on any axioms
'TCSlib.Cryptography.Games.ProbComp.expect_pure' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.expect_query' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.expect_bind' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.expect_map' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.expect_sampleFin' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.expect_sample' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.expect_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.expect_const_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.expect_const' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.expect_sum' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.expect_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.expect_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.prob_eq_expect' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.prob_pure' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.prob_bind' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.prob_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.prob_le_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.prob_mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.prob_congr' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.prob_or_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.prob_not' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.dist_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.simulate_pure' does not depend on any axioms
'TCSlib.Cryptography.Games.simulate_query' does not depend on any axioms
'TCSlib.Cryptography.Games.simulate_bind' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Games.simulate_call' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Games.simulate_comp' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Games.simulate_withLog' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Games.simulate_costBoundedBy' depends on axioms: [propext]
'TCSlib.Cryptography.Games.accept_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.accept_le_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.advantage_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.advantage_comm' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.advantage_self' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.advantage_le_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.advantage_triangle' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.advantage_hybrid' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.exists_advantage_hybrid_gap' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.accept_guessGame' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.guessAdv_eq_half_advantage' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.OracleComp.AllOutputs.mono' does not depend on any axioms
'TCSlib.Cryptography.Games.OracleComp.AllOutputs.bind' does not depend on any axioms
'TCSlib.Cryptography.Games.ProbComp.prob_split' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.expect_mono_of_allOutputs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.prob_eq_one_of_allOutputs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.prob_eq_zero_of_allOutputs' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.abs_prob_sub_le_of_agree' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.ProbComp.prob_mem_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.simulate_allOutputs_bad' does not depend on any axioms
'TCSlib.Cryptography.Games.prob_eq_until_bad' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.identical_until_bad' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.hagree_of_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.identical_until_bad_init' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Games.Party.exec_zero' does not depend on any axioms
'TCSlib.Cryptography.Games.Party.exec_succ' does not depend on any axioms
'TCSlib.Cryptography.Games.Party.stepT_fst' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Games.Party.closeT_fst' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Games.Party.endWithT_fst' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Games.Party.execT_outcome' depends on axioms: [propext, Quot.sound]

## ===== briefs/pass-shelat-ch5-8/gates/02-s2a/evidence-r2/style-lint.log =====

# style lints at 586510c1416afa21881b9a42b5a8d0578c9bd749
$ python3 -I scripts/style_lint.py TCSlib/Cryptography/Games/*.lean TCSlib/Cryptography/Games.lean
0 findings in 7 files
$ python3 -I scripts/campaign_style_lint.py TCSlib/Cryptography/Games
INFO  TCSlib/Cryptography/Games/Advantage.lean    159 lines; 15 public / 0 private declarations
INFO  TCSlib/Cryptography/Games/Hopping.lean      367 lines; 14 public / 1 private declarations
INFO  TCSlib/Cryptography/Games/OracleComp.lean   259 lines; 25 public / 0 private declarations
INFO  TCSlib/Cryptography/Games/Probability.lean  280 lines; 29 public / 0 private declarations
INFO  TCSlib/Cryptography/Games/Protocols.lean    280 lines; 19 public / 0 private declarations
INFO  TCSlib/Cryptography/Games/Simulate.lean     220 lines; 15 public / 0 private declarations
style_lint: 0 FAIL, 0 WARN over 6 files
lines over 100 characters (Unicode code points, Python len): 0

## ===== briefs/pass-shelat-ch5-8/gates/02-s2a/evidence-r2/name-screen.log =====

# name screen at PR #185 head 586510c1416afa21881b9a42b5a8d0578c9bd749
## 117 public names in TCSlib.Cryptography.Games
## relative names of Games declarations that also end a TCSlib.Cryptography name outside Games:
   simulate TCSlib.Cryptography.QueryTree.simulate TCSlib/Cryptography/Pseudorandom/Functions/OracleAdversary.lean:122
   simulate TCSlib.Cryptography.QueryTree.BoundedBy.simulate TCSlib/Cryptography/Pseudorandom/Functions/OracleAdversary.lean:136
   (QueryTree.simulate and QueryTree.BoundedBy.simulate need their QueryTree prefix under both opens, so they do not make Games.simulate ambiguous; they are the generalized concrete layer, bridge B1, listed in round 1.)
## new public names since 597eef43ccd3c8bfafe0c0c16a2444b12adc1644: ExecOutcome, ExecOutcome.swap, Party.close, Party.endWith, Party.Obs, Party.stepT, Party.closeT, Party.endWithT, Party.execT, Party.stepT_fst, Party.closeT_fst, Party.endWithT_fst, Party.execT_outcome, hagree_of_eq, identical_until_bad_init, exists_advantage_hybrid_gap; removed: Party.finish

## ===== briefs/pass-shelat-ch5-8/gates/02-s2a/evidence-r2/diffstat.txt =====

# git diff --stat 597eef43ccd3c8bfafe0c0c16a2444b12adc1644 586510c1416afa21881b9a42b5a8d0578c9bd749
 TCSlib/Cryptography/Games.lean             |   9 +-
 TCSlib/Cryptography/Games/Advantage.lean   |  45 +++---
 TCSlib/Cryptography/Games/Hopping.lean     | 210 ++++++++++++++++++-------
 TCSlib/Cryptography/Games/OracleComp.lean  |  11 +-
 TCSlib/Cryptography/Games/Probability.lean |  10 +-
 TCSlib/Cryptography/Games/Protocols.lean   | 237 +++++++++++++++++++++++++----
 TCSlib/Cryptography/Games/Simulate.lean    |  10 +-
 7 files changed, 416 insertions(+), 116 deletions(-)

## ===== briefs/pass-shelat-ch5-8/gates/02-s2a/evidence-r2/repair.diff.txt =====

diff --git a/TCSlib/Cryptography/Games.lean b/TCSlib/Cryptography/Games.lean
index f6947c6b..d61091be 100644
--- a/TCSlib/Cryptography/Games.lean
+++ b/TCSlib/Cryptography/Games.lean
@@ -39,7 +39,8 @@ the interaction model `Strategy`.
   advantages, the hybrid argument.
 * `TCSlib.Cryptography.Games.Hopping`: the difference lemma, identical until bad, the collision
   bound.
-* `TCSlib.Cryptography.Games.Protocols`: parties, the message exchange, executions.
+* `TCSlib.Cryptography.Games.Protocols`: parties, the message exchange, executions with D8's
+  reading of the end, and traced executions recording views.
 
 ## References
 
@@ -48,8 +49,10 @@ the interaction model `Strategy`.
   Lean*, https://github.com/dtumad/VCV-io, commit 9054989327a7185ff19ef9ff0f119cccea479501
   (2026-11-04), Apache License 2.0. Design adapted (no code transcribed): oracle specifications
   indexed by a type of oracle names (`VCVio/OracleComp/OracleSpec.lean`), oracle computations as
-  a free monad over them (`OracleComp.lean`, `OracleQuery.lean`), and simulation of oracles by
-  stateful handlers with query logging (`SimSemantics/`, `QueryTracking/LoggingOracle`).
+  a free monad over them (`OracleComp.lean`, `OracleQuery.lean`), probabilistic computations as
+  computations over the uniform-selection oracles (`OracleComp/ProbComp/Basic.lean`), and
+  simulation of oracles by stateful handlers with query logging and composition (`SimSemantics/`,
+  `SimSemantics/QueryImpl/Compose.lean`, `QueryTracking/LoggingOracle`).
 * [BR06] M. Bellare, P. Rogaway, *The security of triple encryption and a framework for
   code-based game-playing proofs*, EUROCRYPT 2006.
 * [Sho04] V. Shoup, *Sequences of games: a tool for taming complexity in security proofs*, IACR
diff --git a/TCSlib/Cryptography/Games/Advantage.lean b/TCSlib/Cryptography/Games/Advantage.lean
index ba0525f3..74ff64ea 100644
--- a/TCSlib/Cryptography/Games/Advantage.lean
+++ b/TCSlib/Cryptography/Games/Advantage.lean
@@ -3,6 +3,7 @@ Copyright (c) 2026 TCSlib contributors. All rights reserved.
 Released under Apache 2.0 license as described in the file LICENSE.
 -/
 import TCSlib.Cryptography.Games.Probability
+import TCSlib.Cryptography.Foundations.Probability
 
 set_option maxHeartbeats 0
 set_option relaxedAutoImplicit false
@@ -32,23 +33,27 @@ definitions wrap with "negligible for every efficient adversary".
 
 ## Main results
 
-* `advantage_triangle`, `advantage_hybrid`: the hybrid argument; the advantage between the ends of a
-  chain of games is at most the sum of the advantages between neighbours.
+* `advantage_triangle`, `advantage_hybrid`, `exists_advantage_hybrid_gap`: the hybrid argument;
+  the advantage between the ends of a chain of games is at most the sum of the advantages between
+  neighbours, so some neighbouring pair carries a `1/n` share of it ([PS10, Lemma 71.6]).
 * `guessAdv_eq_half_advantage`: the guess-the-bit advantage is half the distinguishing advantage
   between the games for `b = 1` and `b = 0`.
 
 ## References
 
 * [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
-  §3.1 (computational indistinguishability) and Lemma 70.2 (the hybrid lemma).
+  §3.1 (computational indistinguishability), Lemma 71.6 (the hybrid lemma) and Definition 168.1
+  (the challenge bit of the indistinguishability games).
 * [Sho04] V. Shoup, *Sequences of games: a tool for taming complexity in security proofs*,
-  IACR ePrint 2004/332, §3.
+  IACR ePrint 2004/332.
 * [VCVio] D. Tuma and the VCVio contributors, *VCVio: machine-checked cryptographic proofs in
   Lean*, https://github.com/dtumad/VCV-io, commit 9054989327a7185ff19ef9ff0f119cccea479501
   (2026-11-04), Apache License 2.0. Design adapted (no code transcribed): oracle specifications
   indexed by a type of oracle names (`VCVio/OracleComp/OracleSpec.lean`), oracle computations as
-  a free monad over them (`OracleComp.lean`, `OracleQuery.lean`), and simulation of oracles by
-  stateful handlers with query logging (`SimSemantics/`, `QueryTracking/LoggingOracle`).
+  a free monad over them (`OracleComp.lean`, `OracleQuery.lean`), probabilistic computations as
+  computations over the uniform-selection oracles (`OracleComp/ProbComp/Basic.lean`), and
+  simulation of oracles by stateful handlers with query logging and composition (`SimSemantics/`,
+  `SimSemantics/QueryImpl/Compose.lean`, `QueryTracking/LoggingOracle`).
 -/
 
 namespace TCSlib.Cryptography.Games
@@ -62,7 +67,7 @@ noncomputable def accept (G : ProbComp Bool) : ℝ := prob G (· = true)
 [PS10, §3.1] -/
 noncomputable def advantage (G₀ G₁ : ProbComp Bool) : ℝ := |accept G₀ - accept G₁|
 
-/-- An acceptance probability is between zero and one. -/
+/-- An acceptance probability is nonnegative. -/
 theorem accept_nonneg (G : ProbComp Bool) : 0 ≤ accept G := prob_nonneg G _
 
 /-- An acceptance probability is at most one. -/
@@ -91,21 +96,24 @@ theorem advantage_triangle (G₀ G₁ G₂ : ProbComp Bool) :
   abs_sub_le _ _ _
 
 /-- **The hybrid argument:** along a chain of games `G 0, …, G n`, the advantage between the ends
-is at most the sum of the advantages between neighbours. [PS10, Lemma 70.2], [Sho04, §3]
-
-**Proof sketch.** Induction on `n`, one game hop (`advantage_triangle`) per step. -/
+is at most the sum of the advantages between neighbours: the telescoping inequality in the proof of
+[PS10, Lemma 71.6]. It is the concrete layer's `abs_sub_le_sum_hybrids` for the acceptance
+probabilities. -/
 theorem advantage_hybrid (G : ℕ → ProbComp Bool) (n : ℕ) :
-    advantage (G 0) (G n) ≤ ∑ i ∈ range n, advantage (G i) (G (i + 1)) := by
-  induction n with
-  | zero => simp
-  | succ n ih =>
-    rw [sum_range_succ]
-    exact (advantage_triangle _ (G n) _).trans (by linarith)
+    advantage (G 0) (G n) ≤ ∑ i ∈ range n, advantage (G i) (G (i + 1)) :=
+  abs_sub_le_sum_hybrids (fun i => accept (G i)) n
+
+/-- **The hybrid lemma:** along a chain of `n > 0` games, some neighbouring pair has advantage at
+least a `1/n` share of the advantage between the ends. [PS10, Lemma 71.6] It is the concrete
+layer's `exists_hybrid_gap` for the acceptance probabilities. -/
+theorem exists_advantage_hybrid_gap (G : ℕ → ProbComp Bool) {n : ℕ} (hn : 0 < n) :
+    ∃ i < n, advantage (G 0) (G n) / n ≤ advantage (G i) (G (i + 1)) :=
+  exists_hybrid_gap (fun i => accept (G i)) hn
 
 /-! ### Guess-the-bit games -/
 
 /-- The **guess-the-bit game** over `G`: draw a uniform bit `b`, run `G b`, and win if its output
-is `b`. -/
+is `b`. The challenge bit of the indistinguishability games of [PS10, Def 168.1]. -/
 noncomputable def guessGame (G : Bool → ProbComp Bool) : ProbComp Bool :=
   (sample Bool).bind fun b => (G b).bind fun b' => .pure (decide (b' = b))
 
@@ -139,7 +147,8 @@ theorem accept_guessGame (G : Bool → ProbComp Bool) :
   ring
 
 /-- **Guessing versus distinguishing:** the guess-the-bit advantage is half the distinguishing
-advantage between `G 1` and `G 0`. -/
+advantage between `G 1` and `G 0`. The standard relation between the two forms of
+indistinguishability; [PS10] uses both (§3.1 and Def 168.1) without stating it. -/
 theorem guessAdv_eq_half_advantage (G : Bool → ProbComp Bool) :
     guessAdv G = advantage (G true) (G false) / 2 := by
   unfold guessAdv advantage
diff --git a/TCSlib/Cryptography/Games/Hopping.lean b/TCSlib/Cryptography/Games/Hopping.lean
index 0cf328f1..3c6c96e4 100644
--- a/TCSlib/Cryptography/Games/Hopping.lean
+++ b/TCSlib/Cryptography/Games/Hopping.lean
@@ -15,12 +15,13 @@ set_option autoImplicit false
 The steps of a game-based security proof, proved once:
 - **the difference lemma**: two events that agree unless a "bad" event happens differ in
   probability by at most the probability of the bad event;
-- **identical until bad**: two oracle implementations that answer identically until a flag in
-  their state is raised, and never lower it, give simulations whose outputs differ in probability
-  by at most the probability that the flag is raised;
-- **a collision bound**: a fresh uniform sample lands in a list of at most `q` earlier values with
-  probability at most `q / |T|`. This is the "bad event" of most PRF-based proofs, for example a
-  repeated nonce in [PS10, Thm 168.2].
+- **identical until bad**: two oracle implementations that give the same law to good successors
+  until a flag in their state is raised, and never lower it, give simulations whose outputs differ
+  in probability by at most the probability that the flag is raised;
+- **a collision bound**: one fresh uniform sample lands in a list of at most `q` values fixed
+  before it with probability at most `q / |T|`. The adaptive repeated-nonce event of
+  [PS10, Thm 168.2] (later nonces hitting an earlier one) is a union of such steps; its lemma is
+  scheduled with the statement phase.
 
 The hybrid argument itself is `advantage_hybrid` (`TCSlib.Cryptography.Games.Advantage`).
 
@@ -32,25 +33,29 @@ The hybrid argument itself is `advantage_hybrid` (`TCSlib.Cryptography.Games.Adv
 
 * `ProbComp.prob_eq_one_of_allOutputs`, `ProbComp.expect_mono_of_allOutputs`: reasoning on the
   possible outputs only.
-* `ProbComp.abs_prob_sub_le_of_agree`: the difference lemma [Sho04, Lemma 1].
+* `ProbComp.abs_prob_sub_le_of_agree`: the difference lemma [Sho04].
 * `ProbComp.prob_mem_le`: the collision bound.
-* `Games.prob_eq_until_bad`, `Games.identical_until_bad`: the code-based fundamental lemma
-  [BR06, Lemma 2].
+* `Games.prob_eq_until_bad`, `Games.identical_until_bad`, `Games.identical_until_bad_init`: the
+  code-based fundamental lemma [BR06], in semantic form, from a fixed or a sampled initial
+  state; `Games.hagree_of_eq` recovers the syntactic hypothesis.
 
 ## References
 
 * [BR06] M. Bellare, P. Rogaway, *The security of triple encryption and a framework for
-  code-based game-playing proofs*, EUROCRYPT 2006, §2 (Lemma 2, the fundamental lemma).
+  code-based game-playing proofs*, EUROCRYPT 2006 (the fundamental lemma of game playing).
 * [Sho04] V. Shoup, *Sequences of games: a tool for taming complexity in security proofs*,
-  IACR ePrint 2004/332, §4 (Lemma 1, the difference lemma).
+  IACR ePrint 2004/332 (the difference lemma). Section and lemma numbers are not cited: they vary
+  between revisions, and the revision could not be inspected.
 * [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
   Thm 168.2 (proof sketch: the bad events of the CPA analysis).
 * [VCVio] D. Tuma and the VCVio contributors, *VCVio: machine-checked cryptographic proofs in
   Lean*, https://github.com/dtumad/VCV-io, commit 9054989327a7185ff19ef9ff0f119cccea479501
   (2026-11-04), Apache License 2.0. Design adapted (no code transcribed): oracle specifications
   indexed by a type of oracle names (`VCVio/OracleComp/OracleSpec.lean`), oracle computations as
-  a free monad over them (`OracleComp.lean`, `OracleQuery.lean`), and simulation of oracles by
-  stateful handlers with query logging (`SimSemantics/`, `QueryTracking/LoggingOracle`).
+  a free monad over them (`OracleComp.lean`, `OracleQuery.lean`), probabilistic computations as
+  computations over the uniform-selection oracles (`OracleComp/ProbComp/Basic.lean`), and
+  simulation of oracles by stateful handlers with query logging and composition (`SimSemantics/`,
+  `SimSemantics/QueryImpl/Compose.lean`, `QueryTracking/LoggingOracle`).
 -/
 
 namespace TCSlib.Cryptography.Games
@@ -92,7 +97,8 @@ theorem prob_split (c : ProbComp α) (A F : α → Prop) :
   funext a
   by_cases hA : A a <;> by_cases hF : F a <;> simp [hA, hF]
 
-/-- An expectation only depends on the function's values at the possible outputs. -/
+/-- If every possible output of `c` satisfies `P`, and `f ≤ g` at every output satisfying `P`,
+then the expectation of `f` over `c` is at most that of `g`. -/
 theorem expect_mono_of_allOutputs {c : ProbComp α} {P : α → Prop} (hc : c.AllOutputs P)
     {f g : α → ℝ} (h : ∀ a, P a → f a ≤ g a) : expect c f ≤ expect c g := by
   induction c with
@@ -118,7 +124,7 @@ theorem prob_eq_zero_of_allOutputs {c : ProbComp α} {p : α → Prop}
   linarith
 
 /-- **The difference lemma:** if the events `A` and `B` agree at every output where `F` fails,
-their probabilities differ by at most the probability of `F`. [Sho04, Lemma 1]
+their probabilities differ by at most the probability of `F`. [Sho04] (the difference lemma)
 
 **Proof sketch.** Pointwise, the indicators of `A` and `B` differ by at most the indicator of
 `F`; take expectations in both directions (linearity and monotonicity). -/
@@ -141,8 +147,10 @@ theorem abs_prob_sub_le_of_agree (c : ProbComp α) {A B F : α → Prop}
   · linarith [key B A fun a ha => (h a ha).symm]
   · linarith [key A B h]
 
-/-- **The collision bound:** if every possible output list has length at most `q`, a fresh
-uniform element of `T` lies in the list with probability at most `q / |T|`.
+/-- **The collision bound:** if every possible output list has length at most `q`, one fresh
+uniform element of `T`, drawn after the list, lies in it with probability at most `q / |T|`.
+A standard union-bound fact behind the bad events of [PS10, Thm 168.2]'s proof sketch; the
+adaptive repeated-nonce event is a union of such steps.
 
 **Proof sketch.** By total probability over the list, it suffices that a fixed list `L` of length
 at most `q` is hit with probability `#{t ∈ L} / |T| ≤ q / |T|`; average over the possible lists
@@ -182,16 +190,38 @@ theorem simulate_allOutputs_bad {spec : OracleSpec ι} {impl : QueryImpl spec σ
     rw [simulate_query]
     exact OracleComp.AllOutputs.bind (hstick i x s hs) fun ys hys => ih ys.1 hys
 
-/-- **Equal until bad:** from a good state, two implementations that agree on good states and
-keep bad states bad give the same probability to "`Q` holds and the final state is good", and the
-same probability to "the final state is bad".
-
-**Proof sketch.** Induction on the computation. At a query from a good state both implementations
-are the same computation; for each of its outputs, a good new state is the induction hypothesis,
-and a bad new state makes the first event impossible and the second certain on both sides
-(`simulate_allOutputs_bad`). -/
+/-- Splitting an expectation on a predicate: on `b` the function is `1`, elsewhere `f`. -/
+private theorem expect_ite_one_split {γ : Type} (c : ProbComp γ) (b : γ → Prop) [DecidablePred b]
+    (f : γ → ℝ) :
+    ProbComp.expect c (fun y => if b y then 1 else f y) =
+      (1 - ProbComp.expect c (fun y => if b y then 0 else 1)) +
+        ProbComp.expect c (fun y => if b y then 0 else f y) := by
+  have h : (fun y => if b y then (1 : ℝ) else f y) =
+      fun y => (1 + (-1) * (if b y then (0 : ℝ) else 1)) + (if b y then 0 else f y) := by
+    funext y
+    by_cases hy : b y <;> simp [hy]
+  rw [h, ProbComp.expect_add c (fun y => 1 + (-1) * (if b y then (0 : ℝ) else 1))
+      (fun y => if b y then 0 else f y),
+    ProbComp.expect_add c (fun _ => (1 : ℝ)) (fun y => (-1) * (if b y then (0 : ℝ) else 1)),
+    ProbComp.expect_const, ProbComp.expect_const_mul]
+  ring
+
+/-- **Equal until bad:** let two implementations give, from every good state, the same law to good
+successors (they may differ arbitrarily on bad successors, including in the call that makes the
+state bad), and let each keep bad states bad. Then, from a good state, the two simulations give
+the same probability to "`Q` holds and the final state is good", and the same probability to "the
+final state is bad".
+
+**Proof sketch.** Induction on the computation. At a query from a good state, write `F_b` for the
+continuation's probability of the event. On a bad successor `F_b` is `0` (for "good at the end")
+or `1` (for "bad at the end") on both sides (`simulate_allOutputs_bad`). So each expectation only
+depends on `F_b` at good successors, where `F₀ = F₁` by induction; and the two implementations give
+good successors the same law (`hagree`, once with `g := F₁` and once with `g := 1`). -/
 theorem prob_eq_until_bad {spec : OracleSpec ι} {impl₀ impl₁ : QueryImpl spec σ unifSpec}
-    (bad : σ → Prop) (hagree : ∀ i x s, ¬ bad s → impl₀ i x s = impl₁ i x s)
+    (bad : σ → Prop) [DecidablePred bad]
+    (hagree : ∀ i x s, ¬ bad s → ∀ g : spec.rng i × σ → ℝ,
+      ProbComp.expect (impl₀ i x s) (fun ys => if bad ys.2 then 0 else g ys) =
+        ProbComp.expect (impl₁ i x s) (fun ys => if bad ys.2 then 0 else g ys))
     (hstick₀ : ∀ i x s, bad s → (impl₀ i x s).AllOutputs fun ys => bad ys.2)
     (hstick₁ : ∀ i x s, bad s → (impl₁ i x s).AllOutputs fun ys => bad ys.2)
     (c : OracleComp spec α) (Q : α → Prop) {s : σ} (hs : ¬ bad s) :
@@ -202,44 +232,77 @@ theorem prob_eq_until_bad {spec : OracleSpec ι} {impl₀ impl₁ : QueryImpl sp
   induction c generalizing s with
   | pure a => exact ⟨rfl, rfl⟩
   | query i x k ih =>
-    simp only [simulate_query, ProbComp.prob_bind, hagree i x s hs]
+    simp only [simulate_query, ProbComp.prob_bind]
     constructor
-    · congr 1
-      funext ys
-      by_cases hb : bad ys.2
-      · rw [ProbComp.prob_eq_zero_of_allOutputs
-            ((simulate_allOutputs_bad bad hstick₀ _ hb).mono fun r hr h => h.2 hr),
-          ProbComp.prob_eq_zero_of_allOutputs
-            ((simulate_allOutputs_bad bad hstick₁ _ hb).mono fun r hr h => h.2 hr)]
-      · exact (ih ys.1 hb).1
-    · congr 1
-      funext ys
-      by_cases hb : bad ys.2
-      · rw [ProbComp.prob_eq_one_of_allOutputs (simulate_allOutputs_bad bad hstick₀ _ hb),
-          ProbComp.prob_eq_one_of_allOutputs (simulate_allOutputs_bad bad hstick₁ _ hb)]
-      · exact (ih ys.1 hb).2
+    · -- "`Q` and good at the end"
+      have h0 : ∀ ys : spec.rng i × σ,
+          ProbComp.prob (simulate impl₀ (k ys.1) ys.2) (fun r => Q r.1 ∧ ¬ bad r.2) =
+            if bad ys.2 then 0 else
+              ProbComp.prob (simulate impl₁ (k ys.1) ys.2) (fun r => Q r.1 ∧ ¬ bad r.2) := by
+        intro ys
+        by_cases hb : bad ys.2
+        · rw [if_pos hb]
+          exact ProbComp.prob_eq_zero_of_allOutputs
+            ((simulate_allOutputs_bad bad hstick₀ _ hb).mono fun r hr h => h.2 hr)
+        · rw [if_neg hb]
+          exact (ih ys.1 hb).1
+      have h1 : ∀ ys : spec.rng i × σ,
+          ProbComp.prob (simulate impl₁ (k ys.1) ys.2) (fun r => Q r.1 ∧ ¬ bad r.2) =
+            if bad ys.2 then 0 else
+              ProbComp.prob (simulate impl₁ (k ys.1) ys.2) (fun r => Q r.1 ∧ ¬ bad r.2) := by
+        intro ys
+        by_cases hb : bad ys.2
+        · rw [if_pos hb]
+          exact ProbComp.prob_eq_zero_of_allOutputs
+            ((simulate_allOutputs_bad bad hstick₁ _ hb).mono fun r hr h => h.2 hr)
+        · rw [if_neg hb]
+      rw [funext h0, hagree i x s hs, ← funext h1]
+    · -- "bad at the end"
+      have h0 : ∀ ys : spec.rng i × σ,
+          ProbComp.prob (simulate impl₀ (k ys.1) ys.2) (fun r => bad r.2) =
+            if bad ys.2 then 1 else
+              ProbComp.prob (simulate impl₁ (k ys.1) ys.2) (fun r => bad r.2) := by
+        intro ys
+        by_cases hb : bad ys.2
+        · rw [if_pos hb]
+          exact ProbComp.prob_eq_one_of_allOutputs (simulate_allOutputs_bad bad hstick₀ _ hb)
+        · rw [if_neg hb]
+          exact (ih ys.1 hb).2
+      have h1 : ∀ ys : spec.rng i × σ,
+          ProbComp.prob (simulate impl₁ (k ys.1) ys.2) (fun r => bad r.2) =
+            if bad ys.2 then 1 else
+              ProbComp.prob (simulate impl₁ (k ys.1) ys.2) (fun r => bad r.2) := by
+        intro ys
+        by_cases hb : bad ys.2
+        · rw [if_pos hb]
+          exact ProbComp.prob_eq_one_of_allOutputs (simulate_allOutputs_bad bad hstick₁ _ hb)
+        · rw [if_neg hb]
+      rw [funext h0, expect_ite_one_split, hagree i x s hs (fun _ => 1), hagree i x s hs,
+        ← expect_ite_one_split, ← funext h1]
 
 /-- **Identical until bad** (the code-based fundamental lemma): let two implementations of the
-same oracles agree on every query made from a state where `bad` fails, and let each keep `bad`
+same oracles give, from every good state, the same law to good successors, and let each keep `bad`
 once it holds (every possible new state of a bad state is bad). Then, from a good state, for any
 computation `c` and event `p` on its output, the probabilities of `p` under the two simulations
 differ by at most the probability that the first simulation ends in a bad state.
-[BR06, Lemma 2], [Sho04, §4]
+[BR06] (the fundamental lemma); [Sho04]
+
+**Deviation:** [BR06] assumes the two games' code is syntactically identical up to `bad ← true`.
+Here the hypothesis is semantic: from a good state the two implementations give the same law to
+good successors, and may differ arbitrarily on bad ones, including in the call that raises the
+flag. Stickiness is required; without it the bound fails.
 
 **Proof sketch.**
 1. *Sticky:* from a bad state, every possible final state of either simulation is bad
-   (induction on `c`, from the hypothesis on each implementation).
-2. *Equal until bad:* from a good state, the two simulations give the same probability to
-   "`p` holds and the final state is good", and the same probability to "the final state is bad".
-   Induction on `c`: at a query from a good state both implementations are the same computation;
-   for each of its outputs, a good new state is the induction hypothesis, and a bad new state
-   makes "good at the end" impossible and "bad at the end" certain on both sides (step 1,
-   `prob_eq_zero_of_allOutputs`, `prob_eq_one_of_allOutputs`).
+   (`simulate_allOutputs_bad`).
+2. *Equal until bad:* `prob_eq_until_bad`.
 3. Write each probability of `p` as "`p` and good" plus at most "bad", and conclude with the
    difference lemma's arithmetic. -/
 theorem identical_until_bad {spec : OracleSpec ι}
-    {impl₀ impl₁ : QueryImpl spec σ unifSpec} (bad : σ → Prop)
-    (hagree : ∀ i x s, ¬ bad s → impl₀ i x s = impl₁ i x s)
+    {impl₀ impl₁ : QueryImpl spec σ unifSpec} (bad : σ → Prop) [DecidablePred bad]
+    (hagree : ∀ i x s, ¬ bad s → ∀ g : spec.rng i × σ → ℝ,
+      ProbComp.expect (impl₀ i x s) (fun ys => if bad ys.2 then 0 else g ys) =
+        ProbComp.expect (impl₁ i x s) (fun ys => if bad ys.2 then 0 else g ys))
     (hstick₀ : ∀ i x s, bad s → (impl₀ i x s).AllOutputs fun ys => bad ys.2)
     (hstick₁ : ∀ i x s, bad s → (impl₁ i x s).AllOutputs fun ys => bad ys.2)
     (c : OracleComp spec α) (p : α → Prop) {s : σ} (hs : ¬ bad s) :
@@ -258,4 +321,47 @@ theorem identical_until_bad {spec : OracleSpec ι}
   rw [abs_le]
   constructor <;> linarith
 
+/-- Equal implementations on good states give the same law to good successors: the hypothesis of
+`identical_until_bad` in its syntactic form. -/
+theorem hagree_of_eq {spec : OracleSpec ι} {impl₀ impl₁ : QueryImpl spec σ unifSpec}
+    (bad : σ → Prop) [DecidablePred bad] (h : ∀ i x s, ¬ bad s → impl₀ i x s = impl₁ i x s) :
+    ∀ i x s, ¬ bad s → ∀ g : spec.rng i × σ → ℝ,
+      ProbComp.expect (impl₀ i x s) (fun ys => if bad ys.2 then 0 else g ys) =
+        ProbComp.expect (impl₁ i x s) (fun ys => if bad ys.2 then 0 else g ys) :=
+  fun i x s hs _ => by rw [h i x s hs]
+
+/-- **Identical until bad, from a sampled initial state:** if every possible initial state is
+good, the bound of `identical_until_bad` holds for the games that first sample the state.
+
+**Proof sketch.** Total probability over the initial state, the pointwise bound at every possible
+(good) initial state (`identical_until_bad`), and monotonicity and linearity of expectation. -/
+theorem identical_until_bad_init {spec : OracleSpec ι}
+    {impl₀ impl₁ : QueryImpl spec σ unifSpec} (bad : σ → Prop) [DecidablePred bad]
+    (hagree : ∀ i x s, ¬ bad s → ∀ g : spec.rng i × σ → ℝ,
+      ProbComp.expect (impl₀ i x s) (fun ys => if bad ys.2 then 0 else g ys) =
+        ProbComp.expect (impl₁ i x s) (fun ys => if bad ys.2 then 0 else g ys))
+    (hstick₀ : ∀ i x s, bad s → (impl₀ i x s).AllOutputs fun ys => bad ys.2)
+    (hstick₁ : ∀ i x s, bad s → (impl₁ i x s).AllOutputs fun ys => bad ys.2)
+    (c : OracleComp spec α) (p : α → Prop) (init : ProbComp σ)
+    (hinit : init.AllOutputs fun s => ¬ bad s) :
+    |ProbComp.prob (init.bind fun s => simulate impl₀ c s) (fun r => p r.1) -
+        ProbComp.prob (init.bind fun s => simulate impl₁ c s) (fun r => p r.1)| ≤
+      ProbComp.prob (init.bind fun s => simulate impl₀ c s) (fun r => bad r.2) := by
+  rw [ProbComp.prob_bind, ProbComp.prob_bind, ProbComp.prob_bind]
+  have key := fun s (hs : ¬ bad s) =>
+    abs_le.1 (identical_until_bad bad hagree hstick₀ hstick₁ c p hs)
+  have u := ProbComp.expect_mono_of_allOutputs hinit
+    (f := fun s => ProbComp.prob (simulate impl₀ c s) (fun r => p r.1))
+    (g := fun s => ProbComp.prob (simulate impl₁ c s) (fun r => p r.1) +
+      ProbComp.prob (simulate impl₀ c s) (fun r => bad r.2))
+    (fun s hs => by linarith [(key s hs).2])
+  have v := ProbComp.expect_mono_of_allOutputs hinit
+    (f := fun s => ProbComp.prob (simulate impl₁ c s) (fun r => p r.1))
+    (g := fun s => ProbComp.prob (simulate impl₀ c s) (fun r => p r.1) +
+      ProbComp.prob (simulate impl₀ c s) (fun r => bad r.2))
+    (fun s hs => by linarith [(key s hs).1])
+  rw [ProbComp.expect_add] at u v
+  rw [abs_le]
+  constructor <;> linarith
+
 end TCSlib.Cryptography.Games
diff --git a/TCSlib/Cryptography/Games/OracleComp.lean b/TCSlib/Cryptography/Games/OracleComp.lean
index 3c73dcd4..bb9a1743 100644
--- a/TCSlib/Cryptography/Games/OracleComp.lean
+++ b/TCSlib/Cryptography/Games/OracleComp.lean
@@ -14,8 +14,9 @@ set_option autoImplicit false
 The syntax of security games and protocols. An *oracle specification* names a family of oracles,
 each with a type of queries and a type of answers. An *oracle computation* over it asks one
 oracle a query, looks at the answer, chooses what to do next, and eventually returns a value. It
-is the free monad over the specification: a finite tree whose inner nodes are queries, with one
-subtree per possible answer.
+is the free monad over the specification: a well-founded tree (every run makes finitely many
+queries) whose inner nodes are queries, with one subtree per possible answer. With finite answer
+types, as for probabilistic computations, the tree is finite.
 
 Everything else in the framework is built on this file:
 - uniform sampling is one more oracle (`TCSlib.Cryptography.Games.Probability`);
@@ -51,8 +52,10 @@ layer ([Gar26]); the bridge between the two is in the S2b layer.
   Lean*, https://github.com/dtumad/VCV-io, commit 9054989327a7185ff19ef9ff0f119cccea479501
   (2026-11-04), Apache License 2.0. Design adapted (no code transcribed): oracle specifications
   indexed by a type of oracle names (`VCVio/OracleComp/OracleSpec.lean`), oracle computations as
-  a free monad over them (`OracleComp.lean`, `OracleQuery.lean`), and simulation of oracles by
-  stateful handlers with query logging (`SimSemantics/`, `QueryTracking/LoggingOracle`).
+  a free monad over them (`OracleComp.lean`, `OracleQuery.lean`), probabilistic computations as
+  computations over the uniform-selection oracles (`OracleComp/ProbComp/Basic.lean`), and
+  simulation of oracles by stateful handlers with query logging and composition (`SimSemantics/`,
+  `SimSemantics/QueryImpl/Compose.lean`, `QueryTracking/LoggingOracle`).
 * [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley, draft of
   22 January 2026, Definition 3.9 (oracle adversaries).
 * [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
diff --git a/TCSlib/Cryptography/Games/Probability.lean b/TCSlib/Cryptography/Games/Probability.lean
index cfeee56b..2b1a5766 100644
--- a/TCSlib/Cryptography/Games/Probability.lean
+++ b/TCSlib/Cryptography/Games/Probability.lean
@@ -50,8 +50,10 @@ information-theory layer, so statistical distance and closeness (`EpsClose`) app
   Lean*, https://github.com/dtumad/VCV-io, commit 9054989327a7185ff19ef9ff0f119cccea479501
   (2026-11-04), Apache License 2.0. Design adapted (no code transcribed): oracle specifications
   indexed by a type of oracle names (`VCVio/OracleComp/OracleSpec.lean`), oracle computations as
-  a free monad over them (`OracleComp.lean`, `OracleQuery.lean`), and simulation of oracles by
-  stateful handlers with query logging (`SimSemantics/`, `QueryTracking/LoggingOracle`).
+  a free monad over them (`OracleComp.lean`, `OracleQuery.lean`), probabilistic computations as
+  computations over the uniform-selection oracles (`OracleComp/ProbComp/Basic.lean`), and
+  simulation of oracles by stateful handlers with query logging and composition (`SimSemantics/`,
+  `SimSemantics/QueryImpl/Compose.lean`, `QueryTracking/LoggingOracle`).
   Uniform sampling as an oracle follows VCVio's uniform-selection oracle; the real-valued
   finite-sum semantics here is not VCVio's (which is measure-valued).
 * [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
@@ -67,14 +69,14 @@ element of `Fin (m + 1)`. [VCVio, OracleComp/ProbComp] -/
 abbrev unifSpec : OracleSpec ℕ := ⟨fun _ => Unit, fun m => Fin (m + 1)⟩
 
 /-- **Probabilistic computations**: oracle computations whose only oracles draw uniform samples.
--/
+[VCVio, OracleComp/ProbComp/Basic] -/
 abbrev ProbComp := OracleComp unifSpec
 
 namespace ProbComp
 
 variable {α β : Type}
 
-/-- A uniformly random element of `Fin (m + 1)`. -/
+/-- A uniformly random element of `Fin (m + 1)`. [VCVio, OracleComp/ProbComp/Basic (uniformFin)] -/
 def sampleFin (m : ℕ) : ProbComp (Fin (m + 1)) := .query m () .pure
 
 /-- A uniformly random element of the nonempty finite type `T`, through its enumeration
diff --git a/TCSlib/Cryptography/Games/Protocols.lean b/TCSlib/Cryptography/Games/Protocols.lean
index 664fb3ee..e26e6135 100644
--- a/TCSlib/Cryptography/Games/Protocols.lean
+++ b/TCSlib/Cryptography/Games/Protocols.lean
@@ -14,14 +14,26 @@ set_option autoImplicit false
 A party of a two-party protocol is an oracle computation with two kinds of oracles: the message
 exchange (send a message, receive the other party's next message) and its own coins. Running the
 protocol interleaves the two parties as coroutines: the active party runs until it sends a
-message, the other party resumes with that message and runs until it replies, and so on. When a
-party returns its output, the other party's pending send is answered `none` ("the other party has
-finished"), so it too can finish.
+message, the other party resumes with that message and runs until it replies, and so on, for at
+most `fuel` messages.
 
-This is the same framework as security games: a party's view (its coins and the messages it
-received) is the log of its own oracle answers, and simulation-based security compares two
-`ProbComp`s with `advantage`. The bridge to the next-message strategies of the ch. 2–4 layer
-(`TCSlib.Cryptography.Strategy`, `TCSlib.Cryptography.exec`) is part of the S2b layer.
+**When a party returns.** [PS10, §4.4] ends the protocol when the active machine halts, and gives
+a machine an output only on halting, so the waiting party has none. Yet Definitions 116.1 and
+155.1 use both parties' outputs. As in the ch. 2–4 layer's reading (its foundation decision D8,
+`TCSlib.Cryptography.ZeroKnowledge.Interaction`), the waiting party is activated **once more**:
+its pending send is answered `none` ("the other party has finished"), it may draw coins, and it
+must then return without sending. A send after the end is reported (`ExecOutcome.sentAfterEnd`),
+never hidden. Either party may return early.
+
+**Views.** A party's view (its input and auxiliary input, which are Lean parameters of the party,
+its coins, and the messages delivered to it, starting with the second mover's first message) is
+recorded by the executor: `Party.execT` returns, beside the outcome, each party's received
+messages and coin draws (`Party.Obs`), and its outcome is that of `Party.exec`
+(`Party.execT_outcome`). A party's own oracle log would miss the second mover's first message,
+which reaches it as an argument.
+
+The bridge to the next-message strategies of the ch. 2–4 layer (`TCSlib.Cryptography.Strategy`,
+`TCSlib.Cryptography.exec`) is part of the S2b layer.
 
 ## Main definitions
 
@@ -29,25 +41,31 @@ received) is the log of its own oracle answers, and simulation-based security co
   `none`).
 * `Games.Party Out In α`: a party sending `Out`, receiving `In`, drawing its own coins and returning
   an `α`.
-* `Games.Party.step`: run a party until it returns or sends a message.
-* `Games.Party.finish`: finish a party whose counterpart has returned.
+* `Games.ExecOutcome`: both outputs, out of fuel, or a send after the end.
+* `Games.Party.step`, `Games.Party.close`: run a party to its next send or return; close a party
+  whose counterpart has returned.
 * `Games.Party.exec fuel A B`: execute a protocol in which `A` moves first, with at most `fuel`
   messages.
+* `Games.Party.Obs`, `Games.Party.execT`: the traced execution, recording each party's received
+  messages and coins.
 
 ## Main results
 
 * `Games.Party.exec_zero`, `Party.exec_succ`: the execution equations.
+* `Games.Party.execT_outcome`: the traced execution has the outcome of the execution.
 
 ## References
 
 * [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
-  §4.4 (interactive machines, executions, views) and §6.2 (two-party secure computation).
+  §4.4 (interactive machines, executions, views), Definitions 116.1 and 155.1.
 * [VCVio] D. Tuma and the VCVio contributors, *VCVio: machine-checked cryptographic proofs in
   Lean*, https://github.com/dtumad/VCV-io, commit 9054989327a7185ff19ef9ff0f119cccea479501
   (2026-11-04), Apache License 2.0. Design adapted (no code transcribed): oracle specifications
   indexed by a type of oracle names (`VCVio/OracleComp/OracleSpec.lean`), oracle computations as
-  a free monad over them (`OracleComp.lean`, `OracleQuery.lean`), and simulation of oracles by
-  stateful handlers with query logging (`SimSemantics/`, `QueryTracking/LoggingOracle`).
+  a free monad over them (`OracleComp.lean`, `OracleQuery.lean`), probabilistic computations as
+  computations over the uniform-selection oracles (`OracleComp/ProbComp/Basic.lean`), and
+  simulation of oracles by stateful handlers with query logging and composition (`SimSemantics/`,
+  `SimSemantics/QueryImpl/Compose.lean`, `QueryTracking/LoggingOracle`).
 -/
 
 namespace TCSlib.Cryptography.Games
@@ -60,6 +78,22 @@ abbrev exchangeSpec (Out In : Type) : OracleSpec Unit := ⟨fun _ => Out, fun _
 `In`, draws its own coins, and returns an `α`. [PS10, §4.4] -/
 abbrev Party (Out In α : Type) : Type := OracleComp ((exchangeSpec Out In).add unifSpec) α
 
+/-- The **outcome of an execution**: both outputs; the message budget ran out; or a party sent a
+message after its counterpart had returned. -/
+inductive ExecOutcome (α β : Type) : Type where
+  /-- Both parties returned: the first mover's output and the second mover's. -/
+  | done (a : α) (b : β)
+  /-- The message budget ran out before both parties returned. -/
+  | outOfFuel
+  /-- A party sent a message after its counterpart had returned. -/
+  | sentAfterEnd
+
+/-- Exchange the roles in an outcome. -/
+def ExecOutcome.swap {α β : Type} : ExecOutcome α β → ExecOutcome β α
+  | .done a b => .done b a
+  | .outOfFuel => .outOfFuel
+  | .sentAfterEnd => .sentAfterEnd
+
 namespace Party
 
 variable {Out In α β : Type}
@@ -71,37 +105,176 @@ def step : Party Out In α → ProbComp (α ⊕ (Out × (Option In → Party Out
   | .query (.inl ()) m k => .pure (.inr (m, k))
   | .query (.inr j) x k => .query j x (fun y => step (k y))
 
-/-- Finish a party whose counterpart has returned: every further send is answered `none`. -/
-def finish : Party Out In α → ProbComp α
-  | .pure a => .pure a
-  | .query (.inl ()) _ k => finish (k none)
-  | .query (.inr j) x k => .query j x (fun y => finish (k y))
+/-- **Close** a party whose counterpart has returned (its pending send already answered `none`):
+it may still draw coins, and returns `some` of its output, or `none` if it sends a message. -/
+def close : Party Out In α → ProbComp (Option α)
+  | .pure a => .pure (some a)
+  | .query (.inl ()) _ _ => .pure none
+  | .query (.inr j) x k => .query j x (fun y => close (k y))
+
+/-- The end of an execution in which the active party returned `a`: the waiting party `B` is
+activated once more, with `none`, and closed. -/
+def endWith {M₁ M₂ α β : Type} (a : α) (B : Option M₁ → Party M₂ M₁ β) :
+    ProbComp (ExecOutcome α β) :=
+  (close (B none)).bind fun ob => .pure (Option.elim ob .sentAfterEnd (ExecOutcome.done a))
 
 /-- **Execution** of a two-party protocol with at most `fuel` messages. `A` moves first, and `B`
-waits for `A`'s first message (`none` if `A` returns at once). After each message the roles swap.
-The result is both outputs, or `none` if the fuel runs out first. [PS10, §4.4] -/
+waits for `A`'s first message. After each message the roles swap. A return costs no fuel; when the
+active party returns, the waiting party is activated once more and closed (`endWith`).
+
+**Deviation from [PS10, §4.4]:** the source ends the protocol when the active machine halts and
+defines outputs only on halting, so the waiting party would have none, while Definitions 116.1
+and 155.1 use both outputs. As in the ch. 2–4 layer's D8, the waiting party is activated once
+more; it may draw coins, but a send is reported as `sentAfterEnd`. Unlike D8, which fixes the
+number of messages, a party may return early. -/
 def exec : ℕ → ∀ {M₁ M₂ α β : Type},
-    Party M₁ M₂ α → (Option M₁ → Party M₂ M₁ β) → ProbComp (Option (α × β))
-  | 0, _, _, _, _, _, _ => .pure none
+    Party M₁ M₂ α → (Option M₁ → Party M₂ M₁ β) → ProbComp (ExecOutcome α β)
+  | 0, _, _, _, _, A, B =>
+    (step A).bind (Sum.elim (fun a => endWith a B) (fun _ => .pure .outOfFuel))
   | fuel + 1, _, _, _, _, A, B =>
-    (step A).bind (Sum.elim
-      (fun a => (finish (B none)).bind fun b => .pure (some (a, b)))
-      (fun mk => (exec fuel (B (some mk.1)) mk.2).bind fun r => .pure (r.map Prod.swap)))
+    (step A).bind (Sum.elim (fun a => endWith a B)
+      (fun mk => (exec fuel (B (some mk.1)) mk.2).bind fun r => .pure r.swap))
 
-/-- Without fuel, the execution stops at once. -/
-@[simp] theorem exec_zero {M₁ M₂ : Type} (A : Party M₁ M₂ α) (B : Option M₁ → Party M₂ M₁ β) :
-    exec 0 A B = .pure none := rfl
+/-- With no fuel, the execution ends at the first mover's first send. -/
+theorem exec_zero {M₁ M₂ : Type} (A : Party M₁ M₂ α) (B : Option M₁ → Party M₂ M₁ β) :
+    exec 0 A B = (step A).bind (Sum.elim (fun a => endWith a B) (fun _ => .pure .outOfFuel)) :=
+  rfl
 
-/-- One move of the execution: `A` runs until it returns (then `B` finishes) or sends `m` (then
-`B` resumes with `m` as the first mover, against `A`'s continuation). -/
+/-- One message of the execution: `A` runs until it returns (then `B` is closed) or sends `m`
+(then `B` resumes with `m` as the first mover, against `A`'s continuation). -/
 theorem exec_succ {M₁ M₂ : Type} (fuel : ℕ) (A : Party M₁ M₂ α)
     (B : Option M₁ → Party M₂ M₁ β) :
     exec (fuel + 1) A B =
-      (step A).bind (Sum.elim
-        (fun a => (finish (B none)).bind fun b => .pure (some (a, b)))
-        (fun mk => (exec fuel (B (some mk.1)) mk.2).bind fun r => .pure (r.map Prod.swap))) :=
+      (step A).bind (Sum.elim (fun a => endWith a B)
+        (fun mk => (exec fuel (B (some mk.1)) mk.2).bind fun r => .pure r.swap)) :=
   rfl
 
+/-! ### Sanity checks: fuel counts messages; a send after the end is reported -/
+
+example (a b : Bool) :
+    exec 0 (M₁ := Unit) (M₂ := Unit) (.pure a) (fun _ => .pure b) = .pure (.done a b) := rfl
+
+example (m : Unit) (a b : Bool) :
+    exec 1 (M₂ := Unit) (.query (.inl ()) m fun _ => .pure a) (fun _ => .pure b) =
+      .pure (.done a b) := rfl
+
+example (m : Unit) (a b : Bool) :
+    exec 1 (M₁ := Unit) (.pure a) (fun _ => .query (.inl ()) m fun _ => .pure b) =
+      .pure .sentAfterEnd := rfl
+
+/-! ### The traced execution -/
+
+/-- What one party **observes** during an execution: the messages delivered to it, in order, and
+the coins it drew, each as a sampling oracle `m` with its answer in `Fin (m + 1)`. -/
+structure Obs (In : Type) : Type where
+  /-- The messages delivered to the party, in order. -/
+  received : List In
+  /-- The party's coin draws, in order. -/
+  coins : List (Σ m : ℕ, Fin (m + 1))
+
+/-- `step`, also returning the coins drawn along the way. -/
+def stepT : Party Out In α →
+    ProbComp ((α ⊕ (Out × (Option In → Party Out In α))) × List (Σ m : ℕ, Fin (m + 1)))
+  | .pure a => .pure (.inl a, [])
+  | .query (.inl ()) m k => .pure (.inr (m, k), [])
+  | .query (.inr j) x k => .query j x fun y =>
+      (stepT (k y)).bind fun p => .pure (p.1, ⟨j, y⟩ :: p.2)
+
+/-- `close`, also returning the coins drawn along the way. -/
+def closeT : Party Out In α → ProbComp (Option α × List (Σ m : ℕ, Fin (m + 1)))
+  | .pure a => .pure (some a, [])
+  | .query (.inl ()) _ _ => .pure (none, [])
+  | .query (.inr j) x k => .query j x fun y =>
+      (closeT (k y)).bind fun p => .pure (p.1, ⟨j, y⟩ :: p.2)
+
+/-- The traced end of an execution: `endWith`, also returning the waiting party's coins. -/
+def endWithT {M₁ M₂ α β : Type} (a : α) (B : Option M₁ → Party M₂ M₁ β) :
+    ProbComp (ExecOutcome α β × List (Σ m : ℕ, Fin (m + 1))) :=
+  (closeT (B none)).bind fun p => .pure (Option.elim p.1 .sentAfterEnd (ExecOutcome.done a), p.2)
+
+/-- The **traced execution**: `exec`, also returning what each party observed. The first component
+of the result is the outcome, the second the first mover's observations, and the third the second
+mover's. When the active party sends `m`, `m` is the first message the other party receives in the
+rest of the run. [PS10, §4.4] (views) -/
+def execT : ℕ → ∀ {M₁ M₂ α β : Type},
+    Party M₁ M₂ α → (Option M₁ → Party M₂ M₁ β) →
+      ProbComp (ExecOutcome α β × Obs M₂ × Obs M₁)
+  | 0, _, _, _, _, A, B =>
+    (stepT A).bind fun p => Sum.elim
+      (fun a => (endWithT a B).bind fun q => .pure (q.1, ⟨[], p.2⟩, ⟨[], q.2⟩))
+      (fun _ => .pure (.outOfFuel, ⟨[], p.2⟩, ⟨[], []⟩)) p.1
+  | fuel + 1, _, _, _, _, A, B =>
+    (stepT A).bind fun p => Sum.elim
+      (fun a => (endWithT a B).bind fun q => .pure (q.1, ⟨[], p.2⟩, ⟨[], q.2⟩))
+      (fun mk => (execT fuel (B (some mk.1)) mk.2).bind fun r =>
+        .pure (r.1.swap, ⟨r.2.2.received, p.2 ++ r.2.2.coins⟩,
+          ⟨mk.1 :: r.2.1.received, r.2.1.coins⟩)) p.1
+
+/-- `stepT` projects to `step`. -/
+theorem stepT_fst (A : Party Out In α) : (stepT A).bind (fun p => .pure p.1) = step A := by
+  induction A with
+  | pure a => rfl
+  | query i x k ih =>
+    cases i with
+    | inl u => cases u; rfl
+    | inr j =>
+      simp only [stepT, step, OracleComp.query_bind, OracleComp.bind_assoc, OracleComp.pure_bind]
+      congr 1
+      funext y
+      exact ih y
+
+/-- `closeT` projects to `close`. -/
+theorem closeT_fst (A : Party Out In α) : (closeT A).bind (fun p => .pure p.1) = close A := by
+  induction A with
+  | pure a => rfl
+  | query i x k ih =>
+    cases i with
+    | inl u => cases u; rfl
+    | inr j =>
+      simp only [closeT, close, OracleComp.query_bind, OracleComp.bind_assoc, OracleComp.pure_bind]
+      congr 1
+      funext y
+      exact ih y
+
+/-- `endWithT` projects to `endWith`. -/
+theorem endWithT_fst {M₁ M₂ : Type} (a : α) (B : Option M₁ → Party M₂ M₁ β) :
+    (endWithT a B).bind (fun q => .pure q.1) = endWith a B := by
+  simp only [endWithT, endWith, OracleComp.bind_assoc, OracleComp.pure_bind]
+  rw [← closeT_fst (B none), OracleComp.bind_assoc]
+  simp only [OracleComp.pure_bind]
+
+/-- **The traced execution has the execution's outcome.**
+
+**Proof sketch.** Induction on the fuel, generalizing the parties and their types. Each level of
+`execT` runs `stepT`, which projects to `step` (`stepT_fst`); the branch on the first component
+then matches `exec`'s, with `endWithT` projecting to `endWith` and the recursive call to the
+recursive call. -/
+theorem execT_outcome : ∀ (fuel : ℕ) {M₁ M₂ α β : Type} (A : Party M₁ M₂ α)
+    (B : Option M₁ → Party M₂ M₁ β),
+    (execT fuel A B).bind (fun r => .pure r.1) = exec fuel A B
+  | 0, _, _, _, _, A, B => by
+    simp only [execT, exec, OracleComp.bind_assoc]
+    rw [← stepT_fst A, OracleComp.bind_assoc]
+    simp only [OracleComp.pure_bind]
+    congr 1
+    funext p
+    rcases p with ⟨_ | _, c⟩
+    · simp only [Sum.elim_inl, OracleComp.bind_assoc, OracleComp.pure_bind]
+      rw [← endWithT_fst]
+    · rfl
+  | fuel + 1, _, _, _, _, A, B => by
+    simp only [execT, exec, OracleComp.bind_assoc]
+    rw [← stepT_fst A, OracleComp.bind_assoc]
+    simp only [OracleComp.pure_bind]
+    congr 1
+    funext p
+    rcases p with ⟨_ | mk, c⟩
+    · simp only [Sum.elim_inl, OracleComp.bind_assoc, OracleComp.pure_bind]
+      rw [← endWithT_fst]
+    · simp only [Sum.elim_inr, OracleComp.bind_assoc, OracleComp.pure_bind]
+      rw [← execT_outcome fuel (B (some mk.1)) mk.2, OracleComp.bind_assoc]
+      simp only [OracleComp.pure_bind]
+
 end Party
 
 end TCSlib.Cryptography.Games
diff --git a/TCSlib/Cryptography/Games/Simulate.lean b/TCSlib/Cryptography/Games/Simulate.lean
index b99cbe7e..d8ac0e1d 100644
--- a/TCSlib/Cryptography/Games/Simulate.lean
+++ b/TCSlib/Cryptography/Games/Simulate.lean
@@ -51,8 +51,10 @@ queried" are predicates on that log. Logging never changes the computation
   Lean*, https://github.com/dtumad/VCV-io, commit 9054989327a7185ff19ef9ff0f119cccea479501
   (2026-11-04), Apache License 2.0. Design adapted (no code transcribed): oracle specifications
   indexed by a type of oracle names (`VCVio/OracleComp/OracleSpec.lean`), oracle computations as
-  a free monad over them (`OracleComp.lean`, `OracleQuery.lean`), and simulation of oracles by
-  stateful handlers with query logging (`SimSemantics/`, `QueryTracking/LoggingOracle`).
+  a free monad over them (`OracleComp.lean`, `OracleQuery.lean`), probabilistic computations as
+  computations over the uniform-selection oracles (`OracleComp/ProbComp/Basic.lean`), and
+  simulation of oracles by stateful handlers with query logging and composition (`SimSemantics/`,
+  `SimSemantics/QueryImpl/Compose.lean`, `QueryTracking/LoggingOracle`).
 * [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley, draft of
   22 January 2026, Definition 3.9 (answering an adversary's queries in a reduction).
 -/
@@ -133,7 +135,8 @@ end QueryImpl
 /-- **Composition:** answer the queries of `spec` with `impl₁`, whose own queries (to `spec'`)
 are answered by `impl₂`; the state is the pair of the two states. This is how a reduction that
 answers its adversary's queries by querying its own oracles becomes, after its oracles are
-implemented, a single implementation of the adversary's oracles. -/
+implemented, a single implementation of the adversary's oracles.
+[VCVio, SimSemantics/QueryImpl/Compose (QueryImpl.compose)] -/
 def QueryImpl.comp {ι'' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'}
     {spec'' : OracleSpec ι''} {σ₁ σ₂ : Type} (impl₂ : QueryImpl spec' σ₂ spec'')
     (impl₁ : QueryImpl spec σ₁ spec') : QueryImpl spec (σ₁ × σ₂) spec'' :=
@@ -141,6 +144,7 @@ def QueryImpl.comp {ι'' : Type} {spec : OracleSpec ι} {spec' : OracleSpec ι'}
 
 /-- **Simulation composes:** simulating with `impl₂` a simulation by `impl₁` is simulating once
 with the composed implementation, up to regrouping the states.
+[VCVio, SimSemantics/QueryImpl/Compose (simulateQ_compose)]
 
 **Proof sketch.** Induction on the computation. At a query, both sides first run `impl₁`'s answer
 under `impl₂` (`simulate_bind` on the left, the definition of `comp` on the right), and the
