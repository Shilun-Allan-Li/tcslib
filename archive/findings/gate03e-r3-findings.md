# Gate 03e, round 3 — external delta-audit findings

**Verdict: the audited delta meets the closing threshold — 0 blockers, 0 majors, 1 minor.** The five reading lemmas and the two strengthened NP conclusions match their intended interfaces. One inherited sentence still overstates statistical zero-knowledge. Closure does not certify the existing admissions, the deferred sequential-composition work, or execution checks independently of the supplied evidence.

**Audited material:** the bundle's declared pin `1ea782b11617e15a51c3e2f6bd15dd0e3befbd95`; repair evidence compares base `092083cd10be7a284db4e97fcf42eddb8296edf7` with #206 head `73751f5747d8c0a57aba9939cac8bb16f87ba2ba`. Scope is the first section's round-3 brief: all round-2 resolutions, the changed declarations and documentation, the six consumer files, and the specified DESIGN entries. Other gates' changes in the batch are outside this verdict. I did not run Lean or audit tactic proofs; checking the requested consumer re-points is an interface-use check.

**Source:** the attached Pass–shelat PDF, book pp. 116–119, 121–122, 124 and 128–129 (PDF pages respectively 128–131, 133–134, 136 and 140–141). These distinguish ordinary from efficient-prover proofs, give witness-blind simulation, and describe the witness-preserving NP reduction and computational 3COL argument. Line numbers below refer to individual bundled files. Lean paths are relative to `TCSlib/Cryptography/ZeroKnowledge/`.

## Findings

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | minor | `Defs.lean:34–36` · module deviation paragraph | The inherited phrase “the theorems become statistical” still suggests that truncating the chapter's simulators makes its ZK results statistical. This contradicts the repaired GI/3COL distinction. | `DESIGN.md:1071–1079` correctly distinguishes GI's `StatZK` from 3COL's computational `ZK`. The binding-based witness-separation argument below rules out negligible statistical error for the 3COL protocol. The immediately following, repaired paragraph in `Defs.lean:42–50` now acknowledges that obstruction. This is residual wording, not a new false theorem or a failure of the designated DESIGN repair. | Replace the parenthesis with: “expected polynomial time is not formalized; GI uses a truncated simulator and obtains statistical ZK, while 3COL remains computational ZK with statistical sampling and failure terms.” |

## Resolution dispositions

The grouped review row M1–M5 is expanded below. “Recorded” means the supplied record states the disposition, but the underlying external record is not included for independent verification.

#1: **fixed** — DESIGN's dated D8 erratum (`141–148`) explicitly supersedes its frozen historical sentence; §5 item 11 (`1071–1079`) correctly separates GI and 3COL and retains the one-iteration/sequential-composition distinction. Finding 1 above concerns a separate inherited sentence in `Defs.lean`.

#2: **fixed** — all five ordinary reading lemmas are present beside the definitions, with formula docstrings and without `@[simp]`. The supplied consumers use `proverBounded_iff`; the seal evidence covers all six files, including the two additional soundness files. All five new lemmas have standard-only axiom prints.

#3: **recorded** — the contradictory sentences in round-1 rows 5 and M8 have been removed (`resolutions-03e-r1.md:34,54`). The historical 22-warning count is explicitly tied to round 1; the 21/18 counts are tied to the 126-module closure. The claimed underlying edits to `run3-audit-summary.md`, `SPINE-DESIGN.md` and `inventory-ch5-8.md` remain maintainer attestations: those files are not bundled. Thus the visible accounting correction is fixed, but the omitted edits are not independently certified.

#4: **fixed** — both existential conclusions export `LevinReduction L L3COL R R3COL f w p` for exactly the returned maps and polynomial. The same `f,w,p` occur in every protocol conclusion. The `zk_proof_of_mem_NP` consumer is adjusted without changing its statement. No premise was removed.

#5: **fixed** — `Interaction.lean:39–45`, `GraphIsomorphism.lean:73–78,554–557`, and `ThreeColoring/Protocol.lean:497–500` distinguish empty padding from the final verdict. The supplied verifier bodies agree: GI emits the verdict at its final even history; 3COL does so at `2 * x.length²` received messages, after its padding. For zero total rounds there is no final transmitted move. The ch. 7 filler description agrees with the supplied maintainer review; `SequentialZK.lean` itself is absent, so that implementation detail is recorded rather than independently rechecked.

#6: **fixed** — `Defs.lean:42–50` and DESIGN §7 item 51 (`1312–1320`) restrict the obstruction to the witness-dependent 3COL protocol. They no longer infer failure of every computationally hiding protocol merely from the possibility of opening commitments. The explicit two-witness test below validates the narrowed argument.

#7: **fixed** — `InteractiveProofs.lean:36–54,113–125` and DESIGN §5 item 8 (`1059–1066`) distinguish Definition 116.1's efficient verifier from Definition 119.5's efficient prover. The class-IP claim is restricted to negligible-error proof systems; the `s = 1` degeneracy is expressly acknowledged. The bounded-message normal-form argument remains explicitly unformalized.

M1: **fixed** — the review's former cross-file body-reads, including both sides of `ProverBounded.pullback`, are routed through the characterization. The two additional soundness consumers are included.

M2: **scheduled** — the resolution explicitly assigns the old tactic-level unfolds to clean-up part 2, with the equation-lemma work and `firstHit_eq`. This is accepted as a declared obligation, not as completed work or verification of an unbundled clean-up plan.

M3: **fixed** — covered by #5, with the stated limit on verifying the unbundled ch. 7 implementation.

M4: **fixed** — covered by #7, including the module-level efficiency attribution.

M5: **recorded** — covered by #3: the maintainer supplies locations and a commit for the historical edits, but not the edited files.

## Changed declarations: independent assessment

| Declaration | Mathematical reading and docstring assessment |
|---|---|
| `Protocol.proverBounded_iff` (`Interaction.lean:338`) | Exactly the predicate's defining equivalence: for every related instance/witness pair, every finite tape and every history, the next prover message obeys the same polynomial bound. It adds no reachability, tape-length, efficiency or witness-existence assumption. Matches the docstring. |
| `AbortRetry.attempt_eq` (`Defs.lean:315`) | Exactly the defining layout equation: preserve the decoded parameter and argument, supply empty advice, and take the specified coin block using `drop` followed by `take`. It does not assume that the input layout is well formed or that a full block exists. Matches. |
| `AbortRetry.retry_eq` (`Defs.lean:334`) | Exactly the defining conditional: inspect the least successful index below the decoded parameter length and return that attempt, or `[]` if there is none. No probability or runtime assertion is added. Matches. |
| `AbortRetry.retry_eq_attempt` (`Defs.lean:347`) | Returns attempt `i` only when `i` is in range, nonempty, and all earlier attempts are empty. These are precisely the first-success hypotheses described. Matches. |
| `AbortRetry.retry_eq_nil` (`Defs.lean:359`) | Returns `[]` when every in-range attempt is empty. Together with the preceding lemma, this exhausts the finite search, including zero attempts. Matches. |
| `zk_proof_of_witnessRelation` (`NP.lean:682`) | Adds exactly the promised certificate. Its six fields (`NP.lean:134–147`) give polynomial-time instance and witness maps, membership equivalence, witness preservation, exact output length `p`, and `p ≥ id`. The separately returned `p ≥ id` is redundant but harmless. The arbitrary supplied witness relation and all former conclusions are retained. |
| `zk_proof_of_witnessRelation_of_owp` (`NP.lean:701`) | Exports the same certificate inside the existential for the single commitment scheme. The OWP premise remains sufficient as the caller's cryptographic premise; no hard-core predicate was added. The declared `LevinNPHard` hypothesis and DQ5 limitation remain. Matches. |

The NP conclusions still distinguish **ZK of one iteration** from **an efficient-prover proof for the repeated protocol**. They do not assert ZK of the repeated protocol. Both headline axiom prints still include `sorryAx`, consistent with the existing `col_zk` and `colRep_efficientProverProof` admissions; returning the certificate does not discharge them.

## Adversarial checks

**Zero attempts and short tapes.** Put `N = (NUPPT.inParam w).length`. If `N = 0`, the search condition is false and `retry S w = []`, even for a simulator that always returns a nonempty word. The hypothesis of `retry_eq_nil` is vacuous and correct; `retry_eq_attempt` cannot apply because `i < 0` is impossible. If a coin block is unavailable, `drop`/`take` supplies a shorter block, possibly empty. `attempt_eq` preserves this behavior rather than claiming a full random tape or independence on arbitrary inputs.

**Vacuous relation and a fake reduction.** Taking `R x y := False` makes both sides of `proverBounded_iff` true, as intended. It cannot trivialize the strengthened NP theorem for a nonempty language: `WitnessRelation.mem_iff` would imply

\[
x\in L\iff\exists y,\mathrm{False}\iff\mathrm{False}.
\]

Nor can the new certificate be satisfied by the constant instance map `f x := []`: at `x = [true]`, its `length_eq` and `le_eval` fields would give

\[
1\le p(1)=|f([\mathrm{true}])|=0.
\]

Thus the added conjunct certifies the promised maps rather than merely naming arbitrary functions.

**3COL witness separation and the narrowed auxiliary-input rationale.** On a graph with `n ≥ 3` vertices and the sole undirected edge `{0,1}`, take proper colourings

\[
c_0=(0,1,0,0,\ldots),\qquad c_1=(0,1,2,0,\ldots).
\]

Let `T` test whether the commitments at vertices 0 and 2 admit openings to the same padded colour. Every colour permutation preserves equality and inequality; perfect binding prevents openings to different values. Hence, for the same instance and auxiliary input,

\[
\Pr[T(\mathrm{view}_{c_0})]=1,\qquad
\Pr[T(\mathrm{view}_{c_1})]=0.
\]

If a witness-blind simulator passes this test with probability `q`, then

\[
\max\{|1-q|,|0-q|\}\ge\tfrac12.
\]

This holds along the unbounded family of graph encodings, ruling out a negligible statistical error. Exhaustively checking the three possible padded colours and all `ℓ(n)`-bit opening strings takes `2^{ℓ(n)}` times polynomial overhead. Choosing a common auxiliary string long enough to dominate this work makes the test polynomial in the encoded view's length under the unbounded-auxiliary-input interpretation discussed in the repaired paragraph. No uniform-colour-sampling assumption is needed. This establishes the specific obstruction; it says nothing against a protocol whose fixed-public-value commitments can be simulated exactly.

## Change containment and execution evidence

- I reverse-applied the supplied diff to all eight bundled Lean files in scope. Every current file matches its diff's head Git-blob prefix, and every reconstructed base matches its base prefix. A separate comparison of public declaration signatures finds exactly **five additions, two changes, zero removals** in these files, agreeing with their portion of `statements.txt`. The remaining hunks are the described documentation and consumer/proof adjustments; no definition body or structure field changes. The batch's other five additions belong to other gates.
- `seal.log:1–54` reports all six current consumer files passing with `ProverBounded` sealed, all six base controls failing under the seal, and those same controls passing unsealed. It also reports zero explicit `simp`/`rw`/`unfold` uses of the predicate. Lines 65–70 cover the four retry reading lemmas with the imported definitions sealed and a failing seal-active control. The visible re-points agree with these reports.
- `replay.log` contains **129 successful checks, zero errors**; all eight scoped Lean files have rows. The eight-module maintainer recheck also reports success. The 74 modules common to `base-sync.log` and `replay.log` have identical `sorry` counts. A complete independent head/base replay comparison is not possible from these two logs alone. The batch replay totals 83 warnings across its different module set; this is not the round-2 126-module count discussed in resolution #3.
- `axioms.log` reports 549 print commands covering 548 distinct names, ten additions, no changed old axiom sets, and no nonstandard axioms other than the existing `sorryAx` dependencies. The five scoped additions' actual output lines confirm standard-only axioms. The base comparison is a maintainer-generated summary, not an independently rerun check.
- `lint.log` reports no new lint finding relative to its base. I checked the actual new lemma statements and docstrings; the semantic reading-API obligation is not inferred from lint alone.

**Notation:** `N` is the decoded retry parameter length; `c₀,c₁` are the two displayed colourings; `T` is their commitment-equality test; `q` is its acceptance probability on the simulator's output. Other notation is inherited from the bundled statements.
