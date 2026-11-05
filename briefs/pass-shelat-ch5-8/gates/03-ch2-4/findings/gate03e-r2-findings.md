# Gate 03e, round 2 — external audit findings

**Verdict: DO NOT CLOSE — 0 blockers, 2 majors, 5 minors.**

The bounded-message repair and the abort-to-statistical-ZK bridge are mathematically sound at the statement level. Closure still needs an accurate design record and the required public reading lemmas for the three new definitions. The remaining findings concern documentation, exported witnesses, and resolution accounting; I found no false new Lean theorem statement.

**Audited pin:** `e79397eaf68b156b9db091f464741f6eb75b9c28`, branch `cryptography/pass-shelat-ch2-4`; Lean files identified by the pack as equal to #201's head `0c348ff9`.

**Scope:** the first section's round-2 brief; all 27 resolution rows; every declaration listed as new; all statement, docstring, and proof-sketch changes in section A of the repair diff. Section B is consumer context. Tactic proofs and the scheduled duplication cleanup were not audited. I did not run Lean: execution results below are checks of the supplied attestations, not an independent replay.

**Sources:** the attached Pass–shelat PDF, especially book pp. 116–119, 121–129 and 191 (PDF pages 128–131, 133–141 and 203). The source is available in this round. I also checked the abort definition against [Goldreich's author-hosted chapter, Definition 4.3.1](https://www.wisdom.weizmann.ac.il/~oded/PSBookFrag/part4N.pdf), draft p. 142. Line numbers below refer to the individual files extracted from the bundle, not to bundle line numbers. Lean filenames are under `TCSlib/Cryptography/ZeroKnowledge/` unless qualified.

## Findings

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | **major** | `briefs/pass-shelat/DESIGN.md:1019`, §5 item 11; also D8 at line 136; `resolutions-03e-r1.md`, rows 2 and M5 | The record marked repaired still describes **GI and 3COL as statistical ZK**. This materially overstates the 3COL interface. | Item 11 begins “GI/3COL: statistical ZK”; D8 says both are proved statistically. The exported NP statements instead assert `ZK`, and the 3COL ZK admission is `col_zk`. More decisively, perfect binding makes commitments to two colourings outside the same colour-permutation orbit statistically distinguishable. The explicit family below forces any common simulator's error to be at least $1/2$ for one witness. Truncation and small sampling errors do not remove that obstruction. This is a remaining defect in a record expressly presented as repaired, not a demand to re-audit pack 03g. | Separate the cases throughout the live design record: GI has `StatZK` with negligible error; 3COL has **computational** `ZK`, using commitment hiding and absorbing statistical sampling/truncation errors. Preserve the recorded admissions and sequential-composition debt. Correct rows 2/M5 accordingly. |
| 2 | **major** | `Interaction.lean:331` · `Protocol.ProverBounded`; `Defs.lean:305,314` · `AbortRetry.attempt`, `AbortRetry.retry` | The new definitions lack the reading API explicitly required by `policy.md` §1. | The policy requires an `_iff` characterization for a predicate and an equation or exhaustive case lemmas for other definitions. `ProverBounded.mono`, `.exists_complete`, and `.pullback` do not characterize the predicate. `attempt_poly` and `retry_poly` establish efficiency, not evaluation equations. `exists_retrySimulator` relates a machine to `retry`, but does not expose how `retry` selects an attempt. `firstHit_map_getD_eq` is generic and mentions neither definition. No supplied waiver or scheduled row covers these omissions. This matters particularly for the new predicate exported to ch. 7. A lint report of zero findings does not establish this semantic API requirement. | Publish an ordinary `proverBounded_iff`, `attempt_eq`, and `retry_eq` (or exhaustive retry cases), with formula docstrings. Use those interfaces in consumers. Do not add `@[simp]` without approval. Include the added declarations in the axiom evidence. |
| 3 | minor | `resolutions-03e-r1.md:31,34,44,54` · completion accounting | Some “fixed” records are contradictory or cannot be verified from the closing bundle. | Row 5(c) says the run-3 erratum is fixed, then says it is missing; M8 explicitly says it is not done. The claimed updated run-3 summary, `inventory-ch5-8.md`, and `SPINE-DESIGN.md` are absent, including from the repair diff. Moreover, the current replay has **18 non-ZK warnings**, not 22: 17 in machine/class modules and one in `NonUniform`; the other three are in 3COL. The 22 figure belongs to round 1's larger closure. | Give row 5(c) one accurate status; distinguish historical and current counts. Supply the short changed record excerpts or classify their completion as a maintainer declaration rather than an independently verified fix. Keep gate-06 work explicitly scheduled. |
| 4 | minor | `NP.lean:679,698` · `zk_proof_of_witnessRelation`, `zk_proof_of_witnessRelation_of_owp` | The docstrings promise returned **Levin reductions**, but the conclusions return functions and a polynomial without their `LevinReduction` certificate. | The conclusions retain only `∀ N, N ≤ p.eval N` and the protocol properties. They do not export polynomial-time instance/witness maps, membership preservation, witness preservation, or `length_eq`. Thus a consumer cannot conclude that the returned `f,w,p` are a Levin reduction, or that `p` is the returned map's length polynomial. The explicitly supplied-reduction theorem at line 634 does not have this problem. | Include `LevinReduction L L3COL R R3COL f w p` in both existential conclusions. Alternatively narrow the docstrings to the properties actually exported; retaining the certificate is more useful. |
| 5 | minor | `Interaction.lean:39–43` · repetition convention | The new sentence says an **empty** fourth verifier message is appended to every iteration, including the repeated GI/3COL protocols. | Under the documented verdict convention, a verifier's last message equals its verdict (`outV_eq_getLast_of_moverIsV`). For a prover-first protocol with $4n>0$ messages, an empty final verifier message therefore forces `outV = []`, contradicting completeness on a yes-instance. Section B explicitly gives `giProtocolRep.rounds = 4·var`. The filler slot may be nonempty when it carries the verdict. | Say “an additional verifier move” and distinguish intermediate padding from a final verdict-bearing move. Do not describe every fourth message as empty. |
| 6 | minor | `Defs.lean:42–47`; `DESIGN.md` §7 item 51 · auxiliary-input justification | The copied round-1 argument overgeneralizes from breaking 3COL commitments to failure of **every** protocol whose hiding is only computational. | Breaking a commitment is not by itself a real-versus-simulated-view distinguisher. For example, a one-message prover committing to a fixed public value with a computationally hiding commitment has an exact simulator: sample that same commitment and the verifier's tape. This works for arbitrarily long auxiliary inputs. For 3COL, inequivalent witnesses supply the missing witness-separation argument; see finding 1. | Retain the polynomial auxiliary-input convention. Explain that it keeps reductions within the stated security parameter, and restrict the impossibility example to an explicit witness-dependent protocol such as 3COL. Do not label the universal assertion a source error. |
| 7 | minor | `InteractiveProofs.lean:43–48,114`; `DESIGN.md` §5 item 8 · scope of the bounded-message rationale | Two qualifications are missing: arbitrary-error proof structures need not recognize only IP languages, and an ordinary interactive proof does not have a PPT prover by definition. | For `s := 1`, take zero rounds, an empty-message prover and the always-accepting verifier. `EfficientProverProofErr π L R s` holds for **every** language and relation: the bound is zero and soundness is $0\le0$. The module's unqualified “proof systems hold only for languages … IP” therefore needs an error hypothesis. Also [PS10], book p. 117, explicitly allows inefficient provers; the “text's p.p.t. prover” rationale applies to Def 119.5, not Def 116.1. | Restrict the language claim to `InteractiveProof` and negligible-error conversions, or state a suitable soundness-gap hypothesis. For ordinary IP, describe bounded honest messages as the chosen normal-form convention, motivated by the verifier's polynomial reading bound. |

## Round-1 resolutions

“Not resolved” below distinguishes the successful mathematical part of a repair from its remaining interface or record defect. Scheduled work is accepted as a declared gate-06 obligation, not certified as already integrated.

1: **not resolved** — G3-3 removes the original unbounded-certificate defect and supplies the required message bounds, but the new predicate lacks its required reading API (finding 2); the scope qualifications in finding 7 also remain. The prong-C replacement is scheduled for gate 06.

2: **not resolved** — the GI cost and both abort bridges are correctly stated; the mathematical repair succeeds. The claimed DESIGN repair still incorrectly upgrades 3COL to statistical ZK (finding 1), and the retry definitions have finding 2. Prong-C integration remains scheduled.

3: **not resolved** — the two protocols are now tied to the same commitment and maps, and the one-iteration error is explicit. The new witness-relation forms overdescribe the returned maps (finding 4). The full negligible-soundness ZK theorem remains explicitly scheduled for gate 06.

4: **fixed** — both new witness-relation theorems quantify over an arbitrary supplied `R` and `WitnessRelation L R`; the old NP-membership forms are corollaries. Finding 4 is a separate omission in the exported reduction data.

5: **not resolved** — the five missing headline prints are present and clean; section B identifies the two admitted 3COL dependencies for all seven NP headlines. Part (c)'s contradictory completion record remains (finding 3).

6: **fixed** — `[Gol01]` is supplied; the two p. 116 misquotes are paraphrased; the remaining `ReadsPrefix` quotation agrees with the attached page. The AB reference is broadened to §2.3 as the review permitted. The prong-C tag change is scheduled.

7: **fixed** — Q-1 is recorded, and its conditional rationale is correct: with `ProverBounded` and the ZK auxiliary-input bound, every verifier view has polynomial length. `ZK` alone does not assert `ProverBounded`, nor does this audit infer that it does.

8: **not resolved** — the convention is recorded, but “empty” is inaccurate for a verdict-bearing final verifier move (finding 5).

9: **not resolved** — the convention and justification are now recorded in both places, but the universal impossibility claim needs narrowing (finding 6). The polynomial bound itself is retained.

10: **fixed** — `perfectZK_zeroRounds` gives a nonvacuous exact-simulation example for every relation, including nonempty ones; the module names `gi_statZK` as the substantive GI instance.

11: **fixed** — the docstring accurately distinguishes globally bounded relations from the bounded existential in Def 191.11. Intersecting the source relation with its witness-length bound preserves its language.

12: **recorded** — the same-length/exact-randomness restriction is accurately documented. The review's assertion that `colVerify` checks the lengths is accepted as 03g context, not independently re-audited here.

13: **fixed** — `exists_commitment_of_owp` has precisely the missing OWP-only premise and a standard-axiom print. No hard-core predicate remains as a caller-supplied premise of this theorem.

14: **fixed** — padding is now explicitly assumed and unformalized; the square-length encoding constraint is acknowledged. `LevinNPHard` remains an explicit hypothesis.

15: **recorded** — the two limits are described in the review and resolution, but the claimed `SPINE-DESIGN.md` edit is not supplied. I accept the limits as declared, not the unseen edit as independently verified (finding 3).

16: **fixed** — the closing pack explicitly assigns Thm-124.1 and Claim-124.d to 03g and includes their NP forms in this audit. The historical round-1 pack need not be silently rewritten.

17: **recorded** — the resolution records G3-6 approval; the five current files contain exactly the listed 15 `@[simp]` attributes. No new approval is inferred for other declarations.

M1: **recorded** — the correction is sound: `ReadsPrefix` alone does not bound arbitrary tape length, witness length, or history length. G3-3 imposes the message bound directly.

M2: **recorded** — G3-3 requires no prefix-reading redesign of 3COL. Section B supplies bounded-message claims from the commitment evaluator; their detailed consumer audit belongs to 03g.

M3: **fixed** — both completeness fields contain a single polynomial bound before the instance quantifier, independently of `R`. Taking `R` empty cannot erase that obligation.

M4: **fixed** — the GI-specific fair-coin obstruction is documented: a law on six permutations obtained from finitely many fair bits cannot be uniform. Conditioning an aborting simulator does not repair witness dependence in the real prover's view.

M5: **not resolved** — the perfect-form warning was added, but the live DESIGN row still calls 3COL statistical ZK (finding 1). `SequentialZK.lean` changes are scheduled for gate 06.

M6: **scheduled** — the resolution names prong-C commit `9e6f08bb28b2fcebfa845d47a9fd6e1ed281f951` for amplification statements and gate 06 for the 3COL corollary. Those files are absent; this is accepted as a named integration obligation, not as proof that DQ5 has already been discharged.

M7: **fixed** — the closing pack correctly identifies 03g as 3-colouring and 03k as graph isomorphism.

M8: **not resolved** — #12's no-change disposition and #13's corrected premise are adequate; #5(c)'s record correction is explicitly still undone in this very row (finding 3).

M9: **fixed** — the four efficiency fields say `Strategy.Efficient`/D8, and the second misquote is removed. Finding 7 concerns a different remaining source attribution.

M10: **recorded** — the recorded approval preserves the 15 attributes; no removal or downstream proof migration is claimed.

## New declarations: independent restatement and docstring check

The three definitions were read from their bodies before comparing their docstrings. This table covers all **22** declarations listed in the round-2 brief.

| Declaration | Mathematical content and assessment |
|---|---|
| `Protocol.ProverBounded` | For every related instance/witness pair, every finite tape and every received history, the honest prover's next output has length at most the same polynomial `B` evaluated at the instance length. The body matches the claimed bound, including histories and tapes that cannot arise in an execution; finding 2 concerns its missing characterization. |
| `ProverBounded.mono` | A bound remains valid after pointwise increasing its polynomial. Matches the docstring. |
| `ProverBounded.pullback` | A target protocol bounded for `R'` by `B`, pulled back through a certified length-regular witness-preserving reduction of length `p`, is bounded for `R` by `B.subst p`. Witness preservation and `length_eq` supply exactly the needed hypotheses. |
| `ProverBounded.exists_complete` | Bounded honest messages, probability-one acceptance for every related witness, and a witness for every language member imply the new existential completeness clause. In particular it retains the essential language-to-relation hypothesis. Matches. |
| `npProtocol_proverBounded` | If every `R`-witness has length at most `p`, the prover that copies its witness has message bound `p`, independently of tape/history and of the verifier test. Matches. |
| `InteractiveProof.exists_accept` | Erases the bound from completeness and retains a single auxiliary input working for every verifier auxiliary input. Matches; it does not weaken the structure itself. |
| `InteractiveProofErr.exists_accept` | The same projection for the explicit-error structure, with no soundness assumption needed for this completeness fact. Matches. |
| `PerfectZKAbort.statZK` | An aborting exact conditional simulator with failure probability at most one half yields a strict uniform simulator within $2^{-n}$ of the real view, for every related witness and every auxiliary input. Matches; (n=0) legitimately permits error one. |
| `PerfectZKAbort.zk` | The previous bound is negligible, so the abort notion implies computational ZK. Matches; it does not assert the converse or recover perfect ZK. |
| `perfectZK_zeroRounds` | For arbitrary parties, first mover and relation, a zero-message protocol has an exact simulator for every efficient replacement verifier. Its view contains only the public input, auxiliary input and verifier coins. Matches; it does not claim a proof-system property. |
| `AbortRetry.attempt` | Decode the layout parameter and argument, discard the layout advice, and run `S.output` with empty advice on the selected block of `S.coinLen` bits. Matches, including short or absent blocks. For nonuniform `S` this is not its advised activation; the docstring correctly specifies empty advice. |
| `AbortRetry.retry` | Among indices below the decoded parameter length, output the first nonempty attempt, otherwise `[]`. Matches. There are zero attempts at parameter zero; finding 2 concerns the missing evaluation API. |
| `AbortRetry.attempt_poly` | An attempt is polynomial-time as a function of an encoded pair whose first component's **length** specifies the index. Matches the unary-index docstring; no binary-index running-time claim is made. |
| `AbortRetry.retry_poly` | The deterministic layout-to-output retry function is polynomial-time. A polynomial number of polynomial-time attempts supports the sketch; no uniformity assumption on `S` is needed when its advice is discarded. Matches. |
| `AbortRetry.statClose_retry` | For a nonempty finite uniform attempt space, success probability at least one half, and a target law equal to the successful conditional law, the first success among `K` independent draws, with any default, is within $2^{-K}$ of the target. Matches; the target finite space need not be separately declared nonempty because the hypotheses force it. |
| `AbortRetry.exists_retrySimulator` | Every `S` has a uniform machine implementing its empty-advice retry function, with coin polynomial `var * S.coins` and the stated simulation equation on every typed tape. Matches. This becomes retrying the original `S.simulate` when `S.Uniform` is available in the bridge. |
| `AbortRetry.firstHit_map_getD_eq` | If the indexed output and Boolean test agree with mapped draws and event membership below `K`, first-hit/map/default equals indexed first-success/default. Matches, including `K=0` and the absence of any hit. |
| `AbortRetry.uprob_not_ne_nil_le` | A bound on the event `g = []` is the same bound on the logically identical event `¬ g ≠ []`. Matches; this is not an additional independence or conditional-probability assertion. |
| `exists_commitment_of_owp` | Existence of a one-way permutation implies existence of an efficient, perfectly binding, computationally hiding commitment with a polynomial randomness length. Matches Thm 126.4 in the declared family model. |
| `zk_proof_of_witnessRelation` | Given Levin hardness, a commitment, and any witness relation, returns maps and `p ≥ id` tying the repeated efficient proof and the single-iteration ZK/error guarantee to the same commitment. The protocol assertions match; the claimed certificate for the returned reduction is absent (finding 4). |
| `zk_proof_of_witnessRelation_of_owp` | Adds existence of a single commitment from an OWP-only assumption, then returns the preceding tied protocol guarantees for any supplied witness relation. Same finding 4; the repeated protocol is not asserted to be ZK. |
| `exists_commitment_zk_proof_of_owp_levinReduction` | For a supplied certified reduction and language-to-witness coverage, an OWP yields one commitment supporting both the repeated efficient proof and the single-iteration ZK proof with the explicit error. Matches, subject to the declared DQ5 limitation and imported admissions. |

## Changed existing surface and source fidelity

| Surface / source item | Assessment |
|---|---|
| `InteractiveProof`, `InteractiveProofErr` — Defs 116.1/117.a | Completeness now has `∃ B ∀ x∈L ∃ y`, followed by a bound for **all** tapes/histories and acceptance for **all** verifier auxiliary inputs. Soundness is unchanged. The residual total-input-time convention is declared; the cap argument works for the negligible-error language claim. Finding 7 supplies the missing qualifications. |
| `EfficientProverProof`, `EfficientProverProofErr` — Def 119.5 | They retain their base proof property, efficient prover and every-witness completeness, and add `∃ B, ProverBounded R B`. This is the authorized G3-3 convention, not an assertion of the source's literal worst-case running time. The negligible-error conversions retain `boundedP`. |
| `npProtocol_interactiveProof`, Levin proof transfers — Claim 117.c / Claim 124.d | The theorem texts remain suitable after strengthening the structures. Their updated sketches supply bounded completeness and `boundedP`; pullback composes the message bound with the reduction length. `hLR` is retained. No new semantic regression found. |
| `Strategy.Efficient`, interaction module — Def 116.b | The time convention and separate writing bound are now explicit. The paraphrases agree with book p. 116. The repetition sentence needs finding 5's correction. |
| `WitnessRelation` — Def 191.11 | The added explanation accurately states the stronger bound on the relation itself. It preserves the intended NP-language characterization. |
| `ZK`, `PerfectZK`, `PerfectZKAbort` — Defs 121.2/122.a | Bodies are unchanged. Q-1's conditional view-length argument is valid. The GI obstruction and the abort bridge are accurately described. Treat “instances … are degenerate” as a description of supplied exact instances, not an impossibility theorem about all fair-coin protocols. Finding 6 narrows the auxiliary-input argument. |
| `Commitment` — Def 126.3 | The added length warning matches the existing binding quantifiers and the attached definition. The source's missing distinct-value premise remains explicitly corrected. |
| `LevinReduction`, NP headlines — Def 124.a / Thm 124.1 | Padding is now an assumption, with its square-length restriction acknowledged. Named and tied headlines distinguish the one-iteration ZK guarantee from the repeated negligible-error proof. The membership forms remain valid weaker corollaries. The absence of a returned reduction certificate is finding 4; the full text theorem is still deferred. |

The independent `L ∈ NP` corollary keeps its older OWP-plus-hard-core premise; this is not a regression, since the new arbitrary-witness form supplies the OWP-only theorem. The commitment addition also closes the missing text-form Thm-126.4 item. No new claim of interactive arguments or view/output equivalence is introduced by the repair.

## Adversarial checks

**1. Unbounded halting histories, including the empty-relation escape.** A computation-history prover that sends its full witness cannot supply the new global bound on the witnesses selected for completeness. More generally, truncate every prover message at `B(n)` before the original verifier reads it. Honest messages are unchanged; against any cheating prover, the capped verifier has the same execution as the original verifier against that prover with truncated outputs, by induction on moves. For the language argument fix verifier auxiliary input `[]`. This recovers a polynomial verifier and preserves negligible soundness. Taking `R := ∅` cannot bypass the independent base completeness field. **Attack fails for `InteractiveProof`.** The arbitrary-error `s=1` boundary is separately reported in finding 7.

**2. Echoing prover and doubling verifier.** For a related witness, choose a received message longer than `B(n)`. A prover that echoes it violates `ProverBounded` immediately, even if the history or random tape is not a reachable one. Under the actual bound, the verifier's received-message component has at most `rounds(n)` messages of length at most `B(n)`; its own tape and polynomially bounded auxiliary input add only polynomial length. **The original exponential-view attack is excluded under the stated hypotheses.**

**3. Zero retries and the sharp half-abort case.** Let an attempt output `[]` with probability $1/2$, and a fixed nonempty word otherwise. For `K` independent attempts,

$$
\Pr[\text{all abort}]=2^{-K},\qquad
\Pr[\text{retry}=\text{the nonempty word}]=1-2^{-K}.
$$

The target is the point mass on that word, so the distance is exactly $2^{-K}$. At `K=0`, retry is always `[]` and distance is exactly one. **The bridge's bound is correct and sharp, including the empty input.** A zero-coin aborting simulator is deterministic and, on a related instance, cannot abort at all under the half-abort premise; positive retry counts then give exact simulation.

**4. Empty sample spaces and arbitrary defaults.** `statClose_retry` excludes an empty attempt space explicitly. If its target space were empty, the conditional-law equation with the always-true test would give $0=\Pr[E]$, while the abort bound gives $\Pr[E]\ge1/2$, a contradiction. For an arbitrary default and any test `T`, writing $p=\Pr[E]$ and $f=(1-p)^K$, the stated conditional-law identity yields

$$
\Pr[T(\mathrm{retry})]
=f\,\mathbf1_{T(d_0)}+(1-f)\Pr[T(Y)],
$$
$$
\left|\Pr[T(\mathrm{retry})]-\Pr[T(Y)]\right|
=f\left|\mathbf1_{T(d_0)}-\Pr[T(Y)]\right|
\le f\le2^{-K}.
$$

**No vacuity or default-value loophole was found.**

**5. Statistical ZK for 3COL: the design-record counterexample.** For every $m\ge3$, let $G_m$ have vertices $0,\ldots,m-1$, its sole edge $\{0,1\}$, and encoded instance $x_m$. Define two proper colourings by

$$
c_0(1)=1,\quad c_0(j)=0\ (j\ne1),\qquad
c_1(2)=2,\quad c_1(j)=c_0(j)\ (j\ne2).
$$

Every permutation of the three colours preserves

$$
c_0(0)=c_0(2),\qquad c_1(0)\ne c_1(2).
$$

Fix an efficient verifier that requests the only edge, with auxiliary input `[]`. Let `T_m` be the unrestricted test on its view that the first and third vertex commitments admit openings to the **same** padded colour, using randomness of the required length. This is a legitimate test in `StatClose`; it need not be efficient. Honest openings and perfect binding give, for the two real-view laws,

$$
\Pr[T_m(X_0)]=1,\qquad \Pr[T_m(X_1)]=0.
$$

Indeed, if the second execution also passed the test, either its first or its third commitment would have two distinct valid colour openings, contradicting `Commitment.binding`. Sampling a biased colour permutation does not change the equality/inequality invariant.

A simulator receives the same `x_m` and auxiliary input for both witnesses. If its law is `Q_m`, put $q_m=\Pr[T_m(Q_m)]$. Statistical error `δ` for both witnesses would require

$$
1-q_m\le\delta(|x_m|),\qquad q_m\le\delta(|x_m|),
\qquad\Longrightarrow\qquad \delta(|x_m|)\ge\tfrac12.
$$

The instance lengths grow without bound ($|x_m|=m^2$ in the stated graph encoding), contradicting negligible `δ`. **Finding 1 follows.** This is a mathematical counterexample to the design claim, not a claim that a new Lean impossibility theorem was compiled.

**6. Boundary reduction length.** The tied NP error is strictly below one when `p.eval N > 0`. At `N=0` and `p.eval 0=0`, Lean's inverse-of-zero convention makes the stated error two. This is a harmless finite boundary, not restored asymptotic trivialization: `p.eval N ≥ N` gives a positive polynomial inverse soundness gap for positive lengths. No new finding.

## Execution evidence and deferrals

- The bundle contains 19 sections. Its SHA-256 is `38834d4d0e6b7ec109fef93466add13482a3a3393b020e756131a592cba7daa0`; the brief supplies no expected hash for comparison. The extracted round-1 findings **do** match the declared SHA-256 `8af18f12965eb01b594de42d60e567b4ad5cb2810652a94f70f7daf0aef0a7e3`.
- All **42** section-A diff hunks match the supplied current files on their new side. This checks bundle consistency, not remote commit provenance.
- The supplied replay has **126 module rows**, every return code zero, zero errors and **21** warnings: 17 in machine/class modules, one in `NonUniform`, two in `ThreeColoring/Protocol`, and one in `ThreeColoring/Simulator`. The round-1 closure additionally contained `RecordTable`'s four warnings; its historical count must not be presented as the current count.
- The axiom log has **116** public theorem/lemma entries: **109** use only subsets of `propext`, `Classical.choice`, `Quot.sound`; **7** additionally use `sorryAx`. The latter are `zk_proof_of_levinReduction`, `zk_proof_of_owp_levinReduction`, `exists_commitment_zk_proof_of_owp_levinReduction`, `zk_proof_of_witnessRelation`, `zk_proof_of_witnessRelation_of_owp`, `zk_proof_of_mem_NP`, and `zk_proof_of_mem_NP_of_owp`.
- Section B adds the requested dependency annotations naming `colRep_efficientProverProof` and `col_zk`. The new bound/retry lemmas and `exists_commitment_of_owp` have standard-axiom prints. The supplied admission list is empty for the five in-scope files; the imported admissions remain real and are not hidden by that statement.
- The lint report says zero findings in five files. This does not discharge finding 2's equation/characterization requirement.
- DL-13 explicitly records `negligible_const_zero` for the G3-5 cleanup after #195. The other scheduled duplication rows are not reclassified as new defects. Gate-06 integration of bounded messages, perfect-form wording, and the amplified 3COL ZK corollary remains a declared obligation. Neither the generic amplification statement nor the fact that two protocols use the same commitment, by itself, identifies `colProtocolRep` with the generic sequential-repetition construction.

## Notation

The Lean names retain their bundle meanings. In the calculations, $n=|x|$ is instance length; `B` is the honest-message bound; `K` is the retry count; $p=\Pr[E]$ is retry success probability and $f=(1-p)^K$ its all-failure probability (separate from the NP reduction polynomial named `p`); $d_0,Y,T$ are the retry lemma's default, target sampler and test; $\mathbf1$ is an indicator. In the 3COL counterexample, $m,G_m,x_m,c_0,c_1$ are the vertex count, graph, encoding and two colourings; $T_m$ is the same-colour-opening test; $X_0,X_1,Q_m$ are the two real-view laws and simulator law; $q_m$ is the simulator's test probability; $\delta$ is the proposed statistical error.
