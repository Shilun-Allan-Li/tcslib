## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/03e-pack-r3.md =====

# Gate 03e ([PS10] ch. 2–4, interaction, proof systems, ZK definitions, commitments, NP layer), round 3: delta audit pack

**What is audited:** the repair of round 2, on `cryptography/pass-shelat-ch2-4` at `1ea782b11617e15a51c3e2f6bd15dd0e3befbd95` (the merge of
[Shilun-Allan-Li/tcslib#206](https://github.com/Shilun-Allan-Li/tcslib/pull/206), the gate 03 repair batch, and the records commits of 2026-11-06).
- **The round 2 findings** are `findings/gate03e-r2-findings.md` (in the bundle, verbatim), the maintainer's review `review/gate03e-r2-review.md`, and the resolutions `resolutions-03e-r2.md`.
- **The repair:** #206's diff (`evidence-repairs/03-batch/repair.diff.txt`; it covers five gates, and only this pack's files are under audit) and the records changes named in the resolutions.
- **The deliverable:** **`gate03e-r3-findings.md`**.

The bundle holds this pack, then every file named below under a `## ===== <path> =====` header. **The source is attached separately:** [PS10] (PDF; book page = PDF page − 12).

## Brief for the auditor

1. **Verify each resolution** of `resolutions-03e-r2.md`: fixed, recorded, scheduled, or not resolved (and why).
2. **Audit the changed surface afresh:**
   - the reading lemmas `Protocol.proverBounded_iff`, `AbortRetry.attempt_eq`, `retry_eq`, `retry_eq_attempt`, `retry_eq_nil`: each states its definition's equation (or cases) and nothing more;
   - every former body-read of `ProverBounded` now goes through `proverBounded_iff` (the seal log is the evidence);
   - **the one statement change** (ruling R-03e-r2-1 (A)): `zk_proof_of_witnessRelation` and `_of_owp` now also return `LevinReduction L L3COL R R3COL f w p`; check it is exactly the certificate the docstring describes;
   - the rewritten docstrings (#5–#7) and the DESIGN records (#1, #6, #7).
3. **Check that nothing else changed** in this pack's files: the statement diff (`statements.txt`) lists every added and changed declaration of the batch.

Pack 03a's severity guide applies. Attempt at least one adversarial instantiation against the changed surface. Do not give a blanket approval.

## Scope

| Item | Where |
|---|---|
| Findings, resolutions, the diff | as above |
| Under audit, at the pin | `ZeroKnowledge/{Interaction, InteractiveProofs, Defs, NP}.lean`; context, with re-points and qualifiers only: `ZeroKnowledge/GraphIsomorphism.lean`, `GraphIsomorphism/{Soundness, SoundnessRepGI}.lean`, `ThreeColoring/Protocol.lean`; records: `briefs/pass-shelat/DESIGN.md` (D8 erratum, §5 items 8 and 11, §7 item 51) |
| Context | `03e-pack.md` and earlier round packs, `03a-pack.md`, `policy.md` |

## Attestations (maintainer execution claims; `evidence-repairs/03-batch/`)

- **Elaboration** (`replay.log`): the 128 modules downstream of #206's 21 changed files, then `audits/pass-shelat/Checks`, each checked alone after a base sync (`base-sync.log`): **129 of 129 pass, 0 errors**; every module's `sorry` count equals the base. A maintainer re-check of 8 key modules also passes (`maintainer-recheck.log`).
- **Axioms** (`axioms.log`): 549 prints over the 21 files, compared with the base: no axiom set changed; the 10 new lemmas are standard.
- **Seal** (`seal.log`): the consumers of `ProverBounded` pass sealed (their base versions fail); the new proofs pass with the definitions they could unfold sealed.
- **Lint** (`lint.log`): `scripts/style_lint.py` and `scripts/campaign_style_lint.py --check8b`, compared with the base: no new finding.
- **Statements** (`statements.txt`): 10 added, 2 changed (the two ruled ones in `NP.lean`), 0 removed.

## Findings format (auditor fills)

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Plus one line per resolution row: `<row>: fixed / recorded / scheduled / not resolved — <reason>`. The gate closes at **0 blockers and 0 majors**.

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/findings/gate03e-r2-findings.md =====

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

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/review/gate03e-r2-review.md =====

# Gate 03e, round 2 (closing round): review of the external auditor's findings

- **Reviewed:** `briefs/pass-shelat-ch5-8/gates/03-ch2-4/findings/gate03e-r2-findings.md`: 0 blockers, 2 majors (#1, #2), 5 minors (#3–#7), plus 27 resolution-row verdicts.
- **Pack:** `03e-pack-r2.md`, with `resolutions-03e-r1.md`, `evidence-r2/03e/repair.diff.txt` and `evidence/e2/`.
- **Code at the pin:** worktree `scratchpad/wt-g03c-fix` at `0c348ff94cacf24d96d99078c9dd9e328530c8d2`. Its Lean files equal those of the audited pin `e79397ea` (`git diff 0c348ff9 e79397ea -- TCSlib` is empty). Lean line numbers below refer to it; Lean paths are under `TCSlib/Cryptography/ZeroKnowledge/` unless qualified.
- **Records:** read at the pin `e79397ea` (what the auditor saw) and at the branch head `ee6a8d02`.
  - The five audited Lean files, `Asymptotic/Sampling.lean`, `policy.md` and `resolutions-03e-r1.md` are unchanged from the pin to the head.
  - #203 (clean-up part 1) changed only `ThreeColoring/Machines.lean` in `ZeroKnowledge/`, and DESIGN §2.4/§2.6. **No finding is affected by #203.**
  - #205 (03a round 2, docstrings in `PPT.lean`, `Adversary.lean`, `Ensembles.lean`) does not affect any finding either.
  - DESIGN lines shifted after the pin. D8 is at 136 (pin) / 137 (head); §5 item 8 at 1009 / 1045; §5 item 11 at 1019 / 1055; §7 item 51 at 1254 / 1292. The text of those items is unchanged.
- **Downstream code read:** prong C `scratchpad/wt-prong-c` at `9e6f08bb` (`Composability/SequentialZK.lean`).
- **Source:** `blueprint/src/references/pass-shelat-2010-ch4.raw.md` (pp. 116–117, 119, 121–122), checked against the auditor's quotations.
- **Not done:** no Lean was built or run (`CLAUDE.md` forbids `lean`, and no probe was essential). The `Iff.rfl`/`rfl` lemmas below are definitional. The two case lemmas in §2 are uncompiled sketches.

## Summary

- **Verdicts: 6 true (#1, #2, #4, #5, #6, #7), 1 partly true (#3), 0 false.**
  - #3 is partly true. The contradiction inside `resolutions-03e-r1.md` (rows 5 and M8) is real. But the records the auditor could not see are all present at the pin, so the defect is stale resolution text, not missing record fixes. They are: the run-3 erratum, `SPINE-DESIGN.md`'s "Two limits", and the `inventory-ch5-8.md` Thm-175.1 row.
  - #5 and #7 are **understated** (§2, M3, M4).
- **No new theorem statement is false.** I agree with the auditor here. #4's two conclusions are weaker than their docstrings say, but they are provable and true as stated.
- **Severity: no change.** 2 majors, 5 minors.
  - **#1 stays major, narrowly.** No Lean statement or ch. 5–8 record depends on the error. But DESIGN §5 is the "Deviations register (docstring text, one line each)": its lines are meant to be copied into docstrings. Its item 11 and the frozen D8 both claim statistical ZK for 3COL, which is false here, not merely unproved. The record was also the declared object of a repair (M5).
  - **#2 stays major, because of `ProverBounded` alone.** The precedent is gate 04's F02 (major): a published definition that crosses into ch. 5–8 and is read through its body by consumers in other files. `Protocol.ProverBounded` is both.
    - It is the hypothesis of prong C's `ZK.seqRep`, `StatZK.seqRep`, … (`SequentialZK.lean:376–411`). Gate 06 integration deletes prong C's local copy in favour of this one.
    - Four ch. 2–4 files read it by definitional unfolding at 11 sites (M1).
    - `attempt` and `retry` alone would be **minor**, by gate 03l's precedent (Minor 3: readers in the same file, no ch. 5–8 reader). Prong C reaches `PerfectZKAbort` through `PerfectZKAbort.statZK`, not through these.
- **Fixes, in order of importance:**
  1. **#2:** add `Protocol.proverBounded_iff` (Interaction.lean, after :332), `AbortRetry.attempt_eq` (Defs.lean, after :308) and `AbortRetry.retry_eq` (after :318). Two optional case lemmas for `retry` are also given (§2).
     - Re-point the 11 consumer sites (M1) to `proverBounded_iff`.
     - Run a rule-10 seal (`attribute [local irreducible] TCSlib.Cryptography.Protocol.ProverBounded`) on the four consumer files, with controls.
     - Add prints for the new lemmas to `Checks.lean`. None of the new lemmas gets `@[simp]`.
  2. **#1:** add a dated erratum under D8 (the design is frozen) and rewrite DESIGN §5 item 11. GI is `StatZK` with negligible δ; 3COL is computational `ZK`.
  3. **#4 (ruling R-03e-r2-1):** add `LevinReduction L L3COL R R3COL f w p` to the conclusions of `zk_proof_of_witnessRelation` and `_of_owp`.
  4. **#7, #6, #5:** docstring and record corrections.
     - #7: `InteractiveProofs.lean:35–48, 113–118`, DESIGN §5 item 8.
     - #6: `Defs.lean:42–48`, DESIGN §7 item 51.
     - #5: `Interaction.lean:39–43`, plus the two `…Rep` docstrings in packs 03k and 03g.
  5. **#3:** delete the stale sentences in `resolutions-03e-r1.md` row 5 and M8. State the current counts: 21 `sorry` warnings in the 126-module closure, 18 outside the ZK files (17 `main`'s, 1 `NonUniform`).
  6. **For clean-up part 2, not for closure:** the tactic-level unfolds in the repair's new proofs (M2).
- **Rulings needed: one.**
  - **R-03e-r2-1 (#4)** changes two theorem statements (§5).
  - One more is conditional. If #2's lemmas are deferred to clean-up part 2 instead of landing before closure, that accepts debt on a ch. 5–8 interface and needs a ruling (R-03e-r2-2, §5). I recommend not deferring them.
  - Everything else is the maintainer's: records, docstrings, policy-mandated lemmas.
- **Overlap with clean-up part 2** (`briefs/pass-shelat-ch5-8/fills/cleanup-part2/brief-draft.md`): **none for the findings themselves.**
  - Part 2's items A–F and J do not mention `ProverBounded`, `attempt`, `retry` or `firstHit`.
  - Item J is gate 04 round 4's seal exclusions. Gate 04's ch. 2–4 seal set includes `ZeroKnowledge/Interaction.lean`'s **own** proofs (for example `pairFstD_encodeMsgs`). It does not include the consumers of `ProverBounded`, which are in `InteractiveProofs.lean`, `NP.lean`, `GraphIsomorphism.lean` and `ThreeColoring/Protocol.lean`.
  - There are only two contacts:
    - **Item C.** It adds `NUPPT.coinLen_eq`, `advInput_eq` and `runAtL_eq` and re-points only `Closure.lean`'s sites. Its re-point list should add `Defs.lean:291, :543` (new in this repair) and `InteractiveProofs.lean:449, :462` (M2).
    - **DL-13** deletes `negligible_const_zero` from `Defs.lean`, the file that gains `attempt_eq`/`retry_eq`. Expect a trivial file-level merge if both are in flight.
  - Recommendation: land #2 in the 03e closing repair now. Do not wait for part 2, which is issued only after gate 04 closes and #195 merges.

---

## 1. Major #1: the design record calls 3COL statistically zero-knowledge

### Verdict: **true**. Severity: **major (agree, narrowly)**.

**Evidence at the pin.**
- DESIGN D8, lines 135–137: "… `PerfectZKAbort` are stated; GI and 3COL are proved statistically (truncated simulators, rejection-sampled permutations)."
- §5 item 11, line 1019: "GI/3COL: statistical ZK (truncated simulators, rejection-sampled permutations / edges / colour permutations); …". The round 1 records fix (`e79397ea`) rewrote only the item's tail.
- The code says otherwise:
  - `col_zk : ZK (colProtocol Com ℓ) R3COL` (`ThreeColoring/Simulator.lean:764`, `sorry`). Its sketch (:735–763) uses `hC.multiHiding`, a computational step.
  - Only `gi_statZK : ∃ δ, Negligible δ ∧ StatZK giProtocol Riso δ` (`GraphIsomorphismZK.lean:561`) is statistical. It prints standard axioms (`evidence-repairs/03ac/checks-axioms.log`).
- The other records are right:
  - `inventory-ch4.md:207` says "ZK of the 3COL simulator (computational)".
  - The round 1 review (§2.1, "03g is unaffected, since 3-colouring is computational") says the same.
  - Prong C cites `ZK.seqRep` for 3COL.
  - A grep of `briefs/` and `TCSlib/Cryptography` finds the false claim only at DESIGN lines 136 and 1019.

**Counterexample: rebuilt and confirmed against the Lean definitions.**
- `Commitment.binding` (`Commitment.lean:115–117`) holds for all `n`, all `v₀ ≠ v₁` of length `n` and all `r₀, r₁` of length `ℓ(n)`.
- `colProver` (`ThreeColoring/Protocol.lean:408–424`) commits, for each vertex `i`, to `padColor n (π (c i))` with an `ℓ(n)`-bit block `rr i`, via `colCommit` = `multiCom`.
- Take `G_m`: `m ≥ 3` vertices and the sole edge {0, 1}. Take the colourings:
  - `c₀ = (0, 1, 0, 0, …)`;
  - `c₁ = (0, 1, 2, 0, …)`.

  Both are proper, so both are `R3COL` witnesses for `x_m = encGraph G_m` (`Language.lean:115`).
- Let `T` be the (inefficient) test on the encoded honest-verifier view: "some `v` of length `n`, and some `r, r'` of length `ℓ(n)`, satisfy `Com⟨v, r⟩ = msgAt com 0` and `Com⟨v, r'⟩ = msgAt com 2`".
  - Under `c₀`, `T` holds always: take `v = pad(π 0)` with the real blocks.
  - Under `c₁`, `T` never holds. Binding forces `v = pad(π(c₁ 0))` and `v = pad(π(c₁ 2))`. Since `π` and `padColor` are injective, that gives `c₁ 0 = c₁ 2`, a contradiction.
  - Colour permutations preserve both facts.
- A simulator gets only `(x_m, z)`, so its value `q` on `T` is the same for both witnesses. Hence `δ(m²) ≥ max(1 − q, q) ≥ 1/2` for all `m ≥ 3`, and `δ` is not negligible.
- So `StatZK (colProtocol Com ℓ) R3COL δ` with negligible `δ` is **false** for every `Commitment`, not just unproved.

**Why major and not minor.**
- §5's heading says its lines are docstring text, so a worker copying item 11 would write a false docstring.
- D8 is a frozen foundation decision that ch. 5–8 planners read. Under it, a ch. 7 plan would reach for `StatZK.seqRep` on 3COL (error `Q·δ`), which cannot exist.
- No Lean statement depends on it, so it is not a blocker.

**On the auditor's row verdicts.** Rows 2 and M5 fixed what they targeted: the phrase "`PerfectZKAbort` stated as the perfect form" is gone. The 3COL clause is a separate error that predates them. Round 1's auditor and review both missed it, and it sits in the same sentence. "Not resolved" for rows 2/M5 is defensible only under the pack's "the fix introduces no new one". The work is the same either way.

**Fix** (records only; no ruling).
- **D8: an erratum, not an edit**, following the "as-built erratum; the frozen text above is unchanged" precedent of §2.6. Insert after line 140 (pin) / 141 (head):

  > **Erratum (2026-11-06, gate 03e round 2, finding 1; the frozen text above is unchanged).** Only GI is proved statistically (`gi_statZK`: `StatZK` with negligible δ, truncated simulator, rejection-sampled permutations). 3COL is proved computationally ZK (`col_zk`, by `Commitment.multiHiding`; the truncation and sampling errors are statistical terms inside a computational bound). It cannot be statistical: a perfectly binding commitment makes the real views of two colourings outside one colour-permutation orbit statistically far apart, and the simulator does not see the witness.

- **§5 item 11** (line 1019 pin / 1055 head), replacing the whole item:

  > 11. GI: statistical ZK with negligible δ (`gi_statZK`; truncated simulator, rejection-sampled permutations). 3COL: computational ZK (`col_zk`; `Commitment.multiHiding`, with the statistical errors of the truncated simulator and of the rejection-sampled edges and colour permutations absorbed); not statistical, since with a perfectly binding commitment two inequivalent colourings give statistically distinct views (gate 03e round 2, finding 1). One-iteration ZK; the `n`-fold protocols get soundness only (sequential composition is §7.2.1, out of scope). `PerfectZK` and `PerfectZKAbort` are stated, but no source protocol attains them under D8/D10; `PerfectZKAbort.statZK` turns the abort form into statistical ZK with error `2^{-|x|}` (gate 03e, finding 2; ruling G3-4).

- **Resolutions.** Record the correction in the round 2 resolutions (`resolutions-03e-r2.md`, rows #1 and r1-2/r1-M5). Do not rewrite round 1's rows; at most add "(3COL clause corrected in round 2, finding 1)" to rows 2 and M5.

**Ripple.**
- None in Lean, `Checks.lean`, or packs 03g/03k: `col_zk`'s docstring is already accurate.
- Ch. 5–8: none. Prong C and gate 06's to-do (`gates/06-ch5-8-statements/PLAN.md:55–59`) already treat 3COL as computational.

---

## 2. Major #2: the three new definitions lack their reading lemmas

### Verdict: **true, and understated** (M1). Severity: **major (agree; driven by `ProverBounded`)**.

**Policy.** `policy.md` §1, "Definitions land with their lemmas" (user, 2026-10-16), lines 55–71. Every new public `def` lands in the same PR, beside the definition, with:
- for a predicate, an `_iff` characterization;
- for any other definition, `<name>_eq` (by `rfl` where that holds) or case lemmas covering every input;
- no `@[simp]` without gate approval;
- each docstring stating its formula.

Also, "Consumers never unfold another file's definition."

**Confirmed at the pin.**
- The repair adds exactly three public definitions (grep of section A's added lines): `ProverBounded` (`Interaction.lean:331`), `AbortRetry.attempt` (`Defs.lean:305`) and `AbortRetry.retry` (`Defs.lean:314`).
- None has an `_iff`, an `_eq` or covering case lemmas.
- `ProverBounded.mono/.exists_complete/.pullback`, `attempt_poly`, `retry_poly`, `exists_retrySimulator` and `firstHit_map_getD_eq` do not characterize them, as the auditor says.
- The lint attestation cannot detect this. `style_lint.py` checks presence only, and `campaign_style_lint.py`'s check 8 accepts any lemma whose name contains the definition's name, so `ProverBounded.mono` and `attempt_poly` count as coverage. Gate 03l's review (§3) made the same point.
- No waiver or schedule covers it: I searched `duplication-ledger.md`, `QUEUE.md`, the decision log and the clean-up part 2 draft.

**Missed: consumers already read `ProverBounded` through its body (M1).** These 11 sites in 4 files outside `Interaction.lean` elaborate a `fun` or an application against the `def`, which is a definitional closure that a rule-10 seal would reject:

| File (pack) | Line | How |
|---|---|---|
| `InteractiveProofs.lean` (03e) | 236 | `hB x y r hist hy` (in `ProverBounded.exists_complete`) |
| `InteractiveProofs.lean` (03e) | 468–469 | `fun x y _ _ hxy => hp x y hxy` (`npProtocol_proverBounded`) |
| `NP.lean` (03e) | 278–280 | `intro x y r hist hxy` on the goal, `hB (f x) (w x y) r hist _` |
| `GraphIsomorphism.lean` (03k) | 927, 931, 937, 938 | `fun x y r hist _ => …` |
| `ThreeColoring/Protocol.lean` (03g) | 609 (×2), 616–617 | `fun x y r hist _ => …`, then `show ((colProverRep …).next …).length ≤ …` |
| `ThreeColoring/Protocol.lean` (03g) | 881 | `hB _ _ r hist ⟨n, G, c, rfl, rfl, hc⟩` |

`ProverBounded.mono` (`Interaction.lean:335–337`) is in the same file and may stay as is. Prong C's `ZK.seqRep` fills will read it too, after gate 06 deletes its local copy (`SequentialZK.lean:346`).

**Lemmas to add.** All of them carry no `@[simp]`, and each docstring states its formula.

`Interaction.lean`, inside `namespace Protocol`, directly after the definition (after line 332):

```lean
/-- **Bounded honest messages unfolded:** `π.ProverBounded R B` iff for every `x` and `y` with
`R x y`, every tape `r` and every history `hist`, `|π.P.next x y r hist| ≤ B(|x|)`. -/
theorem proverBounded_iff (π : Protocol) (R : List Bool → List Bool → Prop) (B : PolyExpr) :
    π.ProverBounded R B ↔
      ∀ x y r hist, R x y → (π.P.next x y r hist).length ≤ B.eval x.length :=
  Iff.rfl
```

(The explicit arguments follow the campaign's `hardCore_iff`, `PRG.easy_iff`.)

`Defs.lean`, inside `namespace AbortRetry` (`open EncodingMachines …` is in force), directly after `attempt` (after line 308):

```lean
/-- One attempt unfolded: `attempt S w t` is `S.output` on the layout with parameter
`inParam w`, argument `inArg w`, empty advice and coins
`((inCoins w).drop (t · c)).take c`, where `c = S.coinLen |inParam w|`. -/
theorem attempt_eq (S : NUPPT) (w : List Bool) (t : ℕ) :
    attempt S w t = S.output (NUPPT.layout (NUPPT.inParam w) (NUPPT.inArg w) []
      (((NUPPT.inCoins w).drop (t * S.coinLen (NUPPT.inParam w).length)).take
        (S.coinLen (NUPPT.inParam w).length))) :=
  rfl
```

Directly after `retry` (after line 318):

```lean
/-- The retrying simulator unfolded: with `N = |inParam w|` and `i` the least index below `N`
whose attempt is not `⊥ = []` (`firstIdx`, equal to `N` if there is none), `retry S w` is
attempt `i` if `i < N`, and `[]` otherwise. -/
theorem retry_eq (S : NUPPT) (w : List Bool) :
    retry S w =
      if firstIdx (fun t => decide (attempt S w t ≠ [])) (NUPPT.inParam w).length <
          (NUPPT.inParam w).length then
        attempt S w (firstIdx (fun t => decide (attempt S w t ≠ [])) (NUPPT.inParam w).length)
      else [] :=
  rfl
```

Optional, but they are the semantic form the auditor asked for ("exhaustive retry cases"). Together they cover every input. Uncompiled sketch:

```lean
/-- If attempt `i < |inParam w|` is the first that does not abort, `retry S w` is attempt `i`. -/
theorem retry_eq_attempt {S : NUPPT} {w : List Bool} {i : ℕ}
    (hi : i < (NUPPT.inParam w).length) (hne : attempt S w i ≠ [])
    (hmin : ∀ j < i, attempt S w j = []) : retry S w = attempt S w i := by
  have h : firstIdx (fun t => decide (attempt S w t ≠ [])) (NUPPT.inParam w).length = i :=
    firstIdx_eq_of hi (decide_eq_true hne) fun j hj => decide_eq_false (not_not.2 (hmin j hj))
  rw [retry_eq, h, if_pos hi]

/-- If all `|inParam w|` attempts abort, `retry S w = []`. -/
theorem retry_eq_nil {S : NUPPT} {w : List Bool}
    (h : ∀ t < (NUPPT.inParam w).length, attempt S w t = []) : retry S w = [] := by
  have h' : firstIdx (fun t => decide (attempt S w t ≠ [])) (NUPPT.inParam w).length =
      (NUPPT.inParam w).length :=
    firstIdx_eq_of_forall fun t ht => decide_eq_false (not_not.2 (h t ht))
  rw [retry_eq, h', if_neg (lt_irrefl _)]
```

(`firstIdx_eq_of`, `firstIdx_eq_of_forall`: `EncodingMachines.lean:255, 263`.) The in-file reads `simp only [attempt, …]` (:569) and `simp only [retry, …]` (:370, :581) are allowed, since they are in the same file. They may switch to these lemmas.

**Not recommended: making `attempt`/`retry` private.** It would remove the obligation, but `attempt_poly`, `retry_poly` and `exists_retrySimulator` mention them, the module docstring lists them as main definitions, and `Checks.lean:441` prints `exists_retrySimulator`. That is an interface change for no gain over two `rfl` lemmas.

**Re-pointing** (the maintainer's job; no ruling):
- `InteractiveProofs.lean:236` → `(π.proverBounded_iff R B).1 hB x y r hist hy`.
- `:468–469` → `((npProtocol T p).proverBounded_iff R p).2 fun x y _ _ hxy => hp x y hxy`. `npProtocol` is the same file's definition.
- `NP.lean:278` → `rw [Protocol.proverBounded_iff] at hB ⊢` before the `intro`.
- `GraphIsomorphism.lean:927, 931, 937–938` and `ThreeColoring/Protocol.lean:609, 616` → `(Protocol.proverBounded_iff _ _ _).2 fun …`. The `show` at :617 becomes unnecessary.
- `ThreeColoring/Protocol.lean:881` → `(Protocol.proverBounded_iff _ _ _).1 hB _ _ r hist ⟨…⟩`.
- Then run the rule-10 seal on the four files with `attribute [local irreducible] TCSlib.Cryptography.Protocol.ProverBounded`, with a control on the base text that must fail. This is the clean-up part 1 / gate 04 round 4 procedure.

**Evidence to add.** In `audits/pass-shelat/Checks.lean`, beside :425–427 and :440–441, add `#print axioms` for `Protocol.proverBounded_iff`, `AbortRetry.attempt_eq`, `AbortRetry.retry_eq` (and `retry_eq_attempt`, `retry_eq_nil` if added). Replay the modules downstream of the four touched files; the `sorry` counts must equal the base's.

**Ripple.**
- 03e: `Interaction.lean`, `Defs.lean`, `InteractiveProofs.lean`, `NP.lean`.
- 03k: `GraphIsomorphism.lean`. 03g: `ThreeColoring/Protocol.lean`. These are proof-only re-points; their statements are unchanged.
- `Checks.lean`.
- Prong C: add to gate 06's to-do (`PLAN.md:55–59`): "read `ProverBounded` through `Protocol.proverBounded_iff`".

---

## 3. Minors

| # | Verdict | Severity | Concrete fix | Ripple |
|---|---|---|---|---|
| 3 | **Partly true.** Two parts hold. (i) Row 5 says "**Fixed (records)**", then keeps the stale drafting sentence "The drafter found them missing: … still names `TuringMachine/Build/*` …". M8 says "#5 (c)'s record correction, which is not done". (ii) The counts: `evidence/e/replay.log` (round 1, 358 modules) has 25 warnings, 22 of them outside the ZK files (21 `main`'s including RecordTable's 4, plus 1 `NonUniform`). `evidence/e2/replay.log` (126 modules) has 21, 18 of them outside the ZK files (17 + 1). But the records the auditor calls "absent" **exist at the pin**, all committed in `dd492eac`: the erratum at `audits/pass-shelat/run3-audit-summary.md:17`, `SPINE-DESIGN.md:42–55` ("Two limits of the interaction model D8"), and `inventory-ch5-8.md:130` (the Thm-175.1 row). So #5(c) is done; only the resolution text is wrong. | minor (agree) | In `resolutions-03e-r1.md` row 5, delete from "The drafter found them missing" to the end of the cell, and add "(committed in `dd492eac`; the 22 are round 1's 358-module closure)". In row M8, replace "except #5 (c)'s record correction, which is not done (see #5)" with "#5 (c)'s record correction is done (`run3-audit-summary.md:17`, `dd492eac`)". In `resolutions-03e-r2.md`, state the current figures: 21 `sorry` warnings in the 126-module closure; 18 outside the ZK files (17 `main`'s, 1 `NonUniform`); 3 in 3-colouring. | records only |
| 4 | **True.** `zk_proof_of_witnessRelation` (`NP.lean:679–689`) and `_of_owp` (:698–709) return `f, w, p` with only `∀ N, N ≤ p.eval N` and the protocol facts. Their docstrings (:670–677, :691–696) say "there is a Levin reduction `(f, w)` … with length polynomial `p ≥ id`". The proof has `h : LevinReduction …` in hand (:688) and drops it. The statements are true and provable as stated, just weaker than described. The supplied-reduction forms (:584, :634) are fine. | minor (agree) | **Ruling R-03e-r2-1 (§5); recommended (A).** At :683 insert `LevinReduction L L3COL R R3COL f w p ∧` before `(∀ N, N ≤ p.eval N) ∧`. The proof at :689 becomes `exact ⟨f, w, p, h, h.le_eval, zk_proof_of_levinReduction hC h fun x hx => (hR.mem_iff x).1 hx⟩`. Insert the same conjunct at :703 (`_of_owp`; its proof at :709 is unchanged). Adjust `zk_proof_of_mem_NP`'s pattern at :737 to `obtain ⟨_, _, p, -, hp, h1, h2, h3'⟩ := …`. `zk_proof_of_mem_NP_of_owp` (:751) is unchanged. | 03e only (no consumer outside `NP.lean`; ch. 5–8 does not cite Thm 124.1). 03g's Thm-124.1 inventory row notes the stronger form. Prints keep their names and still reach `sorryAx` (`col_zk`, `colRep_efficientProverProof`). |
| 5 | **True, and understated** (M3). `giProtocolRep` (`GraphIsomorphism.lean:556–560`, `rounds = 4·var`, prover first) and `colProtocolRep` (`ThreeColoring/Protocol.lean:500–504`, `4·var·var`) make the verifier the last mover. Their verifiers return the verdict on the complete history (`GraphIsomorphism.lean:546–551`, `ThreeColoring/Protocol.lean:493–496`). So the last "fourth move" is the verdict (`outV_eq_getLast_of_moverIsV`), and it is nonempty on accepting runs. The sentence also contradicts the verdict-convention sentence just above it (`Interaction.lean:35–37`: "the `n`-fold protocols read the verifier's last message as the verdict"). **Missed:** prong C does **not** follow "one dummy verifier message per iteration". `SequentialZK.lean:21–33` pads each phase with `k = rounds(|x|)` filler moves of both parties, the last filler carrying the verdict. | minor (agree) | Replace `Interaction.lean:39–43` with: "Repetition convention (gate 03e, note 8): an iteration with an odd number of messages (prover, verifier, prover) is repeated under strict alternation by giving each iteration one additional verifier move, so that every iteration starts with the prover. In `giProtocolRep` and `colProtocolRep` that move is the empty message, except for the protocol's final move, which carries the verifier's verdict (the verdict convention above). The sequential repetition of [PS10, §7.2.1] in ch. 7 pads each phase instead with `rounds(\|x\|)` filler moves of both parties, its last filler again carrying the verdict." Same qualifier at `GraphIsomorphism.lean:554–555` (03k: "and an empty verifier message" → "and a verifier message, empty except for the final verdict") and at `ThreeColoring/Protocol.lean:497–498` (03g). | 03e docstring; 03k and 03g docstrings; prong C none (its own text is accurate) |
| 6 | **True.** `Defs.lean:42–48` and DESIGN §7 item 51 (pin :1254–1259) claim that the literal reading fails "for every protocol whose hiding is only computational". The auditor's fixed-value commitment protocol refutes the universal claim: its view is simulable exactly, for any `z`. For 3COL the claim holds, but only through the witness-separation argument of #1. Opening commitments alone is not a distinguisher; separating two witnesses is. That argument covers the source's own Prop 128.8, so a narrowed item 51 is still a genuine §7 source gap. | minor (agree) | Replace `Defs.lean:42–48` with: "The bound `Lz` is necessary for the 3-colouring protocol, not only convenient (gate 03e, note 9; round 2, finding 6). The distinguisher runs in time polynomial in its input, the encoded view, which contains `z`. With `\|z\|` exponential in `ℓ(n)` it can open the perfectly binding commitments by exhaustive search. On a graph with two proper colourings outside one colour-permutation orbit, that tells the two real views apart with advantage 1, while the simulator does not see the witness. Read literally, [PS10, Definition 121.2] (every `z ∈ {0,1}*`, with `D` polynomial-time in its input) has the same defect for that protocol. Protocols with exactly simulable views are not affected. For the same reason the distinguisher's advice is indexed by the parameter `\|x\|`, not by its input length." DESIGN §7 item 51 (pin :1254 / head :1292): replace "fails for every protocol whose hiding is only computational: … open the unopened commitments" with "fails for the 3-colouring protocol 127.5 of Proposition 128.8: with `\|z\|` exponential, the distinguisher, whose input (the view) contains `z`, opens the perfectly binding commitments by exhaustive search, and on a graph with two proper colourings outside one colour-permutation orbit it separates the two real views, which the witness-blind simulator cannot match". Keep the last sentence, adding "round 2, finding 6". | 03e docstring; DESIGN |
| 7 | **True, slightly understated** (M4). (a) With `s = 1`, the zero-message protocol whose verifier always outputs `[true]` and whose prover sends `[]` satisfies `InteractiveProofErr π L (fun _ => 1)` and `EfficientProverProofErr π L R (fun _ => 1)` for every `L` and `R`. I checked each field: the bound is 0, soundness is `0 ≤ uprob`, both parties are `NUPPT.ofPolyTimeUniform` of constants. So `InteractiveProofs.lean:46–47` ("So the proof systems hold only for languages of the text's class IP") is false for the explicit-error forms. The capping argument is sound for `InteractiveProof`. (b) Source p. 117: "the prover in the definition of an interactive proof need not be efficient". Only Def 119.5 (p. 119) has "P is p.p.t.". The same attribution appears in `InteractiveProofs.lean:113–114` (the auditor's :114), in the module text :35–38 ("The parties' efficiency (the text's "p.p.t.")"), and in DESIGN §5 item 8 (pin :1012–1013). `EfficientProverProof`'s docstring (:335–339) is correct. | minor (agree) | `InteractiveProofs.lean:35–36`: "The parties' efficiency (the text's "p.p.t.")" → "The verifier's efficiency (Definition 116.1's "p.p.t.", and the prover's for Definition 119.5)". `:46–48`: "So the proof systems hold only for …" → "So `InteractiveProof` (and `InteractiveProofErr` with negligible error, by `InteractiveProofErr.interactiveProof`) holds only for …"; then add after "… excluded —": "the explicit-error forms with a large error say little (with `s = 1` the zero-message, always-accepting protocol is an `EfficientProverProofErr` for every language and relation) —". `:113–114`: "(the text's p.p.t. prover writes at most `t(\|x\|)` bits; the convention of ch. 6)" → "(Definition 116.1's prover need not be efficient; bounding its messages is the chosen normal form, harmless because a verifier of time `t(\|x\|)` reads at most `t(\|x\|)` bits of each message; the convention of ch. 6)". DESIGN §5 item 8: ": the source's p.p.t. prover writes at most `t(\|x\|)` bits" → ": for Definition 119.5 the source's p.p.t. prover writes at most `t(\|x\|)` bits; for Definition 116.1, whose prover is unbounded, it is a normal form (the verifier reads at most `t(\|x\|)` bits of each message)". | 03e docstrings; DESIGN |

### The round 1 rows (auditor's verdicts)

I agree with every row verdict except these:
- **Row 5 and M8:** *fixed* (the records are at the pin), with stale resolution text (#3 above). The auditor said *not resolved*.
- **Row 15:** *fixed*. `SPINE-DESIGN.md:42–55` at the pin holds exactly the two limits. The auditor said *recorded* because the file was not in the bundle.
- **Rows 2 and M5:** their own defect is fixed. #1 is a pre-existing error in the same item, which I accept as the reason for *not resolved* (§1).

Rows 1, 3, 8 and 9 are rightly *not resolved*: the repair introduced #2/#7, #4, #5 and #6 respectively.

---

## 4. Missed by the auditor

- **M1. `ProverBounded` is already read through its body** at 11 sites in 4 files (table in §2). This is the policy breach that `proverBounded_iff` must repair, and it is what makes #2 a major under gate 04's F02 precedent. It needs a seal, not only the lemma.
- **M2. Tactic-level unfolds in the repair's new proofs** (`Defs.lean`). These are out of the auditor's scope (tactic proofs) but against `policy.md` §1. All four are minor; recommended for clean-up part 2, not for closure.
  - `:409`, `firstHit_map_getD_eq`: `unfold firstHit`. `firstHit` is defined in `Asymptotic/Sampling.lean:451` (pack 03a, written 2026-10-28, after the rule) and has no `_eq` lemma. Add `firstHit_eq : firstHit E xs = (List.finRange T).findSome? fun t => if E (xs t) then some (xs t) else none := rfl` beside it, and rewrite with it.
  - `:543`, `PerfectZKAbort.statZK`: `simp only [NUPPT.coinLen, …]`. Use item C's `NUPPT.coinLen_eq`.
  - `:291`, `perfectZK_zeroRounds`: `simp [NUPPT.inArg, NUPPT.inCoins, NUPPT.advInput]`. Use item C's `advInput_eq` with `inArg_layout`/`inCoins_layout`.
  - `:563`: `simp [finProdFinEquiv]`, a Mathlib definition passed to `simp`. Use its `simps` lemmas instead (`finProdFinEquiv_apply_val`, `finProdFinEquiv_symm_apply`).

  The older `InteractiveProofs.lean:449, :462` (`simp [… NUPPT.advInput …]`) belong in the same item C list. A rule-10 seal does not catch `unfold`/`simp [def]`, so these need the syntactic scan of clean-up part 1 (`users.py`).
- **M3. #5 is broader.** The new sentence contradicts the verdict convention two lines above it, and its claim about ch. 7's fillers is false: prong C pads `k` moves of both parties per phase.
- **M4. #7 is broader.** The Def 116.1 / Def 119.5 misattribution is also in the module text (`InteractiveProofs.lean:35–38`), not only at :114.
- **M5. #3 is narrower.** The run-3 erratum, the SPINE-DESIGN limits and the inventory row are all at the pin. The bundle simply omitted them.

---

## 5. Rulings for the user (multiple choice; recommended option first)

**R-03e-r2-1. The witness-relation forms of Thm 124.1 drop their Levin reduction (#4).** `zk_proof_of_witnessRelation` and `_of_owp` say "there is a Levin reduction `(f, w)`", but they return only the maps and `p ≥ id`.
1. **Export the certificate (recommended).** Add `LevinReduction L L3COL R R3COL f w p ∧` to both conclusions (§3, #4).
   - *Cost:* two statement lines, one proof term, one destructuring pattern in `zk_proof_of_mem_NP`. No consumer outside `NP.lean`; the print names are unchanged.
   - *Benefit:* a consumer can pull further protocols back along the same maps and use `length_eq` and `witness`.
2. **Narrow the two docstrings** to "there are maps `f, w` and a polynomial `p ≥ id` (from the Levin reduction supplied by `h3`, not recorded)".
   - *Cost:* docstrings only. The returned maps cannot be reused as a reduction.

**R-03e-r2-2 (conditional: only if #2's lemmas are not landed before closure).**
1. **Land `proverBounded_iff`, `attempt_eq` and `retry_eq` and the 11 re-points in the 03e closing repair (recommended; then no ruling is needed).**
   - *Cost:* about 30 lines, a seal of four files, prints, a downstream replay.
2. **Close 03e with them scheduled in clean-up part 2** (as a new item beside C and J).
   - *Cost:* accepts a policy-§1 debt on a ch. 5–8 interface until part 2 lands, after gate 04 and #195. Gate 06's prong C re-sync must then wait for part 2, or read the definition through its body.

---

## 6. Ripple map

| Change | ch. 2–4 files (pack) | ch. 5–8 | `Checks.lean` |
|---|---|---|---|
| #1 | DESIGN D8 erratum, §5 item 11; `resolutions-03e-r2.md` | none | none |
| #2 | `Interaction.lean`, `Defs.lean`, `InteractiveProofs.lean`, `NP.lean` (03e); `GraphIsomorphism.lean` (03k); `ThreeColoring/Protocol.lean` (03g), proof-only | prong C reads via `proverBounded_iff` at gate 06 (`PLAN.md:55–59` to-do line) | prints for 3–5 new lemmas |
| #3 | `resolutions-03e-r1.md` rows 5, M8; `resolutions-03e-r2.md` | none | none |
| #4 | `NP.lean:679–709, 737` (03e); 03g's Thm-124.1 inventory note | none | names unchanged |
| #5 | `Interaction.lean:39–43` (03e); `GraphIsomorphism.lean:554–555` (03k); `ThreeColoring/Protocol.lean:497–498` (03g) | none | none |
| #6 | `Defs.lean:42–48`; DESIGN §7 item 51 | none | none |
| #7 | `InteractiveProofs.lean:35–48, 113–118`; DESIGN §5 item 8 | none | none |
| M2 | `Defs.lean:291, 409, 543, 563`; `InteractiveProofs.lean:449, 462`; `Sampling.lean` (03a, `firstHit_eq`) | none | print for `firstHit_eq` |

Pending packs: only 03g and 03k get changes (proof re-points and docstrings), and none of their statements change. 03a gets `firstHit_eq` only if M2 is taken up (part 2).

---

## 7. Proposed closing condition for gate 03e

The gate closes, without an external round 3, when a maintainer delta check at the closing repair's head confirms all of the following:

1. **#2:**
   - `Protocol.proverBounded_iff`, `AbortRetry.attempt_eq` and `AbortRetry.retry_eq` are present beside their definitions, unattributed, with formula docstrings (optionally also `retry_eq_attempt`, `retry_eq_nil`).
   - The 11 sites of M1 are re-pointed.
   - A rule-10 seal of `InteractiveProofs.lean`, `NP.lean`, `GraphIsomorphism.lean` and `ThreeColoring/Protocol.lean` on `Protocol.ProverBounded` passes, with failing controls.
   - The new lemmas print standard axioms in `Checks.lean`.
   - The downstream replay passes with `sorry` counts equal to the base's.
2. **#1:** the D8 erratum and the rewritten §5 item 11 are in DESIGN.
3. **#4:** done per R-03e-r2-1. Under option 1, the two statements carry `LevinReduction …`, and their prints still reach exactly `col_zk` and `colRep_efficientProverProof`.
4. **#5, #6, #7:** the docstring and DESIGN texts of §3 are in (including the 03k/03g qualifiers for #5).
5. **#3:** `resolutions-03e-r1.md` rows 5 and M8 are corrected, and `resolutions-03e-r2.md` records every round 2 finding with the current counts (21/18).
6. **M2:** listed in clean-up part 2 (item C's re-point list extended; a `firstHit_eq` item added). It is not a closing condition.

The result is 0 blockers and 0 majors, and the prong C re-syncs stay on gate 06's integration to-do. An external round 3 is needed only if the user wants the #4 statement change audited independently.

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/resolutions-03e-r2.md =====

# Gate 03e (interaction, proof systems, ZK definitions, commitments, NP layer): round 2 resolutions

- **Round:** findings `findings/gate03e-r2-findings.md`, SHA-256 `e32240876e5117c1f080bfaa798706f94bf4e0df613faa300b951e3735d4e20f`; pin `e79397ea`. **0 blockers, 2 majors, 5 minors.** Review `review/gate03e-r2-review.md`: 6 true, 1 partly true (#3); severities kept. Ruling R-03e-r2-1 (A).
- **Repair:** the gate 03 repair batch, PR [#206](https://github.com/Shilun-Allan-Li/tcslib/pull/206) (head `73751f5747d8c0a57aba9939cac8bb16f87ba2ba`, merged by `1ea782b11617e15a51c3e2f6bd15dd0e3befbd95`; evidence `evidence-repairs/03-batch/`), plus the records commits of 2026-11-06.

| Finding | Severity | Resolution |
|---|---|---|
| #1 | major | **Fixed (records).** DESIGN D8 carries a dated erratum (only GI is statistical; 3COL is computational and cannot be statistical); §5 item 11 is rewritten. No Lean change. |
| #2 | major | **Fixed** (#206, item C). `Protocol.proverBounded_iff` (`Interaction.lean`), `AbortRetry.attempt_eq`, `retry_eq`, `retry_eq_attempt`, `retry_eq_nil` (`Defs.lean`), none `@[simp]`. The 11 sites of the review's M1 table, and 2 more in `GraphIsomorphism/Soundness.lean` and `SoundnessRepGI.lean`, go through `proverBounded_iff`. The seal of the six consumer files on `ProverBounded` passes, and their base versions fail. Prints are in `Checks.lean`. |
| #3 | minor (partly true) | **Fixed (records).** `resolutions-03e-r1.md` rows 5 and M8 corrected. Current counts: 21 `sorry` warnings in the 126-module closure, 18 outside the ZK files (17 `main`'s, 1 `NonUniform`'s). |
| #4 | minor | **Fixed** (ruling R-03e-r2-1 (A), a strengthening). `zk_proof_of_witnessRelation` and `_of_owp` return `LevinReduction L L3COL R R3COL f w p ∧ …`; `zk_proof_of_mem_NP`'s pattern adjusted; docstrings match. |
| #5 | minor | **Fixed.** The repetition convention in `Interaction.lean`'s module docstring is rewritten (the final verifier move carries the verdict; ch. 7 pads each phase with `rounds(|x|)` filler moves). The qualifier is in `GraphIsomorphism.lean` (also its module docstring) and `ThreeColoring/Protocol.lean`. |
| #6 | minor | **Fixed.** `Defs.lean`'s `Lz` necessity paragraph and DESIGN §7 item 51 are narrowed to the 3-colouring protocol (protocols with exactly simulable views are not affected). |
| #7 | minor | **Fixed.** `InteractiveProofs.lean`: the efficiency attribution (Def 116.1's verifier, Def 119.5's prover); the IP scope sentence covers `InteractiveProof`, with the `s = 1` remark on the explicit-error forms; `complete`'s docstring; DESIGN §5 item 8. |
| M1–M5 | (review) | M1, M3, M4, M5: **fixed** with #2, #5, #7 and #3. M2 (tactic-level unfolds in the repair's new proofs): **scheduled** for clean-up part 2 (item C's equation lemmas and `firstHit_eq`). |

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/evidence-repairs/03-batch/repair.diff.txt =====

diff --git a/TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean b/TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean
index 66f802b8..c51a6ff4 100644
--- a/TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean
+++ b/TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean
@@ -38,6 +38,11 @@ inside one finite machine.
   the host: from the host seam at the module's entry state, with any output prefix, the host
   reaches the seam at the module's return state with the module's result word, forwarding exactly
   the module's output, and visits no control state meanwhile; `guard_add` chains such segments.
+* **Head envelopes.** A clean module's heads stay within its budget `B |arg|` of the origin at
+  every time (`Clean.envelope`), and the host's heads stay within `t` cells of the origin up to
+  time `t` of a call (`host_call_envelope`), hence within `B |arg|` during a clean call
+  (`host_clean_envelope`). These are the coarse envelopes from the time bounds and the unit head
+  moves of `Turing.MultiTapeTM.workTapePos_step_le` (gate 03l round 2, finding 1).
 
 ## Origin
 
@@ -62,6 +67,8 @@ machines, the control states and their table, the return map and the start state
   clean install and a clean emit module with a polynomial budget on the argument length.
 * `Turing.ModuleHost.host_call`, `host_clean` — one module call inside the host, with the guard
   that no control state is visited; `guard_add` — chaining guarded segments.
+* `Turing.ModuleHost.Clean.envelope`, `host_call_envelope`, `host_clean_envelope` — the head
+  envelopes of a clean module and of a host call.
 * `Turing.ModuleHost.first_halt`, `live_prefix` — cutting a halting run at its first halt, and
   liveness of the prefix of a live run.
 * `Turing.ModuleHost.request_budget` — a polynomial budget on a bounded request fits a common
@@ -213,6 +220,44 @@ theorem clean_iff (M : FinTM Bool) (result emit : List Bool → List Bool) (B :
           state := none, output := emit arg} :=
   Iff.rfl
 
+/-- **The head envelope of a clean module** (H14's space clause): if `Clean M result emit B`,
+then for every native input `x` and argument `arg`, at every time `v` of the run of `M` from the
+seam at its start state holding `arg` (before, at and after its first halt), every work head is
+within `B |arg|` cells of the origin, where all heads start (`Cfg.ofWords_workTapePos`).
+
+This is the coarse envelope from the time bound: one step moves each head by at most one cell
+(`Turing.MultiTapeTM.workTapePos_step_le`; over a run,
+`Turing.MultiTapeTM.workTapePos_runFrom_mem_Icc`), the first halt comes at a time `t ≤ B |arg|`,
+and the run is constant from `t` on. The contract gives nothing sharper: it fixes the terminal
+seam, not the intermediate head positions, and a clean module may move a head out and back
+before it halts at the seam (gate 03l round 2, finding 1).
+
+**Proof sketch.** Take the first halt `t ≤ B |arg|` of `Clean`. At a time `v ≤ t` each head is
+within `v` cells of its start (`MultiTapeTM.workTapePos_runFrom_mem_Icc`); at `v > t` the run
+is halted, so its configuration is the one at `t` (`MultiTapeTM.runFrom_add`,
+`MultiTapeTM.runFrom_of_halt`). -/
+theorem Clean.envelope {M : FinTM Bool} {result emit : List Bool → List Bool} {B : ℕ → ℕ}
+    (h : Clean M result emit B) (x arg : List Bool) (v : ℕ) (j : Fin M.k) :
+    |(M.tm.runFrom (Cfg.ofWords (input := x) M.tm.q₀ (stateWord M.k arg)) v).workTapePos j| ≤
+      (B arg.length : ℤ) := by
+  obtain ⟨t, -, htB, -, hend⟩ := ((clean_iff M result emit B).1 h).2 x arg
+  have hhalt : (M.tm.runFrom (Cfg.ofWords (input := x) M.tm.q₀ (stateWord M.k arg)) t).state =
+      none := by
+    rw [hend]
+  obtain ⟨u, hut, hu⟩ : ∃ u ≤ t,
+      M.tm.runFrom (Cfg.ofWords (input := x) M.tm.q₀ (stateWord M.k arg)) v =
+        M.tm.runFrom (Cfg.ofWords (input := x) M.tm.q₀ (stateWord M.k arg)) u := by
+    rcases le_total v t with hvt | htv
+    · exact ⟨v, hvt, rfl⟩
+    · refine ⟨t, le_rfl, ?_⟩
+      rw [← Nat.add_sub_of_le htv, MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_of_halt _ hhalt]
+  obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 (M.tm.workTapePos_runFrom_mem_Icc
+    (Cfg.ofWords (input := x) M.tm.q₀ (stateWord M.k arg)) u j)
+  rw [Cfg.ofWords_workTapePos] at h1 h2
+  have hB : (u : ℤ) ≤ B arg.length := by exact_mod_cast hut.trans htB
+  rw [hu, abs_le]
+  constructor <;> omega
+
 /-- Turn a clean-call bridge contract into the uniform first-halting form.
 
 **Proof sketch.** The release wrapper stops one step after the positive exit (`stop_clean`);
@@ -503,6 +548,42 @@ theorem host_call {C : Type} [Fintype C] [DecidableEq C] {n : ℕ} (M : Fin n 
   · rw [hrun t (Nat.le_refl _), show (M i).tm.runFrom c t = _ from he]
     exact host_seam M K ret i hp x result pre out q none
 
+/-- **The head envelope of a host call** (H14's space clause for one call, inclusive of its
+endpoint): run from its seam at the entry state of module `i` holding `arg` with output prefix
+`pre`, the host has, at every time `v ≤ t`, every work head within `t` cells of the origin,
+where all heads start (`Cfg.ofWords_workTapePos`). Under the hypotheses of `host_call`, `t` is
+the duration of the call, so this bounds the heads throughout the call.
+
+This is the coarse envelope from the time bound: one step moves each head by at most one cell
+(`Turing.MultiTapeTM.workTapePos_step_le`; over a run,
+`Turing.MultiTapeTM.workTapePos_runFrom_mem_Icc`). A sharper envelope follows from the proof of
+`host_call` and is not stated here: before the return, the host's tape `j` is module `i`'s
+tape `j` for `j < (M i).k` (the padded module runs in lockstep and the forwarding keeps every
+physical field, `Turing.emit_run`), and every other tape stays blank with its head at the
+origin, so the host's heads obey any head envelope of the module.
+
+**Proof sketch.** `MultiTapeTM.workTapePos_runFrom_mem_Icc` from the host seam, whose heads are
+at the origin, and `v ≤ t`. -/
+theorem host_call_envelope {C : Type} [Fintype C] [DecidableEq C] {n : ℕ}
+    (M : Fin n → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K)
+    (ctrl : C → Option Bool → (Fin K → Option Bool) → Action K Bool (State C M))
+    (ret : Fin n → State C M) (q₀ : State C M) (i : Fin n) (x arg pre : List Bool) (t : ℕ) :
+    ∀ v ≤ t, ∀ j : Fin K, |((hostTM M K hk ctrl ret q₀).tm.runFrom
+      {Cfg.ofWords (input := x) (entry M i) (stateWord K arg) with output := pre} v).workTapePos
+        j| ≤ (t : ℤ) := by
+  intro v hv j
+  have key : ∀ c : Cfg K Bool (State C M) x, c.workTapePos j = 0 →
+      |((hostTM M K hk ctrl ret q₀).tm.runFrom c v).workTapePos j| ≤ (t : ℤ) := by
+    intro c hc
+    obtain ⟨h1, h2⟩ :=
+      Finset.mem_Icc.1 ((hostTM M K hk ctrl ret q₀).tm.workTapePos_runFrom_mem_Icc c v j)
+    rw [hc] at h1 h2
+    have hvt : (v : ℤ) ≤ t := by exact_mod_cast hv
+    rw [abs_le]
+    constructor <;> omega
+  exact key {Cfg.ofWords (input := x) (entry M i) (stateWord K arg) with output := pre}
+    (Cfg.ofWords_workTapePos (input := x) (entry (C := C) M i) (stateWord K arg) j)
+
 /-- **Chaining guarded segments.** If the run from `c` avoids the state `anchor` before time `a`
 and is at `d` at time `a`, and the run from `d` avoids `anchor` before time `b`, then the run
 from `c` avoids `anchor` before time `a + b`. -/
@@ -545,4 +626,38 @@ theorem host_clean {C : Type} [Fintype C] [DecidableEq C] {n : ℕ} (M : Fin n 
     host_call M K hk ctrl ret q₀ i h.1 x arg (f arg) (g arg) pre (M i).tm.q₀ t hg he
   exact ⟨t, hp, ht, hguard, hend⟩
 
+/-- **A clean module call inside the host, with its head envelope** (the bounded call of
+`host_clean` together with H14's space clause): if module `i` is `Clean` with result map `f`,
+emitted chunk `g` and budget `B`, then for every native input `x`, argument `arg` and output
+prefix `pre`, the host, run from its seam at the entry state of module `i` holding `arg` with
+output `pre`, reaches at some time `t` with `0 < t ≤ B |arg|` the seam in the return state
+`ret i` holding `f arg`, with output `pre ++ g arg`, visits no control state before `t`, and at
+every time `v ≤ t` has every work head within `B |arg|` cells of the origin.
+
+The envelope is the coarse one from the time bound (`host_call_envelope`, which also describes
+the sharper envelope inherited from the module).
+
+**Proof sketch.** `host_clean` gives `t` and the call; `host_call_envelope` at `t`, with
+`t ≤ B |arg|`, gives the envelope. -/
+theorem host_clean_envelope {C : Type} [Fintype C] [DecidableEq C] {n : ℕ}
+    (M : Fin n → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K)
+    (ctrl : C → Option Bool → (Fin K → Option Bool) → Action K Bool (State C M))
+    (ret : Fin n → State C M) (q₀ : State C M)
+    (i : Fin n) (f g : List Bool → List Bool) (B : ℕ → ℕ)
+    (h : Clean (M i) f g B) (x arg pre : List Bool) :
+    ∃ t, 0 < t ∧ t ≤ B arg.length ∧
+      (∀ v < t, ∀ c : C, ((hostTM M K hk ctrl ret q₀).tm.runFrom
+        {Cfg.ofWords (input := x) (entry M i) (stateWord K arg) with output := pre} v).state
+          ≠ some (.inl c)) ∧
+      (hostTM M K hk ctrl ret q₀).tm.runFrom
+        {Cfg.ofWords (input := x) (entry M i) (stateWord K arg) with output := pre} t =
+        {Cfg.ofWords (ret i) (stateWord K (f arg)) with output := pre ++ g arg} ∧
+      ∀ v ≤ t, ∀ j : Fin K, |((hostTM M K hk ctrl ret q₀).tm.runFrom
+        {Cfg.ofWords (input := x) (entry M i) (stateWord K arg) with output := pre}
+          v).workTapePos j| ≤ (B arg.length : ℤ) := by
+  obtain ⟨t, hp, ht, hguard, hend⟩ := host_clean M K hk ctrl ret q₀ i f g B h x arg pre
+  refine ⟨t, hp, ht, hguard, hend, fun v hv j => ?_⟩
+  have hB : (t : ℤ) ≤ B arg.length := by exact_mod_cast ht
+  exact (host_call_envelope M K hk ctrl ret q₀ i x arg pre t v hv j).trans hB
+
 end Turing.ModuleHost
diff --git a/TCSlib/Cryptography/Asymptotic/OneWay.lean b/TCSlib/Cryptography/Asymptotic/OneWay.lean
index b2445e44..7ac5de06 100644
--- a/TCSlib/Cryptography/Asymptotic/OneWay.lean
+++ b/TCSlib/Cryptography/Asymptotic/OneWay.lean
@@ -281,8 +281,9 @@ theorem WorstCaseOneWay.toLit {𝓕 : FunFamily} (h : 𝓕.WorstCaseOneWay) : 
   simp only [NUPPT.inverter, NUPPT.inverterLit, NUPPT.runAt_eq, hB, hofn]
 
 /-- **The literal form implies the `1^n` form when the output length determines the
-parameter** (injective `outLen`, the case of every family of the text; repair of the run-3
-audit, P3-2; the analogue of `Ensemble.IndistLit.toIndist`): a `1^n`-inverter `B` is the literal
+parameter** (injective `outLen`, equivalently non-constant output length for these polynomial
+lengths; repair of the run-3 audit, P3-2; the analogue of `Ensemble.IndistLit.toIndist`): a
+`1^n`-inverter `B` is the literal
 inverter `NUPPT.exists_reparam_advice B φ var` with `φ (outLen n) = n`, which hard-wires `1^n`
 and `B.advice n` at the output length and leaves its extra coins unread.
 
diff --git a/TCSlib/Cryptography/Candidates/Concrete.lean b/TCSlib/Cryptography/Candidates/Concrete.lean
index 59dac7c5..938af1fa 100644
--- a/TCSlib/Cryptography/Candidates/Concrete.lean
+++ b/TCSlib/Cryptography/Candidates/Concrete.lean
@@ -519,6 +519,15 @@ def rejectBlocksL (E : ℕ → Prop) [DecidablePred E] (k B T : ℕ) (r : List B
     if E (listToNat ((r.drop (t * B)).take k)) then some (listToNat ((r.drop (t * B)).take k))
     else none
 
+/-- Block rejection sampling unfolded: `rejectBlocksL E k B T r` is the first `some v` over
+`t ∈ [0, T)` (`List.findSome?` over `List.range T`) with `v` the number read from the first `k`
+bits of the `t`-th block of `B` bits of `r`, kept iff `E v`. -/
+theorem rejectBlocksL_eq (E : ℕ → Prop) [DecidablePred E] (k B T : ℕ) (r : List Bool) :
+    rejectBlocksL E k B T r = (List.range T).findSome? fun t =>
+      if E (listToNat ((r.drop (t * B)).take k)) then some (listToNat ((r.drop (t * B)).take k))
+      else none :=
+  rfl
+
 /-- An accepted value satisfies the test and is below `2^k` (it is read from at most `k`
 bits, `listToNat_lt_two_pow`). -/
 theorem rejectBlocksL_spec {E : ℕ → Prop} [DecidablePred E] {k B T : ℕ} {r : List Bool} {v : ℕ}
diff --git a/TCSlib/Cryptography/Candidates/DiscreteLog.lean b/TCSlib/Cryptography/Candidates/DiscreteLog.lean
index 767d14fe..b7fbd309 100644
--- a/TCSlib/Cryptography/Candidates/DiscreteLog.lean
+++ b/TCSlib/Cryptography/Candidates/DiscreteLog.lean
@@ -49,7 +49,8 @@ collection `expCollection H G hV` therefore takes the validity bridge `hV : ∀
 as an argument.
 
 **Full-length primes.** Where a proof divides by `q` or `p − 1` (Lemma 84.1's range reduction,
-the `1/q` term of Theorem 107.3) the prime must have full length `2^{n−1} ≤ p`. This is
+the `1/q` term of Theorem 107.3) the proofs use full length `2^{n−1} ≤ p` (a convenience: the
+hypothesis is dispensable in both headline theorems, gate 03f1 review, M1). This is
 demanded only *except on a negligible set of coins* (`ExpGroupGen.FullLengthExcept δ` with
 `Negligible δ`): a strict-PPT generator may fall back to a fixed instance when its rejection
 loop fails (D10), and demanding full length on every coin string (`ExpGroupGen.FullLength`)
@@ -316,9 +317,11 @@ def FullLength : Prop :=
 
 /-- The generator outputs primes of full length `n` **except on a set of coins of probability
 at most `δ n`**: for `n ≥ n₀`, `Pr_r[p < 2^{n−1}] ≤ δ n` (the fallback instance of a strict-PPT
-rejection sampler, D10). Needed, with `Negligible δ`, where the proofs divide by `q` or
+rejection sampler, D10). Used, with `Negligible δ`, by the proofs that divide by `q` or
 `p − 1` (Lemma 84.1's range reduction, the `1/q` term of Theorem 107.3): the short-prime coins
-are discarded and contribute at most `δ n`. Whether safe primes (resp. primes `≡ 3 (mod 4)`
+are discarded and contribute at most `δ n`. This is a convenience: instances with `p − 1` below
+a polynomial can be inverted by exhaustive search, so `hbig` could be dropped (gate 03f1
+review, M1; ruling R-03f1-1 (A) keeps it). Whether safe primes (resp. primes `≡ 3 (mod 4)`
 with a generator) of full length can be produced for every `n` except with negligible
 probability is itself open ([PS10, p. 52]: the sampler's "basic theoretical properties are
 unknown"); the hypothesis `∃ δ, Negligible δ ∧ G.FullLengthExcept δ` of the headline theorems
@@ -467,6 +470,15 @@ def sampleBelowL (m k B T : ℕ) (r : List Bool) : Option ℕ :=
     if listToNat ((r.drop (t * B)).take k) < m then some (listToNat ((r.drop (t * B)).take k))
     else none
 
+/-- `sampleBelowL` is block rejection sampling with the test `v < m`:
+`sampleBelowL m k B T = rejectBlocksL (· < m) k B T` (the same blocks, the same test; gate 03f1
+review, M2). -/
+theorem sampleBelowL_eq_rejectBlocksL (m k B T : ℕ) :
+    sampleBelowL m k B T = rejectBlocksL (· < m) k B T := by
+  funext r
+  rw [rejectBlocksL_eq]
+  rfl
+
 /-- A sampled value is below `m`. -/
 theorem sampleBelowL_lt {m k B T : ℕ} {r : List Bool} {v : ℕ} (h : sampleBelowL m k B T r = some v) :
     v < m := by
@@ -484,18 +496,15 @@ distance `(1/2)^n` of the uniform number below `m`. The closeness fact behind
 `expCollection_sampleClose` and the El Gamal samplers (`egUnit`, `egGenParts`, `egEncParts`,
 `ddhExpo`).
 
-**Proof sketch.** `k ≤ n` by `Nat.size_le`, so trial `t < n` reads the first `k` bits of the
-`t`-th block of `n` bits of `List.ofFn b` (`NumberTheory.chunk`; `List.drop`/`List.take` of
-`List.ofFn`), and `sampleBelowL m k n n` is `firstHit (· < m)` of the numbers read from the
-blocks (`List.findSome?` over `List.range n` versus `List.finRange n`; `listToNat` of the `k`
-bits is `bitsToNat` of the block's prefix, `bitsToNat_eq_listToNat`). The map from the `n · n`
-coins to the `n` prefixes is a product of coordinate projections, so it pushes the uniform
-distribution to the uniform one on `Fin n → Fin k → Bool` (`StatClose.comp_pushesUniform`),
-and reading bits is the bijection `bitsEquiv k` onto `Fin (2^k)`; `statClose_firstHit` with
-`E = {x < m}` and `d = 0` gives closeness `(1 − m/2^k)^n ≤ (1/2)^n` (`Nat.lt_size_self`:
-`m/2^k ≥ 1/2`), transported along the bijection `{x : Fin (2^k) // x < m} ≃ Fin m` by
-`StatClose.comp_equiv_right` and `StatClose.map` (`Fin.val`), exactly as in
-`statClose_rejectionSample`. -/
+**Proof sketch.** A corollary of `statClose_rejectBlocksL` (gate 03f1 review, M2; that lemma is
+filled first, and this one is not filled a second time). With `k = Nat.size m`, `k ≤ n` by
+`Nat.size_le` (`m < 2^n`), and `sampleBelowL m k n n = rejectBlocksL (· < m) k n n`
+(`sampleBelowL_eq_rejectBlocksL`). `statClose_rejectBlocksL (· < m) k n n` with the default
+`d = 0` (`0 < m`, `0 < 2^k`) gives closeness `(1 − Pr_{v < 2^k}[v < m])^n = (1 − m/2^k)^n` to
+the uniform element of `{v : Fin (2^k) // v < m}`, and `(1 − m/2^k)^n ≤ (1/2)^n` since
+`2^k ≤ 2m` (`Nat.lt_size_self` and the minimality of `Nat.size`: `m/2^k ≥ 1/2`). Transport the
+target along the value-preserving bijection `{v : Fin (2^k) // v < m} ≃ Fin m`
+(`StatClose.comp_equiv_right`) and weaken the bound (`StatClose.mono`). -/
 theorem statClose_sampleBelowL {m n : ℕ} (hm : 0 < m) (hmn : m < 2 ^ n) :
     StatClose (fun b : Fin (n * n) → Bool => (sampleBelowL m (Nat.size m) n n (List.ofFn b)).getD 0)
       (fun x : Fin m => (x : ℕ)) ((1 / 2 : ℝ) ^ n) := by
@@ -514,7 +523,7 @@ def expSampleRaw (z : List Bool) : List Bool :=
 domain `D_i`"] given the arithmetic bundle.
 
 **Proof sketch.** The bit length `Nat.size m` is the length of the numeral of `m` with its
-leading zeros stripped (requested shared primitive, as in the RSA sampler); the trial loop is
+leading zeros stripped (`H.size`); the trial loop is
 `Complexity.polyTimeComputable_iterateFind` over the `n` blocks of `1^n` bits
 (`polyTimeComputable_pairDropPoly`), each trial comparing the first `k` bits with `m`
 (`H.le`); the payload is the accepted block, the `none` branch gives the fallback; the output
diff --git a/TCSlib/Cryptography/Candidates/DiscreteLogHardcore.lean b/TCSlib/Cryptography/Candidates/DiscreteLogHardcore.lean
index 14900a0d..8c1cc2b3 100644
--- a/TCSlib/Cryptography/Candidates/DiscreteLogHardcore.lean
+++ b/TCSlib/Cryptography/Candidates/DiscreteLogHardcore.lean
@@ -558,24 +558,36 @@ set and by `WellFormedIndex`), the domain is `Z_{p−1}` (`expOrd_of_valid`), `f
 `expo g_u x` with `g_u := expUnit` a generator (`orderOf_expUnit`, `IsGenerator` by
 `orderOf_eq_card_of_forall_mem_zpowers`-converse `zpowers_eq_top_of_prime_card`-free counting:
 `Nat.card_zpowers`), and `half_i x = halfBit (p−1) x` (`halfPred_eq`), so `A`'s per-instance
-success is `predProb (expo g_u) (halfBit (p−1)) A_i` with `A_i y ρ := A.distinguisherL n ⟨i, encD y⟩ ρ`.
-Apply `invProb_dlInverter_ge` with `s := ⌊ε(p−1)/4⌋ ≥ 1` (as `p − 1 ≥ 2^{n−1} − 1 ≥ 8n^c` for
-large `n`), `T := ⌈(p−1)/s⌉ ≤ 8n^c + 1`, `k := n`, `ℓ := 4n · (2n^c)² = 16 n^{2c+1}`: the inverter
-succeeds on the good instances with probability `≥ (3/4)/T ≥ 3/(4(8n^c + 1))`, hence overall
-`≥ (ε/2) · 3/(4(8n^c + 1))` (`OneWay.uprob_mul_le_uexp`-style averaging over the good set). The
-machine `B` realising `dlInverter` is a non-uniform PPT: advice `⟨A.advice n, 1^{n}⟩`, coins
-`T·n + n·ℓ·(2n + A.coins)` (all `PolyExpr`), on `⟨1^n, ⟨i, y⟩⟩` it reads `p`, `g` from `i`,
-computes `s` and `T` from `1^n` and `p` (`H.divMod`, `H.mul`), samples `t` and the `r_{j,i}` by
-rejection (`sampleBelowL` with `H.le`; the statistical term `n·ℓ·(1/2)^n + (1/2)^n` by
-`statClose_rejectionSample`/`StatClose.prod`, `StatClose.abs_uprob_sub_le_prod`), shifts
-`y · g^{−ts}` (`H.modExp`, `H.xgcd` for the inverse), and runs the `n` rounds of `dlLoop`
-(`Complexity.polyTimeComputable_iterate` with the state `⟨y_j, bits⟩`, D11): quadratic
-residuosity by `H.modExp` (`y^{(p−1)/2} = 1`, Euler), the root `y^{(p+1)/4}` by `H.modExp`
-(`sqrtMod3`, [PS10, Theorem 58.2]), the `ℓ` oracle calls `A.output` on the layout
-`⟨⟨⟨1^n, ⟨i, z_i⟩⟩, A.advice n⟩, ρ_i⟩` (`polyTimeComputable_iterateEmit`, `NUPPT.polyTimeComputable_layout`),
-the comparison with `half(r_i)` (`halfStr`), the majority (`polyTimeComputable_majority`), the
-negation `p − z` and the bit assembly; finally `(bits + ts) mod (p−1)` as an `n`-bit numeral
-(`decodeFin n` reads it back, `bitsToNat_natToBits`). Thus `G.dlProb B n ≥ 3ε/(8(8n^c+1)) − 2n^{2c+2}(1/2)^n`
+success is `predProb (expo g_u) (halfBit (p−1)) A_i` with
+`A_i y ρ := A.distinguisherL n (pairEncode i (natToList n (y : ZMod p).val)) ρ`.
+Apply `invProb_dlInverter_ge` with `ε := n^{-c}/2`, `s := ⌊(p−1)/(8n^c)⌋` (so `4s ≤ ε(p−1)`),
+`T := ⌈(p−1)/s⌉` (so `Ts ≥ p − 1`), `k := n` (`s ≤ p − 1 < 2^n`) and `ℓ := 16 n^{2c+1}`
+(so `k/(ε²ℓ) = 1/4`). For large `n` the good instances have `p − 1 ≥ 2^{n−1} − 1 ≥ 16 n^c`, so
+`(p−1)/(8n^c) ≥ 2`, `s ≥ (p−1)/(16 n^c) ≥ 1` and `T ≤ K(n) := 16 n^c < 2^n`; the inverter then
+succeeds with probability `≥ (3/4)/T ≥ 3/(4K(n))` on each good instance, with ideal coins.
+The machine `B` realising `dlInverter` is a non-uniform PPT: advice `⟨A.advice n, ⟦8n^c⟧_n⟩`
+(the `n`-bit numeral of `8n^c`: the bundle has no unary-to-binary conversion); coins
+`n·n + n·ℓ·(n·n + A.coins)` (a `PolyExpr`, `c` being fixed): one block of `n·n` coins for `t`
+and, for each of the `n·ℓ` trials, a block of `n·n` coins for `r_{j,i}` and `A.coins` coins for
+`ρ_{j,i}`. On `⟨1^n, ⟨i, y⟩⟩` it reads `p`, `g` from `i`; computes `s` and `T` (`H.sub`,
+`H.divMod`, `H.add`); outputs `0^n` unless `1 ≤ s` and `T < 2^n` (the analysis uses only the
+good instances); samples `t := (sampleBelowL T (Nat.size T) n n ·).getD 0` and
+`r_{j,i} := (sampleBelowL (p−1) (Nat.size (p−1)) n n ·).getD 0` (`H.le`, `H.size`,
+`polyTimeComputable_iterateFind`); shifts `y · g^{−ts}` (`H.modExp`, `H.xgcd`); and runs the
+`n` rounds of `dlLoop` (`Complexity.polyTimeComputable_iterate` with the state `⟨y_j, bits⟩`,
+D11): quadratic residuosity by `H.modExp` (`y^{(p−1)/2} = 1`, Euler), the root `y^{(p+1)/4}` by
+`H.modExp` (`sqrtMod3`, [PS10, Theorem 58.2]), the `ℓ` oracle calls `A.output` on the layout
+`⟨⟨⟨1^n, ⟨i, z_{j,i}⟩⟩, A.advice n⟩, ρ_{j,i}⟩` (`polyTimeComputable_iterateEmit`,
+`NUPPT.polyTimeComputable_layout`), the comparison with `half(r_{j,i})` (`halfStr`), the
+majority (`polyTimeComputable_majority`), the negation `p − z` and the bit assembly; finally
+`(bits + ts) mod (p−1)` as an `n`-bit numeral (`decodeFin n` reads it back,
+`bitsToNat_natToBits`). Sampling: each of the `1 + nℓ` sampled coordinates is within `(1/2)^n`
+of uniform (`statClose_sampleBelowL`, with `0 < T < 2^n` and `0 < p − 1 < 2^n`); the coins of
+`A` are exact; `StatClose.prod` and `StatClose.abs_uprob_sub_le_prod` give a loss of at most
+`(1 + 16 n^{2c+2})(1/2)^n` at every instance. Averaging over the good set (probability
+`≥ ε/2`, `HardcoreBit.uprob_mul_le_uexp`):
+`G.dlProb B n ≥ (ε/2)·3/(4K(n)) − (1 + 16 n^{2c+2})(1/2)^n`
+`= 3/(256 n^{2c}) − (1 + 16 n^{2c+2})(1/2)^n`
 for infinitely many `n`, an inverse polynomial, contradicting `hDL B` via `not_negligible_iff`. -/
 theorem fullDLCollection_hardCore (H : ArithmeticFP) (G : FullGroupGen)
     (hbig : ∃ δ : ℕ → ℝ, Negligible δ ∧ G.FullLengthExcept δ) (hDL : FullDLAssumption G) :
diff --git a/TCSlib/Cryptography/Candidates/ElGamal.lean b/TCSlib/Cryptography/Candidates/ElGamal.lean
index 1f1d1ab4..be4efe98 100644
--- a/TCSlib/Cryptography/Candidates/ElGamal.lean
+++ b/TCSlib/Cryptography/Candidates/ElGamal.lean
@@ -56,10 +56,11 @@ generator's coins (`ExpGroupGen.FullLengthExcept`).
 
 **Run-3 audit repairs.** P8-1: the run-2 DDH ensembles had dependent-sum seeds
 `Σ r, Z_{q_r} × Z_{q_r}` (resp. three factors), on which the uniform seed gives the coin string
-`r` probability `q_r² / Σ q²` (resp. `q_r³ / Σ q³`) instead of `2^{-|r|}` — the two ensembles
-then had different instance laws whenever `q` varies with the coins, and the threshold test
-`[q ≥ θ_n]` distinguished them with constant advantage, so `DDHAssumption` was false for every
-randomized generator. The seeds are now product types (uniform coins for the generator, D6)
+`r` probability `q_r² / Σ q²` (resp. `q_r³ / Σ q³`) instead of `2^{-|r|}` — so the two ensembles
+could have different instance laws, and when `q` varies non-negligibly with the coins (two
+orders `q`, `3q/2` on half the coins each give the laws `(4/13, 9/13)` and `(8/35, 27/35)`) a
+threshold test `[q ≥ θ_n]` distinguished them, making `DDHAssumption` false for reasons
+unrelated to DDH. The seeds are now product types (uniform coins for the generator, D6)
 with the exponents read by `ddhExpo`. P8-2: `elGamal_secure`'s hypothesis `G.FullLength`
 (full length on every coin string) became `∃ δ, Negligible δ ∧ G.FullLengthExcept δ`.
 
@@ -294,8 +295,8 @@ run-3 audit P2-2, by instance resolution).
 
 Repair (run-3 audit P8-1): the run-2 seed type `Σ r : G.gen.Coins n, Z_{q_r} × Z_{q_r}` gave
 the coin string `r` probability `q_r² / Σ_r q_r²` under the uniform seed, so the instance law
-depended on the fibre sizes and differed from `ddhRandom`'s (cubes), making `DDHAssumption`
-false for every generator whose `q` varies with the coins. -/
+depended on the fibre sizes and differed from `ddhRandom`'s (cubes), which could make
+`DDHAssumption` false for reasons unrelated to DDH (DESIGN §5 item 20). -/
 noncomputable def ddhReal (G : SafePrimeGen) : Ensemble ddhLen where
   σ n := G.gen.Coins n × ((Fin (n * n) → Bool) × (Fin (n * n) → Bool))
   X n z := padFin (ddhLen.eval n) (ddhTuple (G.gen.runAt n [] z.1)
@@ -509,9 +510,9 @@ def egGenRaw (G : SafePrimeGen) (z : List Bool) : List Bool :=
 (`polyTimeComputable_pairTakePoly`/`_pairDropPoly` on `⟨1^n, r⟩`); run `G.gen.output` on the
 layout (`NUPPT.polyTimeComputable_layout`, `G.gen.polyTimeComputable_output`); the two
 rejection loops are `Complexity.polyTimeComputable_iterateFind` over `n`-bit blocks with the
-test `H.le` (the decrement `p − 1` and the bit length `Nat.size` are requested shared
-primitives, as in the RSA generator); `h = g² mod p` and `h^x mod p` by `H.modExp`; the
-numerals are padded to width `n` (`polyTimeComputable_unaryPoly`, `_blockMap`); pair. -/
+test `H.le` (the decrement `p − 1` and the bit length `Nat.size`: `H.sub`, `H.size`);
+`h = g² mod p` and `h^x mod p` by `H.modExp`; the numerals are padded to width `n`
+(`polyTimeComputable_unaryPoly`, `_blockMap`); pair. -/
 theorem polyTimeComputable_egGenRaw (H : ArithmeticFP) (G : SafePrimeGen) :
     PolyTimeComputable (egGenRaw G) := by
   sorry
@@ -843,8 +844,11 @@ except on a negligible set of the generator's coins (and under the arithmetic hy
 **Deviation:** message space `G_q` and the chosen-message form of security (the text's
 `m ∈ Z_p` is insecure, source error 28); the DDH assumption is relative to `egGroupGen H G`
 and samples its exponents by rejection (`ddhExpo`, D10); `hbig` (`ExpGroupGen.FullLengthExcept`)
-makes the sampling term `1/q ≤ 8 · 2^{-n}` negligible outside a set of coins of probability
-`δ n`; the text leaves the proof as an exercise and omits the generator-versus-square term.
+is used to make the sampling term `1/q ≤ 8 · 2^{-n}` negligible outside a set of coins of
+probability `δ n` (a convenience: if `E[1/q]` were not negligible, a DDH distinguisher finding
+`a` by exhaustive search when `q ≤ 2n^c` would contradict the DDH assumption, so `hbig` could be
+dropped; gate 03f1 review, M1; ruling R-03f1-1 (A) keeps it); the text leaves the proof as
+an exercise and omits the generator-versus-square term.
 
 Repair (run-3 audit P8-1, P8-2): the DDH ensembles' seeds became products (so hybrid 1 below
 is exact up to the event `g² = 1`), and `hbig : G.FullLength` became
diff --git a/TCSlib/Cryptography/Candidates/Factoring.lean b/TCSlib/Cryptography/Candidates/Factoring.lean
index 42944c08..0566c08f 100644
--- a/TCSlib/Cryptography/Candidates/Factoring.lean
+++ b/TCSlib/Cryptography/Candidates/Factoring.lean
@@ -499,11 +499,17 @@ with the step dropping `n` bits, the test `hP` on the first `n` bits, the payloa
 bits, `R = 2n²`, `P = var`), whose `List.range.find?` form is `firstHit` over `chunk`
 (`samplePrime`); the fallback numeral `natToList n 2 = 0^{n-2}10` of a failed run is the
 `none` branch of `iterateFind` (a constant string of unary-polynomial length,
-`polyTimeComputable_unaryPoly`, `polyTimeComputable_blockMap`); the acceptance test of
-`samplePairOut` is two `H.prime` calls, a `pairEq` test and two `H.le`
-comparisons with `1^{max n 2}` (`polyTimeComputable_ite`), the accepted blocks are re-encoded
-with `max n 2` bits (`polyTimeComputable_unaryPoly`, `polyTimeComputable_blockMap`), and the
-default pair is a constant; pair the two results (`PolyTimeComputable.pairEncode`). -/
+`polyTimeComputable_unaryPoly`, `polyTimeComputable_blockMap`). The acceptance test of
+`samplePairOut` uses `hP` only (this theorem has no `ArithmeticFP` argument): the two prime
+tests are `hP`, and the inequality of the two values is tested by comparing the two `n`-bit
+words directly (a `pairEq` test: words of equal length have equal values iff they are equal);
+the two range checks `< 2^{max n 2}` are discharged from the fixed widths, not computed (each
+`samplePrimeL` output has `n` bits, so its value is `< 2^n ≤ 2^{max n 2}`,
+`listToNat_lt_two_pow`); the branch is `polyTimeComputable_ite`. The accepted words are
+re-encoded with `max n 2` bits by leading-zero padding (the `max n 2`-bit numeral of an `n`-bit
+word is the word preceded by `max n 2 − n` zeros, a constant block of unary-polynomial length:
+`polyTimeComputable_unaryPoly`, `polyTimeComputable_blockMap`), and the default pair is a
+constant; pair the two results (`PolyTimeComputable.pairEncode`). -/
 theorem polyTimeComputable_samplePairRaw (hP : PolyTimeComputable primeStr) :
     PolyTimeComputable samplePairRaw := by
   sorry
diff --git a/TCSlib/Cryptography/Candidates/RSA.lean b/TCSlib/Cryptography/Candidates/RSA.lean
index e548ac26..e2379a32 100644
--- a/TCSlib/Cryptography/Candidates/RSA.lean
+++ b/TCSlib/Cryptography/Candidates/RSA.lean
@@ -755,14 +755,26 @@ so the event is "`A(1^n, ⟨⟨N, e⟩, x^e⟩)` outputs the numeral of `x`", wh
 event of `rsaBreaker A` on the challenge `y := x^e` (`rsaBreaker_runAt`, `decodeFin_ofFn`,
 `bitsToNat_natToBits`, `val_units_pow`). Since `x ↦ x^e` pushes uniform to uniform
 (`pushesUniform_rsaPerm`, `PushesUniform.uprob_eq`), the inner probability equals the RSA
-inner probability at `(z, e)`. The law of `(z, e)` under the generator's coins is within
-`rsaGenErr n` of the ideal uniform law on `DistinctPrimes n × Z*_{Φ(N)}`
-(`statClose_samplePrime` with the prime fallback `natToBits n 2` of `samplePrimeL` — run-3
-audit P7-7 — twice and `StatClose.prod` for `(p, q)`, `StatClose.map` through the validity
-test with `uprob_diag` and `one_div_card_primes_le` for the fallback on `p = q`,
-`statClose_rejectBlocksL` for `e` with the acceptance rate of the sampleClose sketch); `StatClose.abs_uprob_sub_le_prod` with the
-auxiliary coins `(y, r)` turns `uexp` over the generator's coins into `uexp` over `z`
-(`uexp_prod`, `uprob_prod`) up to `rsaGenErr n`. -/
+inner probability at `(z, e)`: a number `h(z, e) ∈ [0, 1]` (over `y` and `A`'s coins).
+The exponent group `Z*_{Φ(N)}` depends on `z`, so the generator's law is not compared with one
+uniform product: the comparison is a conditional expectation over `z`. Split the generator's
+coins into the two prime segments and the exponent segment (`rsaGenParams`, `uexp_prod`,
+`uprob_prod`). (i) For each fixed prime pair `z`, the exponent drawn from the exponent segment
+(`sampleUnitL` modulo `Φ(N)`, fallback `1`) is within `e^{-n}` of the uniform element of
+`Z*_{Φ(N)}` (`statClose_rejectBlocksL` with the acceptance rate of the sampleClose sketch), so
+the conditional success at `z` exceeds `g(z) := E_{e uniform}[h(z, e)]` by at most `e^{-n}`
+(`StatClose.abs_uprob_sub_le_prod`, with `(y, r)` as the auxiliary coins). (ii) The law of `z`
+under the two prime segments is within `2 · 2^{-n} + 2n/2^n` of the uniform law on
+`DistinctPrimes n` (`statClose_samplePrime` with the prime fallback `natToBits n 2` of
+`samplePrimeL` — run-3 audit P7-7 — twice and `StatClose.prod` for `(p, q)`, `StatClose.map`
+through the validity test with `uprob_diag` and `one_div_card_primes_le` for the fallback on
+`p = q`); averaging the `[0, 1]`-valued `g` over that law instead of the uniform one costs at
+most that distance (`StatClose.abs_uprob_sub_le_prod` again, with `g(z)` read as a probability
+over the auxiliary coins `ω : Π z', Z*_{Φ(N')} × Z_{N'}^* × A.Coins n` at `ω z`). (iii) Adding
+the conditional exponent error, the inversion probability is at most
+`uexp g + (2 · 2^{-n} + 2n/2^n) + e^{-n} = rsaProb (rsaBreaker A) n + rsaGenErr n`, as
+`rsaProb` is the outer `uexp` over `z` of the inner probability over `(e, y, r)`. No error
+beyond `rsaGenErr n` is needed. -/
 theorem rsaCollection_invProbAt_le (H : ArithmeticFP) (A : NUPPT) {n : ℕ} (hn : 2 ≤ n) :
     (rsaCollection H).invProbAt A n ≤ rsaProb (rsaBreaker A) n + rsaGenErr n := by
   sorry
diff --git a/TCSlib/Cryptography/Candidates/Rabin.lean b/TCSlib/Cryptography/Candidates/Rabin.lean
index d9c93a07..a0a19227 100644
--- a/TCSlib/Cryptography/Candidates/Rabin.lean
+++ b/TCSlib/Cryptography/Candidates/Rabin.lean
@@ -146,8 +146,12 @@ theorem blumFactoring_of_factoring (hD : BlumDensity) (hF : FactoringAssumption)
 
 /-! ## The symmetry lemma (Claim-62.2) -/
 
-/-- The unit `u = CRT⁻¹(1, −1)` of `Z_{pq}^*`: a square root of `1` different from `±1`
-[PS10, proof of Theorem 61.8, "it can only be that they are congruent modulo `p` and `q`"]. -/
+/-- The unit `u = CRT⁻¹(1, −1)` of `Z_{pq}^*`, for coprime moduli `p`, `q`
+[PS10, proof of Theorem 61.8, "it can only be that they are congruent modulo `p` and `q`"].
+It squares to `1` for all coprime moduli (`crtNegOne_sq`). For primes `p`, `q` it differs from
+`1` when `q` is odd and from `−1` when `p` is odd (`crtNegOne_ne_one`, `crtNegOne_ne_neg_one`),
+so for two odd primes it is a square root of `1` other than `±1`. Coprimality alone does not
+give this: for `p = 2`, `q = 3` it is `5 = −1` in `Z_6`. -/
 noncomputable def crtNegOne {p q : ℕ} (h : p.Coprime q) : (ZMod (p * q))ˣ :=
   (crtUnits h).symm (1, -1)
 
@@ -495,8 +499,9 @@ theorem rabinCollection_index (H : ArithmeticFP) (n : ℕ) (r : (rabinCollection
 /-- The statistical error of the Rabin reductions at parameter `n`: two restricted prime
 samplers and the unit sampler of `rabinFactorer`, the latter counted twice because it enters
 through the factor `2` of the symmetry lemma (`e^{-n}` each: `4e^{-n}`), and the diagonal
-`p = q` of the restricted class: `1/(P − 1) ≤ 2/P ≤ 4n/2^n` for the `P = |Π_n| − 1 ≥ 2` odd
-primes (`one_div_card_primes_le`) and `1/B ≤ 4n/2^n` for the `B` Blum primes (`BlumDensity`).
+`p = q` of the restricted class: `1/(P − 1) ≤ 2/P ≤ 4n/2^n` with `P = |Π_n|` the total prime
+count, of which `P − 1 ≥ 2` are odd (`one_div_card_primes_le`), and `1/B ≤ 4n/2^n` for the `B`
+Blum primes (`BlumDensity`).
 
 Repair (run-3 audit P7-3): the diagonal term was `2n/2^n`, which neither the Chebyshev bound
 `2^n ≤ 2n|Π_n|` (odd class: `1/(|Π_n| − 1)`) nor `BlumDensity` (`1/B`) yields; both give
diff --git a/TCSlib/Cryptography/NumberTheory/Chebyshev.lean b/TCSlib/Cryptography/NumberTheory/Chebyshev.lean
index 423c20bc..ddae2c96 100644
--- a/TCSlib/Cryptography/NumberTheory/Chebyshev.lean
+++ b/TCSlib/Cryptography/NumberTheory/Chebyshev.lean
@@ -36,7 +36,8 @@ arguments by the text's monotonicity of `t / log t`.
 
 **Deviation:** [PS10, Theorem 31.3] claims the strict inequality `π(x) > x / (2 log x)` for
 every real `x > 1`; equality holds at `x = 2` (`π(2) = 1`), so the theorem is stated with `≤`,
-for natural arguments `m ≥ 2`. **Deviation:** [PS10, Claim 32.4] (`p^{ν_p(X)} < 2x`) fails at
+and for natural arguments `m ≥ 2`, which repairs and restricts the real claim (it fails even with
+`≤` at `x = 3/2`, where `π(x) = 0`). **Deviation:** [PS10, Claim 32.4] (`p^{ν_p(X)} < 2x`) fails at
 `x = 1, p = 2`; the correct form `p^{ν_p(C(2x,x))} ≤ 2x` is Mathlib's
 `Nat.pow_factorization_choose_le`. **Deviation:** the density corollary needs `n ≥ 2`
 (`Π_1 = ∅`); the text's "`n`-bit numbers" silently assumes it.
@@ -157,7 +158,9 @@ theorem chebyshev_two_mul (x : ℕ) (hx : 0 < x) :
 `m / (2 log₂ m) ≤ π(m)`.
 
 **Deviation:** stated with `≤` (the text's `>` fails at `m = 2`) and for natural arguments
-`m ≥ 2` (the text's real `x > 1`; `π` is a step function, so nothing is lost).
+`m ≥ 2`. This repairs and restricts the text's claim for every real `x > 1`, which is false even
+with `≤`: at `x = 3/2`, `π(x) = 0 < x / (2 log₂ x)`. The natural-argument form is the one the
+prime-density uses need.
 
 **Proof sketch.** Even `m = 2x`: `chebyshev_two_mul`. Odd `m = 2x − 1 ≥ 3`: `2x` is composite,
 so `π(m) = π(2x) ≥ 2x / (2 log₂(2x))`, and `t ↦ t / log₂ t` is increasing for `t ≥ 3`
diff --git a/TCSlib/Cryptography/NumberTheory/Primality.lean b/TCSlib/Cryptography/NumberTheory/Primality.lean
index e9e0e712..1c496b08 100644
--- a/TCSlib/Cryptography/NumberTheory/Primality.lean
+++ b/TCSlib/Cryptography/NumberTheory/Primality.lean
@@ -41,7 +41,10 @@ The Miller–Rabin test [PS10, §2.6.5] and the prime sampler [PS10, §2.6.6]:
 test reject primes with positive probability; the test draws `α ∈ [1, N−1]` as in the
 standard presentation, matching `|L_N| = N − 1`. Even `N > 2` are rejected outright (the text
 handles only the base case `N = 2`). **Deviation:** [PS10, Theorem 49.14] says "with
-probability `1 − 2^{−t}`" for "at least"; Lemma 50.15's composite case needs `N` odd.
+probability `1 − 2^{−t}`" for "at least"; Lemma 50.15's composite case is proved for odd `N`
+only, as a convenience: for even `N > 2` the liars also lie in a proper subgroup of `Z_N^*` (the
+kernel of `x ↦ x^{N−1}`, which misses `−1` since `(−1)^{N−1} = −1`), and the test rejects even
+`N` outright.
 **Deviation:** `SamplePrime` is truncated to `T` trials (strict PPT with failure `⊥`, D10)
 and tests primality exactly (`Nat.Prime`); with Miller–Rabin in place of the exact test the
 output would only be statistically close to uniform. §2.6.6 (p. 50) misquotes the prime
@@ -386,8 +389,11 @@ private theorem liar_pow_mem {N : ℕ} (hN : 2 < N) {j' : ℕ}
 /-- **Odd composites have few liars** [PS10, Lemma 50.15, second half]: for odd composite
 `N > 2`, `|L_N| ≤ (N−1)/2`, stated as `2 |L_N| ≤ N − 1`.
 
-**Deviation:** the text says `N > 2` composite (oddness is needed) and `<` (the proof gives
-`≤ Φ(N)/2 < (N−1)/2`, so `<` also holds; the weaker form suffices for Theorem 49.14).
+**Deviation:** the text says `N > 2` composite and `<`. The restriction to odd `N` is a
+convenience, not a necessity: for even `N > 2` every liar satisfies `α^{N−1} = 1` while the unit
+`−1` does not (`N − 1` is odd and `−1 ≠ 1`), so the liars again lie in a proper subgroup;
+`uprob_millerRabin_le` rejects even `N` outright and needs only the odd case. The proof gives
+`≤ Φ(N)/2 < (N−1)/2`, so `<` also holds; the weaker form suffices for Theorem 49.14.
 
 **Proof sketch.** ([CLRS09, Theorems 31.38–31.39].) Every liar is a unit (`α^{N−1} = 1`,
 `mrLiar_isUnit`), so it suffices to exhibit a proper subgroup of `Z_N^*` containing every
@@ -859,10 +865,11 @@ private theorem spFind_eq (n : ℕ) (r : Fin (2 * n ^ 2 * n) → Bool) :
     rfl
 
 /-- **`SamplePrime` is a PPT** [PS10, Lemma 51.17, "in time `poly(n)`"], given a
-polynomial-time primality test on binary strings (the hypothesis `Rem-33.2`/Q6 of the plan,
-AKS or Miller–Rabin): there is a uniform `NUPPT` with coin polynomial `2n² · n` whose
-activation at parameter `n` on the empty argument with coins `r` (read as `2n²` blocks of
-`n` bits) outputs the bits of `samplePrime n (2n²)`, or `[]` on failure.
+polynomial-time primality test on binary strings (the hypothesis `Rem-33.2`/Q6 of the plan:
+an exact deterministic primality test such as AKS; a bounded-error Miller–Rabin test does not
+compute `hP`'s function exactly): there is a uniform `NUPPT` with coin polynomial `2n² · n`
+whose activation at parameter `n` on the empty argument with coins `r` (read as `2n²` blocks
+of `n` bits) outputs the bits of `samplePrime n (2n²)`, or `[]` on failure.
 
 **Proof sketch.** Instance of `Complexity.polyTimeComputable_iterateFind` (M3): on the state
 word `⟨1^n, r⟩`, the step `spStep` drops the first `n` bits of the second component
diff --git a/TCSlib/Cryptography/ZeroKnowledge/Defs.lean b/TCSlib/Cryptography/ZeroKnowledge/Defs.lean
index f6c4bc5f..8e81839e 100644
--- a/TCSlib/Cryptography/ZeroKnowledge/Defs.lean
+++ b/TCSlib/Cryptography/ZeroKnowledge/Defs.lean
@@ -39,13 +39,15 @@ and what the non-uniform reduction of [PS10, Proposition 128.8] needs); the erro
 a function of `|x|` (the text's `e(n)` leaves `n` undefined); the honest-verifier notion is
 stated for a protocol and a witness relation without assuming the proof property, which the
 theorems add separately.
-The bound `Lz` is necessary, not only convenient (gate 03e, note 9): the distinguisher runs in
-time polynomial in its input, the encoded view, which contains `z`; with `|z| ≥ 2^n` it could
-invert a one-way permutation on `n`-bit inputs and open the unopened commitments of the
-3-colouring protocol, so computational zero-knowledge would fail for every protocol whose
-hiding is only computational. Read literally, [PS10, Definition 121.2] (every
-`z ∈ {0,1}*`, with `D` polynomial-time in its input) has the same defect. For the same reason
-the distinguisher's advice is indexed by the parameter `|x|`, not by its input length.
+The bound `Lz` is necessary for the 3-colouring protocol, not only convenient (gate 03e,
+note 9; round 2, finding 6). The distinguisher runs in time polynomial in its input, the
+encoded view, which contains `z`. With `|z|` exponential in `ℓ(n)` it can open the perfectly
+binding commitments by exhaustive search. On a graph with two proper colourings outside one
+colour-permutation orbit, that tells the two real views apart with advantage 1, while the
+simulator does not see the witness. Read literally, [PS10, Definition 121.2] (every
+`z ∈ {0,1}*`, with `D` polynomial-time in its input) has the same defect for that protocol.
+Protocols with exactly simulable views are not affected. For the same reason the
+distinguisher's advice is indexed by the parameter `|x|`, not by its input length.
 
 **Perfect zero-knowledge (ruling G3-4 of gate 03).** With strict simulators and honest parties
 drawing polynomially many fair coins (D8, D10), no protocol of the source attains `PerfectZK`
@@ -307,6 +309,15 @@ def attempt (S : NUPPT) (w : List Bool) (t : ℕ) : List Bool :=
     (((NUPPT.inCoins w).drop (t * S.coinLen (NUPPT.inParam w).length)).take
       (S.coinLen (NUPPT.inParam w).length)))
 
+/-- One attempt unfolded: `attempt S w t` is `S.output` on the layout with parameter
+`inParam w`, argument `inArg w`, empty advice and coins
+`((inCoins w).drop (t · c)).take c`, where `c = S.coinLen |inParam w|`. -/
+theorem attempt_eq (S : NUPPT) (w : List Bool) (t : ℕ) :
+    attempt S w t = S.output (NUPPT.layout (NUPPT.inParam w) (NUPPT.inArg w) []
+      (((NUPPT.inCoins w).drop (t * S.coinLen (NUPPT.inParam w).length)).take
+        (S.coinLen (NUPPT.inParam w).length))) :=
+  rfl
+
 /-- The retrying simulator on its machine layout `w = ⟨⟨⟨1^n, y⟩, α⟩, r⟩`
 (for the abort form of [Gol01, Definition 4.3.1], amplified by repetition): the
 first of the `n` attempts that does not output `⊥ = []` (the first accepted index,
@@ -317,6 +328,41 @@ noncomputable def retry (S : NUPPT) (w : List Bool) : List Bool :=
     attempt S w (firstIdx (fun t => decide (attempt S w t ≠ [])) (NUPPT.inParam w).length)
   else []
 
+/-- The retrying simulator unfolded: with `N = |inParam w|` and `i` the least index below `N`
+whose attempt is not `⊥ = []` (`firstIdx`, equal to `N` if there is none), `retry S w` is
+attempt `i` if `i < N`, and `[]` otherwise. -/
+theorem retry_eq (S : NUPPT) (w : List Bool) :
+    retry S w =
+      if firstIdx (fun t => decide (attempt S w t ≠ [])) (NUPPT.inParam w).length <
+          (NUPPT.inParam w).length then
+        attempt S w (firstIdx (fun t => decide (attempt S w t ≠ [])) (NUPPT.inParam w).length)
+      else [] :=
+  rfl
+
+/-- If attempt `i < |inParam w|` is the first that does not abort (`attempt S w i ≠ []`, and
+`attempt S w j = []` for every `j < i`), then `retry S w` is attempt `i`.
+
+**Proof sketch.** `firstIdx` of the non-abort test is `i` (`firstIdx_eq_of`); rewrite
+`retry_eq` with it and take the `i < |inParam w|` branch. -/
+theorem retry_eq_attempt {S : NUPPT} {w : List Bool} {i : ℕ}
+    (hi : i < (NUPPT.inParam w).length) (hne : attempt S w i ≠ [])
+    (hmin : ∀ j < i, attempt S w j = []) : retry S w = attempt S w i := by
+  have h : firstIdx (fun t => decide (attempt S w t ≠ [])) (NUPPT.inParam w).length = i :=
+    firstIdx_eq_of hi (decide_eq_true hne) fun j hj => decide_eq_false (not_not.2 (hmin j hj))
+  rw [retry_eq, h, if_pos hi]
+
+/-- If all `|inParam w|` attempts abort (`attempt S w t = []` for every `t < |inParam w|`),
+then `retry S w = []`. Together with `retry_eq_attempt` this covers every input.
+
+**Proof sketch.** `firstIdx` of the non-abort test is `|inParam w|` (`firstIdx_eq_of_forall`);
+rewrite `retry_eq` with it and take the `else` branch. -/
+theorem retry_eq_nil {S : NUPPT} {w : List Bool}
+    (h : ∀ t < (NUPPT.inParam w).length, attempt S w t = []) : retry S w = [] := by
+  have h' : firstIdx (fun t => decide (attempt S w t ≠ [])) (NUPPT.inParam w).length =
+      (NUPPT.inParam w).length :=
+    firstIdx_eq_of_forall fun t ht => decide_eq_false (not_not.2 (h t ht))
+  rw [retry_eq, h', if_neg (lt_irrefl _)]
+
 /-- One attempt is polynomial-time on the indexed layout `⟨1^t, w⟩`.
 
 **Proof sketch.** The block `(r.drop (t · c)).take c` with `c = S.coinLen n` in unary
diff --git a/TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism.lean b/TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism.lean
index 9869c680..675fa55e 100644
--- a/TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism.lean
+++ b/TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism.lean
@@ -71,9 +71,10 @@ lemmas are proved in this file (the `xor` bijection `adaptiveEquiv` and the chan
 variables `gniShear`), which certifies the repaired statements.
 
 **Deviation (fixed alternation, D8):** the repeated graph-isomorphism protocol uses four
-moves per iteration (`H`, `b`, `γ`, and an empty verifier message) so that the strict
-prover/verifier alternation of `exec` is respected; the repeated protocols run `|x|`
-iterations instead of the text's `n = |G₁|` (so `2^{-|x|}` is negligible in `|x|` directly).
+moves per iteration (`H`, `b`, `γ`, and a verifier message, empty except for the final
+verdict) so that the strict prover/verifier alternation of `exec` is respected; the repeated
+protocols run `|x|` iterations instead of the text's `n = |G₁|` (so `2^{-|x|}` is negligible in
+`|x|` directly).
 
 **Deviation (well-formedness):** the verifiers reject common inputs that are not the
 encoding of two graphs on the same vertex set (`wellFormedInstance`); without this check a
@@ -552,7 +553,8 @@ noncomputable def giVerifierRep : Strategy where
 
 /-- The `|x|`-fold graph isomorphism protocol [PS10, Protocol 120.6, "repeat the procedure
 `|G₁|` times"] (Prot-120.6): prover first, four moves per iteration (`H_i`, `b_i`, `γ_i`, and
-an empty verifier message, D8 fixed alternation), `4|x|` messages. -/
+a verifier message, empty except for the final verdict, D8 fixed alternation), `4|x|`
+messages. -/
 noncomputable def giProtocolRep : Protocol where
   P := giProverRep
   V := giVerifierRep
@@ -924,18 +926,20 @@ theorem gni_interactiveProof : InteractiveProof gniProtocolRep Lniso :=
 `n² ≤ |x|`, so at most `|x|` bits per message, on every instance (ruling G3-3 of gate 03;
 `GI.giProver_length_le`). -/
 theorem giProtocol_proverBounded (R : List Bool → List Bool → Prop) :
-    giProtocol.ProverBounded R .var := fun x y r hist _ => GI.giProver_length_le x y r hist
+    giProtocol.ProverBounded R .var :=
+  (Protocol.proverBounded_iff _ _ _).2 fun x y r hist _ => GI.giProver_length_le x y r hist
 
 /-- The `|x|`-fold form of `giProtocol_proverBounded` (`GI.giProverRep_length_le`). -/
 theorem giProtocolRep_proverBounded (R : List Bool → List Bool → Prop) :
-    giProtocolRep.ProverBounded R .var := fun x y r hist _ => GI.giProverRep_length_le x y r hist
+    giProtocolRep.ProverBounded R .var :=
+  (Protocol.proverBounded_iff _ _ _).2 fun x y r hist _ => GI.giProverRep_length_le x y r hist
 
 /-- The honest graph non-isomorphism prover sends one bit per message (ruling G3-3 of gate 03;
 `GI.gniProver_length_le`), in one iteration and in the `|x|`-fold protocol. -/
 theorem gniProtocol_proverBounded (R : List Bool → List Bool → Prop) :
     gniProtocol.ProverBounded R (.const 1) ∧ gniProtocolRep.ProverBounded R (.const 1) :=
-  ⟨fun x y r hist _ => GI.gniProver_length_le x y r hist,
-    fun x y r hist _ => GI.gniProver_length_le x y r hist⟩
+  ⟨(Protocol.proverBounded_iff _ _ _).2 fun x y r hist _ => GI.gniProver_length_le x y r hist,
+    (Protocol.proverBounded_iff _ _ _).2 fun x y r hist _ => GI.gniProver_length_le x y r hist⟩
 
 /-- One iteration of the graph isomorphism protocol is an interactive proof for `L_iso`
 with soundness error `1/2` and efficient prover with respect to `R_iso`
diff --git a/TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Soundness.lean b/TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Soundness.lean
index a8918e97..22a93238 100644
--- a/TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Soundness.lean
+++ b/TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Soundness.lean
@@ -318,7 +318,8 @@ theorem gi_efficientProverProofErr (hP : giProver.Efficient) (hV : giVerifier.Ef
       rw [HardcoreBit.uprob_eq_one_of_forall hall]
       norm_num
   efficientP := hP
-  boundedP := ⟨.var, fun x y r hist _ => giProver_length_le x y r hist⟩
+  boundedP := ⟨.var, (Protocol.proverBounded_iff _ _ _).2 fun x y r hist _ =>
+    giProver_length_le x y r hist⟩
   completeWitness := by
     rintro x y ⟨n, G₀, G₁, σ, rfl, rfl, hσ⟩ z
     exact gi_complete hσ z
diff --git a/TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRepGI.lean b/TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRepGI.lean
index 4aeed143..22b293d7 100644
--- a/TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRepGI.lean
+++ b/TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRepGI.lean
@@ -474,7 +474,8 @@ theorem gi_rep_efficientProverProofErr (hP : giProverRep.Efficient) (hV : giVeri
       have : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ x.length := by positivity
       linarith
   efficientP := hP
-  boundedP := ⟨.var, fun x y r hist _ => giProverRep_length_le x y r hist⟩
+  boundedP := ⟨.var, (Protocol.proverBounded_iff _ _ _).2 fun x y r hist _ =>
+    giProverRep_length_le x y r hist⟩
   completeWitness := by
     rintro x y ⟨n, G₀, G₁, σ, rfl, rfl, hσ⟩ z
     exact giRep_complete hσ z
diff --git a/TCSlib/Cryptography/ZeroKnowledge/Interaction.lean b/TCSlib/Cryptography/ZeroKnowledge/Interaction.lean
index 23519614..b6f95458 100644
--- a/TCSlib/Cryptography/ZeroKnowledge/Interaction.lean
+++ b/TCSlib/Cryptography/ZeroKnowledge/Interaction.lean
@@ -37,10 +37,12 @@ last message *is* its verdict (`Protocol.outV_eq_getLast_of_moverIsV`); the chap
 are stated with the prover moving last, and the `n`-fold protocols read the verifier's last
 message as the verdict.
 Repetition convention (gate 03e, note 8): an iteration with an odd number of messages (prover,
-verifier, prover) is repeated under strict alternation by appending one dummy empty verifier
-message to each iteration, so that every iteration starts with the prover; the fourth move of
-`giProtocolRep` and of `colProtocolRep`, and the filler moves of the sequential repetition of
-[PS10, §7.2.1] in ch. 7, follow this convention.
+verifier, prover) is repeated under strict alternation by giving each iteration one additional
+verifier move, so that every iteration starts with the prover. In `giProtocolRep` and
+`colProtocolRep` that move is the empty message, except for the protocol's final move, which
+carries the verifier's verdict (the verdict convention above). The sequential repetition of
+[PS10, §7.2.1] in ch. 7 pads each phase instead with `rounds(|x|)` filler moves of both parties,
+its last filler again carrying the verdict.
 `Strategy.Efficient` ([PS10, §4.4], time complexity of an interactive machine) is one
 activation of a uniform `Complexity.NUPPT` at parameter `|x|` on `⟨⟨x, z⟩, messages⟩` with the
 whole random tape; the time is polynomial in the total input length rather than in `|x|`
@@ -331,6 +333,13 @@ of length `2^{rounds}`, which the composition theorems of ch. 7 cannot simulate.
 def ProverBounded (π : Protocol) (R : List Bool → List Bool → Prop) (B : PolyExpr) : Prop :=
   ∀ x y r hist, R x y → (π.P.next x y r hist).length ≤ B.eval x.length
 
+/-- **Bounded honest messages unfolded:** `π.ProverBounded R B` iff for every `x` and `y` with
+`R x y`, every tape `r` and every history `hist`, `|π.P.next x y r hist| ≤ B(|x|)`. -/
+theorem proverBounded_iff (π : Protocol) (R : List Bool → List Bool → Prop) (B : PolyExpr) :
+    π.ProverBounded R B ↔
+      ∀ x y r hist, R x y → (π.P.next x y r hist).length ≤ B.eval x.length :=
+  Iff.rfl
+
 /-- A message bound `B` implies every pointwise larger bound `B'`. -/
 theorem ProverBounded.mono {π : Protocol} {R : List Bool → List Bool → Prop} {B B' : PolyExpr}
     (h : π.ProverBounded R B) (hle : ∀ n, B.eval n ≤ B'.eval n) : π.ProverBounded R B' :=
diff --git a/TCSlib/Cryptography/ZeroKnowledge/InteractiveProofs.lean b/TCSlib/Cryptography/ZeroKnowledge/InteractiveProofs.lean
index 6b774497..09042140 100644
--- a/TCSlib/Cryptography/ZeroKnowledge/InteractiveProofs.lean
+++ b/TCSlib/Cryptography/ZeroKnowledge/InteractiveProofs.lean
@@ -33,8 +33,9 @@ read as the output string `[false]`, the negligible `ε` quantified before the i
 cheating prover and its auxiliary input; cheating provers are arbitrary strategies with a
 polynomial random tape (unbounded computation; polynomial coin tapes lose nothing by
 averaging, `Protocol.exists_proverCoins_le`). Completeness is `uprob = 1`, i.e. acceptance on
-every pair of random tapes. The parties' efficiency (the text's "p.p.t.") is
-`Strategy.Efficient`, polynomial time in `|x| + |z| + |messages|` (D8), together with a
+every pair of random tapes. The verifier's efficiency (Definition 116.1's "p.p.t.", and the
+prover's for Definition 119.5) is `Strategy.Efficient`, polynomial time in
+`|x| + |z| + |messages|` (D8), together with a
 polynomial bound `B(|x|)` on the honest prover's messages (ruling G3-3 of gate 03, the
 convention of ch. 6): in the completeness clause of `InteractiveProof` and
 `InteractiveProofErr` for the completeness witness, and as the field `boundedP`
@@ -43,10 +44,13 @@ witness. The residual deviation is that against a cheating prover the verifier's
 polynomial in the length of the messages it receives, not in `|x|`. Since the honest messages
 are short, the verifier can always be capped: `V` reading only the first `B(|x|)` bits of each
 message is still complete (the honest messages are untouched) and sound (against `P*` it acts
-as `V` against `P*` with truncated messages, another prover strategy). So the proof systems
-hold only for languages of the text's class IP — undecidable languages such as the halting
-problem, whose computation histories are not polynomially bounded, are excluded — while
-`IP` itself is stated with the message-prefix cap `Strategy.ReadsPrefix` of the verifier
+as `V` against `P*` with truncated messages, another prover strategy). So `InteractiveProof`
+(and `InteractiveProofErr` with negligible error, by `InteractiveProofErr.interactiveProof`)
+holds only for languages of the text's class IP — undecidable languages such as the halting
+problem, whose computation histories are not polynomially bounded, are excluded — the
+explicit-error forms with a large error say little (with `s = 1` the zero-message,
+always-accepting protocol is an `EfficientProverProofErr` for every language and relation) —
+while `IP` itself is stated with the message-prefix cap `Strategy.ReadsPrefix` of the verifier
 (run-3 audit P9-1). The capping argument is not formalized as a lemma.
 
 ## Main definitions
@@ -111,12 +115,14 @@ on the complete history of the fixed-alternation execution; `P'` ranges over str
 polynomial random tapes and receives no auxiliary input (the text's `P*(x)`); completeness is
 `uprob = 1` (every pair of random tapes). The verifier's "p.p.t." is `Strategy.Efficient`,
 polynomial-time in `|x| + |z| + |messages|` (D8), and the honest messages on the completeness
-witness are bounded by `B(|x|)` (the text's p.p.t. prover writes at most `t(|x|)` bits; the
-convention of ch. 6). Against a cheating prover the verifier's work is polynomial in the
-length of the messages it receives, not in `|x|`; because the honest messages are short the
-verifier can be capped to their length without losing completeness or soundness (module
-docstring), so the predicate holds only for languages of the text's class IP. The class `IP`
-is stated with the message-prefix cap `Strategy.ReadsPrefix` (run-3 audit P9-1). -/
+witness are bounded by `B(|x|)` (Definition 116.1's prover need not be efficient; bounding its
+messages is the chosen normal form, harmless because a verifier of time `t(|x|)` reads at most
+`t(|x|)` bits of each message; the convention of ch. 6). Against a cheating prover the
+verifier's work is polynomial in the length of the messages it receives, not in `|x|`; because
+the honest messages are short the verifier can be capped to their length without losing
+completeness or soundness (module docstring), so the predicate holds only for languages of the
+text's class IP. The class `IP` is stated with the message-prefix cap `Strategy.ReadsPrefix`
+(run-3 audit P9-1). -/
 structure InteractiveProof (π : Protocol) (L : Language Bool) : Prop where
   /-- The verifier is efficient (`Strategy.Efficient`, D8). -/
   efficientV : π.V.Efficient
@@ -232,7 +238,7 @@ theorem Protocol.ProverBounded.exists_complete {π : Protocol} {L : Language Boo
       ∀ z : List Bool, uprob (fun r : π.ExecCoins π.P x => π.outV π.P x y z r = [true]) = 1 :=
   ⟨B, fun x hx =>
     let ⟨y, hy⟩ := hLR x hx
-    ⟨y, fun r hist => hB x y r hist hy, hc x y hy⟩⟩
+    ⟨y, fun r hist => (π.proverBounded_iff R B).1 hB x y r hist hy, hc x y hy⟩⟩
 
 /-! ### Witness relations -/
 
@@ -466,7 +472,7 @@ theorem npProtocol_efficientP (T : List Bool → Bool) (p : PolyExpr) :
 theorem npProtocol_proverBounded (T : List Bool → Bool) (p : PolyExpr)
     {R : List Bool → List Bool → Prop} (hp : ∀ x y, R x y → y.length ≤ p.eval x.length) :
     (npProtocol T p).ProverBounded R p :=
-  fun x y _ _ hxy => hp x y hxy
+  ((npProtocol T p).proverBounded_iff R p).2 fun x y _ _ hxy => hp x y hxy
 
 /-- Non-vacuity of Definitions 116.1 and 119.5 [PS10, §4.5, "`NP ⊆ IP`"]: for a witness relation
 `R` of `L` decided by the polynomial-time predicate `T`, with witnesses of length at most
diff --git a/TCSlib/Cryptography/ZeroKnowledge/NP.lean b/TCSlib/Cryptography/ZeroKnowledge/NP.lean
index 8ad8b9c0..9e83f76c 100644
--- a/TCSlib/Cryptography/ZeroKnowledge/NP.lean
+++ b/TCSlib/Cryptography/ZeroKnowledge/NP.lean
@@ -275,6 +275,7 @@ theorem Protocol.ProverBounded.pullback {L L' : Language Bool}
     {w : List Bool → List Bool → List Bool} {p : PolyExpr} (h : LevinReduction L L' R R' f w p)
     {π : Protocol} {B : PolyExpr} (hB : π.ProverBounded R' B) :
     (π.pullback f w p).ProverBounded R (B.subst p) := by
+  rw [Protocol.proverBounded_iff] at hB ⊢
   intro x y r hist hxy
   rw [PolyExpr.eval_subst, ← h.length_eq x]
   exact hB (f x) (w x y) r hist (h.witness x y hxy)
@@ -674,25 +675,27 @@ scheme `(Com, ℓ)` and every witness relation `R` of `L` there is a Levin reduc
 one-iteration 3-colouring protocol is zero-knowledge for `R` with soundness error
 `1 - 1/p(|x|) + 2^{-p(|x|)}`, and its `n|E|`-fold repetition is an interactive proof with
 efficient prover (`zk_proof_of_levinReduction`, with `hLR` from `WitnessRelation.mem_iff`).
+The Levin reduction `LevinReduction L L3COL R R3COL f w p` is part of the conclusion (ruling
+R-03e-r2-1 of gate 03e round 2), so further protocols can be pulled back along the same maps.
 
 **Deviation (DQ5):** as for `zk_proof_of_levinReduction`. -/
 theorem zk_proof_of_witnessRelation (h3 : LevinNPHard L3COL R3COL)
     {Com : List Bool → List Bool} {ℓ : PolyExpr} (hC : Commitment Com ℓ) {L : Language Bool}
     {R : List Bool → List Bool → Prop} (hR : WitnessRelation L R) :
     ∃ (f : List Bool → List Bool) (w : List Bool → List Bool → List Bool) (p : PolyExpr),
-      (∀ N, N ≤ p.eval N) ∧
+      LevinReduction L L3COL R R3COL f w p ∧ (∀ N, N ≤ p.eval N) ∧
       EfficientProverProof ((colProtocolRep Com ℓ).pullback f w p) L R ∧
       ZK ((colProtocol Com ℓ).pullback f w p) R ∧
       EfficientProverProofErr ((colProtocol Com ℓ).pullback f w p) L R
         (fun N => 1 - 1 / (p.eval N : ℝ) + (1 / 2 : ℝ) ^ p.eval N) := by
   obtain ⟨f, w, p, h⟩ := h3 L R hR
-  exact ⟨f, w, p, h.le_eval, zk_proof_of_levinReduction hC h fun x hx => (hR.mem_iff x).1 hx⟩
+  exact ⟨f, w, p, h, h.le_eval, zk_proof_of_levinReduction hC h fun x hx => (hR.mem_iff x).1 hx⟩
 
 /-- **[PS10, Theorem 124.1], "if one-way permutations exist then every language in NP has a
 zero-knowledge proof", for every witness relation** (Thm-124.1; gate 03e, minors 3 and 4):
 from the text's hypothesis, a one-way permutation, there is a commitment scheme
-(`exists_commitment_of_owp`) for which the conclusion of `zk_proof_of_witnessRelation` holds,
-under NP-hardness of `3COL` with Levin reductions.
+(`exists_commitment_of_owp`) for which the conclusion of `zk_proof_of_witnessRelation` holds
+(the Levin reduction included), under NP-hardness of `3COL` with Levin reductions.
 
 **Deviation (DQ5):** as for `zk_proof_of_levinReduction`. -/
 theorem zk_proof_of_witnessRelation_of_owp (h3 : LevinNPHard L3COL R3COL)
@@ -700,7 +703,7 @@ theorem zk_proof_of_witnessRelation_of_owp (h3 : LevinNPHard L3COL R3COL)
     {R : List Bool → List Bool → Prop} (hR : WitnessRelation L R) :
     ∃ (Com : List Bool → List Bool) (ℓ : PolyExpr), Commitment Com ℓ ∧
       ∃ (f : List Bool → List Bool) (w : List Bool → List Bool → List Bool) (p : PolyExpr),
-        (∀ N, N ≤ p.eval N) ∧
+        LevinReduction L L3COL R R3COL f w p ∧ (∀ N, N ≤ p.eval N) ∧
         EfficientProverProof ((colProtocolRep Com ℓ).pullback f w p) L R ∧
         ZK ((colProtocol Com ℓ).pullback f w p) R ∧
         EfficientProverProofErr ((colProtocol Com ℓ).pullback f w p) L R
@@ -734,7 +737,7 @@ theorem zk_proof_of_mem_NP (h3 : LevinNPHard L3COL R3COL) {Com : List Bool → L
         EfficientProverProofErr π L R
           (fun N => 1 - 1 / (p.eval N : ℝ) + (1 / 2 : ℝ) ^ p.eval N) := by
   obtain ⟨R, hR⟩ := exists_witnessRelation_of_mem_NP hL
-  obtain ⟨_, _, p, hp, h1, h2, h3'⟩ := zk_proof_of_witnessRelation h3 hC hR
+  obtain ⟨_, _, p, -, hp, h1, h2, h3'⟩ := zk_proof_of_witnessRelation h3 hC hR
   exact ⟨R, hR, ⟨_, h1⟩, _, p, hp, h2, h3'⟩
 
 /-- **[PS10, Theorem 124.1], "if one-way permutations exist then every language in NP has a
diff --git a/TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Language.lean b/TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Language.lean
index 0d3c8409..8e77b389 100644
--- a/TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Language.lean
+++ b/TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Language.lean
@@ -301,8 +301,9 @@ noncomputable def samplePerm3 (T : ℕ) (r : List Bool) : Equiv.Perm (Fin 3) :=
   ((sampleIdx 6 3 T r).map perm3Equiv).getD 1
 
 /-- The verifier's random edge `e ← E` of [PS10, Protocol 127.5] as an index in `[m]`: `T`
-rejection trials of `Nat.size m` bits (so that `m ≤ 2^k < 2m`, success probability `≥ 1/2`),
-the index `0` on failure (D10). -/
+rejection trials of `k = Nat.size m` bits (for `m > 0`, `m < 2^k ≤ 2m`, so each trial succeeds
+with probability `≥ 1/2`; for `m = 0` the sampler returns the default), the index `0` on
+failure (D10). -/
 def sampleEdgeIdx (m T : ℕ) (r : List Bool) : ℕ :=
   ((sampleIdx m (Nat.size m) T r).map Fin.val).getD 0
 
diff --git a/TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean b/TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean
index e8cb2fe1..84e5e0a0 100644
--- a/TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean
+++ b/TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean
@@ -495,8 +495,9 @@ noncomputable def colVerifierRep (Com : List Bool → List Bool) (ℓ : PolyExpr
     else []
 
 /-- The `n|E|`-fold protocol of [PS10, Protocol 127.5] (Prot-127.5): prover first, four moves
-per iteration (commitments, edge, openings, empty verifier message; D8 fixed alternation),
-`4|x|²` moves in all, of which the first `4 n|E|` carry the iterations. -/
+per iteration (commitments, edge, openings, and a verifier message, empty except for the final
+verdict; D8 fixed alternation), `4|x|²` moves in all, of which the first `4 n|E|` carry the
+iterations. -/
 noncomputable def colProtocolRep (Com : List Bool → List Bool) (ℓ : PolyExpr) : Protocol where
   P := colProverRep Com ℓ
   V := colVerifierRep Com ℓ
@@ -607,7 +608,8 @@ theorem colProtocol_proverBounded {Com : List Bool → List Bool} {ℓ : PolyExp
     ∃ B : PolyExpr, (colProtocol Com ℓ).ProverBounded R B ∧
       (colProtocolRep Com ℓ).ProverBounded R B := by
   obtain ⟨B, hB⟩ := colProver_length_le hC.easy ℓ
-  refine ⟨B, fun x y r hist _ => hB x y r hist, fun x y r hist _ => ?_⟩
+  refine ⟨B, (Protocol.proverBounded_iff _ _ _).2 fun x y r hist _ => hB x y r hist,
+    (Protocol.proverBounded_iff _ _ _).2 fun x y r hist _ => ?_⟩
   show ((colProverRep Com ℓ).next x y r hist).length ≤ B.eval x.length
   simp only [colProverRep]
   split_ifs <;> first | exact hB _ _ _ _ | exact Nat.zero_le _
@@ -878,7 +880,8 @@ theorem col_efficientProverProofErr {Com : List Bool → List Bool} {ℓ : PolyE
     obtain ⟨B, hB, -⟩ := colProtocol_proverBounded hC R3COL
     refine ⟨B, fun x hx => ?_⟩
     obtain ⟨y, n, G, c, rfl, rfl, hc⟩ := (mem_L3COL_iff x).1 hx
-    exact ⟨encColoring c, fun r hist => hB _ _ r hist ⟨n, G, c, rfl, rfl, hc⟩,
+    exact ⟨encColoring c,
+      fun r hist => (Protocol.proverBounded_iff _ _ _).1 hB _ _ r hist ⟨n, G, c, rfl, rfl, hc⟩,
       fun z => HardcoreBit.uprob_eq_one_of_forall fun r => colProtocol_outV_honest hc z r⟩
   sound := fun x hx P' z => colProtocol_sound hC x hx P' z
   efficientP := colProver_efficient hC.easy ℓ
diff --git a/TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Simulator.lean b/TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Simulator.lean
index c233cc12..955948e3 100644
--- a/TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Simulator.lean
+++ b/TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Simulator.lean
@@ -31,9 +31,10 @@ the distinct colour pairs, the commitment randomness `Fin n → Fin ℓ(n) → B
 `ρ` of an arbitrary verifier `V*` given as its reply function); the *string* layer is the
 simulator `colSim` run by a uniform `NUPPT` on the tape layout of `colSimBlock`.
 
-**Deviations** (D8, D10, source errors 42 and 46 of the plan): the simulator is strict PPT,
-truncated at `n|E|` attempts and outputting `⊥ = []` on failure, which costs the statistical
-term `(1 - 1/|E|)^{n|E|} ≤ e^{-n}`; `e'`, the colour pair and the honest prover's `π` are
+**Deviations** (D8, D10, source errors 42 and 46 of the plan): the simulator is strict PPT
+(D8's definition of `ZK`); it makes at most `n|E|` attempts and outputs `⊥ = []` on failure, as
+the text does (Algorithm 128.7, steps 4–5), and the failure costs the text's own term
+`(1 − 1/|E|)^{n|E|} ≤ e^{-n}`; `e'`, the colour pair and the honest prover's `π` are
 rejection-sampled from the bit tapes; the hybrid over attempts has `n|E|` steps (the text says
 `2n|E|`) and the text's `6|E|` sub-hybrid is replaced by a non-uniform choice of the worst
 `(e', π)`; "`k ∈ [m] ∖ {i', j'}`" is read as `k ∈ [n]`; if `E = ∅` the simulator commits to
@@ -318,9 +319,9 @@ theorem uprob_colSimAttemptH_some [Fintype ρ] (hm : 0 < edgeCount G)
     (fun a => edgeIdxOfMsg_lt hm _) (fun a => T (colRealView Com ℓn G c V a))
 
 /-- **The truncated `S''` fails with probability `(1 - 1/|E|)^N`** [PS10, proof of Proposition
-128.8, "`S''` fails with probability `(1 - 1/|E|)^{n|E|}`"] (Claim-129.c): the attempts use
-disjoint coins (`OneWay.uprob_pi_forall`) and each fails with probability `1 - 1/|E|`
-(`uprob_colSimAttemptH_none`). -/
+128.8, "`S'` [sic: `S''`] fails with probability `(1 - 1/|E|)^{n|E|}`"] (Claim-129.c): the
+attempts use disjoint coins (`OneWay.uprob_pi_forall`) and each fails with probability
+`1 - 1/|E|` (`uprob_colSimAttemptH_none`). -/
 theorem uprob_colSimTruncH_none [Fintype ρ] [Nonempty ρ] (hm : 0 < edgeCount G)
     (c : Fin n → Fin 3) (V : List Bool → ρ → List Bool) (N : ℕ) :
     uprob (fun w => colSimTruncH Com ℓn G c V N w = none) = (1 - 1 / (edgeCount G : ℝ)) ^ N := by
@@ -633,8 +634,9 @@ noncomputable def colSimAttemptStr (Com : List Bool → List Bool) (ℓ : PolyEx
 the consecutive coin blocks of the tape `r`, the first successful attempt's view, or `⊥ = []`
 after `n|E|` failures; a single attempt if `E = ∅`.
 
-**Deviation (D8):** truncated at `n|E|` attempts (strict PPT) instead of restarting until
-success. -/
+As in [PS10, Algorithm 128.7, steps 4–5], at most `n|E|` attempts, then `fail` (`⊥ = []`).
+**Deviation (D10):** `e'` and the colour pair are rejection-sampled from the tape (defaults `0`
+and `(0, 1)`). -/
 noncomputable def colSim (Com : List Bool → List Bool) (ℓ : PolyExpr) (V' : Strategy)
     (x z r : List Bool) : List Bool :=
   let B := (colSimBlock ℓ V').eval x.length
@@ -676,9 +678,10 @@ theorem exists_colSimulator {Com : List Bool → List Bool} (hCom : PolyTimeComp
 commitment's hiding error `ε(n)` at the vertex count `n = √|x|` into a function of `|x|`,
 Inf-4.4).
 
-**Proof sketch.** Given `c`, take `n₀` from `hμ (2c + 1)` and `N ≥ max ((n₀ + 1)², 4^c · 4)`:
-`n := Nat.sqrt N ≥ n₀` (`Nat.le_sqrt`) and `N < (n + 1)² ≤ 4n²` (`Nat.lt_succ_sqrt`), so
-`N^c ≤ 4^c n^{2c} ≤ n^{2c+1}` once `n ≥ 4^c`, whence `|μ n| < 1/n^{2c+1} ≤ 1/N^c`. -/
+**Proof sketch.** Given `c`, take `n₀` from `hμ (2c + 1)`, `K := max (n₀, 4^c, 1)` and `N ≥ K²`:
+`n := Nat.sqrt N ≥ K` (`Nat.le_sqrt`), so `n ≥ n₀`, `n ≥ 4^c`, `n ≥ 1`, and
+`N < (n + 1)² ≤ 4n²` (`Nat.lt_succ_sqrt`); hence `N^c ≤ 4^c n^{2c} ≤ n^{2c+1}` and
+`|μ n| < 1/n^{2c+1} ≤ 1/N^c`. -/
 theorem Negligible.comp_sqrt {μ : ℕ → ℝ} (hμ : Negligible μ) :
     Negligible fun N => μ (Nat.sqrt N) := by
   intro c
@@ -719,48 +722,59 @@ there is a negligible `ε` with, for all `x`, witnesses `y` and `z` with `|z| 
 advantage of `D` between the view of `V'` in `P(x, y) ↔ V'(x, z)` and `S(x, z)` at most
 `ε(|x|)`.
 
-**Deviation (D8, D10):** strict PPT simulator truncated at `n|E|` attempts, rejection-sampled
+**Deviation (D8, D10):** strict PPT simulator (D8's definition of `ZK`), rejection-sampled
 `π`, `e'` and colour pairs; the error bound is in `|x|` (the text's `e(n)` with `n`
 undefined); one iteration (the `n|E|`-fold protocol's zero-knowledge is sequential
 composition, [PS10, §7.2.1], out of scope).
 
-**Proof sketch.** Fix `V'` efficient and take `S` from `exists_colSimulator hC.easy`. Fix
-`Lz` and `D`. Let `B` be the hiding reduction machine of Claim-129.d (`colSimRed` at the
-string level): at parameter `n` it carries in its advice the worst instance
-`(x_n, y_n, z_n)` with `|x_n| = n²`, `|y_n| = 2n`, `|z_n| ≤ Lz(n²)` (`NUPPT.exists_withAdvice`
-with the polynomial bound `add (add (mul var var) (mul (const 2) var)) (Lz.subst (mul var var))`),
-the hybrid index `k_n`, `e₀`, `π₀` and `D.advice n²`; its coins are the other attempts' blocks
-and `D`'s coins (`NUPPT.exists_split`); it runs `V'`'s machine and `D`'s machine
-(`NUPPT.exists_seq`, `NUPPT.exists_comp`, `polyTimeComputable_iterateFind` for the attempts,
-`polyTimeComputable_blockMap ℓ` with `hC.easy` for the commitments, `msgAt` projections by
-`polyTimeComputable_iterate_pairFstD`). `hC.multiHiding var B` gives a negligible `ε_B` with
-`distAdv (multiCom Com v ·) (multiCom Com v' ·) (B.distinguisherL n) ≤ ε_B n` for all `n`-vectors
-`v, v'`. Put
-`ε N := N · ε_B (Nat.sqrt N) + Real.exp (-(Nat.sqrt N)) + 2 N² (1/4)^N + N² (1/2)^N + (1/4)^N`,
+**Proof sketch.** Fix `V'` efficient, take `S` from `exists_colSimulator hC.easy`, and fix `Lz`
+and `D`. For `x = encGraph G`, `y = encColoring c` with `c` proper and `|z| ≤ Lz |x|`, let `n` be
+the vertex count, `m = |E|`, `K = n m ≤ n³`, and `D'` the distinguisher `D.distinguisherL |x|`
+on the encoded optional view (`⊥ ↦ []`).
+
+(1) The real view, with `π = samplePerm3 |x| …`, is within `(1/4)^{|x|}` of the view with a
+uniform `π`: `statClose_samplePerm3`, `StatClose.prod`/`StatClose.refl` for the prover's
+randomness and `V'`'s tape, and `StatClose.map`. `exec_succ` three times, `decGraph_encGraph`,
+`decColoring_encColoring`, and `colProver` with `V com r_V := V'.next x z r_V [com]` unfold it to
+`some ∘ colRealView`.
+
+If `m > 0`:
+(2) `colSim` is within `K((1/2)^{|x|} + (1/4)^{|x|})` of `colSimTrunc … K`, with uniform
+`(e'_t, (a_t, b_t))` read from disjoint fields of the `t`-th block (`statClose_sampleEdgeIdx`,
+`statClose_sampleColorPair` — the colour-pair analogue of `statClose_samplePerm3`, still to be
+added: the fill ladder's first step, gate 03g review M3 — and `StatClose.prod` over the blocks).
+(3) `uprob_colSimTruncW_eq`.
+(4) `exists_colSimRed_ge` with `N := K` gives `k, e₀, π₀` with
+`distAdv truncW truncH D' ≤ K · distAdv X Y (colSimRed … k e₀ π₀ D')`.
+`CommitmentLemmas.exists_fixCoins` fixes the reduction's attempt table `w₀` without loss.
+With `w₀` fixed, only attempt `k` reads the challenge `cv`, so the fixed reduction is
+`cv ↦ D'(pre <|> planted cv <|> post)` for two constant optional views.
+(5) `statClose_colSimTruncH` and `one_sub_inv_pow_mul_le_exp` give
+`distAdv truncH (some ∘ colRealView) D' ≤ e^{−n}`.
+
+If `m = 0` and `n ≥ 1`, the two views differ only in the commitment vector (`π ∘ c` against
+`0`). For each fixed `π`, `D`'s advantage is the hiding gap of
+`cv ↦ D(encode ⟨x, z, r_V, [cv, []]⟩)`, with `r_V` fixed by `exists_fixCoins`. Average over `π`.
+If `n = 0`, bound the advantage by `1`: the simulator's tape is empty, so its `r_V = []` differs
+from the real tape when `V'.coinLen 0 > 0`.
+
+The machine `B` at parameter `n`: among the finitely many data at vertex count `n` (finite
+because `|z| ≤ Lz(n²)`: this is where the bound `Lz` is used, see the `Defs.lean` module
+docstring), take those whose fixed reduction (either case) has the largest gap on its own
+vectors. Hard-wire `x`, `z`, the case, `ρ_k`, `e₀`, the two endpoint commitments and openings,
+`pre`, `post` and `D.advice (n²)` as advice (`NUPPT.exists_withAdvice`; polynomially bounded by
+`hC.easy.output_length_le` and `colProtocol_proverBounded`). Call `V'`'s uniform machine once
+(`Strategy.Efficient`) and `D` at parameter `n²` on `B`'s coins (`NUPPT.exists_reparam_advice`,
+`φ n = n²`). Its acceptance probabilities on `multiCom` samples are the fixed reduction's (coin
+transport along `finCongr`). `hC.multiHiding var B` gives a negligible `ε_B ≥ 0` (it bounds a
+`distAdv` at every `n`), so the hiding terms are at most
+`K ε_B n ≤ n³ ε_B n ≤ |x|² ε_B (Nat.sqrt |x|)` for `n ≥ 1`.
+
+Put `ε N := N² ε_B (Nat.sqrt N) + exp (−Nat.sqrt N) + N² ((1/2)^N + (1/4)^N) + (1/4)^N`. It is
 negligible by `Negligible.comp_sqrt`, `Negligible.mul_pow`, `negligible_exp_neg_sqrt_div`
-(`C = 1`), `negligible_two_pow_neg` (with `(1/4)^N ≤ (1/2)^N`), `Negligible.add`,
-`Negligible.const_mul`. Now fix `x = encGraph G`, `y = encColoring c` with `c` proper
-(`R3COL`), `|z| ≤ Lz |x|`, `n` the vertex count, `m = |E|`. If `m = 0` the real view is
-`⟨⟨x,z⟩,⟨r_V,[colCommit (π ∘ c) r, []]⟩⟩` and the simulated one has the all-zero colours, so
-`D`'s advantage is at most `ε_B n` by `hC.multiHiding` applied to a machine `B'` built like
-`B` (absorbed into `B` by a case split on `m` in its advice). Otherwise `n ≥ 2` and the chain is:
-(1) the real view with `π = samplePerm3 |x| …` is within `(1/4)^{|x|}` of the view with a
-uniform `π` (`statClose_samplePerm3`, `StatClose.prod` with `StatClose.refl` for the
-randomness and `V'`'s tape, `StatClose.map` by the view encoding; `exec_succ` three times,
-`decGraph_encGraph`, `decColoring_encColoring`, `colProver`/`colVerifier` unfold to
-`colRealView` with `V com r_V := V'.next x z r_V [com]`); (2) `colSim` is `(Option.map enc
-(colSimTrunc … (n m) w)).getD []` with the `t`-th attempt's coins read from the `t`-th block
-(`colCoinSlice`, `colSimBlock`), within `n m ((1/2)^{|x|} + (1/4)^{|x|})` of the same with
-uniform `(e'_t, (a_t, b_t))` (`statClose_sampleEdgeIdx`, the colour-pair analogue of
-`statClose_samplePerm3`, `StatClose.prod` over the blocks); (3) `uprob_colSimTruncW_eq` makes
-that the law of `colSimTruncW`; (4) `exists_colSimRed_ge` with `N := n m` gives `k, e₀, π₀`
-with `distAdv (truncW) (truncH) D' ≤ n m · distAdv (X) (Y) (colSimRed …)`, and
-`colSimRed … = B.distinguisherL n` up to the coin bijection (`acceptProb_comp_equiv`), so
-`≤ n m ε_B n ≤ |x| ε_B (Nat.sqrt |x|)`; (5) `statClose_colSimTruncH` and
-`one_sub_inv_pow_mul_le_exp` give `distAdv (truncH) (some ∘ colRealView) D' ≤ e^{-n}`
-(`distAdv_le_of_statClose`). The triangle inequality for `distAdv` (`abs_sub_le` on the
-acceptance probabilities) sums the five terms, and `Nat.sqrt |x| = n` (`length_encGraph`,
-`Nat.sqrt_eq`). -/
+(`C = 1`), `negligible_two_pow_neg` and `Negligible.add`. At `N = 0` its exponential term is
+`1`. Use the triangle inequality for `distAdv` (`abs_sub_le`), and `Nat.sqrt |x| = n`
+(`length_encGraph`, `Nat.sqrt_eq`). -/
 theorem col_zk {Com : List Bool → List Bool} {ℓ : PolyExpr} (hC : Commitment Com ℓ) :
     ZK (colProtocol Com ℓ) R3COL := by
   sorry
diff --git a/audits/pass-shelat/Checks.lean b/audits/pass-shelat/Checks.lean
index 61fb0276..f6e3c056 100644
--- a/audits/pass-shelat/Checks.lean
+++ b/audits/pass-shelat/Checks.lean
@@ -423,6 +423,8 @@ results must print exactly `[propext, Classical.choice, Quot.sound]`.
 #print axioms TCSlib.Cryptography.Commitment.multiHiding
 -- Ruling G3-3: bounded honest prover messages in the proof systems.
 #print axioms TCSlib.Cryptography.Protocol.ProverBounded.mono
+-- Round 2, finding 2: the reading lemma of `Protocol.ProverBounded`.
+#print axioms TCSlib.Cryptography.Protocol.proverBounded_iff
 #print axioms TCSlib.Cryptography.Protocol.ProverBounded.exists_complete
 #print axioms TCSlib.Cryptography.Protocol.ProverBounded.pullback
 #print axioms TCSlib.Cryptography.InteractiveProof.exists_accept
@@ -439,6 +441,11 @@ results must print exactly `[propext, Classical.choice, Quot.sound]`.
 -- Ruling G3-4: perfect zero-knowledge with abort implies statistical ZK (error 2^{-|x|}).
 #print axioms TCSlib.Cryptography.AbortRetry.statClose_retry
 #print axioms TCSlib.Cryptography.AbortRetry.exists_retrySimulator
+-- Round 2, finding 2: the reading lemmas of `AbortRetry.attempt` and `AbortRetry.retry`.
+#print axioms TCSlib.Cryptography.AbortRetry.attempt_eq
+#print axioms TCSlib.Cryptography.AbortRetry.retry_eq
+#print axioms TCSlib.Cryptography.AbortRetry.retry_eq_attempt
+#print axioms TCSlib.Cryptography.AbortRetry.retry_eq_nil
 #print axioms TCSlib.Cryptography.PerfectZKAbort.statZK
 #print axioms TCSlib.Cryptography.PerfectZKAbort.zk
 #print axioms TCSlib.Cryptography.perfectZK_zeroRounds
diff --git a/machine-library-design.md b/machine-library-design.md
index 1dea9731..52be0e2d 100644
--- a/machine-library-design.md
+++ b/machine-library-design.md
@@ -3087,7 +3087,7 @@ and a statement gate before a second consumer is briefed.
 | H11 | **Indexed input access** (ours, `SpaceComplexity/Logspace/`): the input bit and length languages `inputBitLang`/`inputLenLang` read by an oracle call on a register-held index (their answers `indicator_inputBitLang`/`indicator_inputLenLang`), the stride decoder `boundedDecodeStride_loop` (with `boundedDecode_loop` its stride-one instance), the increment/decrement chain `arm_chain`, and the preimage host (`PreimageHost.compile_decides`, `mem_LOGSPACE_preimage`) | **existing (2026-10-11), public; now a host with received consumers.** The response proposes it stay under `Logspace/` (addendum 1). D7 and `decChain` were done in the payback (PR #101, landed 2026-10-15): `Codec/Engine`'s `decodeStride_loop` and `incChain`/`decChain` are instances of `boundedDecodeStride_loop` and `arm_chain` | every received ARM customer through its decider bank; `Codec/Engine` (its decoder and chains are instances); `PathHardRegs` (`mem_LOGSPACE_preimage` for `dropIdx`); `ARMLoops`, `NARMKit`, `VWord`, `ARMWidthExample` (direct importers) |
 | H12 | **Code reachability with a growing window (`ExpBFS`)**: the reachable-code sets `RCode`/`rset` per radius, the stop rule (`mem_iff_of_card_eq`, `card_rset_succ_of_le`), the window lemma `inWin_runWith_of_decides`, and the breadth-first MARM search giving `NSPACE_subset_exp_dtime_of_le` | **received 2026-10-14; public, ungated; accepted exception.** Built at ARM level, so H4's language-first route and MIG-19 are moot for this theorem | `NSPACE_subset_exp_dtime` (`ExpTime.lean`) and its two corollaries; inductive counting (H13b) uses the stop rule (`ISCountGenRadius` directly, `ISCountGenCorrect` transitively) |
 | H13 | **The customer machines**, each with its named consumers and its own reachability notion: (a) Savitch's midpoint recursion `SavitchARM` with its code-decider bank; (b) inductive counting `ISCount*`; (c) the PATH walk `PathWalk*` with `WalkLe`; (d) PATH hardness `PathHard*` (the code graph `red`); (e) the TQBF walk `TQBFARM`; (f) TQBF hardness `TQBFHard*` (the ∀-folded midpoint formula and Tseitin after the prefix) | **received 2026-10-14; public, ungated; accepted exception.** (a)–(e) are machines over H7–H10; (f) is a reduction over H10 and the polynomial-time closure algebra | (a) `PSPACE_eq_NPSPACE`; (b) `compl_PATH_mem_NL`, `NL_eq_coNL`, `NSPACE_compl_eq`; (c) `PATH_mem_NL`; (d) `PATH_NLComplete`; (e) `TQBF_mem_PSPACE`; (f) `TQBF_PSPACEHard`, `TQBF_PSPACEComplete`. Second uses inside the delivery: (b) uses (a)'s decider bank and H12's stop rule; (b) and (d) use (c)'s `WalkLe` and `rawEdge` |
-| H14 | **Clean-module host** (`TuringMachine/Build/ModuleHost.lean`, namespace `Turing.ModuleHost`): the first-halting clean-module contract `Clean` (a module with a work tape halts first, at a positive time within a budget of its argument's length, at the seam holding a result word, having emitted a declared chunk), the clean install and emit modules of every polynomial-time word function (`clean_install`, `clean_emit`), and the finite host `hostTM` running `n` such modules over a shared bank of work tapes, generic in the modules, the control states and their table, the return map and the start state (`host_call`, `host_clean`, `guard_add`, `hostTM_step_inl`) | **public; harvested 2026-11-05 (gate 03l, R-03l-1); contract gated at gate 03l's delta round.** Harvested from the private module layer of `ClassNP/SAT.lean` (on `main`) and its copy in `Randomized/Build/IterateFindHost.lean` (duplication ledger DL-16); both copies are deleted. The copier `copyTM` of `IterateFindHost` re-derives the private input copier of `TuringMachine/Build/EmitIterBody.lean` (16 % line overlap, gate 03l review §6.1 (d)): a parallel routine, not a copy | `ClassNP/SAT.lean` (the streaming emitter behind `SAT_reducible_SAT3`: six modules, one control state); `Randomized/Build/IterateFind.lean`, through `Randomized/Build/IterateFindHost.lean` (the repetition machine behind `polyTimeComputable_iterateFind`: five modules, three control states) |
+| H14 | **Clean-module host** (`TuringMachine/Build/ModuleHost.lean`, namespace `Turing.ModuleHost`): the first-halting clean-module contract `Clean` (a module with a work tape halts first, at a positive time within a budget of its argument's length, at the seam holding a result word, having emitted a declared chunk), the clean install and emit modules of every polynomial-time word function (`clean_install`, `clean_emit`), and the finite host `hostTM` running `n` such modules over a shared bank of work tapes, generic in the modules, the control states and their table, the return map and the start state (`host_call`, `host_clean`, `guard_add`, `hostTM_step_inl`); head envelopes `Clean.envelope` (a clean module's heads stay within `B \|arg\|` cells of the origin at every time), `host_call_envelope` (within `t` cells up to time `t` of a call) and `host_clean_envelope` (`host_clean` with the envelope `B \|arg\|` throughout the call), the coarse envelopes from the time bounds and the unit head moves of `Turing.MultiTapeTM.workTapePos_step_le` | **public; harvested 2026-11-05 (gate 03l, R-03l-1); contract gated at gate 03l's delta round; head-envelope clauses added 2026-11-06 (gate 03l round 2, finding 1).** Harvested from the private module layer of `ClassNP/SAT.lean` (on `main`) and its copy in `Randomized/Build/IterateFindHost.lean` (duplication ledger DL-16); both copies are deleted. The copier `copyTM` of `IterateFindHost` re-derives the private input copier of `TuringMachine/Build/EmitIterBody.lean` (16 % line overlap, gate 03l review §6.1 (d)): a parallel routine, not a copy | `ClassNP/SAT.lean` (the streaming emitter behind `SAT_reducible_SAT3`: six modules, one control state); `Randomized/Build/IterateFind.lean`, through `Randomized/Build/IterateFindHost.lean` (the repetition machine behind `polyTimeComputable_iterateFind`: five modules, three control states) |
 
 **The received ARM machinery, H7–H13** (registered 2026-10-14: the ARM fill gate's round 2,
 finding 5; user decision 3). The rows' public contracts, with file and line, are in

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/evidence-repairs/03-batch/replay.log =====

# replay 2026-11-06T00:49:44Z HEAD=73751f5747d8c0a57aba9939cac8bb16f87ba2ba BASE=092083cd10be7a284db4e97fcf42eddb8296edf7 tree=/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad/g03batch-oleans; order=replay-order.txt (downstream2.py of the changed modules, DOWN, + audits/pass-shelat/Checks)
TCSlib/Complexity/TuringMachine/Build/ModuleHost rc=0 4s errors=0 sorry=0
TCSlib/Complexity/ClassNP/SAT rc=0 38s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/DAGCircuitSatLang rc=0 2s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/CircuitEvalNP rc=0 2s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/CircuitSatReductionValid rc=0 3s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/CircuitSatReduction rc=0 2s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/KarpLiptonPrefix rc=0 1s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/KarpLipton rc=0 5s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/KarpLiptonSearchFamily rc=0 13s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/UniformTableau rc=0 2s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/CircuitSatNPHard rc=0 2s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/LogspaceTableau rc=0 2s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/MeyerVerifierGlue rc=0 3s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/MeyerVerifier rc=0 4s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/MeyerSound rc=0 4s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/MeyerSoundInput rc=0 3s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/MeyerComplete rc=0 4s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/MeyerSigma rc=0 3s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity/Meyer rc=0 7s errors=0 sorry=0
TCSlib/Complexity/CircuitComplexity rc=0 2s errors=0 sorry=0
TCSlib/Complexity/CookLevin/Hardness rc=0 385s errors=0 sorry=0
TCSlib/Complexity/ClassNP/Tautology rc=0 10s errors=0 sorry=0
TCSlib/Complexity/ClassNP rc=0 1s errors=0 sorry=0
TCSlib/Complexity/ClassOracle/SATOracle rc=0 2s errors=0 sorry=0
TCSlib/Complexity/SpaceComplexity/Inclusions rc=0 29s errors=0 sorry=0
TCSlib/Complexity/ClassPSPACE/TQBFHard rc=0 12s errors=0 sorry=0
TCSlib/Complexity/ClassPSPACE/TQBF rc=0 28s errors=0 sorry=21
TCSlib/Complexity/Randomized/Inclusions rc=0 6s errors=0 sorry=0
TCSlib/Complexity/Randomized/Reductions rc=0 4s errors=0 sorry=0
TCSlib/Complexity/Randomized/PTMEquiv rc=0 3s errors=0 sorry=0
TCSlib/Complexity/Randomized/BPOperator rc=0 2s errors=0 sorry=0
TCSlib/Complexity/Randomized/BPPAmplify rc=0 6s errors=0 sorry=0
TCSlib/Complexity/Randomized/BPTIMEThreshold rc=0 4s errors=0 sorry=0
TCSlib/Complexity/Randomized/BiasedCoin rc=0 3s errors=0 sorry=0
TCSlib/Complexity/Randomized/BiasedCoinHalting rc=0 13s errors=0 sorry=0
TCSlib/Complexity/Randomized/Build/IterateFindHost rc=0 3s errors=0 sorry=0
TCSlib/Complexity/Randomized/Build/IterateFind rc=0 5s errors=0 sorry=0
TCSlib/Complexity/Randomized/Primality rc=0 4s errors=0 sorry=0
TCSlib/Complexity/Randomized/Matching rc=0 8s errors=0 sorry=0
TCSlib/Complexity/Randomized/NPPoly rc=0 8s errors=0 sorry=0
TCSlib/Complexity/Randomized/RPExpected rc=0 3s errors=0 sorry=0
TCSlib/Complexity/Randomized/Repetition rc=0 3s errors=0 sorry=0
TCSlib/Complexity/Randomized/Yap rc=0 6s errors=0 sorry=0
TCSlib/Complexity/Randomized/ZPPEquiv rc=0 3s errors=0 sorry=0
TCSlib/Complexity/Randomized/ZPPHosts rc=0 3s errors=0 sorry=0
TCSlib/Complexity/Randomized/ZPPHostsClasses rc=0 45s errors=0 sorry=0
TCSlib/Complexity/Randomized/ZeroP rc=0 6s errors=0 sorry=0
TCSlib/Complexity/Randomized/ZeroPPIT rc=0 4s errors=0 sorry=0
TCSlib/Complexity/Randomized/ZeroPReduce rc=0 4s errors=0 sorry=0
TCSlib/Complexity/TuringMachine rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/EnsemblesLemmas rc=0 7s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/Ensembles rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/OneWayLemmas rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/OneWayYao rc=0 71s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/OneWay rc=0 12s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/CollectionsLemmas rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/Collections rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/UniversalLemmas rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/UniversalPadding rc=0 5s errors=0 sorry=1
TCSlib/Cryptography/Asymptotic/Universal rc=0 6s errors=0 sorry=1
TCSlib/Cryptography/Asymptotic/Pseudorandom rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/NextBit rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCoreLemmas rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCoreLoops rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCoreGL rc=0 10s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCoreGLColl rc=0 7s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCoreCollection rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCoreGLFamily rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCore rc=0 6s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCoreClaims rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCorePermutation rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/Encryption rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/PRFLemmas rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/GGMReduction rc=0 42s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/GGMReductionEval rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/PRF rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/MultiMessageLemmas rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/MultiMessage rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/BlockEncryptor rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/PublicKeyLemmas rc=0 71s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/PublicKey rc=0 23s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/NumberTheory/Chebyshev rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/NumberTheory/Primality rc=0 6s errors=0 sorry=0
TCSlib/Cryptography/Candidates/Arithmetic rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/Candidates/Concrete rc=0 4s errors=0 sorry=1
TCSlib/Cryptography/Candidates/Factoring rc=0 4s errors=0 sorry=8
TCSlib/Cryptography/Candidates/RSA rc=0 8s errors=0 sorry=9
TCSlib/Cryptography/Candidates/Rabin rc=0 7s errors=0 sorry=19
TCSlib/Cryptography/Candidates/DiscreteLog rc=0 4s errors=0 sorry=6
TCSlib/Cryptography/Candidates/DiscreteLogHardcore rc=0 3s errors=0 sorry=7
TCSlib/Cryptography/Candidates/ElGamal rc=0 4s errors=0 sorry=7
TCSlib/Cryptography/Candidates rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/NumberTheory rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/EncodingMachines rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/EncodingPermutations rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/Encoding rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/Interaction rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/InteractiveProofs rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/Defs rc=0 7s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Proofs rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Efficiency rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/EfficiencyRep rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/EfficiencyRepGI rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Soundness rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Concrete rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRep rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRepGI rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphismZK/Simulator rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphismZK/Closeness rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphismZK rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/CommitmentLemmas rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/Commitment rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Language rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Machines rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Parties rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/ProtocolProofs rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol rc=0 6s errors=0 sorry=2
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/SimulatorLemmas rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/SimulatorNumeric rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/SimulatorMachine rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Simulator rc=0 4s errors=0 sorry=1
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/NPLemmas rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/NP rc=0 11s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/Encryption rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge rc=0 2s errors=0 sorry=0
audits/pass-shelat/Checks rc=0 125s errors=0 sorry=0
# done 2026-11-06T01:12:45Z

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/evidence-repairs/03-batch/axioms.log =====

# Axiom prints, gate 03 repair batch, HEAD 73751f5747d8c0a57aba9939cac8bb16f87ba2ba, tree /tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad/g03batch-oleans (after replay.log)
# Input: axrun/all.lean, generated by g03l-ax/axgen.py over every changed .lean file (changed-lean.txt): 549 #print lines (548 names).
# Base comparison: axrun/base.lean (the same list without the 10 new lemmas) against the untouched #203 tree g03l-oleans (read-only; #203 = BASE in Lean code), axrun/base.out.
# Item B's eight simps equations and the three envelope lemmas: axioms-03l.log.

## Comparison (axcmp.py)
HEAD prints: 548; base prints: 538
sorryAx at HEAD: 100 ; at base: 100
non-standard axioms other than sorryAx at HEAD: []
new names: 10
  NEW TCSlib.Cryptography.AbortRetry.attempt_eq ['Classical.choice', 'Quot.sound', 'propext']
  NEW TCSlib.Cryptography.AbortRetry.retry_eq ['Classical.choice', 'Quot.sound', 'propext']
  NEW TCSlib.Cryptography.AbortRetry.retry_eq_attempt ['Classical.choice', 'Quot.sound', 'propext']
  NEW TCSlib.Cryptography.AbortRetry.retry_eq_nil ['Classical.choice', 'Quot.sound', 'propext']
  NEW TCSlib.Cryptography.Candidates.rejectBlocksL_eq []
  NEW TCSlib.Cryptography.Candidates.sampleBelowL_eq_rejectBlocksL ['Quot.sound']
  NEW TCSlib.Cryptography.Protocol.proverBounded_iff ['propext']
  NEW Turing.ModuleHost.Clean.envelope ['Classical.choice', 'Quot.sound', 'propext']
  NEW Turing.ModuleHost.host_call_envelope ['Classical.choice', 'Quot.sound', 'propext']
  NEW Turing.ModuleHost.host_clean_envelope ['Classical.choice', 'Quot.sound', 'propext']
changed axiom sets: 0
missing at HEAD: []
TCSlib.Cryptography.zk_proof_of_witnessRelation ['Classical.choice', 'Quot.sound', 'propext', 'sorryAx']
TCSlib.Cryptography.zk_proof_of_witnessRelation_of_owp ['Classical.choice', 'Quot.sound', 'propext', 'sorryAx']

## HEAD output (axrun/all.out)
'Turing.ModuleHost.first_halt' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.ModuleHost.live_prefix' depends on axioms: [propext, Quot.sound]
'Turing.ModuleHost.clean_iff' depends on axioms: [propext, Quot.sound]
'Turing.ModuleHost.Clean.envelope' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.ModuleHost.clean_install' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.ModuleHost.clean_emit' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.ModuleHost.request_budget' depends on axioms: [propext, Quot.sound]
'Turing.ModuleHost.state_eq' depends on axioms: [propext, Quot.sound]
'Turing.ModuleHost.entry_eq' depends on axioms: [propext, Quot.sound]
'Turing.ModuleHost.hostTM_step_inl' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.ModuleHost.host_call' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.ModuleHost.host_call_envelope' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.ModuleHost.guard_add' depends on axioms: [propext, Quot.sound]
'Turing.ModuleHost.host_clean' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.ModuleHost.host_clean_envelope' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.FunFamily.invProbAt_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.FunFamily.invProbAt_le_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.FunFamily.invProbAt_eq_uprob' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.FunFamily.WorstCaseOneWay.toLit' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.FunFamily.WorstCaseOneWayLit.toParam' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.FunFamily.ofFn_ofString_f' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.FunFamily.ofString_id_f' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.FunFamily.blocks_symm_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.FunFamily.ofFn_blocks_symm' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.FunFamily.prod_inLen' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.FunFamily.prod_outLen' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.FunFamily.prod_f' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.FunFamily.invProbAt_prod_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.FunFamily.Easy.prod' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.eval_yaoBlocks' depends on axioms: [propext]
'TCSlib.Cryptography.eval_yaoRounds' depends on axioms: [propext]
'TCSlib.Cryptography.yaoBlocks_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.OneWay.invProb_prodFun_le_yaoTry' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.claim_38_2' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.weak_to_strong' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.strong_prod_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.FunFamily.StrongOneWay.weak' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.FunFamily.invProbAt_ofString_id_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.not_strongOneWay_id' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.not_weakOneWay_id' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.not_worstCaseOneWay_id' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.PermFamily.toFunFamily_f' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Candidates.uprob_and_eq_mul_subtype' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.one_sub_div_le_uprob_subtype' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.uprob_le_uprob_subtype_add' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.uprob_subtype_prod_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.uprob_diag' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.invProb_prodFun_le_plant' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.one_sub_one_div_pow_le_exp_neg' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.claim_36_2' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.exp_neg_le_half_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.claim_36_2_half_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.one_div_le_uprob_prime_pair_bits' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.primesPairEquiv_apply_val' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.one_div_card_primes_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.DistinctPrimes.p_prime' depends on axioms: [propext]
'TCSlib.Cryptography.Candidates.DistinctPrimes.q_prime' depends on axioms: [propext]
'TCSlib.Cryptography.Candidates.DistinctPrimes.p_lt' depends on axioms: [propext]
'TCSlib.Cryptography.Candidates.DistinctPrimes.q_lt' depends on axioms: [propext]
'TCSlib.Cryptography.Candidates.DistinctPrimes.p_ne_q' depends on axioms: [propext]
'TCSlib.Cryptography.Candidates.DistinctPrimes.mul_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.DistinctPrimes.totient_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.DistinctPrimes.one_lt_totient' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.DistinctPrimes.ext' depends on axioms: [propext]
'TCSlib.Cryptography.Candidates.DistinctPrimes.isEmpty_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.decodeDistinctPrimes_encode' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.encodeDistinctPrimes_of_decode' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.rejectBlocksL_eq' does not depend on any axioms
'TCSlib.Cryptography.Candidates.rejectBlocksL_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.statClose_rejectBlocksL' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.WellFormedIndex.dlW_eq' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Candidates.WellFormedIndex.length_eq' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Candidates.dlP_lt_two_pow' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Candidates.expOrd_of_valid' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.expOrd_of_not_valid' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.expOrd_le_two_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.val_lt_two_pow_dlW' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.coprime_dlG_dlP' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.coe_expUnit' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.orderOf_expUnit' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.expDec_expEnc' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.expEnc_of_expDec' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.expEval_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.polyTimeComputable_expEval' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.expF_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.ExpGroupGen.dlProb_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.ExpGroupGen.dlProb_le_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.ExpGroupGen.FullLength.fullLengthExcept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.ExpGroupGen.FullLength.exists_fullLengthExcept' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.expValid_dlDefaultIndex' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.expGenFun_poly' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.expGen_runAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.sampleBelowL_eq_rejectBlocksL' depends on axioms: [Quot.sound]
'TCSlib.Cryptography.Candidates.sampleBelowL_lt' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Candidates.statClose_sampleBelowL' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.polyTimeComputable_expSampleRaw' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.expSampler_runAt' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.expSampler_spec' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.expCollection_index' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.expCollection_index_of_lt' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.expCollection_D' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.expCollection_sampleClose' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.expCollection_invProbAt_le' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.expCollection_oneWay' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.SafePrimeValid.expValid' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.dlAssumption_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.dlCollection_index' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.dlCollection_oneWay' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.IsGenerator.orderOf_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.expo_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.expo_bijective' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.expo_dlog' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.dlog_expo' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.two_mul_half' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.neg_one_ne_one_units' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.pow_half_eq_neg_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.pow_mem_QR_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.sq_eq_pow_two_mul_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.neg_pow_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.dlLoop_succ' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.dlQueries_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.dlQueries_succ' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.dlLoop_eq_dlBits' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.dlBits_pow' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.uprob_trial_ge' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.uprob_majOracle_ne_le' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.invProb_shiftInverter_ge' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.invProb_dlInverter_ge' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.good_instances' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.FullGroupValid.expValid' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.fullDLCollection_oneWay' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.halfPred_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.halfStr_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.polyTimeComputable_halfStr' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.fullDLCollection_hardCore' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.safe_ne_two' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Candidates.five_le_safe' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Candidates.safe_half' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.card_QR_safe' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.mem_QR_iff_pow_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.orderOf_eq_of_mem_QR' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.zpowers_eq_QR' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.eq_QR_of_card' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.card_sqrt_safe' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.pushesUniform_sqTo_safe' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.uprob_sq_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.statClose_of_uprob_ne' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.statClose_sq_generator' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.eval_ddhLen' depends on axioms: [propext]
'TCSlib.Cryptography.Candidates.length_ddhTuple' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.ddhExpo_statClose' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.constSelector_runAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.GroupPKScheme.Secure.const' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.egUnit_pos' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Candidates.egUnit_lt' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Candidates.polyTimeComputable_egGenRaw' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.egGen_runAt' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.polyTimeComputable_egEncRaw' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.egEnc_runAt' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.polyTimeComputable_egDecStr' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.egDecStr_apply' depends on axioms: [propext, sorryAx, Quot.sound]
'TCSlib.Cryptography.Candidates.elGamal_correct' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.egSquareGen_valid' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.polyTimeComputable_egGroupGenRaw' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.egGroupGenMachine_runAt' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.egGroupGen_valid' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.egGroupGen_wellFormed' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.elGamal_secure' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.fmultNat_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.fmultNat_eq_mul_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.fmult_inLen' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.fmult_outLen' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.fmult_f' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.fmult_inv_factor' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.fmult_easy' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.modulusBits_eq_fmult' depends on axioms: [propext]
'TCSlib.Cryptography.Candidates.factorProb_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.factorProb_le_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.factorProb_eq_zero_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.coins_oneCallFactorer' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.oneCallFactorer_runAtL' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.eval_fmultWeakPoly' depends on axioms: [propext]
'TCSlib.Cryptography.Candidates.fmult_weakOneWay' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.eval_fmultBlocks' depends on axioms: [propext]
'TCSlib.Cryptography.Candidates.fmult_prod_inLen' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.exists_plantFactorer' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.fmult_prod_strongOneWay' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.samplePairOut_eq_encode' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.polyTimeComputable_samplePairRaw' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.factoringGen_runAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.factoringSampler_runAt' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.factoringSampler_spec' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.factoringCollection_index' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.factoringCollection_sampleClose' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.coins_collectionFactorer' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.collectionFactorer_runAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.factoringCollection_invProbAt_le' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.factoringCollection_oneWay' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.rsaProb_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rsaProb_le_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rsaProb_eq_zero_of_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rsaPerm_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rsaPerm_symm_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.pushesUniform_rsaPerm' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.mul_inv_val_modEq' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Candidates.rsaMod_of_valid' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rsaMod_of_not_valid' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rsaMod_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.val_lt_two_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rsaEval_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.polyTimeComputable_rsaEval' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rsaF_perm' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rsaDec_rsaEnc' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rsaEnc_of_rsaDec' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.sampleUnitL_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.RSAParams.N_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.RSAParams.e_lt_two_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.RSAParams.d_lt_two_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rsaN_indexOf' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rsaE_indexOf' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rsaValid_indexOf' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rsaMod_indexOf' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.polyTimeComputable_rsaGenRaw' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.rsaGen_runAt' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.polyTimeComputable_unitSampleStr' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.polyTimeComputable_rsaSampleRaw' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.polyTimeComputable_rsaInvRaw' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rsaInv_runAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rsaInv_spec' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rsaSampler_spec' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rsaCollection_index' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.negligible_rsaGenErr' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rsaCollection_sampleClose' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.coins_rsaBreaker' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rsaBreaker_runAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rsaCollection_invProbAt_le' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.rsaCollection_oneWay' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.rsaTrapdoor_oneWay' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rsaFromFactorStep_correct' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.polyTimeComputable_rsaFromFactorRaw' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.coins_rsaFromFactorer' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.rsaFromFactorer_runAt' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.factorProb_le_rsaProb' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.rsa_imp_factoring' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.BlumDistinctPrimes.ne_two' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Candidates.oddFactorProb_le' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.blumFactorProb_le' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.blumFactoring_of_factoring' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.crtNegOne_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.crtNegOne_ne_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.crtNegOne_ne_neg_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rabin_symmetry' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.polyTimeComputable_oddGenRaw' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.polyTimeComputable_blumGenRaw' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.oddGen_runAt' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.blumGen_runAt' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.listToNat_rabinIndexOf' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rabinMod_le' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Candidates.rabinDec_rabinEnc' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rabinEval_spec' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Candidates.polyTimeComputable_rabinEval' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rabinSampler_spec' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rabinCollection_index' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.negligible_rabinErr' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rabinCollection_sampleClose' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.polyTimeComputable_rabinFactorRaw' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.rabinFactorer_runAt' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rabinCollection_invProbAt_le' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.rabinCollection_oneWay' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.blumMod_of_valid' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.blumMod_of_not_valid' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.blumMod_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.BlumValid.exists_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.sqTo_bijective_of_exists' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.blum_val_lt_two_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.blumDec_blumEnc' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.blumEval_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.blumF_perm' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.polyTimeComputable_blumSampleRaw' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.polyTimeComputable_blumInvRaw' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.blumInv_spec' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.blumSampler_spec' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Candidates.rabinBlumTrapdoor_index' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.rabinBlumTrapdoor_sampleClose' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.rabinBlumTrapdoor_invProbAt_le' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.rabinBlumTrapdoor_oneWay' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.polyTimeComputable_rabinRootRaw' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.rabinBlumInverter_runAt' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.blumFactorProb_le_invProbAt' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.Candidates.blumFactoring_of_rabinBlum_oneWay' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.NumberTheory.card_primes' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.two_pow_le_pow_primeCounting' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.NumberTheory.chebyshev_two_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.chebyshev' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.two_pow_le_two_mul_card_primes' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.NumberTheory.uprob_prime_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.uprob_prime_bits' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.one_div_le_uprob_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.uprob_prime_pair' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.one_div_le_uprob_prime_pair' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.NumberTheory.two_pow_mrExp_mul_mrOdd' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.mrOdd_odd' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.mrOdd_mul_two_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.mem_mrLiars' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.MRLiar.ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.mrLiar_iff_of_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.card_mrLiars_of_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.two_mul_card_mrLiars_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.millerRabin_of_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.uprob_millerRabin_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.samplePrime_eq_none_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.samplePrime_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.samplePrime_uniform_of_some' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.NumberTheory.uprob_samplePrime_none' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.uprob_samplePrime_none_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.uprob_samplePrime_none_le_exp' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.NumberTheory.uprob_samplePrime_none_le_two_pow' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.NumberTheory.statClose_samplePrime' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NumberTheory.bitsToNat_eq_listToNat' does not depend on any axioms
'TCSlib.Cryptography.NumberTheory.eval_samplePrimeCoins' depends on axioms: [propext]
'TCSlib.Cryptography.NumberTheory.exists_samplePrime_nuppt' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.NUPPT.simulate_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.StatZK.zk' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.StatZK.hvzk' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.ZK.hvzk' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.StatZK.mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.negligible_const_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.PerfectZK.statZK' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.PerfectZK.zk' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.perfectZK_zeroRounds' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.AbortRetry.attempt_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.AbortRetry.retry_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.AbortRetry.retry_eq_attempt' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.AbortRetry.retry_eq_nil' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.AbortRetry.attempt_poly' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.AbortRetry.retry_poly' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.AbortRetry.exists_retrySimulator' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.AbortRetry.firstHit_map_getD_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.AbortRetry.statClose_retry' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.AbortRetry.uprob_not_ne_nil_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.PerfectZKAbort.statZK' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.PerfectZKAbort.zk' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.negligible_inv_pow_sqrt_div' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.negligible_two_pow_neg_sqrt_div' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.negligible_exp_neg_sqrt_div' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.negligible_of_le_inv_pow_sqrt_div' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.inv_pow_le_inv_pow_sqrt_div' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Isomorphic.refl' depends on axioms: [Quot.sound]
'TCSlib.Cryptography.Isomorphic.symm' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Isomorphic.trans' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.isomorphic_permGraph' depends on axioms: [Quot.sound]
'TCSlib.Cryptography.permGraph_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.not_isomorphic_both' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.gi_honest_reply_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.decGraphAt_encGraph' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.decGraph_snd' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.length_encInstance' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.instanceVertices_length_encInstance' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.instanceVertexCount_encInstance' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.encInstance_mem_Liso_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.encInstance_mem_Lniso_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.not_mem_Lniso_of_mem_Liso' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Riso_witnessRelation' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.permCoinLen_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.statClose_samplePerm' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.negligible_mul_permFailBound' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.uprob_permGraph_eq_of_isomorphic' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.uprob_permGraph_eq_of_isomorphic'' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.uprob_adaptive_guess' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.uprob_gi_cheat_le_half' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.uprob_gi_rep_cheat_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.uprob_gni_rep_cheat' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.gni_honest_reply' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.giProver_efficient' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.giVerifier_efficient' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.gniVerifier_efficient' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.gniVerifierRep_efficient' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.giProverRep_efficient' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.giVerifierRep_efficient' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.gni_interactiveProofErr' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.gni_interactiveProof' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.giProtocol_proverBounded' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.giProtocolRep_proverBounded' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.gniProtocol_proverBounded' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.gi_efficientProverProofErr' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.gi_rep_efficientProverProof' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.gi_rep_interactiveProof' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.gniProver_next_encGraph' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.gni_outV_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.gni_complete' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.ofFn_vTapeSplit' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.permCoinLen_le_tape' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.gni_accept_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.gni_interactiveProofErr' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.gi_outV_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.gi_complete' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.ofFn_giBitEquiv' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.giCoinEquiv_fst' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.giCoinEquiv_snd' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.gi_accept_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.gi_efficientProverProofErr' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.exec_repViews' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.GI.length_Vs' depends on axioms: [propext]
'TCSlib.Cryptography.GI.getD_Vs_even' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.GI.getD_Vs_odd' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.GI.PsOf_congr' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.GI.PsOfFin_prefixLT' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.GI.PsOfFin_init_prefixLE' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.GI.prefixLE_last' does not depend on any axioms
'TCSlib.Cryptography.GI.giVerifierRep_next_odd' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.giVerifierRep_next_mid' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.giVerifierRep_next_end' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.giVerifierRep_next_end_enc' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.giProverRep_next_even' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.giProverRep_next_odd' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.giProtocolRep_outV' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.repViews_snd' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.repViews_fst' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.honest_views' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.giRep_complete' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.giRep_accept_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.gi_rep_efficientProverProofErr' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.GI.gi_rep_efficientProverProof' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Strategy.encodeMsgs_nil' does not depend on any axioms
'TCSlib.Cryptography.Strategy.encodeMsgs_cons' does not depend on any axioms
'TCSlib.Cryptography.Strategy.pairFstD_encodeMsgs' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Strategy.ofNUPPT_next' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Strategy.ofNUPPT_efficient' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Strategy.Efficient.exists_uniform' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Strategy.ReadsPrefix.next_congr' depends on axioms: [propext]
'TCSlib.Cryptography.Strategy.ReadsPrefix.mono' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.moverIsV_true' does not depend on any axioms
'TCSlib.Cryptography.moverIsV_false' does not depend on any axioms
'TCSlib.Cryptography.exec_zero' does not depend on any axioms
'TCSlib.Cryptography.exec_succ' does not depend on any axioms
'TCSlib.Cryptography.exec_length' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.Protocol.proverBounded_iff' depends on axioms: [propext]
'TCSlib.Cryptography.Protocol.ProverBounded.mono' depends on axioms: [propext]
'TCSlib.Cryptography.Protocol.withV_V' does not depend on any axioms
'TCSlib.Cryptography.Protocol.withV_P' does not depend on any axioms
'TCSlib.Cryptography.Protocol.withV_rounds' does not depend on any axioms
'TCSlib.Cryptography.Protocol.withV_verifierFirst' does not depend on any axioms
'TCSlib.Cryptography.Protocol.withV_self' does not depend on any axioms
'TCSlib.Cryptography.Protocol.outV_eq_out' depends on axioms: [propext]
'TCSlib.Cryptography.Protocol.outP_eq_out' depends on axioms: [propext]
'TCSlib.Cryptography.Protocol.transcript_eq' depends on axioms: [propext]
'TCSlib.Cryptography.Protocol.outV_withV' depends on axioms: [propext]
'TCSlib.Cryptography.Protocol.outV_eq_getLast_of_moverIsV' depends on axioms: [propext]
'TCSlib.Cryptography.Protocol.uprob_outV_eq_uexp' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Protocol.exists_proverCoins_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.InteractiveProofErr.interactiveProof' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.InteractiveProof.exists_err' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.InteractiveProof.exists_uprob_accept_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.InteractiveProof.exists_accept' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.InteractiveProofErr.exists_accept' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Protocol.ProverBounded.exists_complete' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.mem_witnessLanguage' does not depend on any axioms
'TCSlib.Cryptography.mem_witnessSet' does not depend on any axioms
'TCSlib.Cryptography.WitnessRelation.eq_witnessLanguage' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.WitnessRelation.mem_NP' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.exists_witnessRelation_of_mem_NP' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.EfficientProverProofErr.efficientProverProof' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.EfficientProverProof.exists_err' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.npProtocol_outV' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.npProtocol_readsPrefix' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.npProtocol_efficientV' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.npProtocol_efficientP' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.npProtocol_proverBounded' depends on axioms: [propext]
'TCSlib.Cryptography.npProtocol_interactiveProof' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.WitnessRelation.mem_IP' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.NP_subset_IP' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.LevinReduction.polyTimeReducible' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.LevinReduction.refl' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.LevinReduction.trans' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Strategy.coinLen_pullback' depends on axioms: [propext]
'TCSlib.Cryptography.Protocol.pullback_outV' depends on axioms: [propext]
'TCSlib.Cryptography.Strategy.pullback_efficient' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Protocol.ProverBounded.pullback' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Negligible.comp_of_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.LevinReduction.efficientProverProofErr' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.LevinReduction.efficientProverProof' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.LevinReduction.zk' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.zk_proof_of_levinReduction' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.zk_proof_of_owp_levinReduction' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.exists_commitment_zk_proof_of_owp_levinReduction' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.one_sub_inv_add_half_pow_lt_one' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.zk_proof_of_witnessRelation' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.zk_proof_of_witnessRelation_of_owp' depends on axioms: [propext,
 sorryAx,
 Classical.choice,
 Quot.sound]
'TCSlib.Cryptography.zk_proof_of_mem_NP' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.zk_proof_of_mem_NP_of_owp' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.threeColorable_ofSimpleGraph_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.mem_L3COL_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.encGraph_mem_L3COL_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.mem_edgeList_iff' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.edgeOf_adj' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.exists_edgeOf_eq' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.edgeAt_eq_some_edgeOf' depends on axioms: [propext]
'TCSlib.Cryptography.edgeAt_adj' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.edgeAt_isSome' does not depend on any axioms
'TCSlib.Cryptography.edgeAt_eq_none_iff' depends on axioms: [propext]
'TCSlib.Cryptography.threeColorable_of_edgeCount_eq_zero' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.edgeCount_pos_of_not_threeColorable' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.one_sub_inv_pow_mul_le_exp' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.exp_neg_le_inv_two_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.decColor_encColor' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.encColor_getD_ne' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.padColor_injective' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.sampleEdgeIdx_lt' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.edgeIdxOfMsg_edgeMsg' depends on axioms: [propext]
'TCSlib.Cryptography.edgeIdxOfMsg_lt' does not depend on any axioms
'TCSlib.Cryptography.statClose_samplePerm3' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.statClose_sampleEdgeIdx' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.msgAt_encodeMsgs' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.colVerify_honest' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.committedColor_eq_some' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.exists_bad_edge' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.uprob_adaptive_escape' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.uprob_col_cheat_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.colWellFormed_encGraph' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.colProver_efficient' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.colVerifier_efficient' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.colProverRep_efficient' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.colVerifierRep_efficient' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.length_multiCom_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.colProver_length_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.colProtocol_proverBounded' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.R3COL_witnessRelation' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.col_efficientProverProofErr' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.colRep_efficientProverProof' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.colRep_interactiveProof' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.card_colorPair' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.perm3_ext_of_ne' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.colorPairEquiv_apply' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.simColorsW_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.uprob_colSimAttemptW_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.firstSome_eq_none_iff' depends on axioms: [propext, Quot.sound]
'TCSlib.Cryptography.uprob_colSimTruncW_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.uprob_colSimAttemptH_none' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.uprob_colSimAttemptH_some' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.uprob_colSimTruncH_none' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.statClose_colSimTruncH' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.colSimHyb_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.colSimHyb_self' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.exists_colSimRed_ge' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.exists_colSimulator' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.Negligible.comp_sqrt' depends on axioms: [propext, Classical.choice, Quot.sound]
'TCSlib.Cryptography.col_zk' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.col_hvzk' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'TCSlib.Cryptography.col_zeroKnowledgeProof' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/evidence-repairs/03-batch/seal.log =====

## Part 1: consumers of TCSlib.Cryptography.Protocol.ProverBounded (whole files sealed)

TCSlib/Cryptography/ZeroKnowledge/InteractiveProofs.lean
  seal: ProverBounded
  sealed current: PASS
  control (base text): FAIL (2 error lines); expected fail: as expected
    ctl: TCSlib_Cryptography_ZeroKnowledge_InteractiveProofs_sealed_control.lean:236:22: error: Function expected at
    ctl: TCSlib_Cryptography_ZeroKnowledge_InteractiveProofs_sealed_control.lean:470:2: error: Type mismatch
  the same control unsealed: PASS (so its sealed failure is due to the seal)
  explicit simp/rw/unfold of ProverBounded in the current file: 0

TCSlib/Cryptography/ZeroKnowledge/NP.lean
  seal: ProverBounded
  sealed current: PASS
  control (base text): FAIL (1 error lines); expected fail: as expected
    ctl: TCSlib_Cryptography_ZeroKnowledge_NP_sealed_control.lean:279:8: error: Tactic `introN` failed: There are no additional binders or `let` bindings in the goal to introduce
  the same control unsealed: PASS (so its sealed failure is due to the seal)
  explicit simp/rw/unfold of ProverBounded in the current file: 0

TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism.lean
  seal: ProverBounded
  sealed current: PASS
  control (base text): FAIL (3 error lines); expected fail: as expected
    ctl: TCSlib_Cryptography_ZeroKnowledge_GraphIsomorphism_sealed_control.lean:928:39: error: Type mismatch
    ctl: TCSlib_Cryptography_ZeroKnowledge_GraphIsomorphism_sealed_control.lean:932:42: error: Type mismatch
    ctl: TCSlib_Cryptography_ZeroKnowledge_GraphIsomorphism_sealed_control.lean:938:3: error: Application type mismatch: The argument
  the same control unsealed: PASS (so its sealed failure is due to the seal)
  explicit simp/rw/unfold of ProverBounded in the current file: 0

TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean
  seal: ProverBounded
  sealed current: PASS
  control (base text): FAIL (3 error lines); expected fail: as expected
    ctl: TCSlib_Cryptography_ZeroKnowledge_ThreeColoring_Protocol_sealed_control.lean:611:13: error: Application type mismatch: The argument
    ctl: TCSlib_Cryptography_ZeroKnowledge_ThreeColoring_Protocol_sealed_control.lean:612:2: error: No goals to be solved
    ctl: TCSlib_Cryptography_ZeroKnowledge_ThreeColoring_Protocol_sealed_control.lean:882:40: error: Function expected at
  the same control unsealed: PASS (so its sealed failure is due to the seal)
  explicit simp/rw/unfold of ProverBounded in the current file: 0

TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Soundness.lean
  seal: ProverBounded
  sealed current: PASS
  control (base text): FAIL (1 error lines); expected fail: as expected
    ctl: TCSlib_Cryptography_ZeroKnowledge_GraphIsomorphism_Soundness_sealed_control.lean:322:21: error: Application type mismatch: The argument
  the same control unsealed: PASS (so its sealed failure is due to the seal)
  explicit simp/rw/unfold of ProverBounded in the current file: 0

TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRepGI.lean
  seal: ProverBounded
  sealed current: PASS
  control (base text): FAIL (1 error lines); expected fail: as expected
    ctl: TCSlib_Cryptography_ZeroKnowledge_GraphIsomorphism_SoundnessRepGI_sealed_control.lean:478:21: error: Application type mismatch: The argument
  the same control unsealed: PASS (so its sealed failure is due to the seal)
  explicit simp/rw/unfold of ProverBounded in the current file: 0

## Part 2: new proofs that read another file's definitions (copies in a SealTest namespace)

TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean: Clean.envelope, host_call_envelope, host_clean_envelope
  seal: ofWords stateWord runFrom step
  sealed current: PASS
  control (Clean.envelope with the seam's head position read by `rfl` through `Cfg.ofWords`): FAIL (1 error lines); expected fail: as expected
    ctl: ModuleHost_envelopes_sealed_control.lean:29:89: error: Type mismatch
  the same control unsealed: PASS (so its sealed failure is due to the seal)

TCSlib/Cryptography/ZeroKnowledge/Defs.lean: attempt_eq, retry_eq, retry_eq_attempt, retry_eq_nil
  seal: firstIdx layout inParam inArg inCoins output coinLen
  sealed current: PASS
  control (the copies plus one `rfl` read of `firstIdx` (seal-active check)): FAIL (1 error lines); expected fail: as expected
    ctl: Defs_AbortRetry_sealed_control.lean:41:45: error: Type mismatch
  the same control unsealed: PASS (so its sealed failure is due to the seal)

TCSlib/Cryptography/Candidates/DiscreteLog.lean: sampleBelowL_eq_rejectBlocksL
  seal: rejectBlocksL
  sealed current: PASS
  control (the lemma proved by `funext r; rfl`, reading `rejectBlocksL` through its body): FAIL (1 error lines); expected fail: as expected
    ctl: DiscreteLog_sampleBelowL_sealed_control.lean:15:2: error: Tactic `rfl` failed: The left-hand side
  the same control unsealed: PASS (so its sealed failure is due to the seal)


## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/evidence-repairs/03-batch/lint.log =====

# Lint (check 4), HEAD 73751f5747d8c0a57aba9939cac8bb16f87ba2ba vs BASE 092083cd10be7a284db4e97fcf42eddb8296edf7 (archive in g03batch/basetree)
# lint.sh: scripts/style_lint.py on the 21 changed .lean files; scripts/campaign_style_lint.py --check8b per directory, filtered to them.
# Normalized diff base -> head (line numbers masked):
#   26c26,27
#   < INFO  TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean          548 lines; 16 public / 13 private declarations
#   ---
#   > INFO  TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean          663 lines > target 600
#   > INFO  TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean          663 lines; 19 public / 13 private declarations
#   28,29c29,30
#   < INFO  TCSlib/Cryptography/Asymptotic/OneWay.lean                929 lines > target 600
#   < INFO  TCSlib/Cryptography/Asymptotic/OneWay.lean                929 lines; 44 public / 6 private declarations
#   ---
#   > INFO  TCSlib/Cryptography/Asymptotic/OneWay.lean                930 lines > target 600
#   > INFO  TCSlib/Cryptography/Asymptotic/OneWay.lean                930 lines; 44 public / 6 private declarations
#   45,56c46,57
#   < INFO  TCSlib/Cryptography/Candidates/Concrete.lean             561 lines; 39 public / 0 private declarations
#   < INFO  TCSlib/Cryptography/Candidates/DiscreteLog.lean          710 lines > target 600
#   < INFO  TCSlib/Cryptography/Candidates/DiscreteLog.lean          710 lines; 65 public / 0 private declarations
#   < INFO  TCSlib/Cryptography/Candidates/DiscreteLogHardcore.lean  585 lines; 45 public / 0 private declarations
#   < INFO  TCSlib/Cryptography/Candidates/ElGamal.lean              890 lines > target 600
#   < INFO  TCSlib/Cryptography/Candidates/ElGamal.lean              890 lines; 60 public / 4 private declarations
#   < INFO  TCSlib/Cryptography/Candidates/Factoring.lean            691 lines > target 600
#   < INFO  TCSlib/Cryptography/Candidates/Factoring.lean            691 lines; 47 public / 0 private declarations
#   < INFO  TCSlib/Cryptography/Candidates/RSA.lean                  914 lines > target 600
#   < INFO  TCSlib/Cryptography/Candidates/RSA.lean                  914 lines; 85 public / 0 private declarations
#   < INFO  TCSlib/Cryptography/Candidates/Rabin.lean                994 lines > target 600
#   < INFO  TCSlib/Cryptography/Candidates/Rabin.lean                994 lines; 96 public / 0 private declarations
#   ---
#   > INFO  TCSlib/Cryptography/Candidates/Concrete.lean             570 lines; 40 public / 0 private declarations
#   > INFO  TCSlib/Cryptography/Candidates/DiscreteLog.lean          719 lines > target 600
#   > INFO  TCSlib/Cryptography/Candidates/DiscreteLog.lean          719 lines; 66 public / 0 private declarations
#   > INFO  TCSlib/Cryptography/Candidates/DiscreteLogHardcore.lean  597 lines; 45 public / 0 private declarations
#   > INFO  TCSlib/Cryptography/Candidates/ElGamal.lean              894 lines > target 600
#   > INFO  TCSlib/Cryptography/Candidates/ElGamal.lean              894 lines; 60 public / 4 private declarations
#   > INFO  TCSlib/Cryptography/Candidates/Factoring.lean            697 lines > target 600
#   > INFO  TCSlib/Cryptography/Candidates/Factoring.lean            697 lines; 47 public / 0 private declarations
#   > INFO  TCSlib/Cryptography/Candidates/RSA.lean                  926 lines > target 600
#   > INFO  TCSlib/Cryptography/Candidates/RSA.lean                  926 lines; 85 public / 0 private declarations
#   > INFO  TCSlib/Cryptography/Candidates/Rabin.lean                999 lines > target 600
#   > INFO  TCSlib/Cryptography/Candidates/Rabin.lean                999 lines; 96 public / 0 private declarations
#   58,60c59,61
#   < INFO  TCSlib/Cryptography/NumberTheory/Chebyshev.lean          308 lines; 11 public / 3 private declarations
#   < INFO  TCSlib/Cryptography/NumberTheory/Primality.lean          901 lines > target 600
#   < INFO  TCSlib/Cryptography/NumberTheory/Primality.lean          901 lines; 30 public / 30 private declarations
#   ---
#   > INFO  TCSlib/Cryptography/NumberTheory/Chebyshev.lean          311 lines; 11 public / 3 private declarations
#   > INFO  TCSlib/Cryptography/NumberTheory/Primality.lean          908 lines > target 600
#   > INFO  TCSlib/Cryptography/NumberTheory/Primality.lean          908 lines; 30 public / 30 private declarations
#   67c68
#   < WARN  TCSlib/Cryptography/ZeroKnowledge/Interaction.lean                       10 public def(s) without a lemma beside them (check 8): Efficient, ProverBounded, ReadsPrefix, Strategy.out, View.encode, coinLen, execution, transcriptWith, viewP, viewV
#   ---
#   > WARN  TCSlib/Cryptography/ZeroKnowledge/Interaction.lean                       9 public def(s) without a lemma beside them (check 8): Efficient, ReadsPrefix, Strategy.out, View.encode, coinLen, execution, transcriptWith, viewP, viewV
#   73,86c74,87
#   < INFO  TCSlib/Cryptography/ZeroKnowledge/Defs.lean                              687 lines > target 600
#   < INFO  TCSlib/Cryptography/ZeroKnowledge/Defs.lean                              687 lines; 30 public / 0 private declarations
#   < INFO  TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Soundness.lean        326 lines; 17 public / 0 private declarations
#   < INFO  TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRepGI.lean   489 lines; 30 public / 0 private declarations
#   < INFO  TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism.lean                  981 lines; 68 public / 7 private declarations
#   < INFO  TCSlib/Cryptography/ZeroKnowledge/Interaction.lean                       464 lines; 49 public / 0 private declarations
#   < INFO  TCSlib/Cryptography/ZeroKnowledge/InteractiveProofs.lean                 544 lines; 30 public / 0 private declarations
#   < INFO  TCSlib/Cryptography/ZeroKnowledge/NP.lean                                763 lines > target 600
#   < INFO  TCSlib/Cryptography/ZeroKnowledge/NP.lean                                763 lines; 23 public / 5 private declarations
#   < INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Language.lean            423 lines; 40 public / 3 private declarations
#   < INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean            923 lines > target 600
#   < INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean            923 lines; 34 public / 12 private declarations
#   < INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Simulator.lean           790 lines > target 600
#   < INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Simulator.lean           790 lines; 42 public / 3 private declarations
#   ---
#   > INFO  TCSlib/Cryptography/ZeroKnowledge/Defs.lean                              733 lines > target 600
#   > INFO  TCSlib/Cryptography/ZeroKnowledge/Defs.lean                              733 lines; 34 public / 0 private declarations
#   > INFO  TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Soundness.lean        327 lines; 17 public / 0 private declarations
#   > INFO  TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRepGI.lean   490 lines; 30 public / 0 private declarations
#   > INFO  TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism.lean                  985 lines; 68 public / 7 private declarations
#   > INFO  TCSlib/Cryptography/ZeroKnowledge/Interaction.lean                       473 lines; 50 public / 0 private declarations
#   > INFO  TCSlib/Cryptography/ZeroKnowledge/InteractiveProofs.lean                 550 lines; 30 public / 0 private declarations
#   > INFO  TCSlib/Cryptography/ZeroKnowledge/NP.lean                                766 lines > target 600
#   > INFO  TCSlib/Cryptography/ZeroKnowledge/NP.lean                                766 lines; 23 public / 5 private declarations
#   > INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Language.lean            424 lines; 40 public / 3 private declarations
#   > INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean            926 lines > target 600
#   > INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean            926 lines; 34 public / 12 private declarations
#   > INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Simulator.lean           804 lines > target 600
#   > INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Simulator.lean           804 lines; 42 public / 3 private declarations
#   89,90c90,91
#   < INFO  TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Soundness.lean        326 lines; 17 public / 0 private declarations
#   < INFO  TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRepGI.lean   489 lines; 30 public / 0 private declarations
#   ---
#   > INFO  TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Soundness.lean        327 lines; 17 public / 0 private declarations
#   > INFO  TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRepGI.lean   490 lines; 30 public / 0 private declarations
#   94,98c95,99
#   < INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Language.lean          423 lines; 40 public / 3 private declarations
#   < INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean          923 lines > target 600
#   < INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean          923 lines; 34 public / 12 private declarations
#   < INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Simulator.lean         790 lines > target 600
#   < INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Simulator.lean         790 lines; 42 public / 3 private declarations
#   ---
#   > INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Language.lean          424 lines; 40 public / 3 private declarations
#   > INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean          926 lines > target 600
#   > INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean          926 lines; 34 public / 12 private declarations
#   > INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Simulator.lean         804 lines > target 600
#   > INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Simulator.lean         804 lines; 42 public / 3 private declarations
# => no new WARN/FAIL; Interaction.lean's check-8 list loses ProverBounded; ModuleHost.lean passes the 600-line target (INFO, 663 lines); the rest are line counts.

### HEAD raw
### scripts/style_lint.py on the changed .lean files

1 findings in 21 files



















TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean:723: `colProtocol_sound` proof is 99 lines, no **Proof sketch.**

### scripts/campaign_style_lint.py --check8b, per directory, filtered to the changed files
INFO  TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean          663 lines > target 600
INFO  TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean          663 lines; 19 public / 13 private declarations
WARN  TCSlib/Cryptography/Asymptotic/OneWay.lean                5 public def(s) without a lemma beside them (check 8): Easy, LengthRegular, OneWayPermutation, strOutLen, yaoRounds
INFO  TCSlib/Cryptography/Asymptotic/OneWay.lean                930 lines > target 600
INFO  TCSlib/Cryptography/Asymptotic/OneWay.lean                930 lines; 44 public / 6 private declarations
FAIL  TCSlib/Cryptography/Candidates/ElGamal.lean              line 749: `sorry` without a proof sketch in the preceding docstring
FAIL  TCSlib/Cryptography/Candidates/Rabin.lean                line 145: `sorry` without a proof sketch in the preceding docstring
FAIL  TCSlib/Cryptography/Candidates/Rabin.lean                line 347: `sorry` without a proof sketch in the preceding docstring
FAIL  TCSlib/Cryptography/Candidates/Rabin.lean                line 532: `sorry` without a proof sketch in the preceding docstring
FAIL  TCSlib/Cryptography/Candidates/Rabin.lean                line 805: `sorry` without a proof sketch in the preceding docstring
FAIL  TCSlib/Cryptography/Candidates/Rabin.lean                line 892: `sorry` without a proof sketch in the preceding docstring
FAIL  TCSlib/Cryptography/Candidates/Rabin.lean                line 927: `sorry` without a proof sketch in the preceding docstring
FAIL  TCSlib/Cryptography/Candidates/Rabin.lean                line 951: `sorry` without a proof sketch in the preceding docstring
WARN  TCSlib/Cryptography/Candidates/Concrete.lean             1 public def(s) without a lemma beside them (check 8): default
WARN  TCSlib/Cryptography/Candidates/DiscreteLog.lean          11 public def(s) without a lemma beside them (check 8): DLAssumption, DLHard, FullLength, FullLengthExcept, SafePrimeValid, WellFormedIndex, dlDefaultIndex, dlG, dlM, expSampleRaw, expUnit
WARN  TCSlib/Cryptography/Candidates/DiscreteLogHardcore.lean  9 public def(s) without a lemma beside them (check 8): FullDLAssumption, FullGroupValid, IsGenerator, dlInverter, dlRoot, halfBit, halfOracle, majOracle, shiftInverter
WARN  TCSlib/Cryptography/Candidates/ElGamal.lean              15 public def(s) without a lemma beside them (check 8): DDHAssumption, Secure, challenge, ddhLen, ddhRandom, ddhReal, ddhTuple, egCanon, egEncParts, egEncRaw, egGenCoins, egGenParts, egGenRaw, egGroupGenRaw, egGroupParts
WARN  TCSlib/Cryptography/Candidates/Factoring.lean            7 public def(s) without a lemma beside them (check 8): FactoringAssumption, fmultBlocks, fmultWeakPoly, plantFactor, prodInverter, samplePairRaw, samplePrimeL
WARN  TCSlib/Cryptography/Candidates/RSA.lean                  19 public def(s) without a lemma beside them (check 8): RSAAssumption, RSAValid, rsaBlock, rsaEncVal, rsaFromFactorRaw, rsaGenCoins, rsaGenErr, rsaGenOut, rsaGenParams, rsaGenRaw, rsaIndexOf, rsaInput, rsaInvRaw, rsaPermAt, rsaSampleCoins, rsaSampleRaw, rsaTrapOf, rsaTrials, unitSampleStr
WARN  TCSlib/Cryptography/Candidates/Rabin.lean                28 public def(s) without a lemma beside them (check 8): BlumDensity, BlumFactoringAssumption, BlumValid, blumDefault, blumEnc, blumEncVal, blumInvNat, blumInvRaw, blumPermAt, blumSampleRaw, oddDefault, rabinEnc, rabinErr, rabinF, rabinFactorRaw, rabinFactorStep, rabinGenCoins, rabinGenOut, rabinGenParams, rabinGenRaw, rabinIndexOf, rabinPrimeCoins, rabinRootRaw, rabinRootStep, rabinSampleRaw, rabinTrials, samplePrimePL, smallDistinctPrimes
INFO  TCSlib/Cryptography/Candidates/Concrete.lean             570 lines; 40 public / 0 private declarations
INFO  TCSlib/Cryptography/Candidates/DiscreteLog.lean          719 lines > target 600
INFO  TCSlib/Cryptography/Candidates/DiscreteLog.lean          719 lines; 66 public / 0 private declarations
INFO  TCSlib/Cryptography/Candidates/DiscreteLogHardcore.lean  597 lines; 45 public / 0 private declarations
INFO  TCSlib/Cryptography/Candidates/ElGamal.lean              894 lines > target 600
INFO  TCSlib/Cryptography/Candidates/ElGamal.lean              894 lines; 60 public / 4 private declarations
INFO  TCSlib/Cryptography/Candidates/Factoring.lean            697 lines > target 600
INFO  TCSlib/Cryptography/Candidates/Factoring.lean            697 lines; 47 public / 0 private declarations
INFO  TCSlib/Cryptography/Candidates/RSA.lean                  926 lines > target 600
INFO  TCSlib/Cryptography/Candidates/RSA.lean                  926 lines; 85 public / 0 private declarations
INFO  TCSlib/Cryptography/Candidates/Rabin.lean                999 lines > target 600
INFO  TCSlib/Cryptography/Candidates/Rabin.lean                999 lines; 96 public / 0 private declarations
WARN  TCSlib/Cryptography/NumberTheory/Primality.lean          6 public def(s) without a lemma beside them (check 8): MRLiar, chunk, listToNat, mrExp, mrLiars, samplePrimeCoins
INFO  TCSlib/Cryptography/NumberTheory/Chebyshev.lean          311 lines; 11 public / 3 private declarations
INFO  TCSlib/Cryptography/NumberTheory/Primality.lean          908 lines > target 600
INFO  TCSlib/Cryptography/NumberTheory/Primality.lean          908 lines; 30 public / 30 private declarations
FAIL  TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism.lean                  facade does not import child module `TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.Concrete`
FAIL  TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism.lean                  facade does not import child module `TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.Proofs`
WARN  TCSlib/Cryptography/ZeroKnowledge/Defs.lean                              4 public def(s) without a lemma beside them (check 8): HVZK, PerfectZKAbort, StatZK, ZK
WARN  TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Soundness.lean        2 public def(s) without a lemma beside them (check 8): giBitEquiv, vTapeSplit
WARN  TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRepGI.lean   4 public def(s) without a lemma beside them (check 8): Hfun, Vs, giRepCoins, honestH
WARN  TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism.lean                  12 public def(s) without a lemma beside them (check 8): Liso, Lniso, coinSlice, gniProtocolRep, gniProver, instanceG, instanceG, permFailBound, prefixLE, prefixLT, samplePerm, wellFormedInstance
WARN  TCSlib/Cryptography/ZeroKnowledge/Interaction.lean                       9 public def(s) without a lemma beside them (check 8): Efficient, ReadsPrefix, Strategy.out, View.encode, coinLen, execution, transcriptWith, viewP, viewV
WARN  TCSlib/Cryptography/ZeroKnowledge/InteractiveProofs.lean                 3 public def(s) without a lemma beside them (check 8): IP, witnessLanguage, witnessSet
WARN  TCSlib/Cryptography/ZeroKnowledge/NP.lean                                1 public def(s) without a lemma beside them (check 8): LevinNPHard
WARN  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Language.lean            9 public def(s) without a lemma beside them (check 8): Graph.ofSimpleGraph, L3COL, ProperColoring, R3COL, edgeList, edgeMsg, perm3Equiv, sampleIdx, samplePerm3
WARN  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean            7 public def(s) without a lemma beside them (check 8): challengesBefore, challengesUpTo, colCoinSlice, colCommit, colIterations, colOpen, colProtocolRep
WARN  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Simulator.lean           17 public def(s) without a lemma beside them (check 8): colRealView, colSim, colSimAttempt, colSimAttemptH, colSimAttemptPlanted, colSimAttemptStr, colSimAttemptW, colSimBlock, colSimCoins, colSimRed, colSimTrunc, colSimTruncH, colSimTruncW, pair6Equiv, sampleColorPair, simCoinsEquiv, simColors
INFO  TCSlib/Cryptography/ZeroKnowledge/Defs.lean                              733 lines > target 600
INFO  TCSlib/Cryptography/ZeroKnowledge/Defs.lean                              733 lines; 34 public / 0 private declarations
INFO  TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Soundness.lean        327 lines; 17 public / 0 private declarations
INFO  TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRepGI.lean   490 lines; 30 public / 0 private declarations
INFO  TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism.lean                  985 lines; 68 public / 7 private declarations
INFO  TCSlib/Cryptography/ZeroKnowledge/Interaction.lean                       473 lines; 50 public / 0 private declarations
INFO  TCSlib/Cryptography/ZeroKnowledge/InteractiveProofs.lean                 550 lines; 30 public / 0 private declarations
INFO  TCSlib/Cryptography/ZeroKnowledge/NP.lean                                766 lines > target 600
INFO  TCSlib/Cryptography/ZeroKnowledge/NP.lean                                766 lines; 23 public / 5 private declarations
INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Language.lean            424 lines; 40 public / 3 private declarations
INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean            926 lines > target 600
INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean            926 lines; 34 public / 12 private declarations
INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Simulator.lean           804 lines > target 600
INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Simulator.lean           804 lines; 42 public / 3 private declarations
WARN  TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Soundness.lean        2 public def(s) without a lemma beside them (check 8): giBitEquiv, vTapeSplit
WARN  TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRepGI.lean   4 public def(s) without a lemma beside them (check 8): Hfun, Vs, giRepCoins, honestH
INFO  TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Soundness.lean        327 lines; 17 public / 0 private declarations
INFO  TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRepGI.lean   490 lines; 30 public / 0 private declarations
WARN  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Language.lean          9 public def(s) without a lemma beside them (check 8): Graph.ofSimpleGraph, L3COL, ProperColoring, R3COL, edgeList, edgeMsg, perm3Equiv, sampleIdx, samplePerm3
WARN  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean          7 public def(s) without a lemma beside them (check 8): challengesBefore, challengesUpTo, colCoinSlice, colCommit, colIterations, colOpen, colProtocolRep
WARN  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Simulator.lean         17 public def(s) without a lemma beside them (check 8): colRealView, colSim, colSimAttempt, colSimAttemptH, colSimAttemptPlanted, colSimAttemptStr, colSimAttemptW, colSimBlock, colSimCoins, colSimRed, colSimTrunc, colSimTruncH, colSimTruncW, pair6Equiv, sampleColorPair, simCoinsEquiv, simColors
INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Language.lean          424 lines; 40 public / 3 private declarations
INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean          926 lines > target 600
INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean          926 lines; 34 public / 12 private declarations
INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Simulator.lean         804 lines > target 600
INFO  TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Simulator.lean         804 lines; 42 public / 3 private declarations

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/evidence-repairs/03-batch/statements.txt =====

# Statement diff: decls.py (copied from g03l-fix) over every changed .lean file, BASE=092083cd10be7a284db4e97fcf42eddb8296edf7 vs HEAD=73751f5747d8c0a57aba9939cac8bb16f87ba2ba
# Normalized statement text (comments stripped) of every public declaration, compared by full name.

## Summary: 10 added, 2 changed, 0 removed

## Added
- Turing.ModuleHost.Clean.envelope (theorem, TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean:239)
    theorem Clean.envelope {M : FinTM Bool} {result emit : List Bool → List Bool} {B : ℕ → ℕ} (h : Clean M result emit B) (x arg : List Bool) (v : ℕ) (j : Fin M.k) :
- Turing.ModuleHost.host_call_envelope (theorem, TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean:567)
    theorem host_call_envelope {C : Type} [Fintype C] [DecidableEq C] {n : ℕ} (M : Fin n → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K) (ctrl : C → Option Bool → (Fin K → Option Bool) → Action K Bool (State C M)) (ret : Fin n → State C M) (q₀ : State C M) (i : Fin n) (x arg pre : List Bool) (t : ℕ) : ∀ v ≤ t, ∀ j : Fin K, |((hostTM M K hk ctrl ret q₀).tm.runFrom {Cfg.ofWords (input := x) (entry M i) (stateWord K arg) with output := pre} v).workTapePos j| ≤ (t : ℤ)
- Turing.ModuleHost.host_clean_envelope (theorem, TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean:642)
    theorem host_clean_envelope {C : Type} [Fintype C] [DecidableEq C] {n : ℕ} (M : Fin n → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K) (ctrl : C → Option Bool → (Fin K → Option Bool) → Action K Bool (State C M)) (ret : Fin n → State C M) (q₀ : State C M) (i : Fin n) (f g : List Bool → List Bool) (B : ℕ → ℕ) (h : Clean (M i) f g B) (x arg pre : List Bool) : ∃ t, 0 < t ∧ t ≤ B arg.length ∧ (∀ v < t, ∀ c : C, ((hostTM M K hk ctrl ret q₀).tm.runFrom {Cfg.ofWords (input := x) (entry M i) (stateWord K arg) with output := pre} v).state ≠ some (.inl c)) ∧ (hostTM M K hk ctrl ret q₀).tm.runFrom {Cfg.ofWords (input := x) (entry M i) (stateWord K arg) with output := pre} t = {Cfg.ofWords (ret i) (stateWord K (f arg)) with output := pre ++ g arg} ∧ ∀ v ≤ t, ∀ j : Fin K, |((hostTM M K hk ctrl ret q₀).tm.runFrom {Cfg.ofWords (input := x) (entry M i) (stateWord K arg) with output := pre} v).workTapePos j| ≤ (B arg.length : ℤ)
- TCSlib.Cryptography.Candidates.rejectBlocksL_eq (theorem, TCSlib/Cryptography/Candidates/Concrete.lean:525)
    theorem rejectBlocksL_eq (E : ℕ → Prop) [DecidablePred E] (k B T : ℕ) (r : List Bool) : rejectBlocksL E k B T r = (List.range T).findSome? fun t => if E (listToNat ((r.drop (t * B)).take k)) then some (listToNat ((r.drop (t * B)).take k)) else none
- TCSlib.Cryptography.Candidates.sampleBelowL_eq_rejectBlocksL (theorem, TCSlib/Cryptography/Candidates/DiscreteLog.lean:476)
    theorem sampleBelowL_eq_rejectBlocksL (m k B T : ℕ) : sampleBelowL m k B T = rejectBlocksL (· < m) k B T
- TCSlib.Cryptography.AbortRetry.attempt_eq (theorem, TCSlib/Cryptography/ZeroKnowledge/Defs.lean:315)
    theorem attempt_eq (S : NUPPT) (w : List Bool) (t : ℕ) : attempt S w t = S.output (NUPPT.layout (NUPPT.inParam w) (NUPPT.inArg w) [] (((NUPPT.inCoins w).drop (t * S.coinLen (NUPPT.inParam w).length)).take (S.coinLen (NUPPT.inParam w).length)))
- TCSlib.Cryptography.AbortRetry.retry_eq (theorem, TCSlib/Cryptography/ZeroKnowledge/Defs.lean:334)
    theorem retry_eq (S : NUPPT) (w : List Bool) : retry S w = if firstIdx (fun t => decide (attempt S w t ≠ [])) (NUPPT.inParam w).length < (NUPPT.inParam w).length then attempt S w (firstIdx (fun t => decide (attempt S w t ≠ [])) (NUPPT.inParam w).length) else []
- TCSlib.Cryptography.AbortRetry.retry_eq_attempt (theorem, TCSlib/Cryptography/ZeroKnowledge/Defs.lean:347)
    theorem retry_eq_attempt {S : NUPPT} {w : List Bool} {i : ℕ} (hi : i < (NUPPT.inParam w).length) (hne : attempt S w i ≠ []) (hmin : ∀ j < i, attempt S w j = []) : retry S w = attempt S w i
- TCSlib.Cryptography.AbortRetry.retry_eq_nil (theorem, TCSlib/Cryptography/ZeroKnowledge/Defs.lean:359)
    theorem retry_eq_nil {S : NUPPT} {w : List Bool} (h : ∀ t < (NUPPT.inParam w).length, attempt S w t = []) : retry S w = []
- TCSlib.Cryptography.Protocol.proverBounded_iff (theorem, TCSlib/Cryptography/ZeroKnowledge/Interaction.lean:338)
    theorem proverBounded_iff (π : Protocol) (R : List Bool → List Bool → Prop) (B : PolyExpr) : π.ProverBounded R B ↔ ∀ x y r hist, R x y → (π.P.next x y r hist).length ≤ B.eval x.length

## Changed (both by ruling R-03e-r2-1 (A), item C #4)
- TCSlib.Cryptography.zk_proof_of_witnessRelation (TCSlib/Cryptography/ZeroKnowledge/NP.lean:679->682)
    OLD: theorem zk_proof_of_witnessRelation (h3 : LevinNPHard L3COL R3COL) {Com : List Bool → List Bool} {ℓ : PolyExpr} (hC : Commitment Com ℓ) {L : Language Bool} {R : List Bool → List Bool → Prop} (hR : WitnessRelation L R) : ∃ (f : List Bool → List Bool) (w : List Bool → List Bool → List Bool) (p : PolyExpr), (∀ N, N ≤ p.eval N) ∧ EfficientProverProof ((colProtocolRep Com ℓ).pullback f w p) L R ∧ ZK ((colProtocol Com ℓ).pullback f w p) R ∧ EfficientProverProofErr ((colProtocol Com ℓ).pullback f w p) L R (fun N => 1 - 1 / (p.eval N : ℝ) + (1 / 2 : ℝ) ^ p.eval N)
    NEW: theorem zk_proof_of_witnessRelation (h3 : LevinNPHard L3COL R3COL) {Com : List Bool → List Bool} {ℓ : PolyExpr} (hC : Commitment Com ℓ) {L : Language Bool} {R : List Bool → List Bool → Prop} (hR : WitnessRelation L R) : ∃ (f : List Bool → List Bool) (w : List Bool → List Bool → List Bool) (p : PolyExpr), LevinReduction L L3COL R R3COL f w p ∧ (∀ N, N ≤ p.eval N) ∧ EfficientProverProof ((colProtocolRep Com ℓ).pullback f w p) L R ∧ ZK ((colProtocol Com ℓ).pullback f w p) R ∧ EfficientProverProofErr ((colProtocol Com ℓ).pullback f w p) L R (fun N => 1 - 1 / (p.eval N : ℝ) + (1 / 2 : ℝ) ^ p.eval N)
- TCSlib.Cryptography.zk_proof_of_witnessRelation_of_owp (TCSlib/Cryptography/ZeroKnowledge/NP.lean:698->701)
    OLD: theorem zk_proof_of_witnessRelation_of_owp (h3 : LevinNPHard L3COL R3COL) (how : ∃ P : PermFamily, OneWayPermutation P) {L : Language Bool} {R : List Bool → List Bool → Prop} (hR : WitnessRelation L R) : ∃ (Com : List Bool → List Bool) (ℓ : PolyExpr), Commitment Com ℓ ∧ ∃ (f : List Bool → List Bool) (w : List Bool → List Bool → List Bool) (p : PolyExpr), (∀ N, N ≤ p.eval N) ∧ EfficientProverProof ((colProtocolRep Com ℓ).pullback f w p) L R ∧ ZK ((colProtocol Com ℓ).pullback f w p) R ∧ EfficientProverProofErr ((colProtocol Com ℓ).pullback f w p) L R (fun N => 1 - 1 / (p.eval N : ℝ) + (1 / 2 : ℝ) ^ p.eval N)
    NEW: theorem zk_proof_of_witnessRelation_of_owp (h3 : LevinNPHard L3COL R3COL) (how : ∃ P : PermFamily, OneWayPermutation P) {L : Language Bool} {R : List Bool → List Bool → Prop} (hR : WitnessRelation L R) : ∃ (Com : List Bool → List Bool) (ℓ : PolyExpr), Commitment Com ℓ ∧ ∃ (f : List Bool → List Bool) (w : List Bool → List Bool → List Bool) (p : PolyExpr), LevinReduction L L3COL R R3COL f w p ∧ (∀ N, N ≤ p.eval N) ∧ EfficientProverProof ((colProtocolRep Com ℓ).pullback f w p) L R ∧ ZK ((colProtocol Com ℓ).pullback f w p) R ∧ EfficientProverProofErr ((colProtocol Com ℓ).pullback f w p) L R (fun N => 1 - 1 / (p.eval N : ℝ) + (1 / 2 : ℝ) ^ p.eval N)

## Removed
(none)

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/evidence-repairs/03-batch/maintainer-recheck.log =====

# maintainer re-check at 73751f5747d8c0a57aba9939cac8bb16f87ba2ba: 8 key modules, one at a time in import order, on a copy of the worker's tree
TCSlib/Complexity/TuringMachine/Build/ModuleHost rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/Interaction rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/Defs rc=0 7s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/NP rc=0 9s errors=0 sorry=0
TCSlib/Cryptography/Candidates/Concrete rc=0 4s errors=0 sorry=1
TCSlib/Cryptography/Candidates/DiscreteLog rc=0 4s errors=0 sorry=6
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Simulator rc=0 4s errors=0 sorry=1
audits/pass-shelat/Checks rc=0 121s errors=0 sorry=0
# done 2026-11-06T01:22:50Z

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/evidence-repairs/03-batch/base-sync.log =====

# base-sync 2026-11-06T00:22:41Z BASE=092083cd10be7a284db4e97fcf42eddb8296edf7 tree=/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad/g03batch-oleans (copy of g03l-oleans, #203 Lean files)
TCSlib/Complexity/Randomized/PPT rc=0 5s errors=0 sorry=0
TCSlib/Complexity/Randomized/Closure rc=0 3s errors=0 sorry=0
TCSlib/Complexity/Randomized/NonUniform rc=0 2s errors=0 sorry=1
TCSlib/Cryptography/Asymptotic/Adversary rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/EnsemblesLemmas rc=0 9s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/Ensembles rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/OneWayLemmas rc=0 8s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/OneWayYao rc=0 75s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/OneWay rc=0 10s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/CollectionsHelpers rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/CollectionsLemmas rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/Collections rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/UniversalLemmas rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/UniversalPadding rc=0 5s errors=0 sorry=1
TCSlib/Cryptography/Asymptotic/Universal rc=0 10s errors=0 sorry=1
TCSlib/Cryptography/Asymptotic/Pseudorandom rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/NextBit rc=0 7s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCoreLemmas rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCoreLoops rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCoreGL rc=0 13s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCoreGLColl rc=0 8s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCoreCollection rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCoreGLFamily rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCore rc=0 7s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCoreClaims rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/HardCorePermutation rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/Encryption rc=0 6s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/PRFLemmas rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/GGMReduction rc=0 63s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/GGMReductionEval rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/PRF rc=0 7s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/MultiMessageLemmas rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/MultiMessage rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/BlockEncryptor rc=0 6s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/PublicKeyLemmas rc=0 77s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic/PublicKey rc=0 24s errors=0 sorry=0
TCSlib/Cryptography/Asymptotic rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/NumberTheory/Primality rc=0 8s errors=0 sorry=0
TCSlib/Cryptography/Candidates/Arithmetic rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/Candidates/Concrete rc=0 6s errors=0 sorry=1
TCSlib/Cryptography/Candidates/Factoring rc=0 4s errors=0 sorry=8
TCSlib/Cryptography/Candidates/RSA rc=0 10s errors=0 sorry=9
TCSlib/Cryptography/Candidates/Rabin rc=0 7s errors=0 sorry=19
TCSlib/Cryptography/Candidates/DiscreteLog rc=0 4s errors=0 sorry=6
TCSlib/Cryptography/Candidates/DiscreteLogHardcore rc=0 5s errors=0 sorry=7
TCSlib/Cryptography/Candidates/ElGamal rc=0 5s errors=0 sorry=7
TCSlib/Cryptography/Candidates rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/NumberTheory rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/Interaction rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/InteractiveProofs rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/Defs rc=0 7s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Proofs rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Efficiency rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/EfficiencyRep rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/EfficiencyRepGI rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Soundness rc=0 6s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Concrete rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRep rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRepGI rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphismZK/Simulator rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphismZK/Closeness rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphismZK rc=0 6s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/CommitmentLemmas rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/Commitment rc=0 6s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Language rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Machines rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Parties rc=0 7s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/ProtocolProofs rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol rc=0 6s errors=0 sorry=2
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/SimulatorLemmas rc=0 5s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/SimulatorNumeric rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/SimulatorMachine rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Simulator rc=0 4s errors=0 sorry=1
TCSlib/Cryptography/ZeroKnowledge/ThreeColoring rc=0 2s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/NPLemmas rc=0 4s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/NP rc=0 11s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge/Encryption rc=0 3s errors=0 sorry=0
TCSlib/Cryptography/ZeroKnowledge rc=0 3s errors=0 sorry=0
# done 2026-11-06T00:32:55Z

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
Repetition convention (gate 03e, note 8): an iteration with an odd number of messages (prover,
verifier, prover) is repeated under strict alternation by giving each iteration one additional
verifier move, so that every iteration starts with the prover. In `giProtocolRep` and
`colProtocolRep` that move is the empty message, except for the protocol's final move, which
carries the verifier's verdict (the verdict convention above). The sequential repetition of
[PS10, §7.2.1] in ch. 7 pads each phase instead with `rounds(|x|)` filler moves of both parties,
its last filler again carrying the verdict.
`Strategy.Efficient` ([PS10, §4.4], time complexity of an interactive machine) is one
activation of a uniform `Complexity.NUPPT` at parameter `|x|` on `⟨⟨x, z⟩, messages⟩` with the
whole random tape; the time is polynomial in the total input length rather than in `|x|`
alone (the text's bound `t(|x|)`, which holds whatever the messages received, would leave the
simulator's call to `V*` on long auxiliary inputs ill-defined; see D8). Consequently
`Efficient` alone bounds neither a party's work in `|x|` against a counterparty that sends long
messages nor the length of its own messages. The proof systems (`InteractiveProofs.lean`)
therefore add the bound on the honest prover's messages, `Protocol.ProverBounded` (ruling G3-3
of gate 03, the convention of ch. 6: `Efficient` plus polynomially bounded honest messages);
the message-prefix cap `Strategy.ReadsPrefix m` — the strategy depends only on the first
`m(|x|)` bits of each received message, as a time-`t(|x|)` machine of the text necessarily
does — is the text's bound on the reading side, and the class `IP` (`InteractiveProofs.lean`)
requires it of the verifier (run-3 audit P9-1).

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
* `TCSlib.Cryptography.Protocol.ProverBounded` — the honest prover's messages have at most
  `B(|x|)` bits on instances with a witness (Def-116.b, the writing half of the text's bound
  in `|x|`; ruling G3-3).

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

/-- An efficient strategy, the formal counterpart of the text's PPT interactive machine
[PS10, §4.4, time complexity of an interactive machine] (Def-116.b): the next-message function
is computed by a uniform `NUPPT` with the same coin polynomial, one activation per message at
parameter `|x|` on `⟨⟨x, z⟩, messages⟩` with the whole random tape.

**Deviation (D8):** per-activation time polynomial in the total input length `|x| + |z| +
|messages|` instead of the text's `t(|x|)`, which bounds the running time whatever the
messages received. The number of activations is bounded by the protocol's `rounds`, but the
messages of an unbounded counterparty may be arbitrarily long, so `Efficient` alone does not
bound a party's work in `|x|` (run-3 audit P9-1), nor the length of the messages it writes.
The text's bound is recovered on the reading side by the message-prefix cap `ReadsPrefix m`
(an efficient strategy that reads only `m(|x|)` bits of each message runs in time polynomial
in `|x| + |z|`; the class `IP` requires it of the verifier) and on the writing side, for the
honest prover, by `Protocol.ProverBounded` (its messages have at most `B(|x|)` bits; the proof
systems require it, ruling G3-3 of gate 03). -/
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

/-- **The honest prover's messages are short** with respect to the witness relation `R` and
the polynomial `B` [PS10, §4.4, time complexity: a machine of time complexity `t(|x|)` halts
within `t(|x|)` steps whatever it receives, so each of its messages has at most `t(|x|)` bits]:
on every instance `x` with a witness `y` (`R x y`), whatever its random tape and whatever it
has received, the honest prover's message has at most `B(|x|)` bits.

**Deviation (D8; ruling G3-3 of gate 03, the convention of ch. 6):** `Strategy.Efficient`
bounds a party's work, hence its messages, only in the total length of its input, which
contains the messages it has received; the bound in `|x|` is this separate condition, a field
of `EfficientProverProof` (and, for the completeness witness, part of the completeness clause
of `InteractiveProof`). Without it an honest prover that echoes the verifier's messages —
zero-knowledge for one run — lets a cheating verifier that doubles its messages build a view
of length `2^{rounds}`, which the composition theorems of ch. 7 cannot simulate. -/
def ProverBounded (π : Protocol) (R : List Bool → List Bool → Prop) (B : PolyExpr) : Prop :=
  ∀ x y r hist, R x y → (π.P.next x y r hist).length ≤ B.eval x.length

/-- **Bounded honest messages unfolded:** `π.ProverBounded R B` iff for every `x` and `y` with
`R x y`, every tape `r` and every history `hist`, `|π.P.next x y r hist| ≤ B(|x|)`. -/
theorem proverBounded_iff (π : Protocol) (R : List Bool → List Bool → Prop) (B : PolyExpr) :
    π.ProverBounded R B ↔
      ∀ x y r hist, R x y → (π.P.next x y r hist).length ≤ B.eval x.length :=
  Iff.rfl

/-- A message bound `B` implies every pointwise larger bound `B'`. -/
theorem ProverBounded.mono {π : Protocol} {R : List Bool → List Bool → Prop} {B B' : PolyExpr}
    (h : π.ProverBounded R B) (hle : ∀ n, B.eval n ≤ B'.eval n) : π.ProverBounded R B' :=
  fun x y r hist hxy => (h x y r hist hxy).trans (hle _)

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

## ===== TCSlib/Cryptography/ZeroKnowledge/InteractiveProofs.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.ZeroKnowledge.Interaction
import TCSlib.Cryptography.Foundations.Negligible
import TCSlib.Cryptography.HardcoreBit.Basic
import TCSlib.Complexity.ClassNP.NP
import TCSlib.Complexity.ClassNP.PClosure
import TCSlib.Complexity.Randomized.Primitives

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Interactive proof systems

The definitions of [PS10, §4.5] on top of the interaction model of `Interaction.lean`
(foundation decision D8): interactive proofs with negligible soundness error
[PS10, Definition 116.1], proofs with a stated soundness error `s(|x|)` [PS10, §4.5,
constant-error proofs], witness relations [PS10, Appendix B, Definition 191.11], and
interactive proofs with an efficient prover [PS10, Definition 119.5]. The sanity theorem
`npProtocol_interactiveProof` shows the definitions are satisfiable: the one-message protocol
in which the prover sends a witness (read by the verifier up to the relation's witness-length
bound) is an interactive proof with efficient prover for every polynomially decidable witness
relation, and `WitnessRelation.mem_IP`, `NP_subset_IP` place such languages in the class `IP`
([PS10, §4.5, the remark `NP ⊆ IP`]).

**Deviation (D8):** soundness is the literal `1 - ε(|x|) < Pr[out_V = 0]` with `out_V = 0`
read as the output string `[false]`, the negligible `ε` quantified before the instance, the
cheating prover and its auxiliary input; cheating provers are arbitrary strategies with a
polynomial random tape (unbounded computation; polynomial coin tapes lose nothing by
averaging, `Protocol.exists_proverCoins_le`). Completeness is `uprob = 1`, i.e. acceptance on
every pair of random tapes. The verifier's efficiency (Definition 116.1's "p.p.t.", and the
prover's for Definition 119.5) is `Strategy.Efficient`, polynomial time in
`|x| + |z| + |messages|` (D8), together with a
polynomial bound `B(|x|)` on the honest prover's messages (ruling G3-3 of gate 03, the
convention of ch. 6): in the completeness clause of `InteractiveProof` and
`InteractiveProofErr` for the completeness witness, and as the field `boundedP`
(`Protocol.ProverBounded`) of `EfficientProverProof` and `EfficientProverProofErr` for every
witness. The residual deviation is that against a cheating prover the verifier's work is
polynomial in the length of the messages it receives, not in `|x|`. Since the honest messages
are short, the verifier can always be capped: `V` reading only the first `B(|x|)` bits of each
message is still complete (the honest messages are untouched) and sound (against `P*` it acts
as `V` against `P*` with truncated messages, another prover strategy). So `InteractiveProof`
(and `InteractiveProofErr` with negligible error, by `InteractiveProofErr.interactiveProof`)
holds only for languages of the text's class IP — undecidable languages such as the halting
problem, whose computation histories are not polynomially bounded, are excluded — the
explicit-error forms with a large error say little (with `s = 1` the zero-message,
always-accepting protocol is an `EfficientProverProofErr` for every language and relation) —
while `IP` itself is stated with the message-prefix cap `Strategy.ReadsPrefix` of the verifier
(run-3 audit P9-1). The capping argument is not formalized as a lemma.

## Main definitions

* `TCSlib.Cryptography.InteractiveProof` — interactive proof system [PS10, Definition 116.1]
  (Def-116.1); `TCSlib.Cryptography.InteractiveProofErr` — with soundness error `s` (Def-117.a);
  `TCSlib.Cryptography.IP` — the class of languages with an interactive proof whose verifier
  reads a polynomial prefix of each message (Def-117.b).
* `TCSlib.Cryptography.WitnessRelation` — a witness relation for a language
  [PS10, Definition 191.11] (Def-191.11); `TCSlib.Cryptography.witnessLanguage`,
  `TCSlib.Cryptography.witnessSet` — the language `{x | ∃ y, R x y}` and the set `R_L(x)`.
* `TCSlib.Cryptography.EfficientProverProof`,
  `TCSlib.Cryptography.EfficientProverProofErr` — interactive proofs with efficient prover
  [PS10, Definition 119.5] (Def-119.5).
* `TCSlib.Cryptography.npProtocol` — the one-message protocol in which the prover sends a
  witness, read by the verifier up to a polynomial length bound.

## Main results

* `TCSlib.Cryptography.InteractiveProofErr.interactiveProof`,
  `TCSlib.Cryptography.InteractiveProof.exists_err` — a negligible soundness error gives an
  interactive proof and conversely.
* `TCSlib.Cryptography.InteractiveProof.exists_accept`,
  `TCSlib.Cryptography.Protocol.ProverBounded.exists_complete` — completeness without the
  message bound, and completeness with the bound from bounded messages and completeness for
  every witness.
* `TCSlib.Cryptography.InteractiveProof.exists_uprob_accept_lt` — the acceptance form of
  soundness, `Pr[out_V = [true]] < ε(|x|)`.
* `TCSlib.Cryptography.WitnessRelation.mem_NP`,
  `TCSlib.Cryptography.exists_witnessRelation_of_mem_NP` — witness relations characterize
  `Complexity.NP` (the bridge to the certificate definition of `ClassNP/NP.lean`).
* `TCSlib.Cryptography.npProtocol_interactiveProof` — non-vacuity: sending a witness is an
  interactive proof with efficient prover (`TCSlib.Cryptography.npProtocol_proverBounded`: its
  prover's message is the witness); `TCSlib.Cryptography.npProtocol_readsPrefix`,
  `TCSlib.Cryptography.WitnessRelation.mem_IP`, `TCSlib.Cryptography.NP_subset_IP` — its
  verifier reads a polynomial prefix, hence `NP ⊆ IP` (Claim-117.c).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§4.5 Interactive proofs, pp. 116–120; Appendix B, Definition 191.11.)
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Cambridge
  University Press, 2009. (Definition 2.1, NP via certificates; Chapter 8.)
-/

namespace TCSlib.Cryptography

open Complexity Turing

/-! ### Interactive proofs -/

/-- An interactive proof system for `L` [PS10, Definition 116.1] (Def-116.1): the verifier is
efficient; completeness — for a polynomial `B` and every `x ∈ L` there is an auxiliary input
`y` on which the honest prover's messages have at most `B(|x|)` bits and such that for every
`z` the honest execution `P(x, y) ↔ V(x, z)` makes `V` output `1` with probability one;
soundness — there is a negligible `ε` such that for every `x ∉ L`, every (unbounded) prover
strategy `P'` and every `z`, `V` outputs `0` in `P'(x) ↔ V(x, z)` with probability greater than
`1 - ε(|x|)`.

**Deviation (D8; ruling G3-3 of gate 03):** `out_V = 0` is the literal output string `[false]`
on the complete history of the fixed-alternation execution; `P'` ranges over strategies with
polynomial random tapes and receives no auxiliary input (the text's `P*(x)`); completeness is
`uprob = 1` (every pair of random tapes). The verifier's "p.p.t." is `Strategy.Efficient`,
polynomial-time in `|x| + |z| + |messages|` (D8), and the honest messages on the completeness
witness are bounded by `B(|x|)` (Definition 116.1's prover need not be efficient; bounding its
messages is the chosen normal form, harmless because a verifier of time `t(|x|)` reads at most
`t(|x|)` bits of each message; the convention of ch. 6). Against a cheating prover the
verifier's work is polynomial in the length of the messages it receives, not in `|x|`; because
the honest messages are short the verifier can be capped to their length without losing
completeness or soundness (module docstring), so the predicate holds only for languages of the
text's class IP. The class `IP` is stated with the message-prefix cap `Strategy.ReadsPrefix`
(run-3 audit P9-1). -/
structure InteractiveProof (π : Protocol) (L : Language Bool) : Prop where
  /-- The verifier is efficient (`Strategy.Efficient`, D8). -/
  efficientV : π.V.Efficient
  /-- Completeness: for a polynomial `B`, every `x ∈ L` has an auxiliary input on which the
  honest prover's messages have at most `B(|x|)` bits and the honest verifier accepts with
  probability one. -/
  complete : ∃ B : PolyExpr, ∀ x ∈ L, ∃ y : List Bool,
    (∀ r hist, (π.P.next x y r hist).length ≤ B.eval x.length) ∧
    ∀ z : List Bool, uprob (fun r : π.ExecCoins π.P x => π.outV π.P x y z r = [true]) = 1
  /-- Soundness: against every prover strategy the verifier rejects with probability
  `> 1 - ε(|x|)` for a negligible `ε`. -/
  sound : ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ x ∉ L, ∀ (P' : Strategy) (z : List Bool),
    1 - ε x.length < uprob (fun r : π.ExecCoins P' x => π.outV P' x [] z r = [false])

/-- An interactive proof system with soundness error `s` [PS10, §4.5, after Definition 116.1]
(Def-117.a): as `InteractiveProof` with `1 - s(|x|) ≤ Pr[out_V = [false]]` for the given
function `s` (for instance the constant `1/2` of the single-iteration graph-isomorphism
protocol).

**Deviation (D8; ruling G3-3 of gate 03):** as for `InteractiveProof` (literal `[false]`,
provers with polynomial tapes, `uprob = 1` completeness with honest messages of at most
`B(|x|)` bits; verifier time in the total input length — the message-prefix cap is added in
`IP`, run-3 audit P9-1). -/
structure InteractiveProofErr (π : Protocol) (L : Language Bool) (s : ℕ → ℝ) : Prop where
  /-- The verifier is efficient (`Strategy.Efficient`, D8). -/
  efficientV : π.V.Efficient
  /-- Completeness: for a polynomial `B`, every `x ∈ L` has an auxiliary input on which the
  honest prover's messages have at most `B(|x|)` bits and the honest verifier accepts with
  probability one. -/
  complete : ∃ B : PolyExpr, ∀ x ∈ L, ∃ y : List Bool,
    (∀ r hist, (π.P.next x y r hist).length ≤ B.eval x.length) ∧
    ∀ z : List Bool, uprob (fun r : π.ExecCoins π.P x => π.outV π.P x y z r = [true]) = 1
  /-- Soundness error `s`: the verifier rejects with probability at least `1 - s(|x|)`. -/
  sound : ∀ x ∉ L, ∀ (P' : Strategy) (z : List Bool),
    1 - s x.length ≤ uprob (fun r : π.ExecCoins P' x => π.outV P' x [] z r = [false])

/-- The class `IP` of languages with an interactive proof system [PS10, §4.5] (Def-117.b):
`L ∈ IP` iff some protocol `π` is an interactive proof for `L` whose verifier reads only a
polynomial prefix `m(|x|)` of each received message (`Strategy.ReadsPrefix`), as a verifier of
time complexity `t(|x|)` in the sense of the text necessarily does.

**Repair (run-3 audit P9-1):** the run-2 definition `∃ π, InteractiveProof π L` contained every
language `{x | ∃ y, T ⟨x, y⟩ = true}` with `T` polynomial-time on the pair and no bound on
`|y|` (all of RE, by computation-history checkers): under D8 the verifier's time is polynomial
in the total input including the messages, so an unbounded prover could hand it an arbitrarily
long certificate. With the cap the verifier's work is polynomial in `|x| + |z|`, as in the
text; `WitnessRelation.mem_IP` recovers `NP ⊆ IP`. -/
def IP : Set (Language Bool) :=
  {L | ∃ (π : Protocol) (m : PolyExpr), π.V.ReadsPrefix m ∧ InteractiveProof π L}

/-- A negligible soundness error gives an interactive proof: the strict clause holds with the
negligible function `ε n := s n + 2⁻¹ ^ n`. -/
theorem InteractiveProofErr.interactiveProof {π : Protocol} {L : Language Bool} {s : ℕ → ℝ}
    (hs : Negligible s) (h : InteractiveProofErr π L s) : InteractiveProof π L where
  efficientV := h.efficientV
  complete := h.complete
  sound := by
    refine ⟨fun n => s n + (2 : ℝ)⁻¹ ^ n, hs.add negligible_two_pow_neg, fun x hx P' z => ?_⟩
    have hpos : (0 : ℝ) < (2 : ℝ)⁻¹ ^ x.length := by positivity
    linarith [h.sound x hx P' z]

/-- An interactive proof has a negligible soundness error. -/
theorem InteractiveProof.exists_err {π : Protocol} {L : Language Bool}
    (h : InteractiveProof π L) : ∃ ε : ℕ → ℝ, Negligible ε ∧ InteractiveProofErr π L ε := by
  obtain ⟨ε, hε, hsound⟩ := h.sound
  exact ⟨ε, hε, h.efficientV, h.complete, fun x hx P' z => (hsound x hx P' z).le⟩

/-- Soundness in the acceptance form: for `x ∉ L` the verifier accepts (outputs `[true]`) with
probability less than `ε(|x|)` (the form the inventory records as equivalent; the event
`out_V = [true]` is contained in `out_V ≠ [false]`). -/
theorem InteractiveProof.exists_uprob_accept_lt {π : Protocol} {L : Language Bool}
    (h : InteractiveProof π L) : ∃ ε : ℕ → ℝ, Negligible ε ∧
      ∀ x ∉ L, ∀ (P' : Strategy) (z : List Bool),
        uprob (fun r : π.ExecCoins P' x => π.outV P' x [] z r = [true]) < ε x.length := by
  obtain ⟨ε, hε, hsound⟩ := h.sound
  refine ⟨ε, hε, fun x hx P' z => ?_⟩
  have h1 := hsound x hx P' z
  have h2 : uprob (fun r : π.ExecCoins P' x => π.outV P' x [] z r = [true]) ≤
      uprob (fun r : π.ExecCoins P' x => ¬ π.outV P' x [] z r = [false]) :=
    uprob_mono fun r hr => by simp [hr]
  rw [uprob_not] at h2
  linarith

/-- Completeness without the message bound (the form in which consumers use it): every
`x ∈ L` has an auxiliary input on which the honest verifier accepts with probability one. -/
theorem InteractiveProof.exists_accept {π : Protocol} {L : Language Bool}
    (h : InteractiveProof π L) : ∀ x ∈ L, ∃ y : List Bool, ∀ z : List Bool,
      uprob (fun r : π.ExecCoins π.P x => π.outV π.P x y z r = [true]) = 1 := fun x hx =>
  let ⟨_, hB⟩ := h.complete
  let ⟨y, _, hy⟩ := hB x hx
  ⟨y, hy⟩

/-- Completeness without the message bound, for an interactive proof with soundness error. -/
theorem InteractiveProofErr.exists_accept {π : Protocol} {L : Language Bool} {s : ℕ → ℝ}
    (h : InteractiveProofErr π L s) : ∀ x ∈ L, ∃ y : List Bool, ∀ z : List Bool,
      uprob (fun r : π.ExecCoins π.P x => π.outV π.P x y z r = [true]) = 1 := fun x hx =>
  let ⟨_, hB⟩ := h.complete
  let ⟨y, _, hy⟩ := hB x hx
  ⟨y, hy⟩

/-- The completeness clause of `InteractiveProof` from bounded honest messages: if the honest
prover's messages have at most `B(|x|)` bits on instances with an `R`-witness
(`Protocol.ProverBounded`), every witness makes the honest verifier accept with probability
one, and every `x ∈ L` has a witness, then the clause holds with the bound `B` and the
witnesses as auxiliary inputs. -/
theorem Protocol.ProverBounded.exists_complete {π : Protocol} {L : Language Bool}
    {R : List Bool → List Bool → Prop} {B : PolyExpr} (hB : π.ProverBounded R B)
    (hLR : ∀ x ∈ L, ∃ y, R x y)
    (hc : ∀ x y, R x y → ∀ z : List Bool,
      uprob (fun r : π.ExecCoins π.P x => π.outV π.P x y z r = [true]) = 1) :
    ∃ B : PolyExpr, ∀ x ∈ L, ∃ y : List Bool,
      (∀ r hist, (π.P.next x y r hist).length ≤ B.eval x.length) ∧
      ∀ z : List Bool, uprob (fun r : π.ExecCoins π.P x => π.outV π.P x y z r = [true]) = 1 :=
  ⟨B, fun x hx =>
    let ⟨y, hy⟩ := hLR x hx
    ⟨y, fun r hist => (π.proverBounded_iff R B).1 hB x y r hist hy, hc x y hy⟩⟩

/-! ### Witness relations -/

/-- A witness relation for `L` [PS10, Appendix B, Definition 191.11] (Def-191.11): `x ∈ L` iff
some `y` satisfies `R x y`; witnesses have polynomially bounded length; and the relation is
decidable in polynomial time on the pair `⟨x, y⟩`.

**Deviation:** the text's `R_L(x) = {y : (x, y) ∈ L}` is a typo for `∈ R_L`; the witness-length
bound is an explicit `PolyExpr` and the decider a polynomial-time string function
(`PolyTimeComputable`). The bound is on the relation itself (every `y` with `R x y` is short),
whereas Definition 191.11 bounds only the witnesses that count (`∃ y, |y| ≤ p(|x|) ∧
(x, y) ∈ R_L`); the two agree on languages (intersect `R_L` with the bound), and the bounded
form suits Definition 119.5's "for every `y ∈ R_L(x)`", since a time-`t(|x|)` prover cannot
read a longer `y` (gate 03e, note 11). -/
structure WitnessRelation (L : Language Bool) (R : List Bool → List Bool → Prop) : Prop where
  /-- `x ∈ L` iff `x` has a witness. -/
  mem_iff : ∀ x, x ∈ L ↔ ∃ y, R x y
  /-- Witnesses have length bounded by a polynomial in `|x|`. -/
  bounded : ∃ p : PolyExpr, ∀ x y, R x y → y.length ≤ p.eval x.length
  /-- The relation is decidable in polynomial time on `⟨x, y⟩`. -/
  decidable : ∃ T : List Bool → Bool, PolyTimeComputable (fun z => [T z]) ∧
    ∀ x y, T (pairEncode x y) = true ↔ R x y

/-- The language of a relation, `{x | ∃ y, R x y}` [PS10, Definition 191.11]. -/
def witnessLanguage (R : List Bool → List Bool → Prop) : Language Bool := {x | ∃ y, R x y}

/-- The witness set `R_L(x) = {y | R x y}` [PS10, Definition 191.11]. -/
def witnessSet (R : List Bool → List Bool → Prop) (x : List Bool) : Set (List Bool) := {y | R x y}

/-- Membership in `witnessLanguage R` unfolds to the existence of a witness. -/
@[simp] theorem mem_witnessLanguage (R : List Bool → List Bool → Prop) (x : List Bool) :
    x ∈ witnessLanguage R ↔ ∃ y, R x y := Iff.rfl

/-- Membership in `witnessSet R x` unfolds to `R x y`. -/
@[simp] theorem mem_witnessSet (R : List Bool → List Bool → Prop) (x y : List Bool) :
    y ∈ witnessSet R x ↔ R x y := Iff.rfl

/-- A witness relation for `L` determines `L` as `witnessLanguage R`. -/
theorem WitnessRelation.eq_witnessLanguage {L : Language Bool} {R : List Bool → List Bool → Prop}
    (h : WitnessRelation L R) : L = witnessLanguage R :=
  Set.ext fun x => h.mem_iff x

/-- A language with a witness relation is in `NP` [PS10, Definition 191.11, the "iff" with
[AB09, Definition 2.1]].

**Proof sketch.** Use `Complexity.mem_NP_iff_exists_length_le` (the `pairEncode x u ∈ V`,
`|u| ≤ C(|x|+1)^c` form). From `h.bounded` take `p` and `C, c` with `p.eval n ≤ C(n+1)^c`
(`PolyExpr.eval_le`). From `h.decidable` take `T`; the verifier language is
`V := {z | T z = true}`, in `P` by `Complexity.mem_P_iff_polyTimeComputable` since
`[MultiTapeTM.indicator V z] = [T z]` (`funext`, `Bool.decide_eq_true`). The equivalence
`x ∈ L ↔ ∃ u, |u| ≤ C(|x|+1)^c ∧ pairEncode x u ∈ V` is `h.mem_iff`, the length bound and
the decider's specification. -/
theorem WitnessRelation.mem_NP {L : Language Bool} {R : List Bool → List Bool → Prop}
    (h : WitnessRelation L R) : L ∈ NP := by
  rw [mem_NP_iff_exists_length_le]
  obtain ⟨p, hp⟩ := h.bounded
  obtain ⟨C, c, hCc⟩ := p.eval_le
  obtain ⟨T, hT, hTR⟩ := h.decidable
  refine ⟨C, c, {z | T z = true}, mem_P_of_test hT, fun x => ?_⟩
  rw [h.mem_iff x]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, (hp x y hy).trans (hCc _), (hTR x y).2 hy⟩
  · rintro ⟨u, -, hu⟩
    exact ⟨u, (hTR x u).1 hu⟩

/-- Every `NP` language has a witness relation [PS10, Definition 191.11, converse direction].

**Proof sketch.** From `Complexity.mem_NP_iff_exists_length_le` take `C, c, V`; set
`R x y := y.length ≤ C * (x.length + 1) ^ c ∧ pairEncode x y ∈ V`. `mem_iff` is the
characterization; `bounded` is `PolyExpr.normal C c` (`PolyExpr.eval_normal`); `decidable`:
`T z := decide ((pairSndD z).length ≤ C * ((pairFstD z).length + 1) ^ c) && indicator V z`,
polynomial-time by `Complexity.polyTimeComputable_and`, `polyTimeComputable_lenLe` composed
with `pairEncode (unaryPoly (normal C c) ∘ pairFstD) pairSndD`, and
`mem_P_iff_polyTimeComputable`; on `pairEncode x y` the projections are `x` and `y`
(`pairFstD_pairEncode`, `pairSndD_pairEncode`). -/
theorem exists_witnessRelation_of_mem_NP {L : Language Bool} (h : L ∈ NP) :
    ∃ R : List Bool → List Bool → Prop, WitnessRelation L R := by
  obtain ⟨C, c, V, hV, hL⟩ := mem_NP_iff_exists_length_le.1 h
  refine ⟨fun x y => y.length ≤ C * (x.length + 1) ^ c ∧ pairEncode x y ∈ V, hL, ?_, ?_⟩
  · exact ⟨PolyExpr.normal C c, fun x y hy => by rw [PolyExpr.eval_normal]; exact hy.1⟩
  · refine ⟨fun z => decide ((pairSndD z).length ≤ C * ((pairFstD z).length + 1) ^ c) &&
      MultiTapeTM.indicator V z, ?_, ?_⟩
    · refine polyTimeComputable_and ?_ (test_of_mem_P hV)
      have hlen := polyTimeComputable_lenLe.comp
        (((polyTimeComputable_unaryPoly (PolyExpr.normal C c)).comp
          polyTimeComputable_pairFstD).pairEncode polyTimeComputable_pairSndD)
      convert hlen using 1
      funext z
      simp [PolyExpr.eval_normal]
    · intro x y
      simp [MultiTapeTM.indicator]

/-! ### Efficient provers -/

/-- An interactive proof for `L` with efficient prover with respect to the witness relation
`R` [PS10, Definition 119.5] (Def-119.5): an interactive proof whose prover is efficient (the
witness is its auxiliary input) and which is complete for **every** witness `y` of `x`
(Definition 116.1 only asks for some auxiliary input).

**Deviation (D8; ruling G3-3 of gate 03):** the text's "P is p.p.t." is `Strategy.Efficient`
(time polynomial in the total input length, D8) together with a polynomial bound `B(|x|)` on
the prover's messages on every instance with a witness (`Protocol.ProverBounded`: the text's
p.p.t. machine writes at most `t(|x|)` bits per message, the convention of ch. 6); the
verifier is as in `InteractiveProof`. -/
structure EfficientProverProof (π : Protocol) (L : Language Bool)
    (R : List Bool → List Bool → Prop) : Prop extends InteractiveProof π L where
  /-- The prover is efficient (`Strategy.Efficient`, D8). -/
  efficientP : π.P.Efficient
  /-- The prover's messages have at most `B(|x|)` bits on instances with a witness. -/
  boundedP : ∃ B : PolyExpr, π.ProverBounded R B
  /-- Completeness for every witness. -/
  completeWitness : ∀ x y, R x y → ∀ z : List Bool,
    uprob (fun r : π.ExecCoins π.P x => π.outV π.P x y z r = [true]) = 1

/-- An interactive proof with soundness error `s` and efficient prover with respect to `R`
[PS10, Definition 119.5 with the soundness error of §4.5] (Def-119.5, Def-117.a).

**Deviation (D8; ruling G3-3 of gate 03):** as for `EfficientProverProof` (`Efficient` prover
with messages of at most `B(|x|)` bits on instances with a witness). -/
structure EfficientProverProofErr (π : Protocol) (L : Language Bool)
    (R : List Bool → List Bool → Prop) (s : ℕ → ℝ) : Prop extends InteractiveProofErr π L s where
  /-- The prover is efficient (`Strategy.Efficient`, D8). -/
  efficientP : π.P.Efficient
  /-- The prover's messages have at most `B(|x|)` bits on instances with a witness. -/
  boundedP : ∃ B : PolyExpr, π.ProverBounded R B
  /-- Completeness for every witness. -/
  completeWitness : ∀ x y, R x y → ∀ z : List Bool,
    uprob (fun r : π.ExecCoins π.P x => π.outV π.P x y z r = [true]) = 1

/-- A negligible soundness error gives an interactive proof with efficient prover. -/
theorem EfficientProverProofErr.efficientProverProof {π : Protocol} {L : Language Bool}
    {R : List Bool → List Bool → Prop} {s : ℕ → ℝ} (hs : Negligible s)
    (h : EfficientProverProofErr π L R s) : EfficientProverProof π L R where
  toInteractiveProof := h.toInteractiveProofErr.interactiveProof hs
  efficientP := h.efficientP
  boundedP := h.boundedP
  completeWitness := h.completeWitness

/-- An interactive proof with efficient prover has a negligible soundness error. -/
theorem EfficientProverProof.exists_err {π : Protocol} {L : Language Bool}
    {R : List Bool → List Bool → Prop} (h : EfficientProverProof π L R) :
    ∃ ε : ℕ → ℝ, Negligible ε ∧ EfficientProverProofErr π L R ε := by
  obtain ⟨ε, hε, herr⟩ := h.toInteractiveProof.exists_err
  exact ⟨ε, hε, herr, h.efficientP, h.boundedP, h.completeWitness⟩

/-! ### The trivial NP protocol -/

/-- The one-message protocol in which the prover sends its auxiliary input `y` and the
verifier accepts iff `T ⟨x, y'⟩`, where `y'` is the received message truncated to its first
`p(|x|)` bits [PS10, §4.5, "`NP ⊆ IP`": the certificate is sent in one round, and a
polynomial-time verifier reads at most polynomially many bits of it]: prover first, one
message, no coins.

**Repair (run-3 audit P9-1):** the witness-length bound `p : PolyExpr` is a parameter and the
verifier reads only the first `p(|x|)` bits of the message (`npProtocol_readsPrefix`), so that
the protocol witnesses `L ∈ IP` under the repaired class; the run-2 verifier read the whole
message. -/
def npProtocol (T : List Bool → Bool) (p : PolyExpr) : Protocol where
  P := ⟨fun _ y _ _ => y, .const 0⟩
  V := ⟨fun x _ _ hist => [T (pairEncode x ((hist.headD []).take (p.eval x.length)))], .const 0⟩
  rounds := .const 1
  verifierFirst := false

/-- In `npProtocol T p` the verifier's output against any prover `P'` is the verdict `T` on
`⟨x, m'⟩`, where `m'` is the first `p(|x|)` bits of the single message `P'` sends on the empty
history. -/
theorem npProtocol_outV (T : List Bool → Bool) (p : PolyExpr) (P' : Strategy) (x y z : List Bool)
    (r : (npProtocol T p).ExecCoins P' x) :
    (npProtocol T p).outV P' x y z r =
      [T (pairEncode x ((P'.next x y (List.ofFn r.1) []).take (p.eval x.length)))] := by
  simp [Protocol.outV, Protocol.transcriptWith, npProtocol, exec, moverIsV]

/-- The verifier of `npProtocol T p` reads only the first `p(|x|)` bits of the message
(`List.take_take`). -/
theorem npProtocol_readsPrefix (T : List Bool → Bool) (p : PolyExpr) :
    (npProtocol T p).V.ReadsPrefix p := by
  intro x z r hist
  cases hist with
  | nil => rfl
  | cons m hist => simp [npProtocol, List.take_take]

/-- The verifier of `npProtocol T p` is efficient when `T` is polynomial-time: one activation of
the uniform machine computing `w ↦ [T ⟨x, m.take (p(|x|))⟩]` from the projections of the layout
`⟨⟨⟨1^n, ⟨⟨x, z⟩, msgs⟩⟩, []⟩, r⟩`.

**Proof sketch.** `x` and the first message `m` are fixed `pairFstD`/`pairSndD` projection
chains of the raw input `w` (`PolyTimeComputable.comp`); the truncation `m.take (p(|x|))` is
`Complexity.polyTimeComputable_pairTakePoly p` applied to `⟨x, m⟩`
(`PolyTimeComputable.pairEncode`), and `T` is applied to `⟨x, m.take (p(|x|))⟩` (`hT.comp`).
The uniform machine `NUPPT.ofPolyTimeUniform` of this function has the required next-message
function on every history (`NUPPT.runAtL_ofPolyTimeUniform`, `Strategy.pairFstD_encodeMsgs`). -/
theorem npProtocol_efficientV (T : List Bool → Bool) (p : PolyExpr)
    (hT : PolyTimeComputable fun z => [T z]) : (npProtocol T p).V.Efficient := by
  have harg : PolyTimeComputable fun w => pairSndD (pairFstD (pairFstD w)) :=
    polyTimeComputable_pairSndD.comp (polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD)
  have hx : PolyTimeComputable fun w => pairFstD (pairFstD (pairSndD (pairFstD (pairFstD w)))) :=
    polyTimeComputable_pairFstD.comp (polyTimeComputable_pairFstD.comp harg)
  have hm : PolyTimeComputable fun w => pairFstD (pairSndD (pairSndD (pairFstD (pairFstD w)))) :=
    polyTimeComputable_pairFstD.comp (polyTimeComputable_pairSndD.comp harg)
  have htake : PolyTimeComputable fun w =>
      (pairFstD (pairSndD (pairSndD (pairFstD (pairFstD w))))).take
        (p.eval (pairFstD (pairFstD (pairSndD (pairFstD (pairFstD w))))).length) := by
    convert (polyTimeComputable_pairTakePoly p).comp (hx.pairEncode hm) using 1
    funext w
    simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  have hF : PolyTimeComputable fun w =>
      [T (pairEncode (pairFstD (pairFstD (pairSndD (pairFstD (pairFstD w)))))
        ((pairFstD (pairSndD (pairSndD (pairFstD (pairFstD w))))).take
          (p.eval (pairFstD (pairFstD (pairSndD (pairFstD (pairFstD w))))).length)))] :=
    hT.comp (hx.pairEncode htake)
  refine ⟨NUPPT.ofPolyTimeUniform hF (.const 0), NUPPT.ofPolyTimeUniform_uniform hF _, rfl,
    fun x z r hist => ?_⟩
  simp [npProtocol, Strategy.ofNUPPT_next, NUPPT.runAtL_ofPolyTimeUniform, NUPPT.advInput,
    Strategy.pairFstD_encodeMsgs]

/-- The prover of `npProtocol T p` is efficient: it copies the auxiliary input, the projection
`pairSndD ∘ pairFstD` of the argument of the layout. -/
theorem npProtocol_efficientP (T : List Bool → Bool) (p : PolyExpr) :
    (npProtocol T p).P.Efficient := by
  have harg : PolyTimeComputable fun w => pairSndD (pairFstD (pairFstD w)) :=
    polyTimeComputable_pairSndD.comp (polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD)
  have hF : PolyTimeComputable fun w => pairSndD (pairFstD (pairSndD (pairFstD (pairFstD w)))) :=
    polyTimeComputable_pairSndD.comp (polyTimeComputable_pairFstD.comp harg)
  refine ⟨NUPPT.ofPolyTimeUniform hF (.const 0), NUPPT.ofPolyTimeUniform_uniform hF _, rfl,
    fun x z r hist => ?_⟩
  simp [npProtocol, Strategy.ofNUPPT_next, NUPPT.runAtL_ofPolyTimeUniform, NUPPT.advInput]

/-- The prover of `npProtocol T p` sends its auxiliary input, so on witnesses of length at most
`p(|x|)` its message has at most `p(|x|)` bits (ruling G3-3 of gate 03). -/
theorem npProtocol_proverBounded (T : List Bool → Bool) (p : PolyExpr)
    {R : List Bool → List Bool → Prop} (hp : ∀ x y, R x y → y.length ≤ p.eval x.length) :
    (npProtocol T p).ProverBounded R p :=
  ((npProtocol T p).proverBounded_iff R p).2 fun x y _ _ hxy => hp x y hxy

/-- Non-vacuity of Definitions 116.1 and 119.5 [PS10, §4.5, "`NP ⊆ IP`"]: for a witness relation
`R` of `L` decided by the polynomial-time predicate `T`, with witnesses of length at most
`p(|x|)`, the one-message protocol in which the prover sends a witness is an interactive proof
for `L` with efficient prover with respect to `R` (the verifier rejects every `x ∉ L` with
probability one).

**Repair (run-3 audit P9-1):** the witness-length bound `p` with `hp` added (the verifier of
`npProtocol T p` reads only `p(|x|)` bits).

**Proof sketch.** The verifier's output is `[T ⟨x, m.take (p(|x|))⟩]` for the message `m` sent
(`npProtocol_outV`); the honest prover sends `y`, which the truncation leaves unchanged since
`|y| ≤ p(|x|)` (`hp`, `List.take_of_length_le`). Completeness for every witness `y`:
`T ⟨x, y⟩ = true` (`hTR`) on every coin pair, so the probability is one
(`HardcoreBit.uprob_eq_one_of_forall`); the prover's message `y` has at most `p(|x|)` bits
(`npProtocol_proverBounded`), and completeness follows for `x ∈ L` with a witness from
`hR.mem_iff` (`Protocol.ProverBounded.exists_complete`). Soundness with `ε n := 2⁻¹ ^ n`
(`negligible_two_pow_neg`; the literal clause is strict, so `ε = 0` is not admissible): for
`x ∉ L` no string — in particular no truncated message — is a witness, so `T ⟨x, ·⟩ = false`
and the verifier outputs `[false]` on every coin pair, with probability `1 > 1 - ε(|x|)`.
Efficiency of both parties: `npProtocol_efficientV`, `npProtocol_efficientP`. -/
theorem npProtocol_interactiveProof {L : Language Bool} {R : List Bool → List Bool → Prop}
    (hR : WitnessRelation L R) (T : List Bool → Bool) (p : PolyExpr)
    (hT : PolyTimeComputable fun z => [T z])
    (hTR : ∀ x y, T (pairEncode x y) = true ↔ R x y)
    (hp : ∀ x y, R x y → y.length ≤ p.eval x.length) :
    EfficientProverProof (npProtocol T p) L R := by
  have hcw : ∀ x y, R x y → ∀ z : List Bool,
      uprob (fun r : (npProtocol T p).ExecCoins (npProtocol T p).P x =>
        (npProtocol T p).outV (npProtocol T p).P x y z r = [true]) = 1 := by
    intro x y hy z
    refine HardcoreBit.uprob_eq_one_of_forall fun r => ?_
    rw [npProtocol_outV]
    simp [npProtocol, List.take_of_length_le (hp x y hy), (hTR x y).2 hy]
  refine
    { efficientV := npProtocol_efficientV T p hT
      complete := (npProtocol_proverBounded T p hp).exists_complete
        (fun x hx => (hR.mem_iff x).1 hx) hcw
      sound := ?_
      efficientP := npProtocol_efficientP T p
      boundedP := ⟨p, npProtocol_proverBounded T p hp⟩
      completeWitness := hcw }
  refine ⟨fun n => (2 : ℝ)⁻¹ ^ n, negligible_two_pow_neg, fun x hx P' z => ?_⟩
  have hall : ∀ r : (npProtocol T p).ExecCoins P' x,
      (npProtocol T p).outV P' x [] z r = [false] := by
    intro r
    rw [npProtocol_outV]
    have hno : ¬ R x ((P'.next x [] (List.ofFn r.1) []).take (p.eval x.length)) :=
      fun hw => hx ((hR.mem_iff x).2 ⟨_, hw⟩)
    have hfalse :
        T (pairEncode x ((P'.next x [] (List.ofFn r.1) []).take (p.eval x.length))) = false := by
      rw [← Bool.not_eq_true, hTR]
      exact hno
    rw [hfalse]
  rw [HardcoreBit.uprob_eq_one_of_forall hall]
  exact sub_lt_self _ (by positivity)

/-- Every language with a witness relation is in `IP` [PS10, §4.5, "`NP ⊆ IP`"] (Claim-117.c):
the one-message protocol `npProtocol T p`, with the relation's decider `T` and witness-length
bound `p`, is an interactive proof whose verifier reads only `p(|x|)` bits of the message
(`npProtocol_readsPrefix`, `npProtocol_interactiveProof`). -/
theorem WitnessRelation.mem_IP {L : Language Bool} {R : List Bool → List Bool → Prop}
    (h : WitnessRelation L R) : L ∈ IP := by
  obtain ⟨p, hp⟩ := h.bounded
  obtain ⟨T, hT, hTR⟩ := h.decidable
  exact ⟨npProtocol T p, p, npProtocol_readsPrefix T p,
    (npProtocol_interactiveProof h T p hT hTR hp).toInteractiveProof⟩

/-- `NP ⊆ IP` [PS10, §4.5] (Claim-117.c): every `NP` language has a witness relation
(`exists_witnessRelation_of_mem_NP`), hence an interactive proof with a prefix-reading
verifier (`WitnessRelation.mem_IP`). -/
theorem NP_subset_IP : NP ⊆ IP := fun _ h =>
  (Classical.choose_spec (exists_witnessRelation_of_mem_NP h)).mem_IP

end TCSlib.Cryptography

## ===== TCSlib/Cryptography/ZeroKnowledge/Defs.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.ZeroKnowledge.Interaction
import TCSlib.Cryptography.Asymptotic.Adversary
import TCSlib.Cryptography.Asymptotic.Sampling
import TCSlib.Cryptography.Foundations.Negligible
import TCSlib.Cryptography.ZeroKnowledge.EncodingMachines
import TCSlib.Complexity.Randomized.Closure

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Zero-knowledge: honest-verifier, general, statistical and perfect

The zero-knowledge notions of [PS10, §4.6] on top of the interaction model of
`Interaction.lean` (foundation decision D8): honest-verifier zero-knowledge
[PS10, Definition 121.1], zero-knowledge against every efficient verifier
[PS10, Definition 121.2], and the perfect and statistical variants (Def-122.a) through the
sup-over-test-sets closeness `StatClose` of `Asymptotic/Sampling.lean`, together with the
implications statistical ⇒ computational (`StatZK.zk`, `StatZK.hvzk`), general ⇒ honest-verifier
(`ZK.hvzk`), and the negligibility bookkeeping converting the chapter's per-vertex bounds
`2^{-n}`, `e^{-n}` into functions of the instance length `|x|` (Inf-4.4).

The simulator is a uniform `Complexity.NUPPT` run once at parameter `|x|` on `⟨x, z⟩`
(`Complexity.NUPPT.simulate`); its output is a word read as an encoded view
(`View.encode`: `⟨⟨x, z⟩, ⟨r, messages⟩⟩`), and the distinguisher is a non-uniform PPT run at
parameter `|x|` on the encoded view (`Complexity.NUPPT.distinguisherL`).

**Deviation (D8):** strict PPT simulators (the text's expected polynomial time is not
formalized; the rewinding simulators of the chapter are truncated and the theorems become
statistical); the auxiliary input of the verifier is bounded by an arbitrary polynomial
`Lz : PolyExpr` quantified after the simulator (the class a `t(|x|)`-time verifier can read,
and what the non-uniform reduction of [PS10, Proposition 128.8] needs); the error bound is
a function of `|x|` (the text's `e(n)` leaves `n` undefined); the honest-verifier notion is
stated for a protocol and a witness relation without assuming the proof property, which the
theorems add separately.
The bound `Lz` is necessary for the 3-colouring protocol, not only convenient (gate 03e,
note 9; round 2, finding 6). The distinguisher runs in time polynomial in its input, the
encoded view, which contains `z`. With `|z|` exponential in `ℓ(n)` it can open the perfectly
binding commitments by exhaustive search. On a graph with two proper colourings outside one
colour-permutation orbit, that tells the two real views apart with advantage 1, while the
simulator does not see the witness. Read literally, [PS10, Definition 121.2] (every
`z ∈ {0,1}*`, with `D` polynomial-time in its input) has the same defect for that protocol.
Protocols with exactly simulable views are not affected. For the same reason the
distinguisher's advice is indexed by the parameter `|x|`, not by its input length.

**Perfect zero-knowledge (ruling G3-4 of gate 03).** With strict simulators and honest parties
drawing polynomially many fair coins (D8, D10), no protocol of the source attains `PerfectZK`
or `PerfectZKAbort` (see their docstrings). The source's perfect zero-knowledge protocol,
graph isomorphism [PS10, Theorem 122.3], is formalized as `StatZK` with negligible error
(`gi_statZK`, `ZeroKnowledge/GraphIsomorphismZK.lean`), the substantive instance of the
notions of this file; `perfectZK_zeroRounds` is a degenerate one. The abort form implies
statistical zero-knowledge with error `2^{-|x|}` (`PerfectZKAbort.statZK`), by running the
aborting simulator `|x|` times on fresh coins (`AbortRetry.retry`).

## Main definitions

* `Complexity.NUPPT.simulate` — the simulator's output on `(x, z)`.
* `TCSlib.Cryptography.HVZK` — honest-verifier zero-knowledge [PS10, Definition 121.1]
  (Def-121.1).
* `TCSlib.Cryptography.ZK` — zero-knowledge [PS10, Definition 121.2] (Def-121.2).
* `TCSlib.Cryptography.StatZK`, `TCSlib.Cryptography.PerfectZK`,
  `TCSlib.Cryptography.PerfectZKAbort` — statistical zero-knowledge with error `δ(|x|)`,
  perfect zero-knowledge (`δ = 0`), and the abort form of perfect zero-knowledge
  [Gol01, Definition 4.3.1] (Def-122.a).
* `TCSlib.Cryptography.AbortRetry.attempt`, `TCSlib.Cryptography.AbortRetry.retry` — one
  attempt of an aborting simulator on a coin block, and the simulator that retries it `|x|`
  times (as functions of the machine layout).

## Main results

* `TCSlib.Cryptography.StatZK.zk`, `TCSlib.Cryptography.StatZK.hvzk` — statistical
  zero-knowledge with negligible error implies zero-knowledge and honest-verifier
  zero-knowledge (`distAdv_le_of_statClose`).
* `TCSlib.Cryptography.ZK.hvzk` — zero-knowledge implies honest-verifier zero-knowledge.
* `TCSlib.Cryptography.PerfectZK.zk`, `TCSlib.Cryptography.StatZK.mono` — perfect
  zero-knowledge is zero-knowledge; weakening the error.
* `TCSlib.Cryptography.perfectZK_zeroRounds` — non-vacuity: the protocol with no messages is
  perfectly zero-knowledge.
* `TCSlib.Cryptography.PerfectZKAbort.statZK`, `TCSlib.Cryptography.PerfectZKAbort.zk` — the
  abort form implies statistical zero-knowledge with error `2^{-|x|}`, hence zero-knowledge
  (`TCSlib.Cryptography.AbortRetry.statClose_retry`: the first non-`⊥` output of `K`
  independent runs of an aborting sampler is `2^{-K}`-close to its conditional law;
  `TCSlib.Cryptography.AbortRetry.exists_retrySimulator`: the retrying simulator is a uniform
  PPT, by `EncodingMachines.polyTimeComputable_firstIdx`, an instance of
  `Complexity.polyTimeComputable_iterateFind`).
* `TCSlib.Cryptography.negligible_inv_pow_sqrt_div`,
  `TCSlib.Cryptography.negligible_two_pow_neg_sqrt_div`,
  `TCSlib.Cryptography.negligible_exp_neg_sqrt_div`,
  `TCSlib.Cryptography.negligible_of_le_inv_pow_sqrt_div` — `a^{-√(N/C)}` is negligible
  in `N` (Inf-4.4): the per-vertex bounds of the graph protocols are negligible in `|x|`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§4.6 Zero-knowledge, pp. 120–122.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, Lemma 3.1 (statistical distance bounds every advantage).
* [Gol01] O. Goldreich, *Foundations of Cryptography, Volume I: Basic Tools*, Cambridge
  University Press, 2001, Definition 4.3.1 (perfect zero-knowledge with abort).
-/

namespace TCSlib.Cryptography

open Complexity Turing

/-! ### Simulators -/

/-- The simulator's output on `(x, z)` [PS10, Definitions 121.1 and 121.2, `S(x, z)`]: one
activation of `S` at parameter `|x|` on `⟨x, z⟩`, a word read as an encoded view. -/
def _root_.Complexity.NUPPT.simulate (S : NUPPT) (x z : List Bool) (r : S.Coins x.length) :
    List Bool :=
  S.runAt x.length (pairEncode x z) r

/-- `simulate` unfolds to the typed activation at parameter `|x|`. -/
theorem _root_.Complexity.NUPPT.simulate_eq (S : NUPPT) (x z : List Bool)
    (r : S.Coins x.length) : S.simulate x z r = S.runAt x.length (pairEncode x z) r := rfl

/-! ### Honest-verifier and general zero-knowledge -/

/-- Honest-verifier zero-knowledge of `π` for the witness relation `R`
[PS10, Definition 121.1] (Def-121.1): there is a uniform PPT simulator `S` such that for every
auxiliary-input bound `Lz` and every non-uniform PPT distinguisher `D` there is a negligible `ε`
with, for all `x`, witnesses `y` of `x` and auxiliary inputs `z` of length `≤ Lz(|x|)`, the
advantage of `D` (at parameter `|x|`) between the honest verifier's view of
`P(x, y) ↔ V(x, z)` and `S(x, z)` at most `ε(|x|)`.

**Deviation (D8):** strict PPT simulator; auxiliary inputs bounded by `∀ Lz : PolyExpr`;
simulator and distinguisher at parameter `|x|`; views encoded as `⟨⟨x, z⟩, ⟨r, msgs⟩⟩`. -/
def HVZK (π : Protocol) (R : List Bool → List Bool → Prop) : Prop :=
  ∃ S : NUPPT, S.Uniform ∧ ∀ (Lz : PolyExpr) (D : NUPPT), ∃ ε : ℕ → ℝ, Negligible ε ∧
    ∀ x y z, R x y → z.length ≤ Lz.eval x.length →
      distAdv (fun r => (π.viewV x y z r).encode) (S.simulate x z) (D.distinguisherL x.length) ≤
        ε x.length

/-- Zero-knowledge of `π` for the witness relation `R` [PS10, Definition 121.2] (Def-121.2):
for every efficient verifier strategy `V'` there is a uniform PPT simulator `S` such that for
every auxiliary-input bound `Lz` and every non-uniform PPT distinguisher `D` there is a
negligible `ε` with, for all `x`, witnesses `y` and auxiliary inputs `z` of length `≤ Lz(|x|)`,
the advantage of `D` between the view of `V'` in `P(x, y) ↔ V'(x, z)` and `S(x, z)` at most
`ε(|x|)`.

**Deviation (D8):** strict PPT simulator; auxiliary inputs bounded by `∀ Lz : PolyExpr`;
simulator and distinguisher at parameter `|x|`; views encoded as `⟨⟨x, z⟩, ⟨r, msgs⟩⟩`. The
cheating verifier `V'` is only `Efficient`, with no message-prefix cap (question Q-1 of
gate 03, ruled: no cap on `V*`), so its class is larger than the text's. Since the honest
prover's messages are polynomially bounded in `|x|` in the proof systems
(`Protocol.ProverBounded`, ruling G3-3 of gate 03), the view of every efficient `V'` — `x`,
`z`, its tape and the honest prover's messages — is polynomially bounded all the same. -/
def ZK (π : Protocol) (R : List Bool → List Bool → Prop) : Prop :=
  ∀ V' : Strategy, V'.Efficient → ∃ S : NUPPT, S.Uniform ∧
    ∀ (Lz : PolyExpr) (D : NUPPT), ∃ ε : ℕ → ℝ, Negligible ε ∧
      ∀ x y z, R x y → z.length ≤ Lz.eval x.length →
        distAdv (fun r => ((π.withV V').viewV x y z r).encode) (S.simulate x z)
          (D.distinguisherL x.length) ≤ ε x.length

/-- Statistical zero-knowledge of `π` for `R` with error `δ(|x|)` (Def-122.a, campaign
addition needed for the truncated simulators): for every efficient `V'` there is a uniform PPT
simulator whose output on `(x, z)` is `StatClose` (every test set, sup form) within `δ(|x|)`
to the view of `V'` in `P(x, y) ↔ V'(x, z)`, for all `x`, witnesses `y` and all auxiliary
inputs `z`.

**Deviation (D8):** strict PPT simulator; the bound is in `|x|`. -/
def StatZK (π : Protocol) (R : List Bool → List Bool → Prop) (δ : ℕ → ℝ) : Prop :=
  ∀ V' : Strategy, V'.Efficient → ∃ S : NUPPT, S.Uniform ∧ ∀ x y z, R x y →
    StatClose (fun r => ((π.withV V').viewV x y z r).encode) (S.simulate x z) (δ x.length)

/-- Perfect zero-knowledge [PS10, §4.6, "perfect zero-knowledge"] (Def-122.a): statistical
zero-knowledge with error `0`, i.e. the simulator's output has exactly the law of the view.

**Cost (D8, D10; ruling G3-4 of gate 03):** no protocol of the source attains this notion. A
strict simulator with bit coins outputs every string with a dyadic probability, and an
honest prover drawing polynomially many fair coins cannot draw a uniform permutation of
`n ≥ 3` points (`n! ∤ 2^c`), so the reply of the honest graph-isomorphism prover
[PS10, Protocol 120.6] depends on the witness. [PS10, Theorem 122.3] is formalized as
`StatZK` with negligible error (`gi_statZK`); the instances of this notion are degenerate
(`perfectZK_zeroRounds`). -/
def PerfectZK (π : Protocol) (R : List Bool → List Bool → Prop) : Prop :=
  StatZK π R (fun _ => 0)

/-- Perfect zero-knowledge with abort [Gol01, Definition 4.3.1] (Def-122.a, the GMR form):
for every efficient `V'` there is a uniform PPT simulator that outputs `⊥ = []` with
probability at most `1/2` and whose output, conditioned on not aborting, has exactly the law
of the view of `V'`: for every test set `T`,
`Pr[T(view)] · Pr[S ≠ ⊥] = Pr[S ≠ ⊥ ∧ T(S)]` (`⊥ = []` is never a view encoding).

**Cost (D8, D10; ruling G3-4 of gate 03):** no protocol of the source attains this notion:
as for `PerfectZK`, the honest graph-isomorphism prover's permutation, drawn from fair coins,
is not uniform, so its reply depends on the witness, which no simulator sees. The abort form
holds for ideal permutations at the concrete layer (`giSimAttempt_perfectAbort`). It implies
statistical zero-knowledge with error `2^{-|x|}` (`PerfectZKAbort.statZK`), hence
zero-knowledge (`PerfectZKAbort.zk`); the source's "perfect" results are stated as `StatZK`
with negligible error. -/
def PerfectZKAbort (π : Protocol) (R : List Bool → List Bool → Prop) : Prop :=
  ∀ V' : Strategy, V'.Efficient → ∃ S : NUPPT, S.Uniform ∧ ∀ x y z, R x y →
    uprob (fun r : S.Coins x.length => S.simulate x z r = []) ≤ 1 / 2 ∧
    ∀ T : List Bool → Prop,
      uprob (fun r : (π.withV V').ExecCoins π.P x => T ((π.withV V').viewV x y z r).encode) *
          uprob (fun r : S.Coins x.length => S.simulate x z r ≠ []) =
        uprob (fun r : S.Coins x.length => S.simulate x z r ≠ [] ∧ T (S.simulate x z r))

/-! ### Implications between the notions -/

/-- Statistical zero-knowledge with negligible error implies zero-knowledge
[PS10, §4.6, perfect/statistical ⇒ computational]: the same simulator works for every
distinguisher, with `ε := δ`, since a distinguisher's advantage between `δ`-close samplers is
at most `δ` (`distAdv_le_of_statClose`, [Gar26, Lemma 3.1]). -/
theorem StatZK.zk {π : Protocol} {R : List Bool → List Bool → Prop} {δ : ℕ → ℝ}
    (hδ : Negligible δ) (h : StatZK π R δ) : ZK π R := by
  intro V' hV'
  obtain ⟨S, hS, hclose⟩ := h V' hV'
  exact ⟨S, hS, fun _ D => ⟨δ, hδ, fun x y z hR _ =>
    distAdv_le_of_statClose _ _ (hclose x y z hR) _⟩⟩

/-- Statistical zero-knowledge with negligible error implies honest-verifier zero-knowledge
when the honest verifier is efficient: instantiate `V' := V` (`Protocol.withV_self`) and
apply `distAdv_le_of_statClose`. -/
theorem StatZK.hvzk {π : Protocol} {R : List Bool → List Bool → Prop} {δ : ℕ → ℝ}
    (hδ : Negligible δ) (hV : π.V.Efficient) (h : StatZK π R δ) : HVZK π R := by
  obtain ⟨S, hS, hclose⟩ := h π.V hV
  refine ⟨S, hS, fun _ D => ⟨δ, hδ, fun x y z hR _ => ?_⟩⟩
  have hc := hclose x y z hR
  rw [Protocol.withV_self] at hc
  exact distAdv_le_of_statClose _ _ hc _

/-- Zero-knowledge implies honest-verifier zero-knowledge when the honest verifier is
efficient [PS10, §4.6, after Definition 121.2]: instantiate `V' := V`. -/
theorem ZK.hvzk {π : Protocol} {R : List Bool → List Bool → Prop} (hV : π.V.Efficient)
    (h : ZK π R) : HVZK π R := by
  obtain ⟨S, hS, hsim⟩ := h π.V hV
  refine ⟨S, hS, fun Lz D => ?_⟩
  obtain ⟨ε, hε, hadv⟩ := hsim Lz D
  refine ⟨ε, hε, fun x y z hR hz => ?_⟩
  have hc := hadv x y z hR hz
  rwa [Protocol.withV_self] at hc

/-- Weakening the statistical error. -/
theorem StatZK.mono {π : Protocol} {R : List Bool → List Bool → Prop} {δ δ' : ℕ → ℝ}
    (h : StatZK π R δ) (hle : ∀ n, δ n ≤ δ' n) : StatZK π R δ' := by
  intro V' hV'
  obtain ⟨S, hS, hclose⟩ := h V' hV'
  exact ⟨S, hS, fun x y z hR => (hclose x y z hR).mono (hle _)⟩

/-- The zero function is negligible. -/
theorem negligible_const_zero : Negligible (fun _ => (0 : ℝ)) := fun c =>
  ⟨1, fun n hn => by
    rw [abs_zero]
    exact one_div_pos.mpr (pow_pos (Nat.cast_pos.mpr hn) c)⟩

/-- Perfect zero-knowledge is statistical zero-knowledge with error `0`. -/
theorem PerfectZK.statZK {π : Protocol} {R : List Bool → List Bool → Prop} (h : PerfectZK π R) :
    StatZK π R (fun _ => 0) := h

/-- Perfect zero-knowledge implies zero-knowledge [PS10, §4.6]. -/
theorem PerfectZK.zk {π : Protocol} {R : List Bool → List Bool → Prop} (h : PerfectZK π R) :
    ZK π R :=
  StatZK.zk negligible_const_zero h

/-- Non-vacuity (gate 03e, note 10): the protocol with no messages is perfectly
zero-knowledge for every relation.

**Proof sketch.** The view of any `V'` is `⟨x, z, r, []⟩` (no moves, `exec_zero`), and the
simulator `NUPPT.ofPolyTimeUniform` of the layout map `w ↦ ⟨inArg w, ⟨inCoins w, []⟩⟩` with
`V'`'s coin polynomial outputs `⟨⟨x, z⟩, ⟨r, []⟩⟩` on its own tape `r`; the prover's tape does
not enter the view (`uprob_fst` after `Equiv.prodComm`), so the two laws coincide. -/
theorem perfectZK_zeroRounds (P V : Strategy) (b : Bool) (R : List Bool → List Bool → Prop) :
    PerfectZK ⟨P, V, .const 0, b⟩ R := by
  intro V' _
  have hF : PolyTimeComputable fun w =>
      pairEncode (NUPPT.inArg w) (pairEncode (NUPPT.inCoins w) []) :=
    NUPPT.polyTimeComputable_inArg.pairEncode
      (NUPPT.polyTimeComputable_inCoins.pairEncode (polyTimeComputable_const []))
  refine ⟨NUPPT.ofPolyTimeUniform hF V'.coins, NUPPT.ofPolyTimeUniform_uniform hF _,
    fun x y z _ T => ?_⟩
  have h1 : uprob (fun r : (Protocol.withV ⟨P, V, .const 0, b⟩ V').ExecCoins P x =>
      T ((Protocol.withV ⟨P, V, .const 0, b⟩ V').viewV x y z r).encode) =
      uprob (fun ρ : V'.Coins x.length =>
        T (pairEncode (pairEncode x z) (pairEncode (List.ofFn ρ) []))) := by
    rw [← uprob_comp_equiv (Equiv.prodComm _ _)]
    exact uprob_fst (fun ρ : V'.Coins x.length =>
      T (pairEncode (pairEncode x z) (pairEncode (List.ofFn ρ) [])))
  have h2 : uprob (fun ρ : (NUPPT.ofPolyTimeUniform hF V'.coins).Coins x.length =>
      T ((NUPPT.ofPolyTimeUniform hF V'.coins).simulate x z ρ)) =
      uprob (fun ρ : V'.Coins x.length =>
        T (pairEncode (pairEncode x z) (pairEncode (List.ofFn ρ) []))) := by
    refine OneWay.uprob_congr fun ρ => ?_
    rw [NUPPT.simulate_eq, NUPPT.runAt_eq, NUPPT.runAtL_ofPolyTimeUniform]
    simp [NUPPT.inArg, NUPPT.inCoins, NUPPT.advInput]
  simp only [h2]
  rw [abs_nonpos_iff, sub_eq_zero]
  exact h1

/-! ### Retrying an aborting simulator -/

namespace AbortRetry

open EncodingMachines Finset Complexity.StateLoop

/-- One attempt of the retrying simulator on its machine layout
`w = ⟨⟨⟨1^n, y⟩, α⟩, r⟩` at the index `t`: the simulator `S` at parameter `n = |1^n|` on the
argument `y`, with empty advice and the `t`-th block of `S.coinLen n` coins of `r`. -/
def attempt (S : NUPPT) (w : List Bool) (t : ℕ) : List Bool :=
  S.output (NUPPT.layout (NUPPT.inParam w) (NUPPT.inArg w) []
    (((NUPPT.inCoins w).drop (t * S.coinLen (NUPPT.inParam w).length)).take
      (S.coinLen (NUPPT.inParam w).length)))

/-- One attempt unfolded: `attempt S w t` is `S.output` on the layout with parameter
`inParam w`, argument `inArg w`, empty advice and coins
`((inCoins w).drop (t · c)).take c`, where `c = S.coinLen |inParam w|`. -/
theorem attempt_eq (S : NUPPT) (w : List Bool) (t : ℕ) :
    attempt S w t = S.output (NUPPT.layout (NUPPT.inParam w) (NUPPT.inArg w) []
      (((NUPPT.inCoins w).drop (t * S.coinLen (NUPPT.inParam w).length)).take
        (S.coinLen (NUPPT.inParam w).length))) :=
  rfl

/-- The retrying simulator on its machine layout `w = ⟨⟨⟨1^n, y⟩, α⟩, r⟩`
(for the abort form of [Gol01, Definition 4.3.1], amplified by repetition): the
first of the `n` attempts that does not output `⊥ = []` (the first accepted index,
`EncodingMachines.firstIdx`), or `⊥` if every attempt aborts. -/
noncomputable def retry (S : NUPPT) (w : List Bool) : List Bool :=
  if firstIdx (fun t => decide (attempt S w t ≠ [])) (NUPPT.inParam w).length <
      (NUPPT.inParam w).length then
    attempt S w (firstIdx (fun t => decide (attempt S w t ≠ [])) (NUPPT.inParam w).length)
  else []

/-- The retrying simulator unfolded: with `N = |inParam w|` and `i` the least index below `N`
whose attempt is not `⊥ = []` (`firstIdx`, equal to `N` if there is none), `retry S w` is
attempt `i` if `i < N`, and `[]` otherwise. -/
theorem retry_eq (S : NUPPT) (w : List Bool) :
    retry S w =
      if firstIdx (fun t => decide (attempt S w t ≠ [])) (NUPPT.inParam w).length <
          (NUPPT.inParam w).length then
        attempt S w (firstIdx (fun t => decide (attempt S w t ≠ [])) (NUPPT.inParam w).length)
      else [] :=
  rfl

/-- If attempt `i < |inParam w|` is the first that does not abort (`attempt S w i ≠ []`, and
`attempt S w j = []` for every `j < i`), then `retry S w` is attempt `i`.

**Proof sketch.** `firstIdx` of the non-abort test is `i` (`firstIdx_eq_of`); rewrite
`retry_eq` with it and take the `i < |inParam w|` branch. -/
theorem retry_eq_attempt {S : NUPPT} {w : List Bool} {i : ℕ}
    (hi : i < (NUPPT.inParam w).length) (hne : attempt S w i ≠ [])
    (hmin : ∀ j < i, attempt S w j = []) : retry S w = attempt S w i := by
  have h : firstIdx (fun t => decide (attempt S w t ≠ [])) (NUPPT.inParam w).length = i :=
    firstIdx_eq_of hi (decide_eq_true hne) fun j hj => decide_eq_false (not_not.2 (hmin j hj))
  rw [retry_eq, h, if_pos hi]

/-- If all `|inParam w|` attempts abort (`attempt S w t = []` for every `t < |inParam w|`),
then `retry S w = []`. Together with `retry_eq_attempt` this covers every input.

**Proof sketch.** `firstIdx` of the non-abort test is `|inParam w|` (`firstIdx_eq_of_forall`);
rewrite `retry_eq` with it and take the `else` branch. -/
theorem retry_eq_nil {S : NUPPT} {w : List Bool}
    (h : ∀ t < (NUPPT.inParam w).length, attempt S w t = []) : retry S w = [] := by
  have h' : firstIdx (fun t => decide (attempt S w t ≠ [])) (NUPPT.inParam w).length =
      (NUPPT.inParam w).length :=
    firstIdx_eq_of_forall fun t ht => decide_eq_false (not_not.2 (h t ht))
  rw [retry_eq, h', if_neg (lt_irrefl _)]

/-- One attempt is polynomial-time on the indexed layout `⟨1^t, w⟩`.

**Proof sketch.** The block `(r.drop (t · c)).take c` with `c = S.coinLen n` in unary
(`unaryPoly_comp`, `unaryMul_poly`, `polyTimeComputable_pairDropPoly`, `truncate_poly`), the
layout (`NUPPT.polyTimeComputable_layout`) and the machine of `S`
(`NUPPT.polyTimeComputable_output`). -/
theorem attempt_poly (S : NUPPT) :
    PolyTimeComputable fun u => attempt S (pairSndD u) (pairFstD u).length := by
  have congr : ∀ {f g : List Bool → List Bool}, PolyTimeComputable f → (∀ w, g w = f w) →
      PolyTimeComputable g := fun hf h => by rw [show _ = _ from funext h]; exact hf
  have hpar : PolyTimeComputable fun u => NUPPT.inParam (pairSndD u) :=
    NUPPT.polyTimeComputable_inParam.comp polyTimeComputable_pairSndD
  have hr : PolyTimeComputable fun u => NUPPT.inCoins (pairSndD u) :=
    NUPPT.polyTimeComputable_inCoins.comp polyTimeComputable_pairSndD
  have hc : PolyTimeComputable fun u =>
      List.replicate (S.coinLen (NUPPT.inParam (pairSndD u)).length) true :=
    unaryPoly_comp S.coins hpar
  have ht : PolyTimeComputable fun u => List.replicate (pairFstD u).length true :=
    unaryLength_poly polyTimeComputable_pairFstD
  have hdrop : PolyTimeComputable fun u => (NUPPT.inCoins (pairSndD u)).drop
      ((pairFstD u).length * S.coinLen (NUPPT.inParam (pairSndD u)).length) :=
    congr ((polyTimeComputable_pairDropPoly .var).comp ((unaryMul_poly ht hc).pairEncode hr))
      fun u => by simp
  have hblk := truncate_poly hdrop hc
  have hlay := NUPPT.polyTimeComputable_layout hpar
    (NUPPT.polyTimeComputable_inArg.comp polyTimeComputable_pairSndD)
    (polyTimeComputable_const []) hblk
  exact congr (S.polyTimeComputable_output.comp hlay) fun u => rfl

/-- **The retrying simulator is polynomial-time** as a function of its layout: the first
non-aborting index is `EncodingMachines.polyTimeComputable_firstIdx` (an instance of the
repetition lemma `Complexity.polyTimeComputable_iterateFind`) with the test of
`attempt_poly`, and the output is that attempt (`attempt_poly` at the found index) or `[]`
(`polyTimeComputable_ite`). -/
theorem retry_poly (S : NUPPT) : PolyTimeComputable (retry S) := by
  have congr : ∀ {f g : List Bool → List Bool}, PolyTimeComputable f → (∀ w, g w = f w) →
      PolyTimeComputable g := fun hf h => by rw [show _ = _ from funext h]; exact hf
  have hatt := attempt_poly S
  have hp : PolyTimeComputable fun u =>
      [decide (attempt S (pairSndD u) (pairFstD u).length ≠ [])] :=
    congr (ltTest_poly (unaryConst_poly 0) (unaryLength_poly hatt)) fun u => by
      simp [List.length_pos_iff]
  have hN : PolyTimeComputable fun w => List.replicate (NUPPT.inParam w).length true :=
    unaryLength_poly NUPPT.polyTimeComputable_inParam
  have hidx := polyTimeComputable_firstIdx (p := fun w t => decide (attempt S w t ≠ [])) hp hN
  have hsel : PolyTimeComputable fun w => attempt S w
      (firstIdx (fun t => decide (attempt S w t ≠ [])) (NUPPT.inParam w).length) :=
    congr (hatt.comp (hidx.pairEncode polyTimeComputable_id)) fun w => by simp
  refine congr (polyTimeComputable_ite (ltTest_poly hidx hN) hsel (polyTimeComputable_const []))
    fun w => ?_
  simp only [retry, decide_eq_true_eq]

/-- **The retrying simulator is a uniform PPT**: `NUPPT.ofPolyTimeUniform` of `retry_poly`
with `|x|` blocks of `S.coinLen |x|` coins; on `(x, z)` it computes `retry S` on the layout
`⟨⟨⟨1^{|x|}, ⟨x, z⟩⟩, []⟩, r⟩` (`NUPPT.runAtL_ofPolyTimeUniform`). -/
theorem exists_retrySimulator (S : NUPPT) :
    ∃ S' : NUPPT, S'.Uniform ∧ S'.coins = .mul .var S.coins ∧
      ∀ x z (r : S'.Coins x.length), S'.simulate x z r =
        retry S (NUPPT.layout (List.replicate x.length true) (pairEncode x z) [] (List.ofFn r)) :=
  ⟨NUPPT.ofPolyTimeUniform (retry_poly S) (.mul .var S.coins),
    NUPPT.ofPolyTimeUniform_uniform _ _, rfl, fun x z r => by
      rw [NUPPT.simulate_eq, NUPPT.runAt_eq, NUPPT.runAtL_ofPolyTimeUniform]
      rfl⟩

/-- The first hit of `K` draws read through `EncodingMachines.firstIdx`: if `a t` is `g` of
the `t`-th draw and `q t` tests `E` on it (for `t < K`), then the first hit mapped by `g` and
defaulted to `d` is `a` at the first index accepted by `q`, or `d` if there is none.

**Proof sketch.** If `i := firstIdx q K < K`, the draw `i` is in `E` (`q_firstIdx`) and no
earlier draw is (`firstIdx_min`); splitting `List.finRange K` at `i`
(`List.drop_eq_getElem_cons`, `List.take_append_drop`, `List.getElem_finRange`) gives
`firstHit E xs = some (xs i)` by `List.findSome?_eq_some_iff`. Otherwise no draw is in `E`
(`firstIdx_eq_iff`) and `firstHit E xs = none` (`firstHit_eq_none_iff`). -/
theorem firstHit_map_getD_eq {α β : Type*} (E : α → Prop) [DecidablePred E] {K : ℕ}
    (xs : Fin K → α) (g : α → β) (d : β) (a : ℕ → β) (q : ℕ → Bool)
    (ha : ∀ t (ht : t < K), a t = g (xs ⟨t, ht⟩))
    (hq : ∀ t (ht : t < K), q t = decide (E (xs ⟨t, ht⟩))) :
    ((firstHit E xs).map g).getD d = if firstIdx q K < K then a (firstIdx q K) else d := by
  split_ifs with h
  · set i := firstIdx q K with hi_def
    have hEi : E (xs ⟨i, h⟩) := by
      have := q_firstIdx h
      rw [hq i h] at this
      exact of_decide_eq_true this
    have hmin : ∀ j (hj : j < i), ¬ E (xs ⟨j, hj.trans h⟩) := fun j hj hE => by
      have := firstIdx_min hj
      rw [hq j (hj.trans h)] at this
      exact absurd (decide_eq_true hE) (by rw [this]; decide)
    have hsome : firstHit E xs = some (xs ⟨i, h⟩) := by
      unfold firstHit
      rw [List.findSome?_eq_some_iff]
      refine ⟨(List.finRange K).take i, ⟨i, h⟩, (List.finRange K).drop (i + 1), ?_, ?_, ?_⟩
      · have hlen : i < (List.finRange K).length := by simpa using h
        have hsplit : List.finRange K = (List.finRange K).take i ++
            (List.finRange K)[i] :: (List.finRange K).drop (i + 1) := by
          rw [← List.drop_eq_getElem_cons hlen, List.take_append_drop]
        rw [List.getElem_finRange] at hsplit
        exact hsplit
      · simp [hEi]
      · intro j hj
        obtain ⟨k, hk, rfl⟩ := List.mem_take_iff_getElem.1 hj
        have hki : k < i := lt_of_lt_of_le hk (min_le_left _ _)
        simp [hmin k hki]
    rw [hsome, ha i h]
    rfl
  · have hall := firstIdx_eq_iff.1 (le_antisymm firstIdx_le (not_lt.1 h))
    have hnone : firstHit E xs = none := (firstHit_eq_none_iff E xs).2 fun t hE => by
      have := hall t t.isLt
      rw [hq t t.isLt] at this
      exact absurd (decide_eq_true hE) (by rw [this]; decide)
    rw [hnone]
    rfl

/-- **Retrying an aborting sampler** (amplification by repetition): let `g` be a
sampler on a finite uniform space `Ω`, `E` the event "`g` does not abort", with
`Pr[¬ E] ≤ 1/2`, and suppose the output of `g` conditioned on `E` has the law of the sampler
`Y`. Then the output of `g` on the first of `K` independent draws in `E` (the default `d₀` if
there is none) is within `2^{-K}` of `Y`.

**Proof sketch.** Let `p := Pr[E] ≥ 1/2` and `f := (1 - p)^K`, the probability that no draw
is in `E` (`uprob_firstHit_none`). Each `a ∈ E` is the first hit with the same probability
`q₀` (`firstHit_uniform_of_some`), so for a test set `T`, splitting over the fibres of
`firstHit` (`uprob_comp_eq_sum_fiber`, `Fintype.sum_option`),
`Pr[T(retry)] = [T d₀] · f + q₀ · #{a ∈ E : T (g a)}`, and with `T := ⊤`,
`1 = f + q₀ · #E`. The conditional-law hypothesis times `|Ω|` is
`Pr[T(Y)] · #E = #{a ∈ E : T (g a)}`, so `Pr[T(retry)] = [T d₀] · f + (1 - f) · Pr[T(Y)]`
(`linear_combination`) and `|Pr[T(Y)] - Pr[T(retry)]| = f · |Pr[T(Y)] - [T d₀]| ≤ f ≤ 2^{-K}`. -/
theorem statClose_retry {Ω τ : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω] [Fintype τ]
    (E : Ω → Prop) [DecidablePred E] (g : Ω → List Bool) (Y : τ → List Bool) (d₀ : List Bool)
    (habort : uprob (fun ω => ¬ E ω) ≤ 1 / 2)
    (hcond : ∀ T : List Bool → Prop,
      uprob (fun t => T (Y t)) * uprob E = uprob (fun ω => E ω ∧ T (g ω)))
    (K : ℕ) :
    StatClose Y (fun ws : Fin K → Ω => ((firstHit E ws).map g).getD d₀) ((2 : ℝ)⁻¹ ^ K) := by
  classical
  intro T
  have hpE : uprob E = 1 - uprob (fun ω => ¬ E ω) := by rw [uprob_not]; ring
  obtain ⟨d, hd⟩ : ∃ d, E d := by
    by_contra hne
    push_neg at hne
    have h0 : uprob E = 0 := by
      rw [← uprob_false (α := Ω)]
      exact OneWay.uprob_congr fun ω => ⟨fun h => hne ω h, False.elim⟩
    linarith
  have hsome : ∀ a, E a → uprob (fun xs : Fin K → Ω => firstHit E xs = some a) =
      uprob (fun xs : Fin K → Ω => firstHit E xs = some d) :=
    fun a ha => firstHit_uniform_of_some E K ha hd
  have hnot : ∀ a, ¬ E a → uprob (fun xs : Fin K → Ω => firstHit E xs = some a) = 0 := by
    intro a ha
    rw [← uprob_false (α := Fin K → Ω)]
    exact OneWay.uprob_congr fun xs => ⟨fun h => ha (firstHit_eq_some_imp E h), False.elim⟩
  have hdec : ∀ S' : Option Ω → Prop, uprob (fun xs : Fin K → Ω => S' (firstHit E xs)) =
      (if S' none then (1 - uprob E) ^ K else 0) +
        uprob (fun xs : Fin K → Ω => firstHit E xs = some d) *
          (univ.filter fun a => E a ∧ S' (some a)).card := by
    intro S'
    rw [uprob_comp_eq_sum_fiber (firstHit E) S', sum_filter, Fintype.sum_option,
      uprob_firstHit_none E K]
    congr 1
    rw [mul_comm, ← nsmul_eq_mul, ← sum_const, sum_filter]
    refine sum_congr rfl fun a _ => ?_
    by_cases hSa : S' (some a)
    · by_cases hEa : E a
      · simp [hSa, hEa, hsome a hEa]
      · simp [hSa, hEa, hnot a hEa]
    · simp [hSa]
  have hsim := hdec fun o => T ((o.map g).getD d₀)
  have htot := hdec fun _ => True
  rw [uprob_true] at htot
  simp only [Option.map_none, Option.getD_none, Option.map_some, Option.getD_some, if_true,
    and_true] at hsim htot
  -- the conditional law in counting form
  have hcard : (Fintype.card Ω : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hc := hcond T
  rw [uprob_eq_card_filter E, uprob_eq_card_filter (fun ω => E ω ∧ T (g ω)), mul_div_assoc',
    div_left_inj' hcard] at hc
  generalize uprob (fun xs : Fin K → Ω => firstHit E xs = some d) = q₀ at hsim htot
  generalize hf : (1 - uprob E) ^ K = f at hsim htot
  have hY0 := uprob_nonneg (fun t => T (Y t))
  have hY1 := uprob_le_one (fun t => T (Y t))
  have hsimeq : uprob (fun xs : Fin K → Ω => T (((firstHit E xs).map g).getD d₀)) =
      (if T d₀ then f else 0) + (1 - f) * uprob (fun t => T (Y t)) := by
    rw [hsim]
    linear_combination (-q₀) * hc + (-uprob (fun t => T (Y t))) * htot
  have hf0 : 0 ≤ f := hf ▸ pow_nonneg (by linarith [uprob_le_one E]) K
  have hfK : f ≤ (2 : ℝ)⁻¹ ^ K :=
    hf ▸ pow_le_pow_left₀ (by linarith [uprob_le_one E]) (by linarith) K
  show |uprob (fun t => T (Y t)) -
    uprob (fun xs : Fin K → Ω => T (((firstHit E xs).map g).getD d₀))| ≤ (2 : ℝ)⁻¹ ^ K
  rw [hsimeq, abs_le]
  split_ifs <;> constructor <;> nlinarith

/-- The probability that the retrying simulator's attempt aborts is the complement of its
success probability (a restatement of `PerfectZKAbort`'s first clause for
`AbortRetry.statClose_retry`). -/
theorem uprob_not_ne_nil_le {Ω : Type*} [Fintype Ω] (g : Ω → List Bool)
    (h : uprob (fun ω => g ω = []) ≤ 1 / 2) : uprob (fun ω => ¬ g ω ≠ []) ≤ 1 / 2 := by
  simpa using h

end AbortRetry

open AbortRetry in
/-- **Perfect zero-knowledge with abort implies statistical zero-knowledge with error
`2^{-|x|}`** (the abort form of [Gol01, Definition 4.3.1], amplified by repetition)
(ruling G3-4 of gate 03): retry the aborting simulator on `|x|` disjoint coin blocks and
output the first non-`⊥` result.

**Proof sketch.** For an efficient `V'` take the aborting simulator `S` of `h`; the
retrying simulator `S'` of `AbortRetry.exists_retrySimulator` is a uniform PPT with `|x|`
blocks of `S.coinLen |x|` coins. Read its tape as `|x|` independent blocks (the bijection
`e` built from `finCongr`, `finProdFinEquiv` and `Equiv.curry`, through
`StatClose.comp_equiv_right`): the `t`-th slice of the tape is `List.ofFn` of block `t`, so
attempt `t` is `S` on block `t` (`S` is uniform, so its advice is `[]`), and the retrying
simulator is the first non-`⊥` attempt (`AbortRetry.firstHit_map_getD_eq`). The two clauses
of `h` are the hypotheses of `AbortRetry.statClose_retry` with `K = |x|`. -/
theorem PerfectZKAbort.statZK {π : Protocol} {R : List Bool → List Bool → Prop}
    (h : PerfectZKAbort π R) : StatZK π R (fun n => (2 : ℝ)⁻¹ ^ n) := by
  intro V' hV'
  obtain ⟨S, hSu, hS⟩ := h V' hV'
  obtain ⟨S', hS'u, hS'c, hS'⟩ := exists_retrySimulator S
  refine ⟨S', hS'u, fun x y z hxy => ?_⟩
  obtain ⟨habort, hcond⟩ := hS x y z hxy
  have hlen : S'.coinLen x.length = x.length * S.coinLen x.length := by
    simp only [NUPPT.coinLen, hS'c, PolyExpr.eval_mul, PolyExpr.eval_var]
  -- the tape of `S'` as `|x|` blocks of `S.coinLen |x|` coins
  let e : S'.Coins x.length ≃ (Fin x.length → S.Coins x.length) :=
    ((Equiv.arrowCongr (finCongr hlen) (Equiv.refl Bool)).trans
      (Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl Bool))).trans (Equiv.curry _ _ _)
  have hblock : ∀ (r : S'.Coins x.length) (t : ℕ) (ht : t < x.length),
      ((List.ofFn r).drop (t * S.coinLen x.length)).take (S.coinLen x.length) =
        List.ofFn (e r ⟨t, ht⟩) := by
    intro r t ht
    have hle : t * S.coinLen x.length + S.coinLen x.length ≤ x.length * S.coinLen x.length := by
      rw [← Nat.succ_mul]
      exact Nat.mul_le_mul_right _ ht
    refine List.ext_getElem ?_ fun j h₁ h₂ => ?_
    · simp only [List.length_take, List.length_drop, List.length_ofFn, hlen]
      omega
    · simp only [List.getElem_take, List.getElem_drop, List.getElem_ofFn]
      simp only [e, Equiv.trans_apply, Equiv.arrowCongr_apply, Equiv.coe_refl,
        Function.comp_apply, Equiv.symm_symm, Equiv.curry_apply, Function.curry_apply]
      congr 1
      ext
      simp [finProdFinEquiv]
      ring
  have hatt : ∀ (r : S'.Coins x.length) (t : ℕ) (ht : t < x.length),
      attempt S (NUPPT.layout (List.replicate x.length true) (pairEncode x z) [] (List.ofFn r)) t =
        S.simulate x z (e r ⟨t, ht⟩) := by
    intro r t ht
    simp only [attempt, NUPPT.inParam_layout, NUPPT.inArg_layout, NUPPT.inCoins_layout,
      List.length_replicate]
    rw [hblock r t ht, NUPPT.simulate_eq, NUPPT.runAt_eq, NUPPT.runAtL_eq_output_layout, hSu]
  have heq : ∀ r : S'.Coins x.length, S'.simulate x z r =
      ((firstHit (fun ω => S.simulate x z ω ≠ []) (e r)).map (S.simulate x z)).getD [] := by
    intro r
    rw [hS' x z r, firstHit_map_getD_eq (fun ω => S.simulate x z ω ≠ []) (e r)
      (S.simulate x z) []
      (attempt S (NUPPT.layout (List.replicate x.length true) (pairEncode x z) [] (List.ofFn r)))
      (fun t => decide (attempt S
        (NUPPT.layout (List.replicate x.length true) (pairEncode x z) [] (List.ofFn r)) t ≠ []))
      (hatt r) (fun t ht => by simp only [hatt r t ht])]
    simp only [retry, NUPPT.inParam_layout, List.length_replicate]
  have key := (statClose_retry (fun ω => S.simulate x z ω ≠ []) (S.simulate x z)
    (fun r : (π.withV V').ExecCoins π.P x => ((π.withV V').viewV x y z r).encode) []
    (uprob_not_ne_nil_le _ habort) hcond x.length).comp_equiv_right e
  intro T
  have hu : uprob (fun t : S'.Coins x.length => T (S'.simulate x z t)) =
      uprob (fun t : S'.Coins x.length => T (((firstHit (fun ω => S.simulate x z ω ≠ []) (e t)).map
        (S.simulate x z)).getD [])) :=
    OneWay.uprob_congr fun t => by rw [heq t]
  rw [hu]
  exact key T

/-- **Perfect zero-knowledge with abort implies zero-knowledge** (ruling G3-4 of gate 03):
`PerfectZKAbort.statZK` and `StatZK.zk` with the negligible error `2^{-n}`
(`negligible_two_pow_neg`). -/
theorem PerfectZKAbort.zk {π : Protocol} {R : List Bool → List Bool → Prop}
    (h : PerfectZKAbort π R) : ZK π R :=
  h.statZK.zk negligible_two_pow_neg

/-! ### Negligibility in the instance length (Inf-4.4) -/

/-- For `a > 1` and `C > 0` the function `N ↦ a^{-√(N / C)}` (with `Nat.sqrt` and natural
division) is negligible in `N` (Inf-4.4): the per-vertex error bounds `2^{-n}` and `e^{-n}` of
the graph protocols, whose instances have length `|x| ≥ n² / C`, are negligible in `|x|`.

**Proof sketch.** Fix `c`. Put `t := Nat.sqrt (N / C)`; then `N / C < (t + 1)²`
(`Nat.lt_succ_sqrt`), so `N < C (t + 1)² + C ≤ 2 C (t + 1)²` and
`N ^ c ≤ (2 C)^c (t + 1)^{2c}`. By `tendsto_pow_const_div_const_pow_of_one_lt`
(as in `negligible_two_pow_neg`), `(t + 1)^{2c} / a^{t+1} → 0`, so there is `t₀` with
`(2 C)^c · a · (t + 1)^{2c} < a^{t+1}` for `t ≥ t₀`, i.e. `(2C)^c (t+1)^{2c} < a^t`; and
`t ≥ t₀` as soon as `N ≥ C (t₀ + 1)²` (`Nat.le_sqrt`). Hence for such `N`,
`a⁻¹ ^ t = 1 / a^t < 1 / ((2C)^c (t+1)^{2c}) ≤ 1 / N^c`. -/
theorem negligible_inv_pow_sqrt_div {a : ℝ} (ha : 1 < a) {C : ℕ} (hC : 0 < C) :
    Negligible fun N => a⁻¹ ^ Nat.sqrt (N / C) := by
  intro c
  have ha0 : (0 : ℝ) < a := zero_lt_one.trans ha
  have hCr : (0 : ℝ) < (C : ℝ) ^ c := by positivity
  have hpos : (0 : ℝ) < 1 / ((C : ℝ) ^ c * a) := by positivity
  have ht := tendsto_pow_const_div_const_pow_of_one_lt (2 * c) ha
  obtain ⟨t₀, ht₀⟩ := Filter.eventually_atTop.mp (ht.eventually (gt_mem_nhds hpos))
  refine ⟨max (C * t₀ * t₀) 1, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := le_of_max_le_right hN
  have hNC : C * t₀ * t₀ ≤ N := le_of_max_le_left hN
  set t := Nat.sqrt (N / C) with ht_def
  -- `t₀ ≤ t` since `C t₀² ≤ N`
  have ht0 : t₀ ≤ t := by
    rw [ht_def, Nat.le_sqrt, Nat.le_div_iff_mul_le hC]
    calc t₀ * t₀ * C = C * t₀ * t₀ := by ring
      _ ≤ N := hNC
  -- `N < (t + 1)² C`
  have hNlt : N < (t + 1) * (t + 1) * C :=
    (Nat.div_lt_iff_lt_mul hC).1 (Nat.lt_succ_sqrt (N / C))
  have hNltR : (N : ℝ) < ((t : ℝ) + 1) ^ 2 * C := by
    have := hNlt
    rw [← pow_two] at this
    exact_mod_cast this
  -- the limit at `t + 1`: `(t + 1)^{2c} C^c < a^t`
  have hlim := ht₀ (t + 1) (by omega)
  have hlim' : ((t : ℝ) + 1) ^ (2 * c) * ((C : ℝ) ^ c * a) < a ^ (t + 1) := by
    have hapos : (0 : ℝ) < a ^ (t + 1) := pow_pos ha0 _
    rw [div_lt_iff₀ hapos] at hlim
    push_cast at hlim
    calc ((t : ℝ) + 1) ^ (2 * c) * ((C : ℝ) ^ c * a)
        < 1 / ((C : ℝ) ^ c * a) * a ^ (t + 1) * ((C : ℝ) ^ c * a) := by
          gcongr
      _ = a ^ (t + 1) := by field_simp
  have hkey : ((t : ℝ) + 1) ^ (2 * c) * (C : ℝ) ^ c < a ^ t := by
    rw [pow_succ, ← mul_assoc] at hlim'
    exact lt_of_mul_lt_mul_right hlim' ha0.le
  -- `N^c ≤ (t + 1)^{2c} C^c`
  have hNpow : (N : ℝ) ^ c ≤ ((t : ℝ) + 1) ^ (2 * c) * (C : ℝ) ^ c := by
    rw [pow_mul, ← mul_pow]
    exact pow_le_pow_left₀ (Nat.cast_nonneg N) hNltR.le c
  have hNpos : (0 : ℝ) < (N : ℝ) ^ c := pow_pos (by exact_mod_cast hN1) c
  show |a⁻¹ ^ t| < 1 / (N : ℝ) ^ c
  rw [abs_of_pos (pow_pos (inv_pos.mpr ha0) t), inv_pow, ← one_div]
  exact one_div_lt_one_div_of_lt hNpos (hNpow.trans_lt hkey)

/-- `2^{-√(N / C)}` is negligible in `N` (Inf-4.4, the graph-isomorphism bound). -/
theorem negligible_two_pow_neg_sqrt_div {C : ℕ} (hC : 0 < C) :
    Negligible fun N => (2 : ℝ)⁻¹ ^ Nat.sqrt (N / C) :=
  negligible_inv_pow_sqrt_div one_lt_two hC

/-- `e^{-√(N / C)}` is negligible in `N` (Inf-4.4, the 3-colouring bound). -/
theorem negligible_exp_neg_sqrt_div {C : ℕ} (hC : 0 < C) :
    Negligible fun N => Real.exp (-(Nat.sqrt (N / C) : ℝ)) := by
  have h1 : (1 : ℝ) < Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  refine (negligible_inv_pow_sqrt_div h1 hC).mono ⟨0, fun n _ => le_of_eq ?_⟩
  congr 1
  rw [Real.exp_neg, inv_pow, ← Real.exp_nat_mul, mul_one]

/-- A function bounded by `a^{-√(N / C)}` is negligible (Inf-4.4 in the form used by the
protocol theorems: a bound `a^{-n}` in the number of vertices `n ≥ √(|x| / C)` is a bound
`a^{-√(|x| / C)}` in the instance length). -/
theorem negligible_of_le_inv_pow_sqrt_div {a : ℝ} (ha : 1 < a) {C : ℕ} (hC : 0 < C)
    {ν : ℕ → ℝ} (hν : ∀ N, |ν N| ≤ a⁻¹ ^ Nat.sqrt (N / C)) : Negligible ν :=
  (negligible_inv_pow_sqrt_div ha hC).mono ⟨0, fun N _ => by
    rw [abs_of_nonneg (pow_nonneg (inv_nonneg.mpr (zero_le_one.trans ha.le)) _)]
    exact hν N⟩

/-- A bound `a^{-n}` in a parameter `n ≥ √(N / C)` transfers to `a^{-√(N / C)}`
(monotonicity of `a⁻¹ ^ ·` for `a > 1`). -/
theorem inv_pow_le_inv_pow_sqrt_div {a : ℝ} (ha : 1 < a) {C N n : ℕ}
    (hn : Nat.sqrt (N / C) ≤ n) : a⁻¹ ^ n ≤ a⁻¹ ^ Nat.sqrt (N / C) :=
  pow_le_pow_of_le_one (inv_nonneg.mpr (zero_le_one.trans ha.le)) (inv_le_one_of_one_le₀ ha.le) hn

end TCSlib.Cryptography

## ===== TCSlib/Cryptography/ZeroKnowledge/NP.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.ZeroKnowledge.ThreeColoring
import TCSlib.Cryptography.ZeroKnowledge.NPLemmas
import TCSlib.Complexity.ClassNP.Reductions

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Zero-knowledge proofs for NP: Levin reductions and Theorem 124.1

Step 2 of [PS10, Theorem 124.1]: "to get a zero-knowledge proof `(P, V)` for any NP language
`L`, both `P` and `V` reduce the instance `x` into an instance `x' = f(x)` of graph
3-colouring, the prover additionally reduces the witness `y` to a witness `y' = w(x, y)` for
`x'`, and the parties execute the 3-colouring protocol on `x'`". The reduction must preserve
witnesses, i.e. be a *Levin reduction* (Def-124.a; the text says "Cook's reduction can be
applied to the witness", which Karp/Cook reductions do not provide — source error 47 of the
plan). Zero-knowledge proofs with efficient prover transfer along Levin reductions
(Claim-124.d), which gives [PS10, Theorem 124.1] in the plan's form (A): for every language
`L` with witness relation `R` and every Levin reduction `(f, w)` of `(L, R)` to `(3COL, R_3COL)`,
the pulled-back 3-colouring protocol is a zero-knowledge proof with efficient prover for `L`,
given a commitment scheme (hence given a one-way permutation with a hard-core predicate,
[PS10, Theorem 126.4]). The "every language in NP" form is the corollary under the hypothesis
that `3COL` is NP-hard *with Levin reductions* (`LevinNPHard`); the string-level Levin
reduction from `3SAT` is not formalized (plan decision on Theorem 124.1, Claim-124.b/c
deferred).

**Deviations:**
* a Levin reduction is taken *length-regular* with `|f x| = p(|x|)` for a `PolyExpr p ≥ id`
  (assumed: padding a Levin reduction to `3COL` with isolated vertices should give this form
  with `p = q²` for a polynomial `q`, the lengths of `encGraph` being perfect squares, but the
  padding is not formalized; gate 03e, note 14), which makes the coin and round polynomials
  of the pulled-back protocol `subst p` of the original ones and the error bounds
  `ε(p(|x|))`, negligible in `|x|` (`Negligible.comp_of_le`);
* the text's "execute protocol `(P, V)` on `x'`" is read as `(P', V')`; the hypothesis of a
  hard-core predicate for the one-way permutation is made explicit (as in Theorem 126.4).

**Proof infrastructure (run 4):** the transfer proofs use the sibling file
`TCSlib.Cryptography.ZeroKnowledge.NPLemmas` (namespace `LevinTransfer`): the execution
congruence `exec_congr`, the uniform coin projections `coinTrunc`/`UnifProj` with
`distAdv_eq_of_unifProj` (the padding of the random tapes is uniform and independent), the
verifier `liftVerifier V'` and the view re-encoder `postView` of the zero-knowledge transfer,
the machines `exists_liftSimulator`/`exists_liftDistinguisher`, and the strict monotonicity of
a length polynomial `p ≥ id` (`polyExpr_strictMono_of_le`, which gives the left inverse of
`p.eval` along which the distinguisher is re-parametrized).

**Bounded prover messages (ruling G3-3 of gate 03):** the bound on the honest prover's
messages transfers along a Levin reduction with bound `B.subst p`
(`Protocol.ProverBounded.pullback`).

**Scope of Theorem 124.1 (DQ5; gate 03e, minor 3).** The text's Theorem 124.1 asserts one
zero-knowledge proof with negligible soundness error. Here the zero-knowledge protocol is one
iteration of the 3-colouring protocol, with soundness error `1 - 1/p(|x|) + 2^{-p(|x|)}`, and
the interactive proof with negligible error is its `n|E|`-fold repetition; that the repetition
is also zero-knowledge, with negligible soundness error, is sequential repetition
[PS10, §7.2.1], which ch. 7 supplies (ruling G3-7(d)), and is not stated here. In the
existential forms the conjunct `∃ π, EfficientProverProof π L R` says nothing about the
zero-knowledge protocol (`npProtocol` already witnesses it, `npProtocol_interactiveProof`);
the tied forms `exists_commitment_zk_proof_of_owp_levinReduction`,
`zk_proof_of_witnessRelation` and `zk_proof_of_witnessRelation_of_owp` state both protocols for
one commitment scheme and one Levin reduction, as `zk_proof_of_levinReduction` does.

**Run-3 repairs (audit P11-1, P11-2):** the transfer lemmas and both forms of Theorem 124.1
take the hypothesis `hLR : ∀ x ∈ L, ∃ y, R x y` (`L ⊆ witnessLanguage R`): no field of
`LevinReduction` relates `L` to `R` (with `R = ∅` the `witness` field is vacuous), and without
it the `complete` clause of the pulled-back proof is false. The "every language in NP" forms
keep the explicit soundness error `1 - 1/p(|x|) + (1/2)^{p(|x|)}` of the Levin reduction's
length polynomial `p ≥ id` (the run-2 `∃ s, EfficientProverProofErr π L R s` was vacuous with
`s = 1`; `one_sub_inv_add_half_pow_lt_one` shows the error is below `1`).

## Main definitions

* `TCSlib.Cryptography.LevinReduction` — Levin (witness-preserving) reductions (Def-124.a).
* `TCSlib.Cryptography.Strategy.pullback`, `TCSlib.Cryptography.Protocol.pullback` — the
  protocol for `L` obtained by reducing to `L'` and running a protocol for `L'`.
* `TCSlib.Cryptography.LevinNPHard` — NP-hardness with Levin reductions (the hypothesis of
  the "every language in NP" form).

## Main results

* `TCSlib.Cryptography.LevinReduction.refl`, `TCSlib.Cryptography.LevinReduction.trans`,
  `TCSlib.Cryptography.LevinReduction.polyTimeReducible` — sanity: Levin reductions compose
  and are Karp reductions (proved).
* `TCSlib.Cryptography.LevinReduction.efficientProverProof`,
  `TCSlib.Cryptography.LevinReduction.efficientProverProofErr`,
  `TCSlib.Cryptography.LevinReduction.zk` — interactive proofs with efficient prover and
  zero-knowledge transfer along Levin reductions (Claim-124.d);
  `TCSlib.Cryptography.Protocol.ProverBounded.pullback` — so does the bound on the prover's
  messages.
* `TCSlib.Cryptography.zk_proof_of_levinReduction` — **[PS10, Theorem 124.1], form (A)**:
  a commitment scheme and a Levin reduction to `3COL` give a zero-knowledge protocol for `L`
  with soundness error `1 - 1/p(|x|) + 2^{-p(|x|)}` whose `n|E|`-fold repetition is an
  interactive proof; `TCSlib.Cryptography.zk_proof_of_owp_levinReduction`,
  `TCSlib.Cryptography.exists_commitment_zk_proof_of_owp_levinReduction` — the same from a
  one-way permutation with a hard-core predicate, untied and tied (Thm-124.1).
* `TCSlib.Cryptography.zk_proof_of_witnessRelation`,
  `TCSlib.Cryptography.zk_proof_of_witnessRelation_of_owp` — the "every language in NP" form
  for every witness relation, under `LevinNPHard L3COL R3COL` (the second from a one-way
  permutation, the text's hypothesis); `TCSlib.Cryptography.zk_proof_of_mem_NP`,
  `TCSlib.Cryptography.zk_proof_of_mem_NP_of_owp` — the corollaries for `L ∈ NP` with the
  witness relation of `exists_witnessRelation_of_mem_NP`, with the explicit soundness error of
  the Levin reduction's length polynomial
  (`TCSlib.Cryptography.one_sub_inv_add_half_pow_lt_one`: the error is below `1`).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§4.7: Theorem 124.1; Appendix B, Definition 191.11.)
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Cambridge
  University Press, 2009. (Definition 2.7, Karp reductions; §2.3, Levin reductions.)
-/

namespace TCSlib.Cryptography

open Complexity Turing LevinTransfer

/-! ### Levin reductions (Def-124.a) -/

/-- A **Levin reduction** `(f, w)` from `(L, R)` to `(L', R')` [PS10, §4.7, Theorem 124.1,
step 2, "Cook's reduction can be applied to the witness"] (Def-124.a): `f` is a
polynomial-time Karp reduction (`x ∈ L ↔ f x ∈ L'`), `w` is polynomial-time on the pair
`⟨x, y⟩` and maps witnesses to witnesses (`R x y → R' (f x) (w x y)`), and `f` is
length-regular: `|f x| = p(|x|)` for the polynomial `p ≥ id`.

**Deviation:** the text never defines Levin reductions; length-regularity with `p ≥ id` is
assumed (padding with isolated vertices should achieve it for `3COL`, with `p = q²`; not
formalized) so that the pulled-back protocol's polynomials are `subst p` of the original ones
and its error bounds `ε(p(|x|))` are negligible in `|x|`. -/
structure LevinReduction (L L' : Language Bool) (R R' : List Bool → List Bool → Prop)
    (f : List Bool → List Bool) (w : List Bool → List Bool → List Bool) (p : PolyExpr) : Prop where
  /-- The instance map is polynomial-time. -/
  f_poly : PolyTimeComputable f
  /-- The witness map is polynomial-time on the pair `⟨x, y⟩`. -/
  w_poly : PolyTimeComputable fun z => w (pairFstD z) (pairSndD z)
  /-- `f` is a Karp reduction. -/
  mem_iff : ∀ x, x ∈ L ↔ f x ∈ L'
  /-- `w` maps witnesses of `x` to witnesses of `f x`. -/
  witness : ∀ x y, R x y → R' (f x) (w x y)
  /-- `f` is length-regular with length polynomial `p`. -/
  length_eq : ∀ x, (f x).length = p.eval x.length
  /-- The length polynomial dominates the identity. -/
  le_eval : ∀ N, N ≤ p.eval N

/-- A Levin reduction is a Karp reduction [AB09, Definition 2.7]. -/
theorem LevinReduction.polyTimeReducible {L L' : Language Bool} {R R' : List Bool → List Bool → Prop}
    {f : List Bool → List Bool} {w : List Bool → List Bool → List Bool} {p : PolyExpr}
    (h : LevinReduction L L' R R' f w p) : PolyTimeReducible L L' :=
  ⟨f, h.f_poly, h.mem_iff⟩

/-- Sanity: the identity is a Levin reduction of `(L, R)` to itself. -/
theorem LevinReduction.refl (L : Language Bool) (R : List Bool → List Bool → Prop) :
    LevinReduction L L R R id (fun _ y => y) .var where
  f_poly := polyTimeComputable_id
  w_poly := polyTimeComputable_pairSndD
  mem_iff _ := Iff.rfl
  witness _ _ h := h
  length_eq _ := rfl
  le_eval _ := le_rfl

/-- Sanity: Levin reductions compose, with length polynomial `p'.subst p`.

**Proof sketch.** `f' ∘ f` by `PolyTimeComputable.comp`; the composed witness map
`⟨x, y⟩ ↦ w' (f x) (w x y)` is `w'` on the pair `⟨f x, w x y⟩` built by
`PolyTimeComputable.pairEncode` (`pairFstD_pairEncode`, `pairSndD_pairEncode`); membership
and witnesses by transitivity; lengths by `PolyExpr.eval_subst`. -/
theorem LevinReduction.trans {L L' L'' : Language Bool}
    {R R' R'' : List Bool → List Bool → Prop} {f f' : List Bool → List Bool}
    {w w' : List Bool → List Bool → List Bool} {p p' : PolyExpr}
    (h : LevinReduction L L' R R' f w p) (h' : LevinReduction L' L'' R' R'' f' w' p') :
    LevinReduction L L'' R R'' (f' ∘ f) (fun x y => w' (f x) (w x y)) (p'.subst p) where
  f_poly := h'.f_poly.comp h.f_poly
  w_poly := by
    have hfun : (fun z => w' (f (pairFstD z)) (w (pairFstD z) (pairSndD z))) =
        fun z => w' (pairFstD (pairEncode (f (pairFstD z)) (w (pairFstD z) (pairSndD z))))
          (pairSndD (pairEncode (f (pairFstD z)) (w (pairFstD z) (pairSndD z)))) := by
      funext z
      rw [pairFstD_pairEncode, pairSndD_pairEncode]
    rw [hfun]
    exact h'.w_poly.comp ((h.f_poly.comp polyTimeComputable_pairFstD).pairEncode h.w_poly)
  mem_iff x := (h.mem_iff x).trans (h'.mem_iff (f x))
  witness x y hxy := h'.witness _ _ (h.witness x y hxy)
  length_eq x := by
    rw [Function.comp_apply, h'.length_eq, h.length_eq, PolyExpr.eval_subst]
  le_eval N := by
    rw [PolyExpr.eval_subst]
    exact (h.le_eval N).trans (h'.le_eval _)

/-! ### Pulling a protocol back along a reduction -/

/-- The strategy that runs `S` on the reduced instance `f x` with the transformed auxiliary
input `g x z` [PS10, §4.7, Theorem 124.1, step 2]: `next x z r hist := S.next (f x) (g x z) r hist`,
coins `S.coins.subst p` (so that the tape at `|x|` has exactly `S.coinLen |f x|` bits when
`|f x| = p(|x|)`). -/
def Strategy.pullback (S : Strategy) (f : List Bool → List Bool)
    (g : List Bool → List Bool → List Bool) (p : PolyExpr) : Strategy where
  next x z r hist := S.next (f x) (g x z) r hist
  coins := S.coins.subst p

/-- The pulled-back strategy's coin length at `|x|` is `S`'s at `|f x|` under length
regularity. -/
theorem Strategy.coinLen_pullback (S : Strategy) (f : List Bool → List Bool)
    (g : List Bool → List Bool → List Bool) {p : PolyExpr} {x : List Bool}
    (hx : (f x).length = p.eval x.length) :
    (S.pullback f g p).coinLen x.length = S.coinLen (f x).length := by
  simp [Strategy.pullback, Strategy.coinLen, PolyExpr.eval_subst, hx]

/-- The protocol for `L` obtained from a protocol `π` for `L'` and a reduction `(f, w)`
[PS10, §4.7, Theorem 124.1, step 2]: `P(x, y) := P'(f x, w x y)`, `V(x, z) := V'(f x, z)`,
rounds `π.rounds.subst p`, same first mover (Claim-124.d, construction).

**Deviation:** "execute protocol `(P, V)` on `x'`" read as `(P', V')`. -/
def Protocol.pullback (π : Protocol) (f : List Bool → List Bool)
    (w : List Bool → List Bool → List Bool) (p : PolyExpr) : Protocol where
  P := π.P.pullback f w p
  V := π.V.pullback f (fun _ z => z) p
  rounds := π.rounds.subst p
  verifierFirst := π.verifierFirst

/-- Unfolding: the verifier's output in the pulled-back protocol against a prover `P'` is
`π.V.next` on the reduced instance after `π.rounds.eval (p |x|)` moves of `exec` with the
reduced inputs. -/
theorem Protocol.pullback_outV (π : Protocol) (f : List Bool → List Bool)
    (w : List Bool → List Bool → List Bool) (p : PolyExpr) (P' : Strategy) (x y z : List Bool)
    (r : (π.pullback f w p).ExecCoins P' x) :
    (π.pullback f w p).outV P' x y z r =
      π.V.next (f x) z (List.ofFn r.2)
        (exec P' (π.V.pullback f (fun _ z => z) p) π.verifierFirst x y z (List.ofFn r.1)
          (List.ofFn r.2) (π.rounds.eval (p.eval x.length))).2 := by
  simp [Protocol.outV, Protocol.transcriptWith, Protocol.pullback, Strategy.pullback,
    PolyExpr.eval_subst]

/-- A pulled-back strategy is efficient when the original is and `f`, `g` are
polynomial-time (on `⟨x, z⟩` for `g`): compose the machine of `S` with the FP function
`⟨⟨x, z⟩, msgs⟩ ↦ ⟨⟨f x, g x z⟩, msgs⟩` and re-parametrize `1^{|x|}` to `1^{p |x|}`
(`NUPPT.exists_reparam p`, `NUPPT.exists_comp`, `PolyExpr.eval_subst`, `hx`).

**Proof sketch.** From `hS` take the uniform `A` with `S.next x' z' r hist =
A.runAtL |x'| ⟨⟨x', z'⟩, encodeMsgs hist⟩ r`. `NUPPT.exists_comp A hpre polyTimeComputable_id`
with `pre := ⟨⟨f ∘ pairFstD ∘ pairFstD, g on the pair⟩, pairSndD⟩` (pairing calculus) gives
`B` with `B.runAtL m y r = A.runAtL m (pre y) r`; `NUPPT.exists_reparam B p` gives `C` with
`C.runAtL n y r = B.runAtL (p n) y r`, uniform, coins `A.coins.subst p = (S.pullback …).coins`;
on `n = |x|`, `p n = |f x|` (`hx`), so `C` computes the pulled-back next-message function
(`Strategy.ofNUPPT_next`, `pairFstD_pairEncode`, `pairSndD_pairEncode`). -/
theorem Strategy.pullback_efficient {S : Strategy} (hS : S.Efficient) {f : List Bool → List Bool}
    (hf : PolyTimeComputable f) {g : List Bool → List Bool → List Bool}
    (hg : PolyTimeComputable fun z => g (pairFstD z) (pairSndD z)) {p : PolyExpr}
    (hx : ∀ x, (f x).length = p.eval x.length) : (S.pullback f g p).Efficient := by
  obtain ⟨A, hA, hc, hnext⟩ := hS
  have hpre : PolyTimeComputable fun y =>
      pairEncode (pairEncode (f (pairFstD (pairFstD y)))
        (g (pairFstD (pairFstD y)) (pairSndD (pairFstD y)))) (pairSndD y) :=
    ((hf.comp (polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD)).pairEncode
      (hg.comp polyTimeComputable_pairFstD)).pairEncode polyTimeComputable_pairSndD
  obtain ⟨B, hBc, -, hBadv, hB⟩ := A.exists_comp hpre polyTimeComputable_id
  obtain ⟨C, hCc, hCu, hC⟩ := B.exists_reparam p
  refine ⟨C, hCu fun n => by rw [hBadv]; exact hA n, ?_, fun x z r hist => ?_⟩
  · show S.coins.subst p = C.coins
    rw [hCc, hBc, hc]
  · rw [Strategy.ofNUPPT_next, hC, hB]
    show S.next (f x) (g x z) r hist = _
    rw [hnext, Strategy.ofNUPPT_next, ← hx x]
    simp only [id, pairFstD_pairEncode, pairSndD_pairEncode]

/-- **Bounded prover messages transfer along a Levin reduction** with bound `B.subst p`
(ruling G3-3 of gate 03): the pulled-back prover runs `π.P` on `(f x, w x y)`, `R x y` gives
`R' (f x) (w x y)` (`LevinReduction.witness`), and `|f x| = p(|x|)`
(`LevinReduction.length_eq`, `PolyExpr.eval_subst`). -/
theorem Protocol.ProverBounded.pullback {L L' : Language Bool}
    {R R' : List Bool → List Bool → Prop} {f : List Bool → List Bool}
    {w : List Bool → List Bool → List Bool} {p : PolyExpr} (h : LevinReduction L L' R R' f w p)
    {π : Protocol} {B : PolyExpr} (hB : π.ProverBounded R' B) :
    (π.pullback f w p).ProverBounded R (B.subst p) := by
  rw [Protocol.proverBounded_iff] at hB ⊢
  intro x y r hist hxy
  rw [PolyExpr.eval_subst, ← h.length_eq x]
  exact hB (f x) (w x y) r hist (h.witness x y hxy)

/-! ### Negligibility along polynomial reparametrization -/

/-- A negligible function composed with a map `φ ≥ id` is negligible: for `N ≥ max n₀ 1`,
`φ N ≥ N ≥ n₀` so `|μ (φ N)| < 1 / (φ N)^c ≤ 1 / N^c` (the bookkeeping for the error bounds
`ε(|f x|) = ε(p(|x|))` of the pulled-back protocol, Claim-124.d). -/
theorem Negligible.comp_of_le {μ : ℕ → ℝ} (hμ : Negligible μ) (φ : ℕ → ℕ) (hφ : ∀ N, N ≤ φ N) :
    Negligible fun N => μ (φ N) := by
  intro c
  obtain ⟨n₀, h₀⟩ := hμ c
  refine ⟨max n₀ 1, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hφN : n₀ ≤ φ N := le_trans (le_trans (le_max_left _ _) hN) (hφ N)
  refine lt_of_lt_of_le (h₀ (φ N) hφN) ?_
  have hNpos : (0 : ℝ) < (N : ℝ) ^ c := pow_pos (by exact_mod_cast hN1) c
  exact one_div_le_one_div_of_le hNpos (pow_le_pow_left₀ (by positivity) (by exact_mod_cast hφ N) c)

/-! ### Executions of the pulled-back protocol -/

/-- The execution of two pulled-back strategies on `x` is the execution of the original
strategies on `f x` with the transformed auxiliary inputs and the same random tapes
(`LevinTransfer.exec_congr`; the pulled-back next-message functions are those of the
originals on the reduced inputs by definition). -/
private theorem exec_pullback (P V : Strategy) (f : List Bool → List Bool)
    (g g' : List Bool → List Bool → List Bool) (p : PolyExpr) (vFirst : Bool)
    (x zP zV rP rV : List Bool) (k : ℕ) :
    exec (P.pullback f g p) (V.pullback f g' p) vFirst x zP zV rP rV k =
      exec P V vFirst (f x) (g x zP) (g' x zV) rP rV k := by
  refine exec_congr ?_ ?_ vFirst k <;> intro _ <;> rfl

/-- The execution of an arbitrary prover `P'` against a pulled-back verifier on `x` is the
execution of the prover `⟨fun _ _ r hist => P'.next x [] r hist, const (P'.coinLen |x|)⟩`
(which hard-wires `x` and has `P'`'s random tape) against the original verifier on `f x`
(`LevinTransfer.exec_congr`). -/
private theorem exec_pullback_cheat (P' V : Strategy) (f : List Bool → List Bool)
    (g' : List Bool → List Bool → List Bool) (p : PolyExpr) (vFirst : Bool)
    (x zV rP rV : List Bool) (k : ℕ) :
    exec P' (V.pullback f g' p) vFirst x [] zV rP rV k =
      exec ⟨fun _ _ r hist => P'.next x [] r hist, .const (P'.coinLen x.length)⟩ V vFirst (f x)
        [] (g' x zV) rP rV k := by
  refine exec_congr ?_ ?_ vFirst k <;> intro _ <;> rfl

/-- The coin length of a pulled-back strategy at `|x|` is at least (in fact equal to) the
original's at `|f x|` under length regularity — the form in which `LevinTransfer.coinTrunc`
casts the honest coins of the pulled-back protocol to those of `π` on `f x`. -/
private theorem coinLen_le_coinLen_pullback (S : Strategy) (f : List Bool → List Bool)
    (g : List Bool → List Bool → List Bool) {p : PolyExpr} {x : List Bool}
    (hx : (f x).length = p.eval x.length) :
    S.coinLen (f x).length ≤ (S.pullback f g p).coinLen x.length :=
  (Strategy.coinLen_pullback S f g hx).ge

/-- **The honest execution of the pulled-back protocol is the honest execution of `π` on the
reduced instance:** the verifier's output in `(π.pullback f w p)` on `(x, y, z)` with coins
`r` is the output of `π` on `(f x, w x y, z)` with the coins cast along
`Strategy.coinLen_pullback` (`Protocol.pullback_outV`, `exec_pullback`,
`LevinTransfer.ofFn_coinTrunc_of_eq`, the move count `π.rounds (p |x|) = π.rounds |f x|`). -/
private theorem outV_pullback_honest (π : Protocol) (f : List Bool → List Bool)
    (w : List Bool → List Bool → List Bool) {p : PolyExpr} {x : List Bool}
    (hx : (f x).length = p.eval x.length) (y z : List Bool)
    (r : (π.pullback f w p).ExecCoins (π.pullback f w p).P x) :
    (π.pullback f w p).outV (π.pullback f w p).P x y z r =
      π.outV π.P (f x) (w x y) z
        (Prod.map (coinTrunc (coinLen_le_coinLen_pullback π.P f w hx))
          (coinTrunc (coinLen_le_coinLen_pullback π.V f (fun _ z => z) hx)) r) := by
  rw [Protocol.pullback_outV]
  simp only [Protocol.outV, Protocol.transcriptWith, Protocol.pullback, Prod.map]
  rw [ofFn_coinTrunc_of_eq _ (Strategy.coinLen_pullback π.P f w hx).symm,
    ofFn_coinTrunc_of_eq _ (Strategy.coinLen_pullback π.V f (fun _ z => z) hx).symm,
    exec_pullback, ← hx]

/-- **A cheating prover for the pulled-back protocol is a cheating prover for `π`:** the
verifier's output in `(π.pullback f w p)` against `P'` on `x` with coins `r` is the output
of `π` on `f x` against the prover `P* := ⟨fun _ _ r hist => P'.next x [] r hist,
const (P'.coinLen |x|)⟩` (which hard-wires `x` and has `P'`'s random tape) with the verifier
coins cast along `Strategy.coinLen_pullback` (`exec_congr`). -/
private theorem outV_pullback_cheat (π : Protocol) (f : List Bool → List Bool)
    (w : List Bool → List Bool → List Bool) {p : PolyExpr} {x : List Bool}
    (hx : (f x).length = p.eval x.length) (P' : Strategy) (z : List Bool)
    (r : (π.pullback f w p).ExecCoins P' x) :
    (π.pullback f w p).outV P' x [] z r =
      π.outV ⟨fun _ _ r hist => P'.next x [] r hist, .const (P'.coinLen x.length)⟩ (f x) [] z
        (Prod.map (coinTrunc le_rfl)
          (coinTrunc (coinLen_le_coinLen_pullback π.V f (fun _ z => z) hx)) r) := by
  rw [Protocol.pullback_outV]
  simp only [Protocol.outV, Protocol.transcriptWith, Prod.map]
  rw [ofFn_coinTrunc_of_eq _ rfl,
    ofFn_coinTrunc_of_eq _ (Strategy.coinLen_pullback π.V f (fun _ z => z) hx).symm,
    exec_pullback_cheat, ← hx]

/-! ### Claim-124.d: zero-knowledge proofs transfer along Levin reductions -/

/-- **Interactive proofs with efficient prover transfer along Levin reductions, soundness
error `s ∘ p`** [PS10, §4.7, "it is easy to verify that the above protocol is a
zero-knowledge proof"] (Claim-124.d, proof half): if `π` is an interactive proof for `L'` with
efficient prover w.r.t. `R'` and soundness error `s`, `(f, w)` is a Levin reduction of
`(L, R)` to `(L', R')`, and every `x ∈ L` has an `R`-witness (`hLR`, i.e.
`L ⊆ witnessLanguage R`), then `π.pullback f w p` is an interactive proof for `L` with
efficient prover w.r.t. `R` and soundness error `N ↦ s (p N)`.

**Repair (run-3 audit P11-1):** the hypothesis `hLR : ∀ x ∈ L, ∃ y, R x y` was added. No
field of `LevinReduction` relates `L` to `R` — with `R = ∅` the `witness` field is vacuous, so
a witness map that outputs non-witnesses is a valid Levin reduction — while the `complete`
clause of the conclusion needs the pulled-back honest prover, which runs `π.P` on `w x y`, to
hold a witness `y` with `R x y`; without `hLR` the statement is refutable (`npProtocol` for
the relation `|x| = |y|` pulled back along `id` and `w x y := ⟨x, x⟩`). Equivalent
alternative: state the lemma for `L := witnessLanguage R`.

**Proof sketch.** Efficiency of both parties: `Strategy.pullback_efficient` with `h.f_poly`,
`h.w_poly` (for `V` the map `g := fun _ z => z` is `polyTimeComputable_pairSndD`), `h.length_eq`.
Completeness for every witness: for `R x y`, `R' (f x) (w x y)` (`h.witness`), and the
execution of the pulled-back protocol on `(x, y, z)` with coins `r` is the execution of `π` on
`(f x, w x y, z)` with the coins cast along `Strategy.coinLen_pullback` (`outV_pullback_honest`:
`Protocol.pullback_outV` and `LevinTransfer.exec_congr` — the pulled-back next-message
functions are those of `π` on `(f x, w x y)` and `(f x, z)` by definition — with the move
count `π.rounds.eval (p |x|) = π.rounds.eval |f x|` by `h.length_eq`); the cast is a uniform
projection (`LevinTransfer.unifProj_coinTrunc`, `UnifProj.uprob_comp`), so
`hπ.completeWitness` gives probability one. Bounded prover messages:
`Protocol.ProverBounded.pullback` with the bound `B.subst p` of `hπ.boundedP`. Completeness:
for `x ∈ L` take `y` with `R x y` (`hLR`); the honest messages have at most `B(p(|x|))` bits
and the verifier accepts with probability one (`Protocol.ProverBounded.exists_complete`).
Soundness: for `x ∉ L`, `f x ∉ L'` (`h.mem_iff`); a prover `P'` for the pulled-back protocol
on `x` is the prover `P* := ⟨fun _ _ r hist => P'.next x [] r hist, .const (P'.coinLen |x|)⟩`
for `π` on `f x` with the same coins (`outV_pullback_cheat`,
`P*.coinLen |f x| = P'.coinLen |x|`), and
`hπ.sound (f x) _ P* z` gives `1 - s |f x| ≤ Pr[out = [false]]`, i.e. `1 - s (p |x|)` by
`h.length_eq`. -/
theorem LevinReduction.efficientProverProofErr {L L' : Language Bool}
    {R R' : List Bool → List Bool → Prop} {f : List Bool → List Bool}
    {w : List Bool → List Bool → List Bool} {p : PolyExpr} (h : LevinReduction L L' R R' f w p)
    (hLR : ∀ x ∈ L, ∃ y, R x y) {π : Protocol} {s : ℕ → ℝ}
    (hπ : EfficientProverProofErr π L' R' s) :
    EfficientProverProofErr (π.pullback f w p) L R (fun N => s (p.eval N)) := by
  have hcompl : ∀ x y, R x y → ∀ z : List Bool,
      uprob (fun r : (π.pullback f w p).ExecCoins (π.pullback f w p).P x =>
        (π.pullback f w p).outV (π.pullback f w p).P x y z r = [true]) = 1 := by
    intro x y hxy z
    have hx := h.length_eq x
    have key := hπ.completeWitness (f x) (w x y) (h.witness x y hxy) z
    rw [← ((unifProj_coinTrunc (coinLen_le_coinLen_pullback π.P f w hx)).prod
      (unifProj_coinTrunc (coinLen_le_coinLen_pullback π.V f (fun _ z => z) hx))).uprob_comp
      (fun r' => π.outV π.P (f x) (w x y) z r' = [true])] at key
    rw [← key]
    congr 1
    funext r
    rw [outV_pullback_honest π f w hx]
  obtain ⟨B, hB⟩ := hπ.boundedP
  refine ⟨⟨Strategy.pullback_efficient hπ.efficientV h.f_poly polyTimeComputable_pairSndD
    h.length_eq, (hB.pullback h).exists_complete hLR hcompl, fun x hx P' z => ?_⟩,
    Strategy.pullback_efficient hπ.efficientP h.f_poly h.w_poly h.length_eq,
    ⟨B.subst p, hB.pullback h⟩, hcompl⟩
  · have hlen := h.length_eq x
    have hfx : f x ∉ L' := fun hfx => hx ((h.mem_iff x).2 hfx)
    have hU : UnifProj (Prod.map (coinTrunc le_rfl)
        (coinTrunc (coinLen_le_coinLen_pullback π.V f (fun _ z => z) hlen)) :
          (π.pullback f w p).ExecCoins P' x →
            π.ExecCoins ⟨fun _ _ r hist => P'.next x [] r hist, .const (P'.coinLen x.length)⟩
              (f x)) :=
      (unifProj_coinTrunc _).prod (unifProj_coinTrunc _)
    have key := hπ.sound (f x) hfx
      ⟨fun _ _ r hist => P'.next x [] r hist, .const (P'.coinLen x.length)⟩ z
    rw [← hU.uprob_comp] at key
    refine le_of_eq_of_le (by rw [hlen]) (le_of_le_of_eq key ?_)
    congr 1
    funext r
    rw [outV_pullback_cheat π f w hlen]

/-- **Interactive proofs with efficient prover transfer along Levin reductions** (Claim-124.d,
proof half, negligible error): as `LevinReduction.efficientProverProofErr`, the soundness
error `ε (p N)` being negligible by `Negligible.comp_of_le` with `h.le_eval`
(`EfficientProverProof.exists_err`, `EfficientProverProofErr.efficientProverProof`).

**Repair (run-3 audit P11-1):** hypothesis `hLR : ∀ x ∈ L, ∃ y, R x y` added (see
`LevinReduction.efficientProverProofErr`). -/
theorem LevinReduction.efficientProverProof {L L' : Language Bool}
    {R R' : List Bool → List Bool → Prop} {f : List Bool → List Bool}
    {w : List Bool → List Bool → List Bool} {p : PolyExpr} (h : LevinReduction L L' R R' f w p)
    (hLR : ∀ x ∈ L, ∃ y, R x y) {π : Protocol} (hπ : EfficientProverProof π L' R') :
    EfficientProverProof (π.pullback f w p) L R := by
  obtain ⟨ε, hε, herr⟩ := hπ.exists_err
  exact (h.efficientProverProofErr hLR herr).efficientProverProof (hε.comp_of_le _ h.le_eval)

/-- **Zero-knowledge transfers along Levin reductions** [PS10, §4.7, "it is easy to verify
that the above protocol is a zero-knowledge proof"] (Claim-124.d, zero-knowledge half): if `π`
is zero-knowledge for `R'` and `(f, w)` is a Levin reduction of `(L, R)` to `(L', R')`, then
`π.pullback f w p` is zero-knowledge for `R`.

**Proof sketch.** Let `V*` be an efficient verifier for the pulled-back protocol. The
verifier `V*' := LevinTransfer.liftVerifier V*` for `π`, `V*'.next x' z' r hist := V*.next
(pairFstD z') (pairSndD z') (r.take (V*.coinLen |pairFstD z'|)) hist` with coins `V*.coins`
(at `|x'| = p |x| ≥ |x|` the tape is long enough, `PolyExpr.eval_mono`, `h.le_eval`), recovers
`x` from its auxiliary input `z' = ⟨x, z⟩` and ignores `x'`; it is efficient
(`LevinTransfer.liftVerifier_efficient`, from `V*`'s machine with
`polyTimeComputable_pairTakePoly`). `hzk V*'` gives a uniform simulator `S'`; the simulator for
`V*` is `S` with `S.simulate x z r = post (S'.simulate (f x) ⟨x, z⟩ r)`, where
`post := LevinTransfer.postView V*.coins` re-encodes the view `⟨⟨x', ⟨x, z⟩⟩, ⟨r', msgs⟩⟩` as
`⟨⟨x, z⟩, ⟨r'.take (V*.coinLen |x|), msgs⟩⟩` (`LevinTransfer.exists_liftSimulator`:
`NUPPT.exists_comp` with `pre y := ⟨f (fst y), y⟩`, then `NUPPT.exists_reparam p`; uniform,
coins `S'.coins.subst p`). For `Lz`, `D`: the distinguisher `D'` for `π` at parameter
`|x'| = p |x|` is `D` re-parametrized along the left inverse `φ N' := min (invFun p.eval N') N'`
of `p.eval` — well defined since `p ≥ id` is strictly increasing
(`LevinTransfer.polyExpr_strictMono_of_le`) — composed with `post`
(`LevinTransfer.exists_liftDistinguisher`: `NUPPT.exists_reparam_advice`, `NUPPT.exists_comp`);
auxiliary bound `Lz' := add (add (mul (const 2) var) (const 2)) Lz` (`|⟨x, z⟩| ≤ 2|x| + 2
+ Lz |x| ≤ Lz' |x'|`). `hzk V*' Lz' D'` gives `ε'`; on `R x y` (so `R' (f x) (w x y)`), `post` of
the view of `V*'` in `π` on `(f x, w x y, ⟨x, z⟩)` with coins `(r₁, r₂')` is the view of `V*` in
the pulled-back protocol with coins `(r₁, r₂'.take (V*.coinLen |x|))`
(`LevinTransfer.exec_congr`, `liftVerifier_next`, `postView_encode`), and `D'`'s verdict is
`D`'s on the re-encoded sample with truncated coins (`LevinTransfer.distinguisherL_lift`);
the truncations are uniform projections, so the two advantages coincide
(`LevinTransfer.distAdv_eq_of_unifProj`) and `distAdv ≤ ε' |f x| = ε' (p |x|)`;
`ε := ε' ∘ p.eval` is negligible by `Negligible.comp_of_le`. -/
theorem LevinReduction.zk {L L' : Language Bool} {R R' : List Bool → List Bool → Prop}
    {f : List Bool → List Bool} {w : List Bool → List Bool → List Bool} {p : PolyExpr}
    (h : LevinReduction L L' R R' f w p) {π : Protocol} (hzk : ZK π R') :
    ZK (π.pullback f w p) R := by
  intro V' hV'
  obtain ⟨S', hS'u, hS'⟩ := hzk (liftVerifier V') (liftVerifier_efficient hV')
  obtain ⟨S, hSc, hSu, hS⟩ := exists_liftSimulator S' h.f_poly V'.coins p
  refine ⟨S, hSu hS'u, fun Lz D => ?_⟩
  -- the left inverse `φ` of the (strictly increasing) length polynomial
  have hmono := polyExpr_strictMono_of_le h.le_eval
  set φ : ℕ → ℕ := fun n => min (Function.invFun p.eval n) n with hφ_def
  have hφle : ∀ n, φ n ≤ n := fun n => min_le_right _ _
  have hφp : ∀ N, φ (p.eval N) = N := fun N => by
    simp only [hφ_def, Function.leftInverse_invFun hmono.injective N]
    exact min_eq_left (h.le_eval N)
  obtain ⟨D', hD'c, hD'⟩ := exists_liftDistinguisher D φ hφle V'.coins
  set Lz' : PolyExpr := .add (.add (.mul (.const 2) .var) (.const 2)) Lz with hLz'
  obtain ⟨ε', hε', hadv⟩ := hS' Lz' D'
  refine ⟨fun N => ε' (p.eval N), hε'.comp_of_le _ h.le_eval, fun x y z hxy hz => ?_⟩
  have hlen := h.length_eq x
  have hz' : (pairEncode x z).length ≤ Lz'.eval (f x).length := by
    rw [length_pairEncode, hlen, hLz']
    simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
    have h₁ := h.le_eval x.length
    have h₂ := Lz.eval_mono (h.le_eval x.length)
    omega
  have key := hadv (f x) (w x y) (pairEncode x z) (h.witness x y hxy) hz'
  -- coin-space bookkeeping
  have hxle : x.length ≤ (f x).length := by rw [hlen]; exact h.le_eval _
  have hφx : φ (f x).length = x.length := by rw [hlen]; exact hφp _
  have hDle : D.coinLen x.length ≤ D'.coinLen (f x).length := by
    simp only [NUPPT.coinLen, hD'c]
    exact D.coins.eval_mono hxle
  have hVle : V'.coinLen x.length ≤ (liftVerifier V').coinLen (f x).length := by
    rw [liftVerifier_coinLen]
    exact V'.coins.eval_mono hxle
  have hPeq : (π.P.pullback f w p).coinLen x.length = π.P.coinLen (f x).length :=
    Strategy.coinLen_pullback π.P f w hlen
  have hSeq : S.coinLen x.length = S'.coinLen (f x).length := by
    simp only [NUPPT.coinLen, hSc, PolyExpr.eval_subst, hlen]
  calc distAdv (fun r => (((π.pullback f w p).withV V').viewV x y z r).encode) (S.simulate x z)
        (D.distinguisherL x.length)
      = distAdv (fun r => ((π.withV (liftVerifier V')).viewV (f x) (w x y) (pairEncode x z) r).encode)
          (S'.simulate (f x) (pairEncode x z)) (D'.distinguisherL (f x).length) := by
        refine (distAdv_eq_of_unifProj ((unifProj_coinTrunc hPeq.le).prod (unifProj_coinTrunc hVle))
          (unifProj_coinTrunc hSeq.le) (unifProj_coinTrunc hDle) (fun r ρ => ?_)
          (fun r ρ => ?_)).symm
        · -- the view of `V*'` in `π` re-encodes to the view of `V'` in the pulled-back protocol
          rw [distinguisherL_lift hD' hφx hDle]
          congr 2
          simp only [Protocol.viewV, Protocol.transcriptWith, Protocol.withV_P, Protocol.withV_V,
            Protocol.withV_rounds, Protocol.withV_verifierFirst, Protocol.pullback, Prod.map,
            postView_encode]
          rw [ofFn_coinTrunc_of_eq _ hPeq, ofFn_coinTrunc]
          simp only [PolyExpr.eval_subst, ← hlen, Strategy.coinLen]
          congr 2
          refine congrArg Prod.snd (exec_congr ?_ ?_ _ _)
          · intro _
            rfl
          · intro _
            exact liftVerifier_next V' _ x z _ _
        · -- the simulator for `V'` is `postView` of the simulator for `V*'`
          rw [distinguisherL_lift hD' hφx hDle]
          congr 2
          simp only [NUPPT.simulate, NUPPT.runAt_eq, hS, pairFstD_pairEncode]
          rw [ofFn_coinTrunc_of_eq _ hSeq, ← hlen]
    _ ≤ ε' (f x).length := key
    _ = ε' (p.eval x.length) := by rw [hlen]

/-! ### Theorem 124.1 -/

/-- **[PS10, Theorem 124.1], form (A): a commitment scheme and a Levin reduction to `3COL`
give a zero-knowledge protocol for `L` with soundness error `1 - 1/p(|x|) + 2^{-p(|x|)}` whose
`n|E|`-fold repetition is an interactive proof** (Thm-124.1): for a commitment scheme
`(Com, ℓ)` and a Levin reduction `(f, w)` of `(L, R)` to `(3COL, R_3COL)` with
`L ⊆ witnessLanguage R` (`hLR`),
the pulled-back `n|E|`-fold 3-colouring protocol is an interactive proof for `L` with
efficient prover w.r.t. `R`, and the pulled-back one-iteration protocol is zero-knowledge for
`R` and an interactive proof with efficient prover and soundness error
`1 - 1/p(|x|) + (1/2)^{p(|x|)}`.

**Deviation (DQ5):** the proof and the zero-knowledge statements are for the repeated and
the single-iteration protocols respectively (sequential composition, [PS10, §7.2.1], is out
of scope; the text's single zero-knowledge proof with negligible soundness error is debt that
ch. 7 discharges, ruling G3-7(d)); the reduction is an explicit hypothesis (the text's
"Cook's reduction applied to the witness" is a Levin reduction, never defined there).

**Repair (run-3 audit P11-1):** hypothesis `hLR : ∀ x ∈ L, ∃ y, R x y` added — the first and
third conjuncts are instances of `LevinReduction.efficientProverProofErr`, and without it
the reduction `id`, `w x y := []` of `(3COL, ∅)` to `(3COL, R_3COL)` refutes them on the
2-vertex one-edge graph (the pulled-back prover commits to the constant colouring
`decColoring n [] = 0` and opens two equal colours). -/
theorem zk_proof_of_levinReduction {Com : List Bool → List Bool} {ℓ : PolyExpr}
    (hC : Commitment Com ℓ) {L : Language Bool} {R : List Bool → List Bool → Prop}
    {f : List Bool → List Bool} {w : List Bool → List Bool → List Bool} {p : PolyExpr}
    (h : LevinReduction L L3COL R R3COL f w p) (hLR : ∀ x ∈ L, ∃ y, R x y) :
    EfficientProverProof ((colProtocolRep Com ℓ).pullback f w p) L R ∧
      ZK ((colProtocol Com ℓ).pullback f w p) R ∧
      EfficientProverProofErr ((colProtocol Com ℓ).pullback f w p) L R
        (fun N => 1 - 1 / (p.eval N : ℝ) + (1 / 2 : ℝ) ^ p.eval N) :=
  ⟨h.efficientProverProof hLR (colRep_efficientProverProof hC), h.zk (col_zk hC),
    h.efficientProverProofErr hLR (col_efficientProverProofErr hC)⟩

/-- **[PS10, Theorem 124.1]: if one-way permutations (with a hard-core predicate) exist, every
language with a Levin reduction to `3COL` has a zero-knowledge protocol with soundness error
`1 - 1/p(|x|) + 2^{-p(|x|)}`** (Thm-124.1, untied existential form): for `L ⊆ witnessLanguage R`
(`hLR`) there is a protocol that is an interactive proof for `L` with efficient prover w.r.t.
`R`, and a protocol that is zero-knowledge for `R` and an interactive proof with efficient
prover and soundness error `1 - 1/p(|x|) + (1/2)^{p(|x|)}` — the commitment scheme of
[PS10, Theorem 126.4] (`exists_commitment_of_owp_hardCore`) plugged into
`zk_proof_of_levinReduction`.

**Deviation:** hard-core predicate explicit (source error 47); single OWP rather than a
collection; see `zk_proof_of_levinReduction` for the two-protocol form (DQ5). The first
conjunct alone says nothing about the zero-knowledge protocol (gate 03e, minor 3:
`npProtocol` pulled back along `(f, w)` already witnesses it); the tied form, both protocols
from one commitment scheme, is `exists_commitment_zk_proof_of_owp_levinReduction`.

**Repair (run-3 audit P11-1):** hypothesis `hLR : ∀ x ∈ L, ∃ y, R x y` added (see
`zk_proof_of_levinReduction`). -/
theorem zk_proof_of_owp_levinReduction
    (how : ∃ (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool),
      OneWayPermutation P ∧ HardCore P.toFunFamily h)
    {L : Language Bool} {R : List Bool → List Bool → Prop} {f : List Bool → List Bool}
    {w : List Bool → List Bool → List Bool} {p : PolyExpr}
    (h : LevinReduction L L3COL R R3COL f w p) (hLR : ∀ x ∈ L, ∃ y, R x y) :
    (∃ π : Protocol, EfficientProverProof π L R) ∧
      ∃ π : Protocol, ZK π R ∧ EfficientProverProofErr π L R
        (fun N => 1 - 1 / (p.eval N : ℝ) + (1 / 2 : ℝ) ^ p.eval N) := by
  obtain ⟨Com, ℓ, hC⟩ := exists_commitment_of_owp_hardCore how
  obtain ⟨h1, h2, h3⟩ := zk_proof_of_levinReduction hC h hLR
  exact ⟨⟨_, h1⟩, _, h2, h3⟩

/-- **[PS10, Theorem 124.1], tied form: if one-way permutations exist, every language with a
Levin reduction to `3COL` has a zero-knowledge protocol with soundness error
`1 - 1/p(|x|) + 2^{-p(|x|)}` whose `n|E|`-fold repetition is an interactive proof**
(Thm-124.1; gate 03e, minor 3): from the text's hypothesis, a single one-way permutation, there
is a commitment scheme `(Com, ℓ)` (`exists_commitment_of_owp`, [PS10, Theorem 126.4] with the
hard-core predicate of Goldreich–Levin) for which the conclusion of
`zk_proof_of_levinReduction` holds: both protocols are built from `Com` and the reduction.

**Deviation (DQ5):** as for `zk_proof_of_levinReduction`. -/
theorem exists_commitment_zk_proof_of_owp_levinReduction
    (how : ∃ P : PermFamily, OneWayPermutation P)
    {L : Language Bool} {R : List Bool → List Bool → Prop} {f : List Bool → List Bool}
    {w : List Bool → List Bool → List Bool} {p : PolyExpr}
    (h : LevinReduction L L3COL R R3COL f w p) (hLR : ∀ x ∈ L, ∃ y, R x y) :
    ∃ (Com : List Bool → List Bool) (ℓ : PolyExpr), Commitment Com ℓ ∧
      EfficientProverProof ((colProtocolRep Com ℓ).pullback f w p) L R ∧
      ZK ((colProtocol Com ℓ).pullback f w p) R ∧
      EfficientProverProofErr ((colProtocol Com ℓ).pullback f w p) L R
        (fun N => 1 - 1 / (p.eval N : ℝ) + (1 / 2 : ℝ) ^ p.eval N) := by
  obtain ⟨Com, ℓ, hC⟩ := exists_commitment_of_owp how
  exact ⟨Com, ℓ, hC, zk_proof_of_levinReduction hC h hLR⟩

/-- Sanity (run-3 audit P11-2): the soundness error `1 - 1/k + (1/2)^k` of the one-iteration
protocols is strictly below `1` for `k ≥ 1`, since `k < 2^k` (`Nat.lt_two_pow_self`). Hence
`EfficientProverProofErr π L R (fun N => 1 - 1/(p N) + (1/2)^{p N})` with `p N ≥ N ≥ 1`
asserts genuine soundness: the verifier rejects every `x ∉ L` with probability at least
`1/p(|x|) - 2^{-p(|x|)} > 0`. -/
theorem one_sub_inv_add_half_pow_lt_one {k : ℕ} (hk : 0 < k) :
    1 - 1 / (k : ℝ) + (1 / 2 : ℝ) ^ k < 1 := by
  have hlt : k < 2 ^ k := Nat.lt_two_pow_self
  have h2 : (k : ℝ) < (2 : ℝ) ^ k := by exact_mod_cast hlt
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have h3 : (1 / 2 : ℝ) ^ k = 1 / (2 : ℝ) ^ k := by rw [one_div_pow]
  have h4 : 1 / (2 : ℝ) ^ k < 1 / (k : ℝ) := one_div_lt_one_div_of_lt hkpos h2
  linarith

/-- NP-hardness with Levin reductions [PS10, §4.7, Theorem 124.1, step 2, the implicit
hypothesis] (Claim-124.b/c as a hypothesis): every language with a witness relation Levin-reduces
to `(L', R')`. The string-level Levin reduction `3SAT → 3COL` that would establish
`LevinNPHard L3COL R3COL` is not formalized (plan decision on Theorem 124.1). -/
def LevinNPHard (L' : Language Bool) (R' : List Bool → List Bool → Prop) : Prop :=
  ∀ (L : Language Bool) (R : List Bool → List Bool → Prop), WitnessRelation L R →
    ∃ (f : List Bool → List Bool) (w : List Bool → List Bool → List Bool) (p : PolyExpr),
      LevinReduction L L' R R' f w p

/-- **[PS10, Theorem 124.1], "every language in NP", for every witness relation** (Thm-124.1;
gate 03e, minors 3 and 4): under NP-hardness of `3COL` with Levin reductions, for a commitment
scheme `(Com, ℓ)` and every witness relation `R` of `L` there is a Levin reduction `(f, w)` of
`(L, R)` to `(3COL, R_3COL)` with length polynomial `p ≥ id` for which the pulled-back
one-iteration 3-colouring protocol is zero-knowledge for `R` with soundness error
`1 - 1/p(|x|) + 2^{-p(|x|)}`, and its `n|E|`-fold repetition is an interactive proof with
efficient prover (`zk_proof_of_levinReduction`, with `hLR` from `WitnessRelation.mem_iff`).
The Levin reduction `LevinReduction L L3COL R R3COL f w p` is part of the conclusion (ruling
R-03e-r2-1 of gate 03e round 2), so further protocols can be pulled back along the same maps.

**Deviation (DQ5):** as for `zk_proof_of_levinReduction`. -/
theorem zk_proof_of_witnessRelation (h3 : LevinNPHard L3COL R3COL)
    {Com : List Bool → List Bool} {ℓ : PolyExpr} (hC : Commitment Com ℓ) {L : Language Bool}
    {R : List Bool → List Bool → Prop} (hR : WitnessRelation L R) :
    ∃ (f : List Bool → List Bool) (w : List Bool → List Bool → List Bool) (p : PolyExpr),
      LevinReduction L L3COL R R3COL f w p ∧ (∀ N, N ≤ p.eval N) ∧
      EfficientProverProof ((colProtocolRep Com ℓ).pullback f w p) L R ∧
      ZK ((colProtocol Com ℓ).pullback f w p) R ∧
      EfficientProverProofErr ((colProtocol Com ℓ).pullback f w p) L R
        (fun N => 1 - 1 / (p.eval N : ℝ) + (1 / 2 : ℝ) ^ p.eval N) := by
  obtain ⟨f, w, p, h⟩ := h3 L R hR
  exact ⟨f, w, p, h, h.le_eval, zk_proof_of_levinReduction hC h fun x hx => (hR.mem_iff x).1 hx⟩

/-- **[PS10, Theorem 124.1], "if one-way permutations exist then every language in NP has a
zero-knowledge proof", for every witness relation** (Thm-124.1; gate 03e, minors 3 and 4):
from the text's hypothesis, a one-way permutation, there is a commitment scheme
(`exists_commitment_of_owp`) for which the conclusion of `zk_proof_of_witnessRelation` holds
(the Levin reduction included), under NP-hardness of `3COL` with Levin reductions.

**Deviation (DQ5):** as for `zk_proof_of_levinReduction`. -/
theorem zk_proof_of_witnessRelation_of_owp (h3 : LevinNPHard L3COL R3COL)
    (how : ∃ P : PermFamily, OneWayPermutation P) {L : Language Bool}
    {R : List Bool → List Bool → Prop} (hR : WitnessRelation L R) :
    ∃ (Com : List Bool → List Bool) (ℓ : PolyExpr), Commitment Com ℓ ∧
      ∃ (f : List Bool → List Bool) (w : List Bool → List Bool → List Bool) (p : PolyExpr),
        LevinReduction L L3COL R R3COL f w p ∧ (∀ N, N ≤ p.eval N) ∧
        EfficientProverProof ((colProtocolRep Com ℓ).pullback f w p) L R ∧
        ZK ((colProtocol Com ℓ).pullback f w p) R ∧
        EfficientProverProofErr ((colProtocol Com ℓ).pullback f w p) L R
          (fun N => 1 - 1 / (p.eval N : ℝ) + (1 / 2 : ℝ) ^ p.eval N) := by
  obtain ⟨Com, ℓ, hC⟩ := exists_commitment_of_owp how
  exact ⟨Com, ℓ, hC, zk_proof_of_witnessRelation h3 hC hR⟩

/-- **[PS10, Theorem 124.1], "every language in NP", one-iteration form: a zero-knowledge
protocol with soundness error `1 - 1/p(|x|) + 2^{-p(|x|)}`**, under NP-hardness of `3COL` with
Levin reductions: for a commitment scheme and every `L ∈ NP` there is a witness relation `R` for
`L` with an interactive proof with efficient prover, and a protocol that is zero-knowledge
for `R` and an interactive proof with efficient prover and soundness error
`1 - 1/p(|x|) + (1/2)^{p(|x|)}`, where `p ≥ id` is the length polynomial of the Levin
reduction (the two protocols of `zk_proof_of_levinReduction`; the witness relation from
`exists_witnessRelation_of_mem_NP`, [PS10, Definition 191.11], supplies `hLR`). This is the
corollary of `zk_proof_of_witnessRelation`, which holds for every witness relation (gate 03e,
minor 4) and ties the two protocols together; here the conjunct
`∃ π, EfficientProverProof π L R` alone says nothing about the zero-knowledge protocol
(`npProtocol` witnesses it, minor 3).

**Repair (run-3 audit P11-2):** the run-2 conclusion `∃ s, EfficientProverProofErr π L R s`
asserted no soundness (`s := 1` turns the clause into `0 ≤ uprob …`, so it followed from the
parties' efficiency and completeness alone); the explicit error of the Levin reduction's
length polynomial is kept, together with `∀ N, N ≤ p.eval N`, so that the error is below `1`
by the noticeable margin `1/p(N) - 2^{-p(N)}` (`one_sub_inv_add_half_pow_lt_one`). -/
theorem zk_proof_of_mem_NP (h3 : LevinNPHard L3COL R3COL) {Com : List Bool → List Bool}
    {ℓ : PolyExpr} (hC : Commitment Com ℓ) {L : Language Bool} (hL : L ∈ NP) :
    ∃ R : List Bool → List Bool → Prop, WitnessRelation L R ∧
      (∃ π : Protocol, EfficientProverProof π L R) ∧
      ∃ (π : Protocol) (p : PolyExpr), (∀ N, N ≤ p.eval N) ∧ ZK π R ∧
        EfficientProverProofErr π L R
          (fun N => 1 - 1 / (p.eval N : ℝ) + (1 / 2 : ℝ) ^ p.eval N) := by
  obtain ⟨R, hR⟩ := exists_witnessRelation_of_mem_NP hL
  obtain ⟨_, _, p, -, hp, h1, h2, h3'⟩ := zk_proof_of_witnessRelation h3 hC hR
  exact ⟨R, hR, ⟨_, h1⟩, _, p, hp, h2, h3'⟩

/-- **[PS10, Theorem 124.1], "if one-way permutations exist then every language in NP has a
zero-knowledge proof", one-iteration form: a zero-knowledge protocol with soundness error
`1 - 1/p(|x|) + 2^{-p(|x|)}`**, under NP-hardness of `3COL` with Levin reductions and with the
hard-core predicate explicit (`exists_commitment_of_owp_hardCore`, `zk_proof_of_mem_NP`):
the zero-knowledge protocol has the explicit soundness error `1 - 1/p(|x|) + (1/2)^{p(|x|)}`
of the Levin reduction's length polynomial `p ≥ id`.

**Repair (run-3 audit P11-2):** explicit soundness error instead of the vacuous
`∃ s, EfficientProverProofErr π L R s` (see `zk_proof_of_mem_NP`). The form for every witness
relation, from the text's hypothesis (a one-way permutation) and with the two protocols tied,
is `zk_proof_of_witnessRelation_of_owp` (gate 03e, minors 3 and 4). -/
theorem zk_proof_of_mem_NP_of_owp (h3 : LevinNPHard L3COL R3COL)
    (how : ∃ (P : PermFamily) (h : ∀ n, (Fin n → Bool) → Bool),
      OneWayPermutation P ∧ HardCore P.toFunFamily h)
    {L : Language Bool} (hL : L ∈ NP) :
    ∃ R : List Bool → List Bool → Prop, WitnessRelation L R ∧
      (∃ π : Protocol, EfficientProverProof π L R) ∧
      ∃ (π : Protocol) (p : PolyExpr), (∀ N, N ≤ p.eval N) ∧ ZK π R ∧
        EfficientProverProofErr π L R
          (fun N => 1 - 1 / (p.eval N : ℝ) + (1 / 2 : ℝ) ^ p.eval N) := by
  obtain ⟨Com, ℓ, hC⟩ := exists_commitment_of_owp_hardCore how
  exact zk_proof_of_mem_NP h3 hC hL

end TCSlib.Cryptography

## ===== TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.ZeroKnowledge.Encoding
import TCSlib.Cryptography.ZeroKnowledge.InteractiveProofs
import TCSlib.Cryptography.ZeroKnowledge.Defs
import TCSlib.Cryptography.Pseudorandom.GeneratorFromPermutation
import TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.Efficiency
import TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.EfficiencyRep
import TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.EfficiencyRepGI
import TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.Soundness
import TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.SoundnessRep
import TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.SoundnessRepGI

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The graph non-isomorphism and graph isomorphism protocols

The two graph protocols of [PS10, §4.5]: the interactive proof for graph non-isomorphism
[PS10, Protocol 118.3, Proposition 118.4] (unbounded prover, verifier first) and the
interactive proof with efficient prover for graph isomorphism [PS10, Protocol 120.6,
Proposition 120.7] (prover first). Graphs are the Boolean adjacency relations `Graph n` of
`Encoding.lean`, isomorphism is `Isomorphic G₀ G₁ := ∃ σ, σ(G₀) = G₁` (Def-117.e), the string
languages `Liso`, `Lniso` and the witness relation `Riso` are stated on the encoded instance
`⟨encGraph G₀, encGraph G₁⟩` (Def-118.a). Every protocol is given once for a single iteration
and once repeated `|x|` times (the text's "repeat `|G₁|` times"); the concrete probability
lemmas (Lem-119.a–d, Lem-120.a–d) are stated over typed coins with ideal uniform
permutations, and the string-level propositions carry the statistical term of the
rejection-sampled permutations (D10).

**Deviation (D10, Inf-4.2):** the honest parties sample `σ, π ← S_n` by `samplePerm`
(`permFromCoins` at the campaign parameters of `Asymptotic/Permutations.lean`:
`permBits n = Nat.size n` bits per trial and `permTrials n = 2n²` trials per position,
identity on failure), which fails with probability at most `permFailBound n = n · 2^{-n}`;
the single-iteration graph non-isomorphism proof has soundness error `1/2 + permFailBound n`
and the repeated protocols' soundness errors carry the same term. The frozen scratch's
`permFromCoins n n n` (`n` bits per trial) accepts a trial with probability `(n - i) / 2^n`
and would make the prover's permutation the identity almost surely — under which
Theorem 122.3 fails (the third message would reveal `σ⁻¹`).

**Repair (run-3 audit P2-1):** `samplePerm`, `permCoinLen` and `permFailBound` are stated in
terms of the shared `permBits`/`permTrials`, `permFailBound n = n · 2^{-n}` is the closed
form `uprob_permFromCoins_none_le_two_pow`, `statClose_samplePerm` and
`negligible_mul_permFailBound` are proved from the shared lemmas, and the run-2
`permFailBound_le_exp` (bound `n e^{-n/2}` for the local parameters) was removed.
(Run-3 audit P10-3, which reported the private `polyTimeComputable_encSamplePerm` as a
diverged copy of the shared sampler lemma with `n²` trials, is resolved by the same repair:
the string form of the sampler is `GI.sampleStr_poly` of `GraphIsomorphism/Efficiency.lean`,
a derivation of `polyTimeComputable_encPermFromCoins` at the one set of parameters
`permBits`/`permTrials`, and DESIGN.md §2.15 records them.)

**Proof layout (run 4).** This file is at the file-size limit, so the proofs of its theorems
live in the sibling files `GraphIsomorphism/Proofs.lean` (verbatim shadow copies of the
definitions below in the inner namespace `GI`, definitionally equal to them, with the generic
infrastructure), `GraphIsomorphism/Efficiency.lean` (the machines of the honest parties and the
decider of `Riso`) and `GraphIsomorphism/Soundness.lean` (completeness and soundness); each
target below is closed by `exact GI.…`, which type-checks by `rfl`.

**Repair (run-3 audit P10-1, P10-2):** the exact-probability lemmas `uprob_adaptive_guess`
(Lem-119.c) and `uprob_gni_rep_cheat` (Lem-119.b) assume the auxiliary coin type nonempty
(`[Nonempty W]`, `[Nonempty ρ]`): `uprob` on an empty type is `0`, so the run-2 statements
read `0 = 1` at `m = 0` over `Empty`. Every consumer instantiates the coin type with a tape
`Fin k → Bool` (nonempty), so no downstream statement changes; `uprob_gi_rep_cheat_le`
(an inequality, true for empty coins) is reproved by a case split on `ρ`. Both corrected
lemmas are proved in this file (the `xor` bijection `adaptiveEquiv` and the change of
variables `gniShear`), which certifies the repaired statements.

**Deviation (fixed alternation, D8):** the repeated graph-isomorphism protocol uses four
moves per iteration (`H`, `b`, `γ`, and a verifier message, empty except for the final
verdict) so that the strict prover/verifier alternation of `exec` is respected; the repeated
protocols run `|x|` iterations instead of the text's `n = |G₁|` (so `2^{-|x|}` is negligible in
`|x|` directly).

**Deviation (well-formedness):** the verifiers reject common inputs that are not the
encoding of two graphs on the same vertex set (`wellFormedInstance`); without this check a
malformed `x ∉ L` could decode to a pair of isomorphic graphs and soundness would fail.

## Contents

* `TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.Proofs` — shadow copies of the
  definitions of this file (namespace `GI`) and the generic proof infrastructure.
* `TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.Efficiency` — the machines of the honest
  parties of the single iterations and the decider of `Riso`.
* `TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.EfficiencyRep` — the loop infrastructure
  of the `|x|`-fold parties and the machine of the `|x|`-fold graph non-isomorphism verifier.
* `TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.EfficiencyRepGI` — the machines of the
  parties of the `|x|`-fold graph isomorphism protocol.
* `TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.Soundness` — completeness and soundness of
  the single iterations.
* `TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.Concrete` — shadow copies of the concrete
  repetition lemmas (Lem-119.b, Lem-119.c, Lem-120.d) for the sibling proofs.
* `TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.SoundnessRep` — completeness and soundness
  of the `|x|`-fold graph non-isomorphism protocol.
* `TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.SoundnessRepGI` — completeness and
  soundness of the `|x|`-fold graph isomorphism protocol.

## Main definitions

* `TCSlib.Cryptography.Isomorphic` — `∃ σ, σ(G₀) = G₁` [PS10, §4.5] (Def-117.e).
* `TCSlib.Cryptography.Liso`, `TCSlib.Cryptography.Lniso`, `TCSlib.Cryptography.Riso` —
  the languages of isomorphic / non-isomorphic encoded pairs and the witness relation
  (Def-118.a); `encInstance`, `wellFormedInstance`, `instanceVertices`.
* `TCSlib.Cryptography.samplePerm`, `TCSlib.Cryptography.permFailBound` — the honest parties'
  permutation sampler and its failure bound (D10).
* `TCSlib.Cryptography.gniProtocol`, `TCSlib.Cryptography.gniProtocolRep` — the graph
  non-isomorphism protocol, one iteration and `|x|` iterations [PS10, Protocol 118.3]
  (Prot-118.3).
* `TCSlib.Cryptography.giProtocol`, `TCSlib.Cryptography.giProtocolRep` — the graph
  isomorphism protocol, one iteration and `|x|` iterations [PS10, Protocol 120.6]
  (Prot-120.6).

## Main results

* `TCSlib.Cryptography.uprob_permGraph_eq_of_isomorphic` — uniformly permuted isomorphic
  graphs are identically distributed (Lem-119.a, proved).
* `TCSlib.Cryptography.uprob_adaptive_guess` — the adaptive guessing lemma `2^{-m}`
  (Lem-119.c, proved); `TCSlib.Cryptography.uprob_gni_rep_cheat` — `n`-fold GNI soundness
  (Lem-119.b, proved); `TCSlib.Cryptography.gni_honest_reply` — GNI completeness (Lem-119.d,
  proved).
* `TCSlib.Cryptography.gi_honest_reply_eq` (Lem-120.a, proved),
  `TCSlib.Cryptography.not_isomorphic_both` (Lem-120.b, proved),
  `TCSlib.Cryptography.uprob_gi_cheat_le_half` (Lem-120.c, proved),
  `TCSlib.Cryptography.uprob_gi_rep_cheat_le` (Lem-120.d, proved from Lem-119.c).
* `TCSlib.Cryptography.gni_interactiveProofErr`, `TCSlib.Cryptography.gni_interactiveProof`
  — [PS10, Proposition 118.4]; `TCSlib.Cryptography.gi_efficientProverProofErr`,
  `TCSlib.Cryptography.gi_rep_efficientProverProof` — [PS10, Proposition 120.7];
  `TCSlib.Cryptography.giProtocol_proverBounded`, `TCSlib.Cryptography.gniProtocol_proverBounded`
  (and the `Rep` forms) — the honest messages are bounded (ruling G3-3).
* `TCSlib.Cryptography.Riso_witnessRelation` — `Riso` is a witness relation for `Liso`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§4.5 Interactive proofs, pp. 117–120.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026 (the concrete probability layer).
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Cambridge
  University Press, 2009. (Chapter 8, the graph non-isomorphism protocol.)
-/

namespace TCSlib.Cryptography

open Complexity Turing Finset

/-! ### Isomorphism of graphs (Def-117.e) -/

/-- Two graphs on `Fin n` are isomorphic when some relabelling `σ` maps the first onto the
second, `σ(G₀) = G₁` [PS10, §4.5] (Def-117.e). The "same number of vertices" condition of
the text is the common type `Graph n`. -/
def Isomorphic {n : ℕ} (G₀ G₁ : Graph n) : Prop := ∃ σ : Equiv.Perm (Fin n), permGraph G₀ σ = G₁

/-- Isomorphism is decidable (finitely many permutations). -/
instance {n : ℕ} (G₀ G₁ : Graph n) : Decidable (Isomorphic G₀ G₁) := by
  unfold Isomorphic
  infer_instance

/-- Every graph is isomorphic to itself (via the identity). -/
theorem Isomorphic.refl {n : ℕ} (G : Graph n) : Isomorphic G G := ⟨1, permGraph_one G⟩

/-- Isomorphism is symmetric (via the inverse permutation). -/
theorem Isomorphic.symm {n : ℕ} {G₀ G₁ : Graph n} (h : Isomorphic G₀ G₁) : Isomorphic G₁ G₀ := by
  obtain ⟨σ, hσ⟩ := h
  exact ⟨σ⁻¹, by rw [← hσ, permGraph_permGraph_inv]⟩

/-- Isomorphism is transitive (via the product of the permutations). -/
theorem Isomorphic.trans {n : ℕ} {G₀ G₁ G₂ : Graph n} (h₁ : Isomorphic G₀ G₁)
    (h₂ : Isomorphic G₁ G₂) : Isomorphic G₀ G₂ := by
  obtain ⟨σ, hσ⟩ := h₁
  obtain ⟨τ, hτ⟩ := h₂
  exact ⟨τ * σ, by rw [← permGraph_mul, hσ, hτ]⟩

/-- A graph is isomorphic to each of its relabellings. -/
theorem isomorphic_permGraph {n : ℕ} (G : Graph n) (σ : Equiv.Perm (Fin n)) :
    Isomorphic G (permGraph G σ) := ⟨σ, rfl⟩

/-- Relabelling by a fixed permutation is injective on graphs. -/
theorem permGraph_injective {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Function.Injective fun G : Graph n => permGraph G σ := by
  intro G G' h
  have := congrArg (fun K => permGraph K σ⁻¹) h
  simpa only [permGraph_permGraph_inv] using this

/-- A graph is isomorphic to at most one of two non-isomorphic graphs [PS10, proof of
Proposition 120.7, "`H` can be isomorphic to at most one of them"] (Lem-120.b): by symmetry
and transitivity of `Isomorphic`. -/
theorem not_isomorphic_both {n : ℕ} {G₀ G₁ H : Graph n} (h : ¬ Isomorphic G₀ G₁) :
    ¬ (Isomorphic G₀ H ∧ Isomorphic G₁ H) := fun ⟨h₀, h₁⟩ => h (h₀.trans h₁.symm)

/-- The honest prover's third message is accepted whatever the challenge [PS10, proof of
Proposition 120.7, corrected: `π(G₀) = H` and `(π σ⁻¹)(G₁) = H`] (Lem-120.a): if
`σ(G₀) = G₁` then `γ(G_b) = π(G₀)` for `γ = if b then π σ⁻¹ else π`. -/
theorem gi_honest_reply_eq {n : ℕ} {G₀ G₁ : Graph n} {σ : Equiv.Perm (Fin n)}
    (hσ : permGraph G₀ σ = G₁) (π : Equiv.Perm (Fin n)) (b : Bool) :
    permGraph (cond b G₁ G₀) (if b then π * σ⁻¹ else π) = permGraph G₀ π := by
  cases b
  · rfl
  · exact permGraph_mul_inv_of_eq hσ π

/-! ### Encoded instances and the languages (Def-118.a) -/

/-- The total decoding of a graph on a *given* vertex count `n` (entries read with default
`false`): the second component of `decGraph` at `n`, used to read the other party's graph
message on the vertex set of the common input. -/
def decGraphAt (n : ℕ) (w : List Bool) : Graph n := fun u v => w.getD (finProdFinEquiv (u, v)) false

/-- Decoding an encoded graph on its own vertex count gives the graph back. -/
@[simp] theorem decGraphAt_encGraph {n : ℕ} (G : Graph n) : decGraphAt n (encGraph G) = G :=
  funext fun u => funext fun v => encGraph_getD G u v

/-- The second component of `decGraph` is `decGraphAt` at the decoded vertex count. -/
theorem decGraph_snd (w : List Bool) : (decGraph w).2 = decGraphAt (decGraph w).1 w := rfl

/-- The encoded instance `x = ⟨encGraph G₀, encGraph G₁⟩` of the graph protocols
[PS10, Protocols 118.3 and 120.6, "`x = (G₀, G₁)`"]. -/
def encInstance {n : ℕ} (G₀ G₁ : Graph n) : List Bool := pairEncode (encGraph G₀) (encGraph G₁)

/-- An encoded instance on `n` vertices has `3n² + 2` bits. -/
theorem length_encInstance {n : ℕ} (G₀ G₁ : Graph n) : (encInstance G₀ G₁).length = 3 * (n * n) + 2 := by
  simp only [encInstance, length_pairEncode, length_encGraph]
  ring

/-- The vertex count read from a common input: `Nat.sqrt` of the length of the first
component (the `n` of `decGraph`). -/
def instanceVertexCount (x : List Bool) : ℕ := Nat.sqrt (pairFstD x).length

/-- The first graph of a common input, on the decoded vertex set. -/
def instanceG₀ (x : List Bool) : Graph (instanceVertexCount x) := decGraphAt _ (pairFstD x)

/-- The second graph of a common input, on the vertex set of the first. -/
def instanceG₁ (x : List Bool) : Graph (instanceVertexCount x) := decGraphAt _ (pairSndD x)

/-- A common input is well formed when it is a pair whose two components are adjacency
matrices of the same size `n²` (the "same number of vertices" of [PS10, §4.5]). -/
def wellFormedInstance (x : List Bool) : Bool :=
  decide ((pairDecode x).isSome ∧ (pairFstD x).length = instanceVertexCount x * instanceVertexCount x ∧
    (pairSndD x).length = instanceVertexCount x * instanceVertexCount x)

/-- The vertex count of an encoded instance from its length: `n = √((|x| - 2) / 3)`. -/
def instanceVertices (N : ℕ) : ℕ := Nat.sqrt ((N - 2) / 3)

/-- `instanceVertices` recovers `n` from the length of an encoded instance on `n` vertices. -/
theorem instanceVertices_length_encInstance {n : ℕ} (G₀ G₁ : Graph n) :
    instanceVertices (encInstance G₀ G₁).length = n := by
  rw [instanceVertices, length_encInstance, Nat.add_sub_cancel, Nat.mul_div_cancel_left _ (by norm_num),
    Nat.sqrt_eq]

/-- The vertex count decoded from an encoded instance is `n`. -/
theorem instanceVertexCount_encInstance {n : ℕ} (G₀ G₁ : Graph n) :
    instanceVertexCount (encInstance G₀ G₁) = n := by
  simp [instanceVertexCount, encInstance, Nat.sqrt_eq]

/-- The language of pairs of isomorphic graphs, `L_iso` [PS10, §4.5] (Def-118.a): the encoded
instances `⟨encGraph G₀, encGraph G₁⟩` with `σ(G₀) = G₁` for some `σ`. -/
def Liso : Language Bool :=
  {x | ∃ (n : ℕ) (G₀ G₁ : Graph n) (σ : Equiv.Perm (Fin n)),
    x = pairEncode (encGraph G₀) (encGraph G₁) ∧ permGraph G₀ σ = G₁}

/-- The language of pairs of non-isomorphic graphs with the same number of vertices,
`L_niso` [PS10, §4.5] (Def-118.a); malformed strings are not in `L_niso`. -/
def Lniso : Language Bool :=
  {x | ∃ (n : ℕ) (G₀ G₁ : Graph n), x = pairEncode (encGraph G₀) (encGraph G₁) ∧ ¬ Isomorphic G₀ G₁}

/-- The witness relation of `L_iso` [PS10, Theorem 122.3, "some canonical witness relation"]
(Def-118.a): the witness of `⟨encGraph G₀, encGraph G₁⟩` is the encoding of a permutation `σ`
with `σ(G₀) = G₁`. -/
def Riso (x y : List Bool) : Prop :=
  ∃ (n : ℕ) (G₀ G₁ : Graph n) (σ : Equiv.Perm (Fin n)),
    x = pairEncode (encGraph G₀) (encGraph G₁) ∧ y = encPerm σ ∧ permGraph G₀ σ = G₁

/-- Equal encodings come from the same vertex count and the same graph (as a `Sigma`). -/
private theorem sigma_eq_of_encGraph_eq {n n' : ℕ} {G : Graph n} {G' : Graph n'}
    (h : encGraph G = encGraph G') : (⟨n, G⟩ : Σ m, Graph m) = ⟨n', G'⟩ := by
  rw [← decGraph_encGraph G, ← decGraph_encGraph G', h]

/-- An encoded instance is in `L_iso` exactly when its graphs are isomorphic. -/
theorem encInstance_mem_Liso_iff {n : ℕ} (G₀ G₁ : Graph n) : encInstance G₀ G₁ ∈ Liso ↔ Isomorphic G₀ G₁ := by
  constructor
  · rintro ⟨n', G₀', G₁', σ, hx, hσ⟩
    have h0 : encGraph G₀ = encGraph G₀' := by simpa [encInstance] using congrArg pairFstD hx
    have h1 : encGraph G₁ = encGraph G₁' := by simpa [encInstance] using congrArg pairSndD hx
    obtain ⟨rfl, hG₀⟩ := Sigma.mk.inj_iff.1 (sigma_eq_of_encGraph_eq h0)
    obtain ⟨-, hG₁⟩ := Sigma.mk.inj_iff.1 (sigma_eq_of_encGraph_eq h1)
    rw [eq_of_heq hG₀, eq_of_heq hG₁]
    exact ⟨σ, hσ⟩
  · rintro ⟨σ, hσ⟩
    exact ⟨n, G₀, G₁, σ, rfl, hσ⟩

/-- An encoded instance is in `L_niso` exactly when its graphs are not isomorphic. -/
theorem encInstance_mem_Lniso_iff {n : ℕ} (G₀ G₁ : Graph n) :
    encInstance G₀ G₁ ∈ Lniso ↔ ¬ Isomorphic G₀ G₁ := by
  constructor
  · rintro ⟨n', G₀', G₁', hx, hni⟩
    have h0 : encGraph G₀ = encGraph G₀' := by simpa [encInstance] using congrArg pairFstD hx
    have h1 : encGraph G₁ = encGraph G₁' := by simpa [encInstance] using congrArg pairSndD hx
    obtain ⟨rfl, hG₀⟩ := Sigma.mk.inj_iff.1 (sigma_eq_of_encGraph_eq h0)
    obtain ⟨-, hG₁⟩ := Sigma.mk.inj_iff.1 (sigma_eq_of_encGraph_eq h1)
    rw [eq_of_heq hG₀, eq_of_heq hG₁]
    exact hni
  · intro h
    exact ⟨n, G₀, G₁, rfl, h⟩

/-- The languages `L_iso` and `L_niso` are disjoint. -/
theorem not_mem_Lniso_of_mem_Liso {x : List Bool} (h : x ∈ Liso) : x ∉ Lniso := by
  obtain ⟨n, G₀, G₁, σ, rfl, hσ⟩ := h
  rw [show pairEncode (encGraph G₀) (encGraph G₁) = encInstance G₀ G₁ from rfl,
    encInstance_mem_Lniso_iff]
  exact fun hni => hni ⟨σ, hσ⟩

/-- `Riso` is a witness relation for `L_iso` [PS10, Definition 191.11 for Theorem 122.3]
(Def-118.a).

**Proof sketch.** `mem_iff`: both sides unfold to the same existential (the witness of
`⟨encGraph G₀, encGraph G₁⟩` is `encPerm σ`). `bounded` with `p := var`: `|encPerm σ| = n² ≤
3n² + 2 = |x|` (`length_encPerm`, `length_encInstance`). `decidable`: the predicate
`T z := wellFormedInstance x && decide (encPerm (decPerm n y) = y) &&
decide (encGraph (permGraph G₀ (decPerm n y)) = pairSndD x)` with `x := pairFstD z`,
`y := pairSndD z`, `n := instanceVertexCount x`; it is polynomial-time by
`Complexity.polyTimeComputable_and`, `polyTimeComputable_pairEq`, `polyTimeComputable_lenEq`
and `polyTimeComputable_encPermGraph` composed with the pairing projections (the identity
`encPerm ∘ decPerm` test is a scan of the `n²` bits with the row/column uniqueness check of
`decPerm`'s sketch); on well-formed inputs `T ⟨x, y⟩ = true ↔ Riso x y` by
`decGraph_encGraph`, `decPerm_encPerm`, `encGraph_injective`, `encPerm_injective` and the
well-formedness characterization of `wellFormedInstance`. -/
theorem Riso_witnessRelation : WitnessRelation Liso Riso := by
  refine ⟨fun x => ?_, ⟨.var, ?_⟩, ?_⟩
  · constructor
    · rintro ⟨n, G₀, G₁, σ, hx, hσ⟩
      exact ⟨encPerm σ, n, G₀, G₁, σ, hx, rfl, hσ⟩
    · rintro ⟨y, n, G₀, G₁, σ, hx, -, hσ⟩
      exact ⟨n, G₀, G₁, σ, hx, hσ⟩
  · rintro x y ⟨n, G₀, G₁, σ, rfl, rfl, -⟩
    rw [PolyExpr.eval_var, length_encPerm, show pairEncode (encGraph G₀) (encGraph G₁) = encInstance G₀ G₁ from rfl,
      length_encInstance]
    omega
  · exact GI.Riso_decidable

/-! ### The permutation sampler of the honest parties (D10) -/

/-- The honest parties' permutation sampler: `permFromCoins` at the campaign parameters
(`permBits n = Nat.size n` bits per trial, so that `n ≤ 2^k ≤ 2n`, and `permTrials n = 2n²`
trials per position), read from the tape by `coinTable`; the identity on failure
[PS10, Protocols 118.3 and 120.6, "`σ ← S_n`", "`π ← S_n`"] (D10).

**Repair (run-3 audit P2-1):** parameters taken from `Asymptotic/Permutations.lean`
(the run-2 file used `Nat.size n` bits and `n²` trials locally). -/
noncomputable def samplePerm (n : ℕ) (r : List Bool) : Equiv.Perm (Fin n) :=
  (permFromCoins n (permBits n) (permTrials n) (coinTable n (permTrials n) (permBits n) r)).getD 1

/-- The number of tape bits consumed by `samplePerm n`: `n · permTrials n · permBits n`
(`= 2n³ · Nat.size n`).

**Repair (run-3 audit P2-1):** stated in terms of `permTrials`/`permBits`. -/
def permCoinLen (n : ℕ) : ℕ := n * permTrials n * permBits n

/-- The failure bound of the permutation sampler at the campaign parameters, `n · 2^{-n}`
(`uprob_permFromCoins_none_le_two_pow`).

**Repair (run-3 audit P2-1):** the run-2 bound `n (1 - 2^{-size n})^{n²}` had no closed form;
the closed form `n · 2^{-n}` is owned by `Asymptotic/Permutations.lean`. -/
noncomputable def permFailBound (n : ℕ) : ℝ := n * (2 : ℝ)⁻¹ ^ n

/-- The sampler consumes at most `(N + 1)²` tape bits whenever `2n² ≤ N` (every encoded
instance on `n` vertices has length `3n² + 2`, `length_encInstance`), so the coin polynomial
`normal 1 2` of the parties suffices: `n · 2n² · permBits n ≤ 2n⁴ ≤ N² ≤ (N + 1)²`.

**Repair (run-3 audit P2-1):** hypothesis strengthened from `n² ≤ N` to `2n² ≤ N` to absorb
the factor `2` of `permTrials` (satisfied by every encoded instance). -/
theorem permCoinLen_le {n N : ℕ} (h : 2 * (n * n) ≤ N) : permCoinLen n ≤ (N + 1) ^ 2 := by
  have hnn : n * n ≤ N := le_trans (Nat.le_mul_of_pos_left (n * n) two_pos) h
  calc permCoinLen n = n * (2 * n * n) * permBits n := rfl
    _ ≤ n * (2 * n * n) * n := Nat.mul_le_mul_left _ (permBits_le n)
    _ = (2 * (n * n)) * (n * n) := by ring
    _ ≤ N * N := Nat.mul_le_mul h hnn
    _ ≤ (N + 1) ^ 2 := by nlinarith

/-- The permutation sampler is within `permFailBound n = n · 2^{-n}` of a uniform permutation
(D10): `pushesUniform_coinTable` identifies the tape with a uniform coin table
(`StatClose.comp_pushesUniform`) and `statClose_permFromCoins_two_pow` is the closeness of
`permFromCoins` at the campaign parameters.

**Repair (run-3 audit P2-1):** proved from the shared lemmas of
`Asymptotic/Permutations.lean` (previously sorried with the argument restated). -/
theorem statClose_samplePerm (n : ℕ) :
    StatClose (fun r : Fin (permCoinLen n) → Bool => samplePerm n (List.ofFn r))
      (id : Equiv.Perm (Fin n) → Equiv.Perm (Fin n)) (permFailBound n) :=
  (statClose_permFromCoins_two_pow n 1).comp_pushesUniform
    (pushesUniform_coinTable n (permTrials n) (permBits n))

/-- The sampling error of the repeated protocols, `|x| · permFailBound n` with
`n = instanceVertices |x|`, is negligible in `|x|` (Inf-4.4): for `N ≥ 8`,
`√(N/4) ≤ instanceVertices N ≤ N`, so the term is at most `N² · 2^{-√(N/4)}`
(`negligible_two_pow_neg_sqrt_div`, `Negligible.mul_pow`, `Negligible.mono`).

**Repair (run-3 audit P2-1):** proved (the run-2 sketch went through `permFailBound_le_exp`,
removed). -/
theorem negligible_mul_permFailBound :
    Negligible fun N : ℕ => (N : ℝ) * permFailBound (instanceVertices N) := by
  refine ((negligible_two_pow_neg_sqrt_div (C := 4) (by norm_num)).mul_pow 2).mono
    ⟨8, fun N hN => ?_⟩
  have hv : instanceVertices N ≤ N := (Nat.sqrt_le_self _).trans (by omega)
  have hsq : Nat.sqrt (N / 4) ≤ instanceVertices N := Nat.sqrt_le_sqrt (by omega)
  have hpow : (2 : ℝ)⁻¹ ^ instanceVertices N ≤ (2 : ℝ)⁻¹ ^ Nat.sqrt (N / 4) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hsq
  have hv' : (instanceVertices N : ℝ) ≤ N := by exact_mod_cast hv
  unfold permFailBound
  rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
  calc (N : ℝ) * (instanceVertices N * (2 : ℝ)⁻¹ ^ instanceVertices N)
      ≤ N * (N * (2 : ℝ)⁻¹ ^ Nat.sqrt (N / 4)) := by gcongr
    _ = (N : ℝ) ^ 2 * (2 : ℝ)⁻¹ ^ Nat.sqrt (N / 4) := by ring

/-- The `i`-th block of `c` bits of a tape (the coins of iteration `i` of a repeated
protocol). -/
def coinSlice (c i : ℕ) (r : List Bool) : List Bool := (r.drop (i * c)).take c

/-! ### The graph non-isomorphism protocol [PS10, Protocol 118.3] (Prot-118.3) -/

/-- The honest (unbounded) prover of the graph non-isomorphism protocol [PS10, Protocol
118.3]: on the latest received graph `H` it answers `b' = 0` if `H ≅ G₀` and `b' = 1`
otherwise (so `b' = b` whenever `G₀ ≇ G₁`); no coins, no auxiliary input. The text's
"exponential time" is the search over all permutations in the `Decidable` instance. -/
def gniProver : Strategy where
  coins := .const 0
  next x _ _ hist :=
    [decide (¬ Isomorphic (instanceG₀ x) (decGraphAt (instanceVertexCount x) (hist.getLastD [])))]

/-- The verifier of one iteration of the graph non-isomorphism protocol [PS10, Protocol
118.3]: with random tape `b :: r`, it first sends `H = σ(G_b)` for `σ := samplePerm n r`, and
on the reply `b'` outputs `[decide (x well formed ∧ b' = b)]`.

**Deviation:** `σ` by rejection sampling (D10); well-formedness check on `x`. -/
noncomputable def gniVerifier : Strategy where
  coins := .add (.const 1) (.normal 1 2)
  next x _ r hist :=
    let b := r.headD false
    match hist with
    | [] => encGraph (permGraph (if b then instanceG₁ x else instanceG₀ x)
        (samplePerm (instanceVertexCount x) (r.drop 1)))
    | [b'] => [decide (wellFormedInstance x = true ∧ b'.headD false = b)]
    | _ => [false]

/-- One iteration of the graph non-isomorphism protocol [PS10, Protocol 118.3]
(Prot-118.3): verifier first, two messages (`H`, then `b'`); the verdict is the verifier's
third activation. -/
noncomputable def gniProtocol : Protocol where
  P := gniProver
  V := gniVerifier
  rounds := .const 2
  verifierFirst := true

/-- The verifier of the `|x|`-fold graph non-isomorphism protocol [PS10, Protocol 118.3,
"repeat the procedure `|G₁|` times"]: iteration `i` uses the coin block
`coinSlice (1 + (|x|+1)²) i r` (bit `b_i`, then the permutation coins); after `i < |x|`
replies it sends `H_i`, and on the complete history of `|x|` replies it accepts iff `x` is
well formed and every reply `b'_i` equals `b_i`.

**Deviation:** `|x|` iterations instead of `n`; rejection-sampled `σ_i` (D10). -/
noncomputable def gniVerifierRep : Strategy where
  coins := .mul .var (.add (.const 1) (.normal 1 2))
  next x _ r hist :=
    let c := 1 + (x.length + 1) ^ 2
    if hist.length < x.length then
      let ri := coinSlice c hist.length r
      encGraph (permGraph (if ri.headD false then instanceG₁ x else instanceG₀ x)
        (samplePerm (instanceVertexCount x) (ri.drop 1)))
    else
      [decide (wellFormedInstance x = true ∧
        ∀ j : Fin x.length, (hist.getD j []).headD false = (coinSlice c j r).headD false)]

/-- The `|x|`-fold graph non-isomorphism protocol [PS10, Protocol 118.3] (Prot-118.3):
verifier first, `2|x|` messages; the honest prover answers each `H_i` as in one iteration. -/
noncomputable def gniProtocolRep : Protocol where
  P := gniProver
  V := gniVerifierRep
  rounds := .mul (.const 2) .var
  verifierFirst := true

/-! ### The graph isomorphism protocol [PS10, Protocol 120.6] (Prot-120.6) -/

/-- The prover of the graph isomorphism protocol [PS10, Protocol 120.6]: with witness
`y = encPerm σ` it samples `π ← S_n` from its tape, sends `H = π(G₀)`, and on the challenge
`b` sends `γ = if b then π σ⁻¹ else π` (so that `γ(G_b) = H`, `gi_honest_reply_eq`).

**Deviation (D10):** `π` by `samplePerm` (rejection sampling, identity on failure). -/
noncomputable def giProver : Strategy where
  coins := .normal 1 2
  next x y r hist :=
    let n := (decGraph (pairFstD x)).1
    let G₀ : Graph n := (decGraph (pairFstD x)).2
    let σ := decPerm n y
    let π := samplePerm n r
    match hist with
    | [] => encGraph (permGraph G₀ π)
    | _ :: _ => encPerm (if (hist.headD []).headD false then π * σ⁻¹ else π)

/-- The verifier of the graph isomorphism protocol [PS10, Protocol 120.6]: with the single
coin `b` it answers the first message `H` with `[b]`, and on `[H, γ]` outputs
`[decide (x well formed ∧ γ(G_b) = H)]`.

**Deviation:** well-formedness check on `x` (needed for soundness on malformed inputs). -/
noncomputable def giVerifier : Strategy where
  coins := .const 1
  next x _ r hist :=
    let n := (decGraph (pairFstD x)).1
    let G₀ : Graph n := (decGraph (pairFstD x)).2
    let G₁ : Graph n := fun u v => (pairSndD x).getD (finProdFinEquiv (u, v)) false
    let b := r.headD false
    match hist with
    | [H, γ] => [decide (wellFormedInstance x = true ∧
        encGraph (permGraph (if b then G₁ else G₀) (decPerm n γ)) = H)]
    | [_] => [b]
    | _ => [false]

/-- One iteration of the graph isomorphism protocol [PS10, Protocol 120.6] (Prot-120.6):
three messages (`H`, `b`, `γ`), prover first; the verdict is the verifier's activation on
the complete history `[H, γ]`. -/
noncomputable def giProtocol : Protocol where
  P := giProver
  V := giVerifier
  rounds := .const 3
  verifierFirst := false

/-- The prover of the `|x|`-fold graph isomorphism protocol: iteration `i` (the prover has
received `2i` or `2i + 1` messages: the challenges and the verifier's empty fourth messages)
uses `π_i := samplePerm n (coinSlice (|x|+1)² i r)`; on an even history it sends `H_i`, on an
odd one `γ_i` for the latest challenge. -/
noncomputable def giProverRep : Strategy where
  coins := .mul .var (.normal 1 2)
  next x y r hist :=
    let n := instanceVertexCount x
    let σ := decPerm n y
    let π := samplePerm n (coinSlice ((x.length + 1) ^ 2) (hist.length / 2) r)
    if hist.length % 2 = 0 then encGraph (permGraph (instanceG₀ x) π)
    else encPerm (if (hist.getLastD []).headD false then π * σ⁻¹ else π)

/-- The verifier of the `|x|`-fold graph isomorphism protocol: it has received
`[H_0, γ_0, H_1, γ_1, …]`; on an odd history it sends the challenge `b_i = r_i`, on an even
incomplete history the empty message, and on the complete history it accepts iff `x` is
well formed and `γ_j(G_{b_j}) = H_j` for every `j < |x|`. -/
noncomputable def giVerifierRep : Strategy where
  coins := .var
  next x _ r hist :=
    let n := instanceVertexCount x
    if hist.length % 2 = 1 then [r.getD (hist.length / 2) false]
    else if hist.length < 2 * x.length then []
    else [decide (wellFormedInstance x = true ∧ ∀ j : Fin x.length,
      encGraph (permGraph (if r.getD j false then instanceG₁ x else instanceG₀ x)
        (decPerm n (hist.getD (2 * j + 1) []))) = hist.getD (2 * j) [])]

/-- The `|x|`-fold graph isomorphism protocol [PS10, Protocol 120.6, "repeat the procedure
`|G₁|` times"] (Prot-120.6): prover first, four moves per iteration (`H_i`, `b_i`, `γ_i`, and
a verifier message, empty except for the final verdict, D8 fixed alternation), `4|x|`
messages. -/
noncomputable def giProtocolRep : Protocol where
  P := giProverRep
  V := giVerifierRep
  rounds := .mul (.const 4) .var
  verifierFirst := false

/-! ### Concrete probability lemmas (ideal uniform permutations) -/

/-- Uniformly permuted isomorphic graphs are identically distributed, jointly with
independent auxiliary coins [PS10, proof of Lemma 123.5 and of Proposition 118.4,
"`H` is independent of the bit `b`"] (Lem-119.a): if `σ₀(G₀) = G₁` then
`σ(G₁) = (σ σ₀)(G₀)` and `σ ↦ σ σ₀` is a bijection of `S_n` (`Equiv.mulRight`). -/
theorem uprob_permGraph_eq_of_isomorphic {n : ℕ} {ρ : Type*} [Fintype ρ] {G₀ G₁ : Graph n}
    {σ₀ : Equiv.Perm (Fin n)} (hσ : permGraph G₀ σ₀ = G₁) (p : Graph n → ρ → Prop) :
    uprob (fun z : Equiv.Perm (Fin n) × ρ => p (permGraph G₁ z.1) z.2) =
      uprob (fun z : Equiv.Perm (Fin n) × ρ => p (permGraph G₀ z.1) z.2) := by
  rw [← uprob_comp_equiv (Equiv.prodCongr (Equiv.mulRight σ₀) (Equiv.refl ρ))
    (fun z : Equiv.Perm (Fin n) × ρ => p (permGraph G₀ z.1) z.2)]
  congr 1
  funext z
  simp [← hσ, permGraph_mul]

/-- The one-coordinate form of Lem-119.a: `σ(G₁)` and `σ(G₀)` have the same law. -/
theorem uprob_permGraph_eq_of_isomorphic' {n : ℕ} {G₀ G₁ : Graph n} {σ₀ : Equiv.Perm (Fin n)}
    (hσ : permGraph G₀ σ₀ = G₁) (p : Graph n → Prop) :
    uprob (fun σ : Equiv.Perm (Fin n) => p (permGraph G₁ σ)) =
      uprob (fun σ : Equiv.Perm (Fin n) => p (permGraph G₀ σ)) := by
  rw [← uprob_comp_equiv (Equiv.mulRight σ₀) (fun σ : Equiv.Perm (Fin n) => p (permGraph G₀ σ))]
  congr 1
  funext σ
  simp [← hσ, permGraph_mul]

/-- The strict prefix `b_0, …, b_{i-1}` of a bit tuple (the history an adaptive prover has
seen before challenge `i`). -/
def prefixLT {m : ℕ} {α : Type*} (b : Fin m → α) (i : Fin m) : Fin i → α :=
  fun j => b (Fin.castLE i.isLt.le j)

/-- The prefix `b_0, …, b_i` of a tuple (the history including the current challenge). -/
def prefixLE {m : ℕ} {α : Type*} (b : Fin m → α) (i : Fin m) : Fin (i + 1) → α :=
  fun j => b (Fin.castLE i.isLt j)

/-- The adaptive guess map `b ↦ (i ↦ b_i xor g_i(b_{<i}, w))` of Lem-119.c: triangular with
identity diagonal, hence a bijection of `Fin m → Bool` for every `w` (`adaptiveXorEquiv`); it
carries the event "`b_i = g_i(b_{<i}, w)` for every `i`" to "`b = 0`". -/
private def adaptiveXor {m : ℕ} {W : Type*} (g : (i : Fin m) → (Fin i → Bool) → W → Bool) (w : W)
    (b : Fin m → Bool) : Fin m → Bool :=
  fun i => xor (b i) (g i (prefixLT b i) w)

/-- `adaptiveXor g w` is injective.

**Proof sketch.** If the images agree then `b_i = b'_i` for every `i`, by induction on a bound
`k > i`: the prefixes `b_{<i}`, `b'_{<i}` agree by the induction hypothesis, so the guesses
`g_i(b_{<i}, w)`, `g_i(b'_{<i}, w)` agree and `xor` cancels (`Bool.xor_left_inj`). -/
private theorem adaptiveXor_injective {m : ℕ} {W : Type*}
    (g : (i : Fin m) → (Fin i → Bool) → W → Bool) (w : W) :
    Function.Injective (adaptiveXor g w) := by
  intro b b' h
  have key : ∀ k, ∀ i : Fin m, i.val < k → b i = b' i := by
    intro k
    induction k with
    | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
    | succ k ih =>
      intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
      · exact ih i hlt
      · have hpre : prefixLT b i = prefixLT b' i := by
          funext j
          have hj := j.isLt
          exact ih _ (by simp only [Fin.coe_castLE]; omega)
        have hi' := congrFun h i
        simp only [adaptiveXor, hpre] at hi'
        exact Bool.xor_left_inj.mp hi'
  funext i
  exact key (i.val + 1) i (Nat.lt_succ_self _)

/-- The bijection `adaptiveXor g w` of `Fin m → Bool` (an injection of a finite type into
itself, `Finite.injective_iff_bijective`). -/
private noncomputable def adaptiveXorEquiv {m : ℕ} {W : Type*}
    (g : (i : Fin m) → (Fin i → Bool) → W → Bool) (w : W) : (Fin m → Bool) ≃ (Fin m → Bool) :=
  Equiv.ofBijective (adaptiveXor g w)
    (Finite.injective_iff_bijective.mp (adaptiveXor_injective g w))

/-- The coin bijection `(b, w) ↦ (adaptiveXor g w b, w)` of `(Fin m → Bool) × W`. -/
private noncomputable def adaptiveEquiv {m : ℕ} {W : Type*}
    (g : (i : Fin m) → (Fin i → Bool) → W → Bool) : (Fin m → Bool) × W ≃ (Fin m → Bool) × W where
  toFun z := (adaptiveXorEquiv g z.2 z.1, z.2)
  invFun z := ((adaptiveXorEquiv g z.2).symm z.1, z.2)
  left_inv z := by simp
  right_inv z := by simp

/-- The adaptive guessing lemma [PS10, proof of Proposition 118.4, "each iteration is
independent of all prior iterations"] (Lem-119.c): for every finite nonempty `W` and every
family of guesses `g i` depending on the earlier bits and on `w`, the probability that a
uniform tuple `b` satisfies `b_i = g_i(b_{<i}, w)` for every `i` is exactly `2^{-m}`. The
engine of every `2^{-n}` soundness bound against adaptive provers.

**Deviation:** `W` nonempty (`uprob` on an empty type is `0`, so the equality fails for
`W = Empty`; every consumer uses a tape type `Fin k → Bool`).

**Repair (run-3 audit P10-1):** hypothesis `[Nonempty W]` added (the run-2 statement
specialised to `W := Empty`, `m := 0` reads `0 = 1`).

**Proof sketch.** For each `w` the map `b ↦ (i ↦ b_i xor g_i(b_{<i}, w))` is a bijection of
`Fin m → Bool` (`adaptiveXorEquiv`: triangular with identity diagonal, injective by strong
induction on `i`, hence bijective on a finite type) carrying the event to `{b = 0}`; so
`uprob_comp_equiv` with the coin bijection `adaptiveEquiv`, `uprob_fst` (here `W ≠ ∅` is
used) and `OneWay.uprob_eq_one_div_card` give `1 / 2^m` (`Fintype.card_fun`). Equivalently,
exactly one `b` per `w` satisfies all the constraints (`|W|` elements out of `2^m |W|`). -/
theorem uprob_adaptive_guess (m : ℕ) {W : Type*} [Fintype W] [Nonempty W]
    (g : (i : Fin m) → (Fin i → Bool) → W → Bool) :
    uprob (fun z : (Fin m → Bool) × W => ∀ i, z.1 i = g i (prefixLT z.1 i) z.2) =
      (2 : ℝ)⁻¹ ^ m := by
  have hev : ∀ z : (Fin m → Bool) × W,
      (∀ i, z.1 i = g i (prefixLT z.1 i) z.2) ↔ (adaptiveEquiv g z).1 = fun _ => false := by
    intro z
    simp only [adaptiveEquiv, adaptiveXorEquiv, Equiv.coe_fn_mk, Equiv.ofBijective_apply,
      adaptiveXor, funext_iff]
    exact forall_congr' fun i => by cases z.1 i <;> cases g i (prefixLT z.1 i) z.2 <;> simp
  rw [OneWay.uprob_congr hev,
    uprob_comp_equiv (adaptiveEquiv g) (fun z : (Fin m → Bool) × W => z.1 = fun _ => false),
    uprob_fst (β := W) (fun b : Fin m → Bool => b = fun _ => false),
    OneWay.uprob_eq_one_div_card (fun _ : Fin m => false), Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin]
  push_cast
  rw [one_div, inv_pow]

/-- Soundness of one iteration of the graph isomorphism protocol against an arbitrary
prover [PS10, proof of Proposition 120.7] (Lem-120.c): if `G₀ ≇ G₁` then, for a prover
whose first message is `H(r)` and whose reply to the challenge `b` is `γ(b, r)`, the verifier
accepts with probability at most `1/2` over the uniform `b` and the prover's coins `r`.

**Proof sketch.** `uprob_bool_prod`; for each `r` at most one `b` can be accepted
(`not_isomorphic_both`), so the `b = false` event is contained in the complement of the
`b = true` event (`uprob_mono`, `uprob_not`). -/
theorem uprob_gi_cheat_le_half {n : ℕ} {ρ : Type*} [Fintype ρ] {G₀ G₁ : Graph n}
    (h : ¬ Isomorphic G₀ G₁) (H : ρ → Graph n) (γ : Bool → ρ → Equiv.Perm (Fin n)) :
    uprob (fun z : Bool × ρ => permGraph (cond z.1 G₁ G₀) (γ z.1 z.2) = H z.2) ≤ 1 / 2 := by
  rw [uprob_bool_prod]
  have hsub : uprob (fun r : ρ => permGraph (cond false G₁ G₀) (γ false r) = H r) ≤
      uprob (fun r : ρ => ¬ permGraph (cond true G₁ G₀) (γ true r) = H r) := by
    refine uprob_mono fun r h0 h1 => ?_
    exact not_isomorphic_both h ⟨⟨γ false r, h0⟩, ⟨γ true r, h1⟩⟩
  rcases isEmpty_or_nonempty ρ with hρ | hρ
  · have h0 : uprob (fun r : ρ => permGraph (cond false G₁ G₀) (γ false r) = H r) = 0 := by
      rw [uprob_eq_card_filter, Fintype.card_eq_zero]
      simp
    have h1 : uprob (fun r : ρ => permGraph (cond true G₁ G₀) (γ true r) = H r) = 0 := by
      rw [uprob_eq_card_filter, Fintype.card_eq_zero]
      simp
    rw [h0, h1]
    norm_num
  · rw [uprob_not] at hsub
    linarith

/-- Soundness of the `m`-fold graph isomorphism protocol against adaptive provers
[PS10, Proposition 120.7, "repeated … to drive the error as low as desired"] (Lem-120.d):
if `G₀ ≇ G₁` then for a prover whose `i`-th graph `H_i` depends on the earlier challenges and
its coins and whose `i`-th reply `γ_i` also depends on the current challenge, the verifier
accepts all `m` iterations with probability at most `2^{-m}`.

**Proof sketch.** For empty `ρ` the probability is `0`. Otherwise acceptance in iteration `i` forces
`b_i = g_i(b_{<i}, r)` for the guess `g_i := decide (G₁ ≅ H_i)` (`not_isomorphic_both`), so
`uprob_mono` reduces to `uprob_adaptive_guess`.

**Repair (run-3 audit P10-1):** statement unchanged (an inequality, true for empty coins);
the proof splits on `ρ` empty since `uprob_adaptive_guess` now assumes `Nonempty`. -/
theorem uprob_gi_rep_cheat_le {n m : ℕ} {ρ : Type*} [Fintype ρ] {G₀ G₁ : Graph n}
    (h : ¬ Isomorphic G₀ G₁) (H : (i : Fin m) → (Fin i → Bool) → ρ → Graph n)
    (γ : (i : Fin m) → (Fin (i + 1) → Bool) → ρ → Equiv.Perm (Fin n)) :
    uprob (fun z : (Fin m → Bool) × ρ => ∀ i,
      permGraph (cond (z.1 i) G₁ G₀) (γ i (prefixLE z.1 i) z.2) = H i (prefixLT z.1 i) z.2) ≤
      (2 : ℝ)⁻¹ ^ m := by
  rcases isEmpty_or_nonempty ρ with hρ | hρ
  · have h0 : uprob (fun z : (Fin m → Bool) × ρ => ∀ i,
        permGraph (cond (z.1 i) G₁ G₀) (γ i (prefixLE z.1 i) z.2) = H i (prefixLT z.1 i) z.2) = 0 := by
      classical
      rw [uprob_eq_card_filter, Fintype.card_eq_zero]
      simp
    rw [h0]
    positivity
  · rw [← uprob_adaptive_guess m fun i p r => decide (Isomorphic G₁ (H i p r))]
    refine uprob_mono fun z hz i => ?_
    have hi := hz i
    cases hb : z.1 i
    · rw [hb] at hi
      have h0 : Isomorphic G₀ (H i (prefixLT z.1 i) z.2) := ⟨_, hi⟩
      exact (decide_eq_false fun h1 => not_isomorphic_both h ⟨h0, h1⟩).symm
    · rw [hb] at hi
      exact (decide_eq_true ⟨_, hi⟩).symm

/-- The change of variables of Lem-119.b, `σ_i ↦ if b_i then σ_i σ₀⁻¹ else σ_i`, with the
coins regrouped as `(b, (σ, w))` (inverse: multiply by `σ₀` instead). -/
private def gniShear {n m : ℕ} (ρ : Type*) (σ₀ : Equiv.Perm (Fin n)) :
    (Fin m → Bool) × ((Fin m → Equiv.Perm (Fin n)) × ρ) ≃
      ((Fin m → Bool) × (Fin m → Equiv.Perm (Fin n))) × ρ where
  toFun z := ((z.1, fun i => if z.1 i then z.2.1 i * σ₀⁻¹ else z.2.1 i), z.2.2)
  invFun z := (z.1.1, (fun i => if z.1.1 i then z.1.2 i * σ₀ else z.1.2 i, z.2))
  left_inv z := by
    rcases z with ⟨b, σ, w⟩
    simp only [Prod.mk.injEq, true_and, and_true]
    funext i
    cases hb : b i <;> simp
  right_inv z := by
    rcases z with ⟨⟨b, σ⟩, w⟩
    simp only [Prod.mk.injEq, true_and, and_true]
    funext i
    cases hb : b i <;> simp

/-- Under `gniShear` every graph `H_j = σ'_j(G₀)` is independent of `b`
(`permGraph_mul_inv_of_eq`), so the event "every reply equals the verifier's bit" is the
adaptive guessing event of `uprob_adaptive_guess` with guesses ignoring the earlier bits. -/
private theorem gniShear_event_iff {n m : ℕ} {ρ : Type*} {G₀ G₁ : Graph n}
    {σ₀ : Equiv.Perm (Fin n)} (hσ : permGraph G₀ σ₀ = G₁)
    (g : (i : Fin m) → (Fin (i + 1) → Graph n) → ρ → Bool) :
    ∀ z : (Fin m → Bool) × ((Fin m → Equiv.Perm (Fin n)) × ρ),
      (∀ i, g i (prefixLE (fun j => permGraph (cond ((gniShear (m := m) ρ σ₀ z).1.1 j) G₁ G₀)
          ((gniShear (m := m) ρ σ₀ z).1.2 j)) i) (gniShear (m := m) ρ σ₀ z).2 =
            (gniShear (m := m) ρ σ₀ z).1.1 i) ↔
      (∀ i, z.1 i = g i (prefixLE (fun j => permGraph G₀ (z.2.1 j)) i) z.2.2) := by
  rintro ⟨b, σ, w⟩
  have hH : (fun j => permGraph (cond ((gniShear (m := m) ρ σ₀ (b, σ, w)).1.1 j) G₁ G₀)
      ((gniShear (m := m) ρ σ₀ (b, σ, w)).1.2 j)) = fun j => permGraph G₀ (σ j) := by
    funext j
    show permGraph (cond (b j) G₁ G₀) (if b j then σ j * σ₀⁻¹ else σ j) = permGraph G₀ (σ j)
    cases b j
    · rfl
    · exact permGraph_mul_inv_of_eq hσ (σ j)
  rw [hH]
  exact forall_congr' fun i => eq_comm

/-- Soundness of the `m`-fold graph non-isomorphism protocol against adaptive provers
[PS10, proof of Proposition 118.4] (Lem-119.b): if `σ₀(G₀) = G₁`, then for every prover
whose `i`-th reply `g_i` depends on the graphs `H_0, …, H_i` received so far and on its
(nonempty type of) coins `w`, the probability (over the verifier's bits `b`, permutations `σ`
and `w`) that every reply equals the verifier's bit is exactly `2^{-m}`.

**Deviation:** `ρ` nonempty (`uprob` on an empty type is `0`; the consumer
`gni_interactiveProof` uses `ρ := P'.Coins |x|`, a tape type).

**Repair (run-3 audit P10-2):** hypothesis `[Nonempty ρ]` added (the run-2 statement
specialised to `ρ := Empty`, `n = m = 0`, `σ₀ = 1` reads `0 = 1`).

**Proof sketch.** Change variables `σ_i ↦ if b_i then σ_i σ₀⁻¹ else σ_i`, a bijection of the
coins fixing `b` and `w` (`gniShear`, with `uprob_comp_equiv`); then every `H_i = σ'_i(G₀)`
(`permGraph_mul_inv_of_eq`, `hσ`) is a function of `σ'` alone, the event is
`∀ i, b_i = g'_i(b_{<i}, (σ', w))` with `g'_i` ignoring `b_{<i}` (`gniShear_event_iff`), and
`uprob_adaptive_guess` with `W := (Fin m → S_n) × ρ` (nonempty since `ρ` is) gives
`2^{-m}`. -/
theorem uprob_gni_rep_cheat {n m : ℕ} {ρ : Type*} [Fintype ρ] [Nonempty ρ] {G₀ G₁ : Graph n}
    {σ₀ : Equiv.Perm (Fin n)} (hσ : permGraph G₀ σ₀ = G₁)
    (g : (i : Fin m) → (Fin (i + 1) → Graph n) → ρ → Bool) :
    uprob (fun z : ((Fin m → Bool) × (Fin m → Equiv.Perm (Fin n))) × ρ => ∀ i,
      g i (prefixLE (fun j => permGraph (cond (z.1.1 j) G₁ G₀) (z.1.2 j)) i) z.2 = z.1.1 i) =
      (2 : ℝ)⁻¹ ^ m := by
  have h1 := uprob_comp_equiv (gniShear (m := m) ρ σ₀)
    (fun z : ((Fin m → Bool) × (Fin m → Equiv.Perm (Fin n))) × ρ => ∀ i,
      g i (prefixLE (fun j => permGraph (cond (z.1.1 j) G₁ G₀) (z.1.2 j)) i) z.2 = z.1.1 i)
  have h2 := uprob_adaptive_guess m
    fun i (_ : Fin i → Bool) (w : (Fin m → Equiv.Perm (Fin n)) × ρ) =>
      g i (prefixLE (fun j => permGraph G₀ (w.1 j)) i) w.2
  rw [← h1, ← h2]
  exact OneWay.uprob_congr (gniShear_event_iff hσ g)

/-- Completeness of the graph non-isomorphism protocol [PS10, proof of Proposition 118.4,
"the prover will always succeed in finding `b'` such that `b' = b`"] (Lem-119.d): if
`G₀ ≇ G₁` then for every `b` and `σ` the honest reply `decide (¬ G₀ ≅ σ(G_b))` is `b`. -/
theorem gni_honest_reply {n : ℕ} {G₀ G₁ : Graph n} (h : ¬ Isomorphic G₀ G₁) (b : Bool)
    (σ : Equiv.Perm (Fin n)) :
    decide (¬ Isomorphic G₀ (permGraph (cond b G₁ G₀) σ)) = b := by
  cases b
  · exact decide_eq_false (not_not.2 (isomorphic_permGraph G₀ σ))
  · exact decide_eq_true fun h' => h (h'.trans (isomorphic_permGraph G₁ σ).symm)

/-! ### Efficiency of the honest parties (Inf-4.2) -/

/-- The honest prover of the graph isomorphism protocol is efficient (D8)
[PS10, Proposition 120.7, efficient prover] (Inf-4.2).

**Proof sketch.** `Strategy.Efficient` with `NUPPT.ofPolyTimeUniform` of the string function
of the layout `⟨⟨⟨1^n, ⟨⟨x, y⟩, msgs⟩⟩, []⟩, r⟩` (`Complexity.inArg`, `inCoins`,
`polyTimeComputable_inArg`): `encPerm π` by `polyTimeComputable_encSamplePerm` on
`⟨x, r⟩`; message 1 by `polyTimeComputable_encPermGraph` on `⟨pairFstD x, encPerm π⟩`;
message 3 by `polyTimeComputable_encPermMulInv` on `⟨encPerm π, y⟩` (branch on the challenge
bit `pairFstD msgs` with `polyTimeComputable_ite`; the `γ = π` branch outputs `encPerm π`),
the case split on `msgs = []` by `polyTimeComputable_lenEq`; the equation with `giProver.next`
by `NUPPT.runAtL_ofPolyTimeUniform`, `Strategy.pairFstD_encodeMsgs`, `decPerm_encPerm`. -/
theorem giProver_efficient : giProver.Efficient := GI.giProver_efficient

/-- The verifier of the graph isomorphism protocol is efficient (D8) [PS10, Definition 116.1
for Proposition 120.7] (Inf-4.2).

**Proof sketch.** As `giProver_efficient`: the challenge is the first coin
(`polyTimeComputable_pairFstD`-style projection of one bit), the verdict compares
`polyTimeComputable_encPermGraph` on `⟨G_b, γ⟩` with `H` by `polyTimeComputable_pairEq`,
conjoined (`polyTimeComputable_and`) with the well-formedness test (`polyTimeComputable_lenEq`
against the squared vertex count in unary and `computesFunInTime_pairValid`). -/
theorem giVerifier_efficient : giVerifier.Efficient := GI.giVerifier_efficient

/-- The verifier of one iteration of the graph non-isomorphism protocol is efficient (D8)
[PS10, Proposition 118.4] (Inf-4.2): as `giVerifier_efficient`, with the first message
`polyTimeComputable_encPermGraph` on `⟨G_b, encPerm σ⟩` for `σ` from
`polyTimeComputable_encSamplePerm` and the verdict a one-bit comparison. -/
theorem gniVerifier_efficient : gniVerifier.Efficient := GI.gniVerifier_efficient

/-- The verifier of the `|x|`-fold graph non-isomorphism protocol is efficient (D8)
(Inf-4.2): the coin block of iteration `hist.length` is cut by `pairTakePoly`/`pairDropPoly`
with the unary block length, the message as in `gniVerifier_efficient`, and the verdict is a
loop over the `|x|` replies (`polyTimeComputable_iterate` with an accumulated conjunction). -/
theorem gniVerifierRep_efficient : gniVerifierRep.Efficient := GI.gniVerifierRep_efficient

/-- The prover of the `|x|`-fold graph isomorphism protocol is efficient (D8) (Inf-4.2): as
`giProver_efficient` with the coin block of iteration `hist.length / 2` cut by
`pairTakePoly`/`pairDropPoly` and the parity test of the history length. -/
theorem giProverRep_efficient : giProverRep.Efficient := GI.giProverRep_efficient

/-- The verifier of the `|x|`-fold graph isomorphism protocol is efficient (D8) (Inf-4.2):
the challenge is coin `hist.length / 2`, and the verdict is a loop over the `|x|` pairs
`(H_j, γ_j)` of the history (`polyTimeComputable_iterate` over `polyTimeComputable_encPermGraph`
and `polyTimeComputable_pairEq`). -/
theorem giVerifierRep_efficient : giVerifierRep.Efficient := GI.giVerifierRep_efficient

/-! ### The propositions [PS10, Propositions 118.4 and 120.7] -/

/-- One iteration of the graph non-isomorphism protocol is an interactive proof for
`L_niso` with soundness error `1/2 + permFailBound n` [PS10, Proposition 118.4, one
iteration] (Prop-118.4).

**Deviation (D10):** the verifier's `σ` is rejection-sampled; on a sampling failure `H = G_b`
may reveal `b`, whence the additional term `permFailBound n` with `n = instanceVertices |x|`.

**Proof sketch.** Completeness: for `x = encInstance G₀ G₁ ∈ L_niso` the verifier's message
decodes to `σ(G_b)` (`decGraphAt_encGraph`, `instanceVertexCount_encInstance`), the honest
reply is `b` by `gni_honest_reply`, and `wellFormedInstance x = true`, so the verdict is
`[true]` on every coin pair (`HardcoreBit.uprob_eq_one_of_forall`). Soundness: for
`x ∉ L_niso`, either `wellFormedInstance x = false` (verdict `[false]` always) or
`x = encInstance G₀ G₁` with `σ₀(G₀) = G₁` (`encInstance_mem_Lniso_iff`); fix the prover's
coins (`Protocol.exists_proverCoins_le`), split the verifier's tape into `b` and the sampler
bits (`uprob_prod` through the bijection `Fin (1 + c) → Bool ≃ Bool × (Fin c → Bool)`), and
bound `Pr[b' = b] ≤ Pr[b' = b ∧ sampler succeeds] + Pr[fail]`; on success the permutation is
uniform (`statClose_samplePerm`, `StatClose.abs_uprob_sub_le_prod`) and
`uprob_permGraph_eq_of_isomorphic` makes `H` independent of `b`, so the first term is
`≤ 1/2` (`uprob_bool_prod`); the second is `≤ permFailBound n` with
`n = instanceVertices |x|` (`instanceVertices_length_encInstance`). Efficiency:
`gniVerifier_efficient`. -/
theorem gni_interactiveProofErr :
    InteractiveProofErr gniProtocol Lniso (fun N => 1 / 2 + permFailBound (instanceVertices N)) :=
  GI.gni_interactiveProofErr gniVerifier_efficient

/-- The `|x|`-fold graph non-isomorphism protocol is an interactive proof for `L_niso`
[PS10, Proposition 118.4] (Prop-118.4).

**Deviation:** `|x|` iterations (soundness `2^{-|x|}`) plus the sampling term
`|x| · permFailBound n` (D10).

**Proof sketch.** Completeness as in `gni_interactiveProofErr`, iteration by iteration
(the history has exactly `|x|` replies, `exec_length`). Soundness with
`ε N := 2⁻¹ ^ N + N · permFailBound (instanceVertices N) + 2⁻¹ ^ N` (strict clause): fix the
prover's coins, condition on all `|x|` samplers succeeding (union bound `uprob_exists_le`
over the iterations, `statClose_samplePerm` per block via `pushesUniform_coinTable`), and
apply `uprob_gni_rep_cheat` (with `ρ := P'.Coins |x|`, a nonempty tape type) with `g_i := `
the prover's reply after the graphs `H_0, …, H_i` (the prover's `i`-th activation reads
exactly the graphs received so far, `exec_succ`).
Negligibility: `negligible_two_pow_neg`, `negligible_mul_permFailBound`, `Negligible.add`.
Efficiency: `gniVerifierRep_efficient`. -/
theorem gni_interactiveProof : InteractiveProof gniProtocolRep Lniso :=
  GI.gni_interactiveProof gniVerifierRep_efficient

/-- The honest provers of the graph-isomorphism protocols send `n²`-bit words with
`n² ≤ |x|`, so at most `|x|` bits per message, on every instance (ruling G3-3 of gate 03;
`GI.giProver_length_le`). -/
theorem giProtocol_proverBounded (R : List Bool → List Bool → Prop) :
    giProtocol.ProverBounded R .var :=
  (Protocol.proverBounded_iff _ _ _).2 fun x y r hist _ => GI.giProver_length_le x y r hist

/-- The `|x|`-fold form of `giProtocol_proverBounded` (`GI.giProverRep_length_le`). -/
theorem giProtocolRep_proverBounded (R : List Bool → List Bool → Prop) :
    giProtocolRep.ProverBounded R .var :=
  (Protocol.proverBounded_iff _ _ _).2 fun x y r hist _ => GI.giProverRep_length_le x y r hist

/-- The honest graph non-isomorphism prover sends one bit per message (ruling G3-3 of gate 03;
`GI.gniProver_length_le`), in one iteration and in the `|x|`-fold protocol. -/
theorem gniProtocol_proverBounded (R : List Bool → List Bool → Prop) :
    gniProtocol.ProverBounded R (.const 1) ∧ gniProtocolRep.ProverBounded R (.const 1) :=
  ⟨(Protocol.proverBounded_iff _ _ _).2 fun x y r hist _ => GI.gniProver_length_le x y r hist,
    (Protocol.proverBounded_iff _ _ _).2 fun x y r hist _ => GI.gniProver_length_le x y r hist⟩

/-- One iteration of the graph isomorphism protocol is an interactive proof for `L_iso`
with soundness error `1/2` and efficient prover with respect to `R_iso`
[PS10, Proposition 120.7, corrected: for `L_iso`, not `L_niso`] (Prop-120.7).

**Proof sketch.** Completeness for every witness: for `x = encInstance G₀ G₁`,
`y = encPerm σ` with `σ(G₀) = G₁`, the transcript is `[H, γ]` with `H = encGraph (π(G₀))` and
`γ = encPerm (if b then π σ⁻¹ else π)` (`exec_succ`, `decPerm_encPerm`), and the verdict is
`[true]` by `gi_honest_reply_eq`, `decGraph_encGraph`, `wellFormedInstance` on every coin
pair (`HardcoreBit.uprob_eq_one_of_forall`) — for every value of `π`, so the sampler's
failures are harmless. Completeness of `InteractiveProofErr` is the witness
`encPerm σ` of `Liso`. Soundness: for `x ∉ L_iso` either `x` is malformed (verdict `[false]`)
or `x = encInstance G₀ G₁` with `G₀ ≇ G₁` (`encInstance_mem_Liso_iff`); the verifier's tape is
one bit (`Fin 1 → Bool ≃ Bool`), so after `Protocol.exists_proverCoins_le`,
`uprob_gi_cheat_le_half` with `H r :=` the prover's first message decoded and
`γ b r :=` its reply to `[b]` decoded gives `Pr[accept] ≤ 1/2`, i.e. `1/2 ≤ Pr[out = [false]]`
(`uprob_not`). Efficiency: `giProver_efficient`, `giVerifier_efficient`. -/
theorem gi_efficientProverProofErr : EfficientProverProofErr giProtocol Liso Riso (fun _ => 1 / 2) :=
  GI.gi_efficientProverProofErr giProver_efficient giVerifier_efficient

/-- The `|x|`-fold graph isomorphism protocol is an interactive proof for `L_iso` with
efficient prover with respect to `R_iso` [PS10, Proposition 120.7, repeated] (Prop-120.7,
Lem-120.d).

**Deviation:** `|x|` iterations of four moves each (D8 fixed alternation).

**Proof sketch.** Completeness as in `gi_efficientProverProofErr` for each of the `|x|`
iterations (the verifier's history is `[H_0, γ_0, …]`, `exec_succ`, parity bookkeeping of
`giProverRep`/`giVerifierRep`). Soundness with `ε N := 2⁻¹ ^ N + 2⁻¹ ^ N` (strict clause): fix
the prover's coins; the verifier's tape is the challenge tuple `Fin |x| → Bool` (`List.ofFn`),
and `uprob_gi_rep_cheat_le` with `H_i` the decoded `i`-th graph message and `γ_i` the decoded
`i`-th reply (functions of the earlier challenges through `exec`) gives
`Pr[accept] ≤ 2^{-|x|}`; `negligible_two_pow_neg`. Efficiency: `giProverRep_efficient`,
`giVerifierRep_efficient`. -/
theorem gi_rep_efficientProverProof : EfficientProverProof giProtocolRep Liso Riso :=
  GI.gi_rep_efficientProverProof giProverRep_efficient giVerifierRep_efficient

/-- The `|x|`-fold graph isomorphism protocol is an interactive proof for `L_iso`
[PS10, Proposition 120.7]. -/
theorem gi_rep_interactiveProof : InteractiveProof giProtocolRep Liso :=
  gi_rep_efficientProverProof.toInteractiveProof

end TCSlib.Cryptography

## ===== TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/Soundness.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.Proofs

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The graph protocols: completeness and soundness of the single iterations

[PS10, Proposition 118.4] (one iteration of the graph non-isomorphism protocol, soundness
error `1/2 + n·2^{-n}`) and [PS10, Proposition 120.7] (one iteration of the graph isomorphism
protocol, soundness error `1/2`, efficient prover), proved for the shadow protocols of
`GraphIsomorphism/Proofs.lean`; the main file `ZeroKnowledge/GraphIsomorphism.lean` closes
`gni_interactiveProofErr` and `gi_efficientProverProofErr` by `exact GI.…` (the efficiency
clauses are passed in as hypotheses, so that this file does not depend on the machine
constructions of `GraphIsomorphism/Efficiency.lean`).

**Completeness** is exact (`uprob = 1`): on an encoded instance the honest verdict is `[true]`
for every pair of random tapes (`gni_honest_reply`, `gi_honest_reply_eq`), whatever the
rejection-sampled permutation. **Soundness** of the graph non-isomorphism iteration is the
statistical argument of the text: against isomorphic graphs the relabelled graph `σ(G_b)` is
independent of `b` (`uprob_guess_eq_half`), and the honest verifier's `σ` is within
`permFailBound n` of uniform on its tape (`statClose_samplePerm_long`), whence
`Pr[accept] ≤ 1/2 + permFailBound n` after fixing the prover's coins
(`Protocol.exists_proverCoins_le`). Soundness of the graph isomorphism iteration is
`uprob_gi_cheat_le_half` (Lem-120.c): a prover can answer at most one of the two challenges.
Malformed common inputs are rejected outright by the well-formedness test.

## Main definitions

* `TCSlib.Cryptography.GI.vTapeSplit`, `GI.giBitEquiv`, `GI.giCoinEquiv` — the verifiers' random
  tapes as (challenge bit, sampler coins) and the joint coins as (bit, prover's coins).

## Main results

* `TCSlib.Cryptography.GI.gni_complete`, `GI.gni_accept_le` — completeness and the acceptance
  bound of one iteration of the graph non-isomorphism protocol.
* `TCSlib.Cryptography.GI.gi_complete`, `GI.gi_accept_le` — the same for the graph isomorphism
  protocol.
* `TCSlib.Cryptography.GI.gni_interactiveProofErr` — [PS10, Proposition 118.4], one iteration.
* `TCSlib.Cryptography.GI.gi_efficientProverProofErr` — [PS10, Proposition 120.7], one iteration.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§4.5 Interactive proofs, pp. 117–120.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026 (the concrete probability layer).
-/

namespace TCSlib.Cryptography.GI

open Complexity Turing Finset

/-! ### Verdicts of the graph non-isomorphism iteration on encoded instances -/

/-- The honest prover's reply to the graph `encGraph K` on an encoded instance:
`decide (¬ G₀ ≅ K)`. -/
theorem gniProver_next_encGraph {n : ℕ} (G₀ G₁ K : Graph n) (y r : List Bool) :
    gniProver.next (encInstance G₀ G₁) y r [encGraph K] = [decide (¬ Isomorphic G₀ K)] := by
  show [decide (¬ Isomorphic
    (decGraphAt (instanceVertexCount (encInstance G₀ G₁)) (pairFstD (encInstance G₀ G₁)))
    (decGraphAt (instanceVertexCount (encInstance G₀ G₁)) (encGraph K)))] = _
  rw [show pairFstD (encInstance G₀ G₁) = encGraph G₀ from pairFstD_pairEncode _ _]
  generalize hm : instanceVertexCount (encInstance G₀ G₁) = m
  rw [instanceVertexCount_encInstance] at hm
  subst hm
  rw [decGraphAt_encGraph, decGraphAt_encGraph]

/-- The verdict of the graph non-isomorphism iteration against a prover `P'` on an encoded
instance: the reply's first bit equals the verifier's first coin `b`, the graph sent being
`σ(G_b)` for `σ` sampled from the remaining coins. -/
theorem gni_outV_eq (P' : Strategy) {n : ℕ} (G₀ G₁ : Graph n) (y z : List Bool)
    (r : gniProtocol.ExecCoins P' (encInstance G₀ G₁)) :
    gniProtocol.outV P' (encInstance G₀ G₁) y z r =
      [decide ((P'.next (encInstance G₀ G₁) y (List.ofFn r.1)
        [encGraph (permGraph (cond ((List.ofFn r.2).headD false) G₁ G₀)
          (samplePerm n ((List.ofFn r.2).drop 1)))]).headD false = (List.ofFn r.2).headD false)] := by
  rw [gniProtocol_outV, gniVerifier_next_nil, gniVerifier_next_one, wellFormedInstance_encInstance]
  simp only [true_and]

/-- **Completeness of the graph non-isomorphism iteration** [PS10, Proposition 118.4]
(Lem-119.d): on a non-isomorphic encoded instance the honest prover's reply is the verifier's
bit for every pair of tapes (`gni_honest_reply`), so the verdict is `[true]` with probability
one. -/
theorem gni_complete {n : ℕ} {G₀ G₁ : Graph n} (h : ¬ Isomorphic G₀ G₁) (y z : List Bool) :
    uprob (fun r : gniProtocol.ExecCoins gniProver (encInstance G₀ G₁) =>
      gniProtocol.outV gniProver (encInstance G₀ G₁) y z r = [true]) = 1 := by
  refine HardcoreBit.uprob_eq_one_of_forall fun r => ?_
  rw [gni_outV_eq, gniProver_next_encGraph]
  simp only [List.headD_cons, gni_honest_reply h, decide_true]

/-- The verifier's tape of the graph non-isomorphism iteration as its first bit and the
sampler's `(N + 1)²` coins (`tapeSplit`, at the verifier's coin polynomial
`1 + (N + 1)²`). -/
def vTapeSplit (N : ℕ) : Bool × (Fin (1 * (N + 1) ^ 2) → Bool) ≃ gniProtocol.V.Coins N :=
  tapeSplit (1 * (N + 1) ^ 2)

/-- The list of a split verifier tape. -/
theorem ofFn_vTapeSplit (N : ℕ) (b : Bool) (t : Fin (1 * (N + 1) ^ 2) → Bool) :
    List.ofFn (vTapeSplit N (b, t)) = b :: List.ofFn t :=
  ofFn_tapeSplit _ b t

/-- The sampler's coins fit in the verifier's tape: `permCoinLen n ≤ (|x| + 1)²` for an
encoded instance `x` on `n` vertices (`permCoinLen_le`, `length_encInstance`). -/
theorem permCoinLen_le_tape {n : ℕ} (G₀ G₁ : Graph n) :
    permCoinLen n ≤ 1 * ((encInstance G₀ G₁).length + 1) ^ 2 := by
  rw [one_mul]
  exact permCoinLen_le (by rw [length_encInstance]; omega)

/-- **The acceptance bound of the graph non-isomorphism iteration against isomorphic graphs**
[PS10, proof of Proposition 118.4]: for `σ₀(G₀) = G₁` and every prover `P'`, the verifier
accepts with probability at most `1/2 + permFailBound n`.

**Proof sketch.** Fix the prover's coins (`Protocol.exists_proverCoins_le`); the prover's reply
is then a function `g` of the graph it receives. Split the verifier's tape into the bit `b`
and the sampler's coins (`vTapeSplit`); the event is `g (σ(G_b)) = b` with `σ` the sampled
permutation. Replacing `σ` by a uniform permutation changes the probability by at most
`permFailBound n` (`statClose_samplePerm_long`, `StatClose.abs_uprob_sub_le_prod` with `b` as
the auxiliary coin), and for a uniform `σ` the probability is exactly `1/2`
(`uprob_guess_eq_half`). -/
theorem gni_accept_le {n : ℕ} {G₀ G₁ : Graph n} {σ₀ : Equiv.Perm (Fin n)}
    (hσ : permGraph G₀ σ₀ = G₁) (P' : Strategy) (y z : List Bool) :
    uprob (fun r : gniProtocol.ExecCoins P' (encInstance G₀ G₁) =>
      gniProtocol.outV P' (encInstance G₀ G₁) y z r = [true]) ≤ 1 / 2 + permFailBound n := by
  obtain ⟨r₁, hr₁⟩ := gniProtocol.exists_proverCoins_le P' (encInstance G₀ G₁) y z (fun o => o = [true])
  refine hr₁.trans ?_
  set g : Graph n → Bool := fun K =>
    (P'.next (encInstance G₀ G₁) y (List.ofFn r₁) [encGraph K]).headD false with hg
  have hev : ∀ r₂ : gniProtocol.V.Coins (encInstance G₀ G₁).length,
      gniProtocol.outV P' (encInstance G₀ G₁) y z (r₁, r₂) = [true] ↔
        g (permGraph (cond ((List.ofFn r₂).headD false) G₁ G₀)
          (samplePerm n ((List.ofFn r₂).drop 1))) = (List.ofFn r₂).headD false := by
    intro r₂
    rw [gni_outV_eq]
    simp [hg]
  rw [OneWay.uprob_congr hev, ← uprob_comp_equiv (vTapeSplit (encInstance G₀ G₁).length)]
  have hev2 : ∀ p : Bool × (Fin (1 * ((encInstance G₀ G₁).length + 1) ^ 2) → Bool),
      g (permGraph (cond ((List.ofFn (vTapeSplit _ p)).headD false) G₁ G₀)
          (samplePerm n ((List.ofFn (vTapeSplit _ p)).drop 1))) =
            (List.ofFn (vTapeSplit _ p)).headD false ↔
        g (permGraph (cond p.1 G₁ G₀) (samplePerm n (List.ofFn p.2))) = p.1 := by
    rintro ⟨b, t⟩
    rw [ofFn_vTapeSplit, List.headD_cons, List.drop_one, List.tail_cons]
  rw [OneWay.uprob_congr hev2,
    ← uprob_comp_equiv (Equiv.prodComm (Fin (1 * ((encInstance G₀ G₁).length + 1) ^ 2) → Bool) Bool)]
  have hclose := (statClose_samplePerm_long (permCoinLen_le_tape G₀ G₁)).abs_uprob_sub_le_prod
    fun σ b => g (permGraph (cond b G₁ G₀) σ) = b
  have hideal : uprob (fun q : Equiv.Perm (Fin n) × Bool =>
      g (permGraph (cond q.2 G₁ G₀) (id q.1)) = q.2) = 1 / 2 := by
    rw [← uprob_comp_equiv (Equiv.prodComm Bool (Equiv.Perm (Fin n)))]
    exact uprob_guess_eq_half hσ g
  rw [hideal] at hclose
  have := (abs_le.1 hclose).2
  simp only [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
  linarith

/-- **One iteration of the graph non-isomorphism protocol is an interactive proof for
`L_niso` with soundness error `1/2 + permFailBound n`** [PS10, Proposition 118.4, one
iteration] (Prop-118.4), given the verifier's efficiency.

**Proof sketch.** Completeness: `gni_complete` with the empty auxiliary input. Soundness: a
malformed `x` is rejected outright (`gniVerifier_next_one`); a well-formed `x ∉ L_niso` is
`encInstance G₀ G₁` with `G₀ ≅ G₁` (`eq_encInstance_of_wellFormed`,
`encInstance_mem_Lniso_iff`), and `gni_accept_le` bounds the acceptance probability, the
verdict being a single bit (`gni_outV_eq`, `uprob_not`). -/
theorem gni_interactiveProofErr (hV : gniVerifier.Efficient) :
    InteractiveProofErr gniProtocol Lniso (fun N => 1 / 2 + permFailBound (instanceVertices N)) where
  efficientV := hV
  complete := by
    refine ⟨.const 1, ?_⟩
    rintro x ⟨n, G₀, G₁, rfl, hni⟩
    exact ⟨[], gniProver_length_le _ [], fun z => gni_complete hni [] z⟩
  sound := by
    intro x hx P' z
    by_cases hwf : wellFormedInstance x = true
    · obtain ⟨n, G₀, G₁, rfl⟩ := exists_eq_encInstance_of_wellFormed hwf
      obtain ⟨σ₀, hσ⟩ : Isomorphic G₀ G₁ := by
        by_contra hni
        exact hx ((encInstance_mem_Lniso_iff G₀ G₁).2 hni)
      have hacc := gni_accept_le hσ P' [] z
      have hnot : ∀ r : gniProtocol.ExecCoins P' (encInstance G₀ G₁),
          gniProtocol.outV P' (encInstance G₀ G₁) [] z r = [false] ↔
            ¬ gniProtocol.outV P' (encInstance G₀ G₁) [] z r = [true] := by
        intro r
        rw [gni_outV_eq]
        simp
      rw [OneWay.uprob_congr hnot, uprob_not, instanceVertices_length_encInstance]
      linarith
    · have hall : ∀ r : gniProtocol.ExecCoins P' x, gniProtocol.outV P' x [] z r = [false] := by
        intro r
        rw [gniProtocol_outV, gniVerifier_next_one]
        simp [hwf]
      rw [HardcoreBit.uprob_eq_one_of_forall hall]
      linarith [permFailBound_nonneg (instanceVertices x.length)]

/-! ### Verdicts of the graph isomorphism iteration on encoded instances -/

/-- The verdict of the graph isomorphism iteration against a prover `P'` on an encoded
instance: `γ(G_b) = H` for the prover's two messages `H` (on the empty history) and `γ` (on
the challenge `[b]`). -/
theorem gi_outV_eq (P' : Strategy) {n : ℕ} (G₀ G₁ : Graph n) (y z : List Bool)
    (r : giProtocol.ExecCoins P' (encInstance G₀ G₁)) :
    giProtocol.outV P' (encInstance G₀ G₁) y z r =
      [decide (encGraph (permGraph (cond ((List.ofFn r.2).headD false) G₁ G₀)
        (decPerm n (P'.next (encInstance G₀ G₁) y (List.ofFn r.1) [[(List.ofFn r.2).headD false]]))) =
        P'.next (encInstance G₀ G₁) y (List.ofFn r.1) [])] := by
  rw [giProtocol_outV, giVerifier_next_one, giVerifier_next_two]

/-- **Completeness of the graph isomorphism iteration for every witness**
[PS10, Proposition 120.7] (Lem-120.a): with witness `encPerm σ`, `σ(G₀) = G₁`, the honest
transcript is `H = π(G₀)`, `γ = if b then π σ⁻¹ else π`, and `γ(G_b) = H` for every pair of
tapes (`gi_honest_reply_eq`), whatever the sampled `π`. -/
theorem gi_complete {n : ℕ} {G₀ G₁ : Graph n} {σ : Equiv.Perm (Fin n)}
    (hσ : permGraph G₀ σ = G₁) (z : List Bool) :
    uprob (fun r : giProtocol.ExecCoins giProver (encInstance G₀ G₁) =>
      giProtocol.outV giProver (encInstance G₀ G₁) (encPerm σ) z r = [true]) = 1 := by
  refine HardcoreBit.uprob_eq_one_of_forall fun r => ?_
  rw [gi_outV_eq, giProver_next_nil, giProver_next_cons, decPerm_encPerm, List.headD_cons,
    gi_honest_reply_eq hσ]
  simp

/-- The single coin of the graph isomorphism verifier as a tape (`Equiv.funUnique`). -/
def giBitEquiv (N : ℕ) : Bool ≃ giProtocol.V.Coins N := (Equiv.funUnique (Fin 1) Bool).symm

/-- The list of the verifier's single-coin tape. -/
theorem ofFn_giBitEquiv (N : ℕ) (b : Bool) : List.ofFn (giBitEquiv N b) = [b] := by
  show List.ofFn (fun _ : Fin 1 => b) = [b]
  rw [List.ofFn_succ, List.ofFn_zero]

/-- The joint coins of the graph isomorphism iteration as (challenge bit, prover's coins). -/
def giCoinEquiv (P' : Strategy) (x : List Bool) :
    Bool × P'.Coins x.length ≃ giProtocol.ExecCoins P' x :=
  (Equiv.prodComm _ _).trans (Equiv.prodCongr (Equiv.refl _) (giBitEquiv x.length))

/-- The prover's coins of a transported pair. -/
theorem giCoinEquiv_fst (P' : Strategy) (x : List Bool) (b : Bool) (r₁ : P'.Coins x.length) :
    (giCoinEquiv P' x (b, r₁)).1 = r₁ := rfl

/-- The verifier's tape of a transported pair. -/
theorem giCoinEquiv_snd (P' : Strategy) (x : List Bool) (b : Bool) (r₁ : P'.Coins x.length) :
    (giCoinEquiv P' x (b, r₁)).2 = giBitEquiv x.length b := rfl

/-- **The acceptance bound of the graph isomorphism iteration against non-isomorphic graphs**
[PS10, proof of Proposition 120.7] (Lem-120.c): for `G₀ ≇ G₁` and every prover `P'`, the
verifier accepts with probability at most `1/2`.

**Proof sketch.** Acceptance means `γ(G_b) = H` for the decoded first message `H` and decoded
reply `γ` (`gi_outV_eq`, `decGraphAt_encGraph`); the event is contained in the event of
`uprob_gi_cheat_le_half` with `H r₁ := decGraphAt n (first message)` and
`γ b r₁ := decPerm n (reply to [b])`, after reading the joint coins as (bit, prover's coins)
(`giCoinEquiv`). -/
theorem gi_accept_le {n : ℕ} {G₀ G₁ : Graph n} (h : ¬ Isomorphic G₀ G₁) (P' : Strategy)
    (y z : List Bool) :
    uprob (fun r : giProtocol.ExecCoins P' (encInstance G₀ G₁) =>
      giProtocol.outV P' (encInstance G₀ G₁) y z r = [true]) ≤ 1 / 2 := by
  set H : P'.Coins (encInstance G₀ G₁).length → Graph n := fun r₁ =>
    decGraphAt n (P'.next (encInstance G₀ G₁) y (List.ofFn r₁) []) with hH
  set γ : Bool → P'.Coins (encInstance G₀ G₁).length → Equiv.Perm (Fin n) := fun b r₁ =>
    decPerm n (P'.next (encInstance G₀ G₁) y (List.ofFn r₁) [[b]]) with hγ
  have hmono : ∀ r : giProtocol.ExecCoins P' (encInstance G₀ G₁),
      giProtocol.outV P' (encInstance G₀ G₁) y z r = [true] →
        permGraph (cond ((List.ofFn r.2).headD false) G₁ G₀) (γ ((List.ofFn r.2).headD false) r.1) =
          H r.1 := by
    intro r hr
    rw [gi_outV_eq] at hr
    simp only [List.cons.injEq, decide_eq_true_eq, and_true] at hr
    show permGraph _ (decPerm n (P'.next (encInstance G₀ G₁) y (List.ofFn r.1)
      [[(List.ofFn r.2).headD false]])) = decGraphAt n (P'.next (encInstance G₀ G₁) y (List.ofFn r.1) [])
    rw [← hr, decGraphAt_encGraph]
  refine (uprob_mono hmono).trans ?_
  rw [← uprob_comp_equiv (giCoinEquiv P' (encInstance G₀ G₁))]
  refine le_of_eq_of_le (OneWay.uprob_congr ?_) (uprob_gi_cheat_le_half h H γ)
  rintro ⟨b, r₁⟩
  rw [giCoinEquiv_fst, giCoinEquiv_snd, ofFn_giBitEquiv, List.headD_cons]

/-- **One iteration of the graph isomorphism protocol is an interactive proof for `L_iso`
with soundness error `1/2` and efficient prover with respect to `R_iso`**
[PS10, Proposition 120.7, corrected: for `L_iso`] (Prop-120.7), given the parties'
efficiency.

**Proof sketch.** Completeness for every witness: `gi_complete`; completeness of
`InteractiveProofErr`: the witness `encPerm σ`. Soundness: a malformed `x` is rejected
outright (`giVerifier_next_two'`); a well-formed `x ∉ L_iso` is `encInstance G₀ G₁` with
`G₀ ≇ G₁` (`eq_encInstance_of_wellFormed`, `encInstance_mem_Liso_iff`) and `gi_accept_le`
bounds the acceptance probability, the verdict being a single bit (`gi_outV_eq`,
`uprob_not`). -/
theorem gi_efficientProverProofErr (hP : giProver.Efficient) (hV : giVerifier.Efficient) :
    EfficientProverProofErr giProtocol Liso Riso (fun _ => 1 / 2) where
  efficientV := hV
  complete := by
    refine ⟨.var, ?_⟩
    rintro x ⟨n, G₀, G₁, σ, rfl, hσ⟩
    exact ⟨encPerm σ, giProver_length_le _ _, fun z => gi_complete hσ z⟩
  sound := by
    intro x hx P' z
    by_cases hwf : wellFormedInstance x = true
    · obtain ⟨n, G₀, G₁, rfl⟩ := exists_eq_encInstance_of_wellFormed hwf
      have hni : ¬ Isomorphic G₀ G₁ := fun hiso => hx ((encInstance_mem_Liso_iff G₀ G₁).2 hiso)
      have hacc := gi_accept_le hni P' [] z
      have hnot : ∀ r : giProtocol.ExecCoins P' (encInstance G₀ G₁),
          giProtocol.outV P' (encInstance G₀ G₁) [] z r = [false] ↔
            ¬ giProtocol.outV P' (encInstance G₀ G₁) [] z r = [true] := by
        intro r
        rw [gi_outV_eq]
        simp
      rw [OneWay.uprob_congr hnot, uprob_not]
      linarith
    · have hall : ∀ r : giProtocol.ExecCoins P' x, giProtocol.outV P' x [] z r = [false] := by
        intro r
        rw [giProtocol_outV, giVerifier_next_one, giVerifier_next_two']
        simp [hwf]
      rw [HardcoreBit.uprob_eq_one_of_forall hall]
      norm_num
  efficientP := hP
  boundedP := ⟨.var, (Protocol.proverBounded_iff _ _ _).2 fun x y r hist _ =>
    giProver_length_le x y r hist⟩
  completeWitness := by
    rintro x y ⟨n, G₀, G₁, σ, rfl, rfl, hσ⟩ z
    exact gi_complete hσ z

end TCSlib.Cryptography.GI

## ===== TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism/SoundnessRepGI.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.SoundnessRep

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The `|x|`-fold graph isomorphism protocol: completeness and soundness

[PS10, Proposition 120.7] for the `|x|`-fold protocol `giProtocolRep` (Prot-120.6, repeated,
four moves per iteration), proved for the shadow protocol of `GraphIsomorphism/Proofs.lean`;
the main file closes `gi_rep_efficientProverProof` by
`exact GI.gi_rep_efficientProverProof giProverRep_efficient giVerifierRep_efficient`.

The execution is described iteration by iteration (`repViews`, `exec_repViews`): in iteration
`i` the prover sends `H_i`, the verifier the challenge `[b_i]` with `b_i` its `i`-th coin
(`giVerifierRep_next_odd`), the prover `γ_i`, and the verifier the empty message (or, in the
last iteration, its verdict). The verifier's view is the interleaving `Vs` of the `H_i` and
`γ_i`; the prover's view, before the last iteration, is determined by the challenges
(`PsOf`). **Completeness** is exact (`gi_honest_reply_eq`). **Soundness**: the accepting event
implies the typed event of `uprob_gi_rep_cheat_le` (Lem-120.d) with `H_i` a function of the
earlier challenges and `γ_i` of the challenges up to `i`, whence `Pr[accept] ≤ 2^{-|x|}`.

## Main definitions

* `TCSlib.Cryptography.GI.repViews` — the two parties' views after `i` iterations.
* `TCSlib.Cryptography.GI.Vs`, `GI.PsOf`, `GI.PsOfFin` — the verifier's and the prover's views
  as functions of the messages and challenges.

## Main results

* `TCSlib.Cryptography.GI.exec_repViews` — the four-move iterations of a prover-first protocol.
* `TCSlib.Cryptography.GI.giRep_complete`, `GI.giRep_accept_le` — completeness and the
  acceptance bound of the `|x|`-fold protocol.
* `TCSlib.Cryptography.GI.gi_rep_efficientProverProofErr`, `GI.gi_rep_efficientProverProof` —
  [PS10, Proposition 120.7] for the repeated protocol.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§4.5 Interactive proofs, pp. 117–120.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026 (the concrete probability layer).
-/

namespace TCSlib.Cryptography.GI

open Complexity Turing Finset

/-! ### Four-move iterations of a prover-first protocol -/

/-- The views (prover's received messages, verifier's received messages) after `i` iterations
of four moves: the prover sends `H`, the verifier `b`, the prover `γ`, the verifier `e`. -/
def repViews (P' V : Strategy) (x y z rP rV : List Bool) : ℕ → List (List Bool) × List (List Bool)
  | 0 => ([], [])
  | i + 1 =>
    let v := repViews P' V x y z rP rV i
    let H := P'.next x y rP v.1
    let b := V.next x z rV (v.2 ++ [H])
    let γ := P'.next x y rP (v.1 ++ [b])
    let e := V.next x z rV (v.2 ++ [H, γ])
    (v.1 ++ [b, e], v.2 ++ [H, γ])

/-- After `4i` moves of a prover-first execution the views are `repViews i`
(`moverIsV false k = decide (k % 2 = 1)`: the prover moves at `4i` and `4i + 2`, the verifier
at `4i + 1` and `4i + 3`). -/
theorem exec_repViews (P' V : Strategy) (x y z rP rV : List Bool) :
    ∀ i, exec P' V false x y z rP rV (4 * i) = repViews P' V x y z rP rV i
  | 0 => rfl
  | i + 1 => by
    have h0 : moverIsV false (4 * i) = false := by
      simp only [moverIsV_false, decide_eq_false_iff_not]
      omega
    have h1 : moverIsV false (4 * i + 1) = true := by
      simp only [moverIsV_false, decide_eq_true_eq]
      omega
    have h2 : moverIsV false (4 * i + 1 + 1) = false := by
      simp only [moverIsV_false, decide_eq_false_iff_not]
      omega
    have h3 : moverIsV false (4 * i + 1 + 1 + 1) = true := by
      simp only [moverIsV_false, decide_eq_true_eq]
      omega
    rw [show 4 * (i + 1) = 4 * i + 1 + 1 + 1 + 1 by ring, exec_succ, exec_succ, exec_succ, exec_succ,
      exec_repViews P' V x y z rP rV i]
    simp only [h0, h1, h2, h3, Bool.false_eq_true, if_false, if_true, repViews, List.append_assoc,
      List.singleton_append]

/-- The verifier's view after `i` iterations as the interleaving of the graphs and replies. -/
def Vs (H γ : ℕ → List Bool) : ℕ → List (List Bool)
  | 0 => []
  | i + 1 => Vs H γ i ++ [H i, γ i]

/-- The verifier's view after `i` iterations has `2i` messages. -/
theorem length_Vs (H γ : ℕ → List Bool) : ∀ i, (Vs H γ i).length = 2 * i
  | 0 => rfl
  | i + 1 => by
    rw [Vs, List.length_append, length_Vs H γ i]
    rfl

/-- Message `2j` of the verifier's view is the graph `H_j`. -/
theorem getD_Vs_even (H γ : ℕ → List Bool) : ∀ i j, j < i → (Vs H γ i).getD (2 * j) [] = H j
  | 0, _, hj => absurd hj (Nat.not_lt_zero _)
  | i + 1, j, hj => by
    rw [Vs, List.getD_eq_getElem?_getD]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | rfl
    · rw [List.getElem?_append_left (by rw [length_Vs]; omega), ← List.getD_eq_getElem?_getD]
      exact getD_Vs_even H γ i j h
    · rw [List.getElem?_append_right (by rw [length_Vs]), length_Vs, Nat.sub_self]
      rfl

/-- Message `2j + 1` of the verifier's view is the reply `γ_j`. -/
theorem getD_Vs_odd (H γ : ℕ → List Bool) : ∀ i j, j < i → (Vs H γ i).getD (2 * j + 1) [] = γ j
  | 0, _, hj => absurd hj (Nat.not_lt_zero _)
  | i + 1, j, hj => by
    rw [Vs, List.getD_eq_getElem?_getD]
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with h | rfl
    · rw [List.getElem?_append_left (by rw [length_Vs]; omega), ← List.getD_eq_getElem?_getD]
      exact getD_Vs_odd H γ i j h
    · rw [List.getElem?_append_right (by rw [length_Vs]; omega), length_Vs,
        show 2 * j + 1 - 2 * j = 1 by omega]
      rfl

/-- The prover's view after `i` iterations when the verifier's even messages are empty: the
challenges `[b_0], [], …, [b_{i-1}], []`. -/
def PsOf (b : ℕ → Bool) : ℕ → List (List Bool)
  | 0 => []
  | i + 1 => PsOf b i ++ [[b i], []]

/-- The prover's view depends only on the first `i` challenges. -/
theorem PsOf_congr {f g : ℕ → Bool} : ∀ i, (∀ k < i, f k = g k) → PsOf f i = PsOf g i
  | 0, _ => rfl
  | i + 1, h => by
    rw [PsOf, PsOf, PsOf_congr i (fun k hk => h k (by omega)), h i (by omega)]

/-- The prover's view as a function of a tuple of challenges. -/
def PsOfFin {i : ℕ} (bs : Fin i → Bool) : List (List Bool) :=
  PsOf (fun k => if h : k < i then bs ⟨k, h⟩ else false) i

/-- The prover's view from the strict prefix of a challenge tuple is its view from the tape. -/
theorem PsOfFin_prefixLT {m : ℕ} (b : Fin m → Bool) (i : Fin m) :
    PsOfFin (prefixLT b i) = PsOf (fun k => (List.ofFn b).getD k false) i := by
  unfold PsOfFin
  refine PsOf_congr i fun k hk => ?_
  rw [dif_pos hk, getD_ofFn_lt' b (by omega)]
  rfl

/-- The prover's view from the initial segment of a challenge prefix is its view from the tape. -/
theorem PsOfFin_init_prefixLE {m : ℕ} (b : Fin m → Bool) (i : Fin m) :
    PsOfFin (Fin.init (prefixLE b i)) = PsOf (fun k => (List.ofFn b).getD k false) i := by
  unfold PsOfFin
  refine PsOf_congr i fun k hk => ?_
  rw [dif_pos hk, getD_ofFn_lt' b (by omega)]
  rfl

/-- The last challenge of a prefix `b_0, …, b_i` is `b_i`. -/
theorem prefixLE_last {m : ℕ} (b : Fin m → Bool) (i : Fin m) : prefixLE b i (Fin.last i) = b i := rfl

/-! ### The `|x|`-fold graph isomorphism verifier and prover, unfolded -/

/-- The `|x|`-fold verifier's challenge on an odd history: its coin `|hist| / 2`. -/
theorem giVerifierRep_next_odd (x z r : List Bool) (hist : List (List Bool)) (h : hist.length % 2 = 1) :
    giVerifierRep.next x z r hist = [r.getD (hist.length / 2) false] := by
  show (if hist.length % 2 = 1 then _ else _) = _
  rw [if_pos h]

/-- The `|x|`-fold verifier's empty message on an even history of fewer than `2|x|` messages. -/
theorem giVerifierRep_next_mid (x z r : List Bool) (hist : List (List Bool)) (h1 : hist.length % 2 ≠ 1)
    (h2 : hist.length < 2 * x.length) : giVerifierRep.next x z r hist = [] := by
  show (if hist.length % 2 = 1 then _ else if hist.length < 2 * x.length then _ else _) = _
  rw [if_neg h1, if_pos h2]

/-- The `|x|`-fold verifier's verdict on an even complete history. -/
theorem giVerifierRep_next_end (x z r : List Bool) (hist : List (List Bool)) (h1 : hist.length % 2 ≠ 1)
    (h2 : ¬ hist.length < 2 * x.length) :
    giVerifierRep.next x z r hist =
      [decide (wellFormedInstance x = true ∧ ∀ j : Fin x.length,
        encGraph (permGraph (if r.getD j false then instanceG₁ x else instanceG₀ x)
          (decPerm (instanceVertexCount x) (hist.getD (2 * j + 1) []))) = hist.getD (2 * j) [])] := by
  show (if hist.length % 2 = 1 then _ else if hist.length < 2 * x.length then _ else _) = _
  rw [if_neg h1, if_neg h2]

/-- The `|x|`-fold verifier's verdict on an encoded instance: `γ_j(G_{b_j}) = H_j` for every
iteration, with the graphs read on `n` vertices. -/
theorem giVerifierRep_next_end_enc {n : ℕ} (G₀ G₁ : Graph n) (z r : List Bool) (hist : List (List Bool))
    (h1 : hist.length % 2 ≠ 1) (h2 : ¬ hist.length < 2 * (encInstance G₀ G₁).length) :
    giVerifierRep.next (encInstance G₀ G₁) z r hist =
      [decide (∀ j : Fin (encInstance G₀ G₁).length,
        encGraph (permGraph (cond (r.getD j false) G₁ G₀) (decPerm n (hist.getD (2 * j + 1) []))) =
          hist.getD (2 * j) [])] := by
  rw [giVerifierRep_next_end _ _ _ _ h1 h2, wellFormedInstance_encInstance]
  simp only [true_and]
  show [decide (∀ j : Fin (encInstance G₀ G₁).length, encGraph (permGraph
    (if r.getD j false then decGraphAt (instanceVertexCount (encInstance G₀ G₁)) (pairSndD (encInstance G₀ G₁))
      else decGraphAt (instanceVertexCount (encInstance G₀ G₁)) (pairFstD (encInstance G₀ G₁)))
    (decPerm (instanceVertexCount (encInstance G₀ G₁)) (hist.getD (2 * j + 1) []))) = hist.getD (2 * j) [])] = _
  rw [show pairSndD (encInstance G₀ G₁) = encGraph G₁ from pairSndD_pairEncode _ _,
    show pairFstD (encInstance G₀ G₁) = encGraph G₀ from pairFstD_pairEncode _ _]
  generalize hm : instanceVertexCount (encInstance G₀ G₁) = m
  rw [instanceVertexCount_encInstance] at hm
  subst hm
  simp only [decGraphAt_encGraph, Bool.cond_eq_ite]

/-- The `|x|`-fold prover's graph on an even history of an encoded instance: `π(G₀)` for the
permutation sampled from coin block `|hist| / 2`. -/
theorem giProverRep_next_even {n : ℕ} (G₀ G₁ : Graph n) (y r : List Bool) (hist : List (List Bool))
    (h : hist.length % 2 = 0) :
    giProverRep.next (encInstance G₀ G₁) y r hist =
      encGraph (permGraph G₀ (samplePerm n
        (coinSlice (((encInstance G₀ G₁).length + 1) ^ 2) (hist.length / 2) r))) := by
  show (if hist.length % 2 = 0 then encGraph (permGraph
    (decGraphAt (instanceVertexCount (encInstance G₀ G₁)) (pairFstD (encInstance G₀ G₁)))
    (samplePerm (instanceVertexCount (encInstance G₀ G₁))
      (coinSlice (((encInstance G₀ G₁).length + 1) ^ 2) (hist.length / 2) r))) else _) = _
  rw [if_pos h, show pairFstD (encInstance G₀ G₁) = encGraph G₀ from pairFstD_pairEncode _ _]
  generalize hm : instanceVertexCount (encInstance G₀ G₁) = m
  rw [instanceVertexCount_encInstance] at hm
  subst hm
  rw [decGraphAt_encGraph]

/-- The `|x|`-fold prover's reply on an odd history of an encoded instance with witness
`encPerm σ`: `π σ⁻¹` or `π` according to the last challenge received. -/
theorem giProverRep_next_odd {n : ℕ} (G₀ G₁ : Graph n) (σ : Equiv.Perm (Fin n)) (r : List Bool)
    (hist : List (List Bool)) (h : hist.length % 2 ≠ 0) :
    giProverRep.next (encInstance G₀ G₁) (encPerm σ) r hist =
      encPerm (if (hist.getLastD []).headD false then
        samplePerm n (coinSlice (((encInstance G₀ G₁).length + 1) ^ 2) (hist.length / 2) r) * σ⁻¹
      else samplePerm n (coinSlice (((encInstance G₀ G₁).length + 1) ^ 2) (hist.length / 2) r)) := by
  show (if hist.length % 2 = 0 then _ else encPerm (if (hist.getLastD []).headD false then
    samplePerm (instanceVertexCount (encInstance G₀ G₁))
        (coinSlice (((encInstance G₀ G₁).length + 1) ^ 2) (hist.length / 2) r) *
      (decPerm (instanceVertexCount (encInstance G₀ G₁)) (encPerm σ))⁻¹
    else samplePerm (instanceVertexCount (encInstance G₀ G₁))
      (coinSlice (((encInstance G₀ G₁).length + 1) ^ 2) (hist.length / 2) r))) = _
  rw [if_neg h]
  generalize hm : instanceVertexCount (encInstance G₀ G₁) = m
  rw [instanceVertexCount_encInstance] at hm
  subst hm
  rw [decPerm_encPerm]

/-- The verdict of the `|x|`-fold protocol against `P'`: the verifier's next-message function on
the `4|x|`-move execution. -/
theorem giProtocolRep_outV (P' : Strategy) (x y z : List Bool) (r : giProtocolRep.ExecCoins P' x) :
    giProtocolRep.outV P' x y z r =
      giVerifierRep.next x z (List.ofFn r.2)
        (exec P' giVerifierRep false x y z (List.ofFn r.1) (List.ofFn r.2) (4 * x.length)).2 := rfl

/-! ### The views against the honest verifier -/

/-- Against the `|x|`-fold verifier, the verifier's view after `i` iterations interleaves the
prover's graphs (its next message on its view) and replies (its next message on its view
extended by the challenge `[b_j]`, `b_j` the verifier's `j`-th coin), and the prover's view
has `2i` messages.

**Proof sketch.** Induction on `i`: the challenge is the verifier's coin `i`
(`giVerifierRep_next_odd` on the odd history of `2i + 1` messages). -/
theorem repViews_snd (P' : Strategy) (x y z rP rV : List Bool) :
    ∀ i, (repViews P' giVerifierRep x y z rP rV i).2 =
      Vs (fun j => P'.next x y rP (repViews P' giVerifierRep x y z rP rV j).1)
        (fun j => P'.next x y rP ((repViews P' giVerifierRep x y z rP rV j).1 ++ [[rV.getD j false]])) i ∧
      (repViews P' giVerifierRep x y z rP rV i).1.length = 2 * i
  | 0 => ⟨rfl, rfl⟩
  | i + 1 => by
    obtain ⟨h2, h1⟩ := repViews_snd P' x y z rP rV i
    have hb : giVerifierRep.next x z rV
        (Vs (fun j => P'.next x y rP (repViews P' giVerifierRep x y z rP rV j).1)
          (fun j => P'.next x y rP ((repViews P' giVerifierRep x y z rP rV j).1 ++ [[rV.getD j false]])) i ++
          [P'.next x y rP (repViews P' giVerifierRep x y z rP rV i).1]) = [rV.getD i false] := by
      rw [giVerifierRep_next_odd _ _ _ _ (by rw [List.length_append, length_Vs, List.length_singleton]; omega),
        List.length_append, length_Vs, List.length_singleton, show (2 * i + 1) / 2 = i by omega]
    simp only [repViews]
    rw [h2, hb]
    refine ⟨rfl, ?_⟩
    simp only [List.length_append, h1, List.length_cons, List.length_nil]
    omega

/-- Against the `|x|`-fold verifier, before the last iteration the prover's view is determined
by the challenges.

**Proof sketch.** Induction on `i < |x|`: the challenge of iteration `i` is the verifier's coin
`i` (`giVerifierRep_next_odd`) and its fourth message is empty, the history having `2i + 2 < 2|x|`
messages (`giVerifierRep_next_mid`). -/
theorem repViews_fst (P' : Strategy) (x y z rP rV : List Bool) :
    ∀ i, i < x.length → (repViews P' giVerifierRep x y z rP rV i).1 = PsOf (fun k => rV.getD k false) i
  | 0, _ => rfl
  | i + 1, hi => by
    have ih := repViews_fst P' x y z rP rV i (by omega)
    obtain ⟨h2, h1⟩ := repViews_snd P' x y z rP rV i
    have hb : giVerifierRep.next x z rV
        (Vs (fun j => P'.next x y rP (repViews P' giVerifierRep x y z rP rV j).1)
          (fun j => P'.next x y rP ((repViews P' giVerifierRep x y z rP rV j).1 ++ [[rV.getD j false]])) i ++
          [P'.next x y rP (repViews P' giVerifierRep x y z rP rV i).1]) = [rV.getD i false] := by
      rw [giVerifierRep_next_odd _ _ _ _ (by rw [List.length_append, length_Vs, List.length_singleton]; omega),
        List.length_append, length_Vs, List.length_singleton, show (2 * i + 1) / 2 = i by omega]
    have he : giVerifierRep.next x z rV
        (Vs (fun j => P'.next x y rP (repViews P' giVerifierRep x y z rP rV j).1)
          (fun j => P'.next x y rP ((repViews P' giVerifierRep x y z rP rV j).1 ++ [[rV.getD j false]])) i ++
          [P'.next x y rP (repViews P' giVerifierRep x y z rP rV i).1,
            P'.next x y rP ((repViews P' giVerifierRep x y z rP rV i).1 ++ [[rV.getD i false]])]) = [] := by
      apply giVerifierRep_next_mid
      · rw [List.length_append, length_Vs, List.length_cons, List.length_singleton]
        omega
      · rw [List.length_append, length_Vs, List.length_cons, List.length_singleton]
        omega
    simp only [repViews]
    rw [h2, hb, he, ih]
    rfl

/-! ### Completeness -/

/-- The honest prover's graph of iteration `j`: `π_j(G₀)` for `π_j` sampled from coin block `j`
(block length `c`) of its tape. -/
noncomputable def honestH {n : ℕ} (G₀ : Graph n) (c : ℕ) (rP : List Bool) (j : ℕ) : List Bool :=
  encGraph (permGraph G₀ (samplePerm n (coinSlice c j rP)))

/-- The honest prover's reply of iteration `j`: `π_j σ⁻¹` or `π_j` according to the verifier's
coin `j`. -/
noncomputable def honestγ {n : ℕ} (σ : Equiv.Perm (Fin n)) (c : ℕ) (rP rV : List Bool) (j : ℕ) : List Bool :=
  encPerm (if rV.getD j false then samplePerm n (coinSlice c j rP) * σ⁻¹ else samplePerm n (coinSlice c j rP))

/-- The honest views on an encoded instance with witness `encPerm σ`: the verifier's view
interleaves `honestH` and `honestγ`.

**Proof sketch.** Induction on `i` with `giProverRep_next_even` (the prover's view has `2i`
messages), `giVerifierRep_next_odd` (the verifier's has `2i + 1`) and `giProverRep_next_odd`
(the last message the prover received is the challenge `[b_i]`, `List.getLastD_concat`). -/
theorem honest_views {n : ℕ} (G₀ G₁ : Graph n) (σ : Equiv.Perm (Fin n)) (z rP rV : List Bool) :
    ∀ i, (repViews giProverRep giVerifierRep (encInstance G₀ G₁) (encPerm σ) z rP rV i).2 =
        Vs (honestH G₀ (((encInstance G₀ G₁).length + 1) ^ 2) rP)
          (honestγ σ (((encInstance G₀ G₁).length + 1) ^ 2) rP rV) i ∧
      (repViews giProverRep giVerifierRep (encInstance G₀ G₁) (encPerm σ) z rP rV i).1.length = 2 * i
  | 0 => ⟨rfl, rfl⟩
  | i + 1 => by
    obtain ⟨h2, h1⟩ := honest_views G₀ G₁ σ z rP rV i
    have hH : giProverRep.next (encInstance G₀ G₁) (encPerm σ) rP
        (repViews giProverRep giVerifierRep (encInstance G₀ G₁) (encPerm σ) z rP rV i).1 =
        encGraph (permGraph G₀ (samplePerm n (coinSlice (((encInstance G₀ G₁).length + 1) ^ 2) i rP))) := by
      rw [giProverRep_next_even _ _ _ _ _ (by rw [h1]; omega), h1, show 2 * i / 2 = i by omega]
    have hb : giVerifierRep.next (encInstance G₀ G₁) z rV
        (Vs (honestH G₀ (((encInstance G₀ G₁).length + 1) ^ 2) rP)
          (honestγ σ (((encInstance G₀ G₁).length + 1) ^ 2) rP rV) i ++
          [encGraph (permGraph G₀ (samplePerm n (coinSlice (((encInstance G₀ G₁).length + 1) ^ 2) i rP)))]) =
        [rV.getD i false] := by
      rw [giVerifierRep_next_odd _ _ _ _ (by rw [List.length_append, length_Vs, List.length_singleton]; omega),
        List.length_append, length_Vs, List.length_singleton, show (2 * i + 1) / 2 = i by omega]
    have hγ : giProverRep.next (encInstance G₀ G₁) (encPerm σ) rP
        ((repViews giProverRep giVerifierRep (encInstance G₀ G₁) (encPerm σ) z rP rV i).1 ++ [[rV.getD i false]]) =
        honestγ σ (((encInstance G₀ G₁).length + 1) ^ 2) rP rV i := by
      rw [giProverRep_next_odd _ _ _ _ _ (by rw [List.length_append, h1, List.length_singleton]; omega),
        List.getLastD_concat, List.headD_cons, List.length_append, h1, List.length_singleton,
        show (2 * i + 1) / 2 = i by omega]
      rfl
    simp only [repViews]
    rw [h2, hH, hb, hγ]
    refine ⟨rfl, ?_⟩
    simp only [List.length_append, h1, List.length_cons, List.length_nil]
    omega

/-- **Completeness of the `|x|`-fold graph isomorphism protocol for every witness**
[PS10, Proposition 120.7]: every iteration's check `γ_j(G_{b_j}) = H_j` holds on the honest
views (`honest_views`, `gi_honest_reply_eq`), for every pair of tapes. -/
theorem giRep_complete {n : ℕ} {G₀ G₁ : Graph n} {σ : Equiv.Perm (Fin n)}
    (hσ : permGraph G₀ σ = G₁) (z : List Bool) :
    uprob (fun r : giProtocolRep.ExecCoins giProverRep (encInstance G₀ G₁) =>
      giProtocolRep.outV giProverRep (encInstance G₀ G₁) (encPerm σ) z r = [true]) = 1 := by
  refine HardcoreBit.uprob_eq_one_of_forall fun r => ?_
  rw [giProtocolRep_outV, exec_repViews, (honest_views G₀ G₁ σ z _ _ _).1,
    giVerifierRep_next_end_enc _ _ _ _ _ (by rw [length_Vs]; omega) (by rw [length_Vs]; omega)]
  simp only [List.cons.injEq, and_true, decide_eq_true_eq]
  intro j
  rw [getD_Vs_odd _ _ _ _ j.isLt, getD_Vs_even _ _ _ _ j.isLt, honestγ, honestH, decPerm_encPerm,
    gi_honest_reply_eq hσ]

/-! ### Soundness -/

/-- The joint coins of the `|x|`-fold graph isomorphism protocol as (challenges, prover's
coins). -/
def giRepCoins (P' : Strategy) (x : List Bool) :
    (Fin x.length → Bool) × P'.Coins x.length ≃ giProtocolRep.ExecCoins P' x :=
  Equiv.prodComm _ _

/-- The decoded graph a prover with coins `r₁` sends in iteration `i` after the challenges `bs`
(the `H_i` of `uprob_gi_rep_cheat_le`). -/
noncomputable def Hfun {n : ℕ} (P' : Strategy) (x y : List Bool) (i : Fin x.length) (bs : Fin i → Bool)
    (r₁ : P'.Coins x.length) : Graph n :=
  decGraphAt n (P'.next x y (List.ofFn r₁) (PsOfFin bs))

/-- The decoded permutation a prover with coins `r₁` replies in iteration `i` after the
challenges `bs` (the last one being the current challenge; the `γ_i` of `uprob_gi_rep_cheat_le`). -/
noncomputable def γfun {n : ℕ} (P' : Strategy) (x y : List Bool) (i : Fin x.length)
    (bs : Fin (i + 1) → Bool) (r₁ : P'.Coins x.length) : Equiv.Perm (Fin n) :=
  decPerm n (P'.next x y (List.ofFn r₁) (PsOfFin (Fin.init bs) ++ [[bs (Fin.last i)]]))

/-- **The acceptance bound of the `|x|`-fold graph isomorphism protocol against non-isomorphic
graphs** [PS10, Proposition 120.7, "repeated … to drive the error as low as desired"]: for
`G₀ ≇ G₁` and every prover `P'`, the verifier accepts with probability at most `2^{-|x|}`.

**Proof sketch.** Acceptance means `γ_j(G_{b_j}) = H_j` for every `j` (`giVerifierRep_next_end_enc`,
`repViews_snd`), where `H_j` is the prover's message on its view `PsOf b j` and `γ_j` on
`PsOf b j ++ [[b_j]]` (`repViews_fst`); decoding both sides (`decGraphAt_encGraph`) gives the
event of `uprob_gi_rep_cheat_le` with `Hfun`, `γfun` (`PsOfFin_prefixLT`, `PsOfFin_init_prefixLE`),
after reading the joint coins as (challenges, prover's coins) (`giRepCoins`). -/
theorem giRep_accept_le {n : ℕ} {G₀ G₁ : Graph n} (h : ¬ Isomorphic G₀ G₁) (P' : Strategy)
    (y z : List Bool) :
    uprob (fun r : giProtocolRep.ExecCoins P' (encInstance G₀ G₁) =>
      giProtocolRep.outV P' (encInstance G₀ G₁) y z r = [true]) ≤ (2 : ℝ)⁻¹ ^ (encInstance G₀ G₁).length := by
  have hmono : ∀ r : giProtocolRep.ExecCoins P' (encInstance G₀ G₁),
      giProtocolRep.outV P' (encInstance G₀ G₁) y z r = [true] →
      ∀ i : Fin (encInstance G₀ G₁).length,
        permGraph (cond ((List.ofFn r.2).getD i false) G₁ G₀)
          (decPerm n (P'.next (encInstance G₀ G₁) y (List.ofFn r.1)
            (PsOf (fun k => (List.ofFn r.2).getD k false) i ++ [[(List.ofFn r.2).getD i false]]))) =
        decGraphAt n (P'.next (encInstance G₀ G₁) y (List.ofFn r.1)
          (PsOf (fun k => (List.ofFn r.2).getD k false) i)) := by
    intro r hr i
    rw [giProtocolRep_outV, exec_repViews, (repViews_snd P' _ y z _ _ _).1,
      giVerifierRep_next_end_enc _ _ _ _ _ (by rw [length_Vs]; omega) (by rw [length_Vs]; omega)] at hr
    simp only [List.cons.injEq, decide_eq_true_eq, and_true] at hr
    have hi := hr i
    rw [getD_Vs_odd _ _ _ _ i.isLt, getD_Vs_even _ _ _ _ i.isLt, repViews_fst P' _ y z _ _ i i.isLt] at hi
    rw [← hi, decGraphAt_encGraph]
  refine (uprob_mono hmono).trans ?_
  rw [← uprob_comp_equiv (giRepCoins P' (encInstance G₀ G₁))]
  refine le_of_eq_of_le (OneWay.uprob_congr ?_)
    (uprob_gi_rep_cheat_le h (Hfun P' (encInstance G₀ G₁) y) (γfun P' (encInstance G₀ G₁) y))
  rintro ⟨b, r₁⟩
  refine forall_congr' fun i => ?_
  show permGraph (cond ((List.ofFn b).getD i false) G₁ G₀) (decPerm n (P'.next _ y (List.ofFn r₁)
      (PsOf (fun k => (List.ofFn b).getD k false) i ++ [[(List.ofFn b).getD i false]]))) =
    decGraphAt n (P'.next _ y (List.ofFn r₁) (PsOf (fun k => (List.ofFn b).getD k false) i)) ↔
    permGraph (cond (b i) G₁ G₀) (γfun P' _ y i (prefixLE b i) r₁) = Hfun P' _ y i (prefixLT b i) r₁
  rw [getD_ofFn_lt' b i.isLt, Hfun, γfun, PsOfFin_init_prefixLE, prefixLE_last, PsOfFin_prefixLT]

/-- **The `|x|`-fold graph isomorphism protocol is an interactive proof for `L_iso` with
soundness error `2^{-|x|}` and efficient prover with respect to `R_iso`**
[PS10, Proposition 120.7, repeated] (Prop-120.7, Lem-120.d), given the parties' efficiency.

**Proof sketch.** Completeness for every witness is `giRep_complete`; soundness is
`giRep_accept_le` on well-formed inputs (a well-formed `x ∉ L_iso` has non-isomorphic graphs)
and the outright rejection of malformed inputs (`giVerifierRep_next_end`). -/
theorem gi_rep_efficientProverProofErr (hP : giProverRep.Efficient) (hV : giVerifierRep.Efficient) :
    EfficientProverProofErr giProtocolRep Liso Riso (fun N => (2 : ℝ)⁻¹ ^ N) where
  efficientV := hV
  complete := by
    refine ⟨.var, ?_⟩
    rintro x ⟨n, G₀, G₁, σ, rfl, hσ⟩
    exact ⟨encPerm σ, giProverRep_length_le _ _, fun z => giRep_complete hσ z⟩
  sound := by
    intro x hx P' z
    by_cases hwf : wellFormedInstance x = true
    · obtain ⟨n, G₀, G₁, rfl⟩ := exists_eq_encInstance_of_wellFormed hwf
      have hni : ¬ Isomorphic G₀ G₁ := fun hiso => hx ((encInstance_mem_Liso_iff G₀ G₁).2 hiso)
      have hacc := giRep_accept_le hni P' [] z
      have hnot : ∀ r : giProtocolRep.ExecCoins P' (encInstance G₀ G₁),
          giProtocolRep.outV P' (encInstance G₀ G₁) [] z r = [false] ↔
            ¬ giProtocolRep.outV P' (encInstance G₀ G₁) [] z r = [true] := by
        intro r
        rw [giProtocolRep_outV, exec_repViews, (repViews_snd P' _ [] z _ _ _).1,
          giVerifierRep_next_end_enc _ _ _ _ _ (by rw [length_Vs]; omega) (by rw [length_Vs]; omega)]
        simp
      rw [OneWay.uprob_congr hnot, uprob_not]
      linarith
    · have hall : ∀ r : giProtocolRep.ExecCoins P' x, giProtocolRep.outV P' x [] z r = [false] := by
        intro r
        rw [giProtocolRep_outV, exec_repViews, giVerifierRep_next_end _ _ _ _
          (by rw [(repViews_snd P' x [] z _ _ _).1, length_Vs]; omega)
          (by rw [(repViews_snd P' x [] z _ _ _).1, length_Vs]; omega)]
        simp [hwf]
      rw [HardcoreBit.uprob_eq_one_of_forall hall]
      have : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ x.length := by positivity
      linarith
  efficientP := hP
  boundedP := ⟨.var, (Protocol.proverBounded_iff _ _ _).2 fun x y r hist _ =>
    giProverRep_length_le x y r hist⟩
  completeWitness := by
    rintro x y ⟨n, G₀, G₁, σ, rfl, rfl, hσ⟩ z
    exact giRep_complete hσ z

/-- **[PS10, Proposition 120.7], repeated:** the `|x|`-fold graph isomorphism protocol is an
interactive proof for `L_iso` with efficient prover with respect to `R_iso`, given the
parties' efficiency (`gi_rep_efficientProverProofErr`, `negligible_two_pow_neg`). -/
theorem gi_rep_efficientProverProof (hP : giProverRep.Efficient) (hV : giVerifierRep.Efficient) :
    EfficientProverProof giProtocolRep Liso Riso :=
  (gi_rep_efficientProverProofErr hP hV).efficientProverProof negligible_two_pow_neg

end TCSlib.Cryptography.GI

## ===== TCSlib/Cryptography/ZeroKnowledge/ThreeColoring/Protocol.lean =====

/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.Language
import TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.ProtocolProofs
import TCSlib.Cryptography.ZeroKnowledge.Commitment
import TCSlib.Cryptography.ZeroKnowledge.Defs

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Zero-knowledge for graph 3-colouring: the protocol, completeness and soundness

The protocol of [PS10, Protocol 127.5] for the language `3COL` of `ThreeColoring/Language.lean`
(Def-124.f), built on a commitment scheme
`(Com, ℓ)` of `Commitment.lean`, and the completeness and soundness halves of
[PS10, Proposition 127.6]: one iteration (soundness error `1 - 1/|E|`) and the `n|E|`-fold
sequential repetition (soundness error `(1 - 1/|E|)^{n|E|} ≤ e^{-n}`, Claim-125.a). The
zero-knowledge half is `ThreeColoring/Simulator.lean`; the machine infrastructure behind the
efficiency theorems (the parties as polynomial-time string functions of the interactive
layout) is `ThreeColoring/Machines.lean`, `ThreeColoring/Parties.lean` and
`ThreeColoring/ProtocolProofs.lean`.

Graphs are the Boolean relations `Graph n` of `Encoding.lean`; a 3-colouring is a map
`Fin n → Fin 3`, proper when the endpoints of every edge receive different colours; the edges
are enumerated by `edgeList` and the verifier's challenge is the index of an edge in that
list, sent in unary. The prover commits to the colour `π (c i)` of every vertex, padded to an
`n`-bit value (`padColor`, DQ4), with `n` the number of vertices as the security parameter of
the commitment.

**Deviations** ([PS10, Protocol 127.5], source errors 41–43 of the plan):
* the verifier checks the two openings against the commitments (the text's "`V` accepts iff
  `c'_i ≠ c'_j`" is unsound without it) and the lengths of the opening randomness;
* if `E = ∅` the verifier accepts outright (every edgeless graph is 3-colourable; the text's
  "random edge" is undefined), and if `E ≠ ∅` but the graph has fewer than two vertices (so
  the edge is a loop and the graph is not colourable) it rejects outright, which is what makes
  the `n`-bit padding of the colours injective in every case that matters;
* colours are padded to `n` bits (DQ4; the text commits to 2-bit colours, i.e. at security
  parameter `2`);
* the witness is `c₁, …, c_n` (the text lists `c₀, …, c_m`), and the protocol is repeated
  `n|E|` times (the text's proof says `|E|²`);
* (D8, D10) the colour permutation `π ← S₃` and the edge `e ← E` are rejection-sampled from
  the parties' bit tapes with `|x|` trials, so the theorems carry the statistical terms
  `(1/4)^{|x|}` and `(1/2)^{|x|}`; the repeated protocol runs `4|x|²` fixed moves of which the
  first `4 n|E|` are the iterations and the rest are empty messages;
* (run-3 audit P11-3) `Graph n` is an arbitrary Boolean relation and `E` is the list of
  ordered pairs `(u, v)` with `G u v` (`edgeList`, loops included), so for the text's
  symmetric loopless graph `edgeCount G = 2|E|`: the per-iteration soundness error
  `1 - 1/edgeCount G` is `1 − 1/(2|E|)` and the protocol repeats `n · edgeCount G = 2n|E|`
  times; the challenge is uniform over the ordered pairs, i.e. over the text's undirected
  edges, and `(1 − 1/m)^{nm} ≤ e^{-n}` is unchanged. In this file `|E|` abbreviates
  `edgeCount G`.

## Main definitions

* `TCSlib.Cryptography.colCommit`,
  `TCSlib.Cryptography.colOpen`, `TCSlib.Cryptography.colVerify` — the commitment message,
  the opening message and the verifier's check of one iteration.
* `TCSlib.Cryptography.colProver`, `TCSlib.Cryptography.colVerifier`,
  `TCSlib.Cryptography.colProtocol` — one iteration of [PS10, Protocol 127.5];
  `TCSlib.Cryptography.colProverRep`, `TCSlib.Cryptography.colVerifierRep`,
  `TCSlib.Cryptography.colProtocolRep` — the `n|E|`-fold protocol (Prot-127.5).
* `TCSlib.Cryptography.committedColor` — the colour a commitment string can be opened to
  (Lem-127.f).

## Main results

* `TCSlib.Cryptography.colVerify_honest` — completeness of one iteration (Claim-127.e).
* `TCSlib.Cryptography.committedColor_eq_some`, `TCSlib.Cryptography.exists_bad_edge` — the
  committed colouring and its bad edge (Lem-127.f).
* `TCSlib.Cryptography.uprob_adaptive_escape` — adaptive sequential soundness with escape
  probability `1/m` (Lem-127.g); `TCSlib.Cryptography.uprob_col_cheat_le` — soundness of the
  `k`-fold protocol against adaptive provers (Claim-127.h).
* `TCSlib.Cryptography.col_efficientProverProofErr`,
  `TCSlib.Cryptography.colRep_efficientProverProof` — **[PS10, Proposition 127.6]**, the
  interactive-proof half (Prop-127.6).
* `TCSlib.Cryptography.colProver_length_le`, `TCSlib.Cryptography.colProtocol_proverBounded`
  — the honest provers' messages are polynomially bounded in `|x|` (ruling G3-3).
* `TCSlib.Cryptography.R3COL_witnessRelation` — `R_3COL` is a witness relation for `3COL`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§4.7: Theorem 124.1, Protocol 127.5, Proposition 127.6.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026 (the concrete probability layer).
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Cambridge
  University Press, 2009. (Chapter 2, 3-colouring; Chapter 9, zero knowledge.)
-/

namespace TCSlib.Cryptography

open Complexity Turing

/-! ### Messages of one iteration -/

/-- The `i`-th component of an encoded message list (`Strategy.encodeMsgs`): the first
projection after `i` second projections. -/
def msgAt (w : List Bool) (i : ℕ) : List Bool := pairFstD (pairSndD^[i] w)

/-- `msgAt` reads the `i`-th message of an encoded list. -/
theorem msgAt_encodeMsgs (l : List (List Bool)) (i : ℕ) (hi : i < l.length) :
    msgAt (Strategy.encodeMsgs l) i = l[i] := by
  induction l generalizing i with
  | nil => exact absurd hi (Nat.not_lt_zero _)
  | cons a l ih =>
    cases i with
    | zero => simp [msgAt]
    | succ i =>
      have := ih i (by simpa using hi)
      simpa [msgAt, Function.iterate_succ_apply] using this

/-- The prover's first message of [PS10, Protocol 127.5]: the commitments to the (permuted)
colours `c' i`, padded to `n` bits, with randomness `r i ∈ {0,1}^{ℓ(n)}`, as one encoded list
(`multiCom`). -/
def colCommit (Com : List Bool → List Bool) (n ℓn : ℕ) (c' : Fin n → Fin 3)
    (r : Fin n → Fin ℓn → Bool) : List Bool :=
  multiCom Com (fun i => padColor n (c' i)) r

/-- The prover's opening message of [PS10, Protocol 127.5] for the edge `p = (i, j)`:
`⟨⟨c'_i, r_i⟩, ⟨c'_j, r_j⟩⟩`. -/
def colOpen {n ℓn : ℕ} (c' : Fin n → Fin 3) (r : Fin n → Fin ℓn → Bool) (p : Fin n × Fin n) :
    List Bool :=
  pairEncode (pairEncode (encColor (c' p.1)) (List.ofFn (r p.1)))
    (pairEncode (encColor (c' p.2)) (List.ofFn (r p.2)))

/-- The verifier's check of one iteration of [PS10, Protocol 127.5] on the edge of index `e`,
the commitment message `com` and the opening `opn = ⟨⟨a, r_i⟩, ⟨b, r_j⟩⟩`: the randomness has
length `ℓ(n)`, both openings match the commitments, and `a ≠ b`.

**Deviation:** the opening check (the text's "`V` accepts iff `c'_i ≠ c'_j`"); `false` when
`E = ∅` (handled by the verifier before calling this check). -/
def colVerify (Com : List Bool → List Bool) (ℓn : ℕ) {n : ℕ} (G : Graph n) (e : ℕ)
    (com opn : List Bool) : Bool :=
  match edgeAt G e with
  | none => false
  | some p =>
    let a := decColor (pairFstD (pairFstD opn))
    let ri := pairSndD (pairFstD opn)
    let b := decColor (pairFstD (pairSndD opn))
    let rj := pairSndD (pairSndD opn)
    decide (ri.length = ℓn ∧ rj.length = ℓn ∧
      Com (pairEncode (List.ofFn (padColor n a)) ri) = msgAt com p.1 ∧
      Com (pairEncode (List.ofFn (padColor n b)) rj) = msgAt com p.2 ∧ a ≠ b)

/-- **Completeness of one iteration** [PS10, proof of Proposition 127.6, "completeness follows
by inspection"] (Claim-127.e): for a proper colouring `c`, any colour permutation `π`, any
randomness `r` and any edge `p = edgeAt G e`, the honest commitment and opening pass the
verifier's check: the openings match by `msgAt_encodeMsgs`, and `π (c i) ≠ π (c j)` since
`c i ≠ c j` on the edge and `π` is injective. -/
theorem colVerify_honest (Com : List Bool → List Bool) {n ℓn : ℕ} {G : Graph n}
    {c : Fin n → Fin 3} (hc : ProperColoring G c) (π : Equiv.Perm (Fin 3))
    (r : Fin n → Fin ℓn → Bool) {e : ℕ} {p : Fin n × Fin n} (hp : edgeAt G e = some p) :
    colVerify Com ℓn G e (colCommit Com n ℓn (fun i => π (c i)) r)
      (colOpen (fun i => π (c i)) r p) = true := by
  have hadj := edgeAt_adj G hp
  unfold colVerify
  rw [hp]
  simp only [colOpen, pairFstD_pairEncode, pairSndD_pairEncode, decColor_encColor,
    List.length_ofFn, decide_eq_true_eq]
  refine ⟨trivial, trivial, ?_, ?_, fun h => hc _ _ hadj (π.injective h)⟩
  · rw [colCommit, multiCom, msgAt_encodeMsgs _ _ (by simp), List.getElem_ofFn]
  · rw [colCommit, multiCom, msgAt_encodeMsgs _ _ (by simp), List.getElem_ofFn]

/-! ### The committed colouring (Lem-127.f) -/

/-- The colour a commitment string `w` can be opened to at security parameter `n` with
randomness of length `ℓn` (Lem-127.f): `some a` if some `(a, r)` opens `w`, `none` otherwise.
By binding (`committedColor_eq_some`) the colour is unique. -/
noncomputable def committedColor (Com : List Bool → List Bool) (n ℓn : ℕ) (w : List Bool) :
    Option (Fin 3) := by
  classical
  exact if h : ∃ a : Fin 3, ∃ r : Fin ℓn → Bool,
      Com (pairEncode (List.ofFn (padColor n a)) (List.ofFn r)) = w
    then some (Classical.choose h) else none

/-- A list of length `k` is the `ofFn` of its entries read with a default. -/
private theorem ofFn_getD_of_length {r : List Bool} {k : ℕ} (hr : r.length = k) :
    List.ofFn (fun i : Fin k => r.getD i false) = r := by
  subst hr
  exact List.ext_getElem (by simp) fun i _ h₂ => by
    simp [List.getD_eq_getElem?_getD]

/-- **The committed colouring is well defined** [PS10, proof of Proposition 127.6,
"soundness follows by the binding property"] (Lem-127.f): for a commitment scheme, `n ≥ 2`,
an opening `(a, r)` of `w` with `|r| = ℓ(n)` forces `committedColor w = some a` — any other
opening `(a', r')` would give `Com ⟨pad a', r'⟩ = Com ⟨pad a, r⟩` with `pad a' ≠ pad a`
(`padColor_injective`), contradicting `Commitment.binding_ofFn`. -/
theorem committedColor_eq_some {Com : List Bool → List Bool} {ℓ : PolyExpr}
    (hC : Commitment Com ℓ) {n : ℕ} (hn : 2 ≤ n) {a : Fin 3} {r : List Bool}
    (hr : r.length = ℓ.eval n) {w : List Bool}
    (h : Com (pairEncode (List.ofFn (padColor n a)) r) = w) :
    committedColor Com n (ℓ.eval n) w = some a := by
  classical
  have hex : ∃ a : Fin 3, ∃ r : Fin (ℓ.eval n) → Bool,
      Com (pairEncode (List.ofFn (padColor n a)) (List.ofFn r)) = w :=
    ⟨a, fun i => r.getD i false, by rwa [ofFn_getD_of_length hr]⟩
  unfold committedColor
  rw [dif_pos hex, Option.some.injEq]
  obtain ⟨r', hr'⟩ := Classical.choose_spec hex
  by_contra hne
  have hpad : padColor n (Classical.choose hex) ≠ padColor n a :=
    fun h' => hne (padColor_injective hn h')
  have := hC.binding_ofFn hpad r' (fun i => r.getD i false)
  rw [ofFn_getD_of_length hr, hr', h] at this
  exact this rfl

/-- **A non-colourable graph has a bad edge for every partial colouring**
[PS10, proof of Proposition 127.6, "for each coloring there exists at least one edge which
has the same colors on both endpoints"] (Lem-127.f): if `G` is not 3-colourable then for every
`ct : Fin n → Option (Fin 3)` some edge has an uncoloured endpoint or equal colours at both
endpoints — otherwise `i ↦ (ct i).getD 0` would be a proper colouring. -/
theorem exists_bad_edge {n : ℕ} {G : Graph n} (hG : ¬ ThreeColorable G)
    (ct : Fin n → Option (Fin 3)) :
    ∃ e : Fin (edgeCount G), ct (edgeOf G e).1 = none ∨ ct (edgeOf G e).2 = none ∨
      ct (edgeOf G e).1 = ct (edgeOf G e).2 := by
  by_contra hcon
  push_neg at hcon
  refine hG ⟨fun i => (ct i).getD 0, fun u v huv heq => ?_⟩
  obtain ⟨e, he⟩ := exists_edgeOf_eq G huv
  obtain ⟨h1, h2, h3⟩ := hcon e
  simp only [he] at h1 h2 h3
  obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.1 h1
  obtain ⟨b, hb⟩ := Option.ne_none_iff_exists'.1 h2
  simp only [ha, hb] at h3 heq
  exact h3 (by simpa using heq)

/-! ### Adaptive sequential soundness (Lem-127.g, Claim-127.h) -/

/-- The strict prefix `e_0, …, e_{i-1}` of a challenge tuple (the history an adaptive prover
has seen before challenge `i`). -/
def challengesBefore {k : ℕ} {α : Type*} (e : Fin k → α) (i : Fin k) : Fin i → α :=
  fun j => e (Fin.castLE i.isLt.le j)

/-- The prefix `e_0, …, e_i` of a challenge tuple (the history including the current
challenge). -/
def challengesUpTo {k : ℕ} {α : Type*} (e : Fin k → α) (i : Fin k) : Fin (i + 1) → α :=
  fun j => e (Fin.castLE i.isLt j)

/-- A `(k+1)`-tuple of challenges with auxiliary data as a `k`-tuple, the data and the last
challenge (`Fin.snoc`): the splitting of the sequential-soundness induction. -/
private def snocEquivW (k m : ℕ) (W : Type*) :
    ((Fin k → Fin m) × W) × Fin m ≃ (Fin (k + 1) → Fin m) × W where
  toFun y := (Fin.snoc y.1.1 y.2, y.1.2)
  invFun z := ((Fin.init z.1, z.2), z.1 (Fin.last k))
  left_inv y := by
    rcases y with ⟨⟨e, w⟩, x⟩
    simp [Fin.init_snoc, Fin.snoc_last]
  right_inv z := by
    rcases z with ⟨e, w⟩
    simp [Fin.snoc_init_self]

/-- The history before a non-final challenge of `Fin.snoc e x` is the history before it in `e`. -/
private theorem challengesBefore_snoc_castSucc {k m : ℕ} (e : Fin k → Fin m) (x : Fin m)
    (i : Fin k) :
    challengesBefore (Fin.snoc e x : Fin (k + 1) → Fin m) (Fin.castSucc i) =
      challengesBefore e i := by
  funext j
  simp only [challengesBefore]
  have : (Fin.castLE (Fin.castSucc i).isLt.le j : Fin (k + 1)) =
      Fin.castSucc (Fin.castLE i.isLt.le j) := Fin.ext rfl
  rw [this, Fin.snoc_castSucc]

/-- The history before the last challenge of `Fin.snoc e x` is `e`. -/
private theorem challengesBefore_snoc_last {k m : ℕ} (e : Fin k → Fin m) (x : Fin m) :
    challengesBefore (Fin.snoc e x : Fin (k + 1) → Fin m) (Fin.last k) = e := by
  funext j
  simp only [challengesBefore]
  have : (Fin.castLE (Fin.last k).isLt.le j : Fin (k + 1)) = Fin.castSucc j := Fin.ext rfl
  rw [this, Fin.snoc_castSucc]

/-- **Adaptive sequential soundness with escape probability `1/m`** [PS10, proof of
Proposition 127.6, "in each iteration a cheating prover is caught with probability `1/|E|`"]
(Lem-127.g): for `k` rounds with uniform challenges `e_i ∈ [m]` and, for every round, a
nonempty set `Bad i` of challenges (depending on the earlier challenges and on the prover's
coins `w`) on which the prover is caught, the probability that no challenge ever lands in its
bad set is at most `(1 - 1/m)^k`.

**Proof sketch.** Induction on `k`. Split the tuple as `Fin.snoc e' e_last` (the bijection
`(Fin (k+1) → Fin m) ≃ (Fin k → Fin m) × Fin m`, `Fin.snocEquiv`; `uprob_comp_equiv`); by
`uprob_prod` the probability is the average over `(e', w)` of the probability over `e_last`,
which is `0` if some earlier round is caught and at most `1 - |Bad k e' w| / m ≤ 1 - 1/m` otherwise
(`uprob_eq_card_filter`, `Finset.card_pos` from `hBad`); so the total is at most `(1 - 1/m)`
times the probability of the `k`-round event (`OneWay.uprob_and_le_mul`), and the induction
hypothesis applies to the latter. -/
theorem uprob_adaptive_escape (m k : ℕ) (hm : 0 < m) {W : Type*} [Fintype W]
    (Bad : (i : Fin k) → (Fin i → Fin m) → W → Finset (Fin m))
    (hBad : ∀ i h w, (Bad i h w).Nonempty) :
    uprob (fun z : (Fin k → Fin m) × W => ∀ i, z.1 i ∉ Bad i (challengesBefore z.1 i) z.2) ≤
      (1 - 1 / (m : ℝ)) ^ k := by
  induction k with
  | zero => simpa using uprob_le_one _
  | succ k ih =>
    have hm' : (0 : ℝ) < m := by exact_mod_cast hm
    have hθ : 0 ≤ 1 - 1 / (m : ℝ) := by
      rw [sub_nonneg, div_le_one hm']
      exact_mod_cast hm
    have hih := ih (fun i h w => Bad (Fin.castSucc i) h w) (fun i h w => hBad _ _ _)
    rw [← uprob_comp_equiv (snocEquivW k m W)]
    have hmono : uprob (fun y : ((Fin k → Fin m) × W) × Fin m => ∀ i,
          ((snocEquivW k m W) y).1 i ∉
            Bad i (challengesBefore ((snocEquivW k m W) y).1 i) ((snocEquivW k m W) y).2) ≤
        uprob (fun y : ((Fin k → Fin m) × W) × Fin m =>
          (∀ i, y.1.1 i ∉ Bad (Fin.castSucc i) (challengesBefore y.1.1 i) y.1.2) ∧
            y.2 ∉ Bad (Fin.last k) y.1.1 y.1.2) := by
      apply uprob_mono
      rintro ⟨⟨e, w⟩, x⟩ h
      refine ⟨fun i => ?_, ?_⟩
      · have := h (Fin.castSucc i)
        simpa [snocEquivW, Fin.snoc_castSucc, challengesBefore_snoc_castSucc] using this
      · have := h (Fin.last k)
        simpa [snocEquivW, Fin.snoc_last, challengesBefore_snoc_last] using this
    have hbound := OneWay.uprob_and_le_mul
      (fun a : (Fin k → Fin m) × W => ∀ i, a.1 i ∉ Bad (Fin.castSucc i) (challengesBefore a.1 i) a.2)
      (fun y : ((Fin k → Fin m) × W) × Fin m => y.2 ∉ Bad (Fin.last k) y.1.1 y.1.2)
      (θ := 1 - 1 / (m : ℝ)) (fun a _ => ?_)
    · calc _ ≤ _ := hmono
        _ ≤ _ := hbound
        _ ≤ (1 - 1 / (m : ℝ)) * (1 - 1 / (m : ℝ)) ^ k := mul_le_mul_of_nonneg_left hih hθ
        _ = (1 - 1 / (m : ℝ)) ^ (k + 1) := by ring
    · haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
      classical
      rw [uprob_not, uprob_eq_card_filter, Fintype.card_fin]
      have hcard : 1 ≤ (Finset.univ.filter fun b : Fin m => b ∈ Bad (Fin.last k) a.1 a.2).card := by
        rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
        exact Finset.card_pos.2 (hBad _ _ _)
      have : (1 : ℝ) / m ≤
          ((Finset.univ.filter fun b : Fin m => b ∈ Bad (Fin.last k) a.1 a.2).card : ℝ) / m := by
        gcongr
        exact_mod_cast hcard
      linarith

/-- **Soundness of the `k`-fold protocol against adaptive provers** [PS10, proof of
Proposition 127.6] (Claim-127.h, concrete): for a commitment scheme, a graph on `n ≥ 2`
vertices that is not 3-colourable, and a cheating prover whose `i`-th commitment message
`comF i` depends on the earlier challenges and its coins `w`, and whose `i`-th opening
`opnF i` also depends on the current challenge, the verifier accepts all `k` iterations with
probability at most `(1 - 1/|E|)^k` over the uniform challenges and `w` (`|E| = edgeCount G`,
the number of ordered edge pairs; run-3 audit P11-3).

**Proof sketch.** Apply `uprob_adaptive_escape` with
`Bad i h w := {e | the edge `edgeOf G e` is bad for the committed colouring
`k ↦ committedColor Com n ℓ(n) (msgAt (comF i h w) k)`}`, nonempty by `exists_bad_edge`
(`edgeCount_pos_of_not_threeColorable`). Acceptance in round `i` on the challenge `e_i`
means (`colVerify`, `edgeAt_eq_some_edgeOf`) that both openings `(a, r_i)`, `(b, r_j)` have
randomness of length `ℓ(n)` and match the commitments at the endpoints, so by
`committedColor_eq_some` the committed colours at the endpoints are `some a`, `some b` with
`a ≠ b`: the edge is not bad, i.e. `e_i ∉ Bad i …`. Hence the acceptance event is contained
in the escape event (`uprob_mono`). -/
theorem uprob_col_cheat_le {Com : List Bool → List Bool} {ℓ : PolyExpr} (hC : Commitment Com ℓ)
    {n : ℕ} (hn : 2 ≤ n) {G : Graph n} (hG : ¬ ThreeColorable G) (k : ℕ) {W : Type*} [Fintype W]
    (comF : (i : Fin k) → (Fin i → Fin (edgeCount G)) → W → List Bool)
    (opnF : (i : Fin k) → (Fin (i + 1) → Fin (edgeCount G)) → W → List Bool) :
    uprob (fun z : (Fin k → Fin (edgeCount G)) × W => ∀ i,
      colVerify Com (ℓ.eval n) G (z.1 i) (comF i (challengesBefore z.1 i) z.2)
        (opnF i (challengesUpTo z.1 i) z.2) = true) ≤
      (1 - 1 / (edgeCount G : ℝ)) ^ k := by
  classical
  have hm := edgeCount_pos_of_not_threeColorable hG
  let ct : (i : Fin k) → (Fin i → Fin (edgeCount G)) → W → Fin n → Option (Fin 3) :=
    fun i h w v => committedColor Com n (ℓ.eval n) (msgAt (comF i h w) v)
  let Bad : (i : Fin k) → (Fin i → Fin (edgeCount G)) → W → Finset (Fin (edgeCount G)) :=
    fun i h w => Finset.univ.filter fun e => ct i h w (edgeOf G e).1 = none ∨
      ct i h w (edgeOf G e).2 = none ∨ ct i h w (edgeOf G e).1 = ct i h w (edgeOf G e).2
  have hBad : ∀ i h w, (Bad i h w).Nonempty := by
    intro i h w
    obtain ⟨e, he⟩ := exists_bad_edge hG (ct i h w)
    exact ⟨e, by simpa [Bad] using he⟩
  refine le_trans (uprob_mono ?_) (uprob_adaptive_escape (edgeCount G) k hm Bad hBad)
  rintro ⟨es, w⟩ hacc i
  have h := hacc i
  simp only at h ⊢
  unfold colVerify at h
  rw [edgeAt_eq_some_edgeOf] at h
  simp only [decide_eq_true_eq] at h
  obtain ⟨hri, hrj, hci, hcj, hab⟩ := h
  have h1 := committedColor_eq_some hC hn hri hci
  have h2 := committedColor_eq_some hC hn hrj hcj
  simp only [Bad, ct, Finset.mem_filter, Finset.mem_univ, true_and, not_or]
  rw [h1, h2]
  simp [hab]

/-! ### Protocol 127.5, one iteration (Prot-127.5) -/

/-- The well-formedness test of a common input: `x` is the encoding of the graph it decodes
to (i.e. `|x|` is a perfect square). -/
def colWellFormed (x : List Bool) : Bool := decide (x = encGraph (decGraph x).2)

/-- An encoded graph is well formed. -/
theorem colWellFormed_encGraph {n : ℕ} (G : Graph n) : colWellFormed (encGraph G) = true := by
  unfold colWellFormed
  rw [decide_eq_true_eq]
  have h := decGraph_encGraph G
  rw [show encGraph (decGraph (encGraph G)).2 = encGraph (⟨n, G⟩ : Σ n, Graph n).2 by rw [h]]

/-- The honest prover of one iteration of [PS10, Protocol 127.5] (Prot-127.5): with common
input `x = encGraph G` (`n` vertices) and witness `y = encColoring c`, it samples `π ← S₃` from
the first `3|x|` bits of its tape and `r_i ∈ {0,1}^{ℓ(n)}` from the next `n ℓ(n)` bits; on the
empty history it sends the commitments to `π (c i)` (`colCommit`), and on the challenge `w`
it opens the two commitments of the edge `edgeAt G (edgeIdxOfMsg |E| w)` (`colOpen`), or
sends `[]` if `E = ∅`. Coins: `3|x| + |x| ℓ(|x|)` bits (an upper bound for every `n ≤ |x|`).

**Deviation (D10):** `π` by rejection sampling (identity on failure). -/
noncomputable def colProver (Com : List Bool → List Bool) (ℓ : PolyExpr) : Strategy where
  coins := .add (.mul (.const 3) .var) (.mul .var ℓ)
  next x y r hist :=
    let n := (decGraph x).1
    let G : Graph n := (decGraph x).2
    let c := decColoring n y
    let π := samplePerm3 x.length (r.take (3 * x.length))
    let rr : Fin n → Fin (ℓ.eval n) → Bool :=
      fun i j => r.getD (3 * x.length + i * ℓ.eval n + j) false
    let c' : Fin n → Fin 3 := fun i => π (c i)
    match hist with
    | [] => colCommit Com n (ℓ.eval n) c' rr
    | w :: _ =>
      match edgeAt G (edgeIdxOfMsg (edgeCount G) w) with
      | some p => colOpen c' rr p
      | none => []

/-- The verifier of one iteration of [PS10, Protocol 127.5] (Prot-127.5): it samples the
edge index `e ← [|E|]` from its tape (`sampleEdgeIdx` with `|x|` trials); on the commitment
message it sends `1^e`; on the complete history `[com, opn]` it outputs `[true]` iff `x` is
well formed and either `E = ∅` or (`n ≥ 2` and `colVerify` accepts the openings on the edge
`e`). Coins: `(|x| + 1)²` bits.

**Deviation:** opening check, `E = ∅` accepted outright, `n < 2` with `E ≠ ∅` rejected outright,
well-formedness test (see the module docstring); `e` by rejection sampling (D10). -/
noncomputable def colVerifier (Com : List Bool → List Bool) (ℓ : PolyExpr) : Strategy where
  coins := .normal 1 2
  next x _ r hist :=
    let n := (decGraph x).1
    let G : Graph n := (decGraph x).2
    let m := edgeCount G
    let e := sampleEdgeIdx m x.length r
    match hist with
    | [com, opn] => [decide (colWellFormed x = true ∧
        (m = 0 ∨ (2 ≤ n ∧ colVerify Com (ℓ.eval n) G e com opn = true)))]
    | [_] => edgeMsg e
    | _ => [false]

/-- One iteration of [PS10, Protocol 127.5] (Prot-127.5): three messages (commitments,
edge, openings), prover first; the verdict is the verifier's activation on `[com, opn]`. -/
noncomputable def colProtocol (Com : List Bool → List Bool) (ℓ : PolyExpr) : Protocol where
  P := colProver Com ℓ
  V := colVerifier Com ℓ
  rounds := .const 3
  verifierFirst := false

/-! ### The `n|E|`-fold protocol (Prot-127.5, repeated) -/

/-- The `t`-th block of `c` bits of a tape (the coins of iteration `t` of the repeated
protocol). -/
def colCoinSlice (c t : ℕ) (r : List Bool) : List Bool := (r.drop (t * c)).take c

/-- The number of iterations of the repeated protocol on `x`: `n |E|` [PS10, Protocol 127.5,
"repeat the procedure `n|E|` times"], with `|E| = edgeCount G` the number of ordered edge
pairs (for the text's simple graph `2n|E|` iterations; run-3 audit P11-3). -/
def colIterations (x : List Bool) : ℕ := (decGraph x).1 * edgeCount (decGraph x).2

/-- The prover of the `n|E|`-fold protocol: iteration `t = hist.length / 2` (it has received
the challenges and the empty verifier messages of the earlier iterations) runs `colProver`
on the `t`-th block of `3|x| + |x| ℓ(|x|)` coins; after the `n|E|` iterations it sends `[]`. -/
noncomputable def colProverRep (Com : List Bool → List Bool) (ℓ : PolyExpr) : Strategy where
  coins := .mul (.mul .var .var) (.add (.mul (.const 3) .var) (.mul .var ℓ))
  next x y r hist :=
    let t := hist.length / 2
    if t < colIterations x then
      (colProver Com ℓ).next x y
        (colCoinSlice ((colProver Com ℓ).coinLen x.length) t r)
        (if hist.length % 2 = 0 then [] else [hist.getLastD []])
    else []

/-- The verifier of the `n|E|`-fold protocol: it has received `[com_0, opn_0, com_1, …]`; on
an odd history it sends the challenge of iteration `t = hist.length / 2` (from the `t`-th
block of `(|x|+1)²` coins); on the complete history (`2|x|²` received messages) it accepts iff
`x` is well formed and either `E = ∅` or `n ≥ 2` and every one of the `n|E|` iterations passes
`colVerify`; on every other even history it sends `[]`. -/
noncomputable def colVerifierRep (Com : List Bool → List Bool) (ℓ : PolyExpr) : Strategy where
  coins := .mul (.mul .var .var) (.normal 1 2)
  next x _ r hist :=
    let n := (decGraph x).1
    let G : Graph n := (decGraph x).2
    let m := edgeCount G
    let e : ℕ → ℕ := fun t => sampleEdgeIdx m x.length (colCoinSlice ((x.length + 1) ^ 2) t r)
    if hist.length % 2 = 1 then
      (if hist.length / 2 < colIterations x then edgeMsg (e (hist.length / 2)) else [])
    else if hist.length = 2 * (x.length * x.length) then
      [decide (colWellFormed x = true ∧ (m = 0 ∨ (2 ≤ n ∧ ∀ t : Fin (colIterations x),
        colVerify Com (ℓ.eval n) G (e t) (hist.getD (2 * t) []) (hist.getD (2 * t + 1) []) = true)))]
    else []

/-- The `n|E|`-fold protocol of [PS10, Protocol 127.5] (Prot-127.5): prover first, four moves
per iteration (commitments, edge, openings, and a verifier message, empty except for the final
verdict; D8 fixed alternation), `4|x|²` moves in all, of which the first `4 n|E|` carry the
iterations. -/
noncomputable def colProtocolRep (Com : List Bool → List Bool) (ℓ : PolyExpr) : Protocol where
  P := colProverRep Com ℓ
  V := colVerifierRep Com ℓ
  rounds := .mul (.const 4) (.mul .var .var)
  verifierFirst := false

/-! ### Efficiency of the honest parties (Inf-4.2) -/

/-- The honest prover of one iteration is efficient (D8) when `Com` is polynomial-time
[PS10, Proposition 127.6, efficient prover] (Inf-4.2).

**Proof sketch.** `Strategy.Efficient` with `NUPPT.ofPolyTimeUniform` of the string function
of the layout `⟨⟨⟨1^N, ⟨⟨x, y⟩, msgs⟩⟩, []⟩, r⟩` (`Complexity.inArg`, `inCoins`): `n = Nat.sqrt |x|`
in unary by `polyTimeComputable_iterateFind` over `polyTimeComputable_lenLe` against unary
squares; `π` by `polyTimeComputable_iterateFind` over the `|x|` three-bit trials
(`pairTakePoly`/`pairDropPoly`); the `n` commitments by `polyTimeComputable_blockMap ℓ` on
the randomness blocks composed with `hCom` on `⟨pad (π (c i)), r_i⟩` (`PolyTimeComputable.pairEncode`,
the colour permutation as a table lookup, `polyTimeComputable_ite`) and
`polyTimeComputable_iterateEmit` for the `encodeMsgs` fold; the opening by the two projections
of the challenge's decoded index (`polyTimeComputable_lenLe` against the unary `|E|`, the edge
list scanned by `polyTimeComputable_iterateFind`); the case split on `msgs = []` by
`polyTimeComputable_lenEq`. The equation with `colProver.next` is
`NUPPT.runAtL_ofPolyTimeUniform` and `Strategy.pairFstD_encodeMsgs`. -/
theorem colProver_efficient {Com : List Bool → List Bool} (hCom : PolyTimeComputable Com)
    (ℓ : PolyExpr) : (colProver Com ℓ).Efficient :=
  ColProofs.colProver_efficient hCom ℓ

/-- The verifier of one iteration is efficient (D8) when `Com` is polynomial-time
[PS10, Definition 116.1 for Proposition 127.6] (Inf-4.2).

**Proof sketch.** As `colProver_efficient`: the edge index by `polyTimeComputable_iterateFind`
over the `|x|` trials of `Nat.size |E|` bits (`|E|` in unary by scanning the matrix with
`polyTimeComputable_iterateEmit`), the challenge `1^e` by `polyTimeComputable_unaryPoly`-style
emission, and the verdict by `polyTimeComputable_and` of the well-formedness test
(`polyTimeComputable_pairEq` on `x` and the re-encoded matrix), the two commitment checks
(`hCom` on the parsed openings, `msgAt` by `polyTimeComputable_iterate_pairFstD`-style
projections, `polyTimeComputable_pairEq`), the length tests (`polyTimeComputable_lenEq`) and
the colour comparison. -/
theorem colVerifier_efficient {Com : List Bool → List Bool} (hCom : PolyTimeComputable Com)
    (ℓ : PolyExpr) : (colVerifier Com ℓ).Efficient :=
  ColProofs.colVerifier_efficient hCom ℓ

/-- The prover of the `n|E|`-fold protocol is efficient (D8) (Inf-4.2): `colProver_efficient`
on the coin block `hist.length / 2` cut by `pairTakePoly`/`pairDropPoly`, with the parity and
iteration tests by `polyTimeComputable_lenLe` on unary counters. -/
theorem colProverRep_efficient {Com : List Bool → List Bool} (hCom : PolyTimeComputable Com)
    (ℓ : PolyExpr) : (colProverRep Com ℓ).Efficient :=
  ColProofs.colProverRep_efficient hCom ℓ

/-- The verifier of the `n|E|`-fold protocol is efficient (D8) (Inf-4.2): the challenge as in
`colVerifier_efficient` on the block `hist.length / 2`, and the verdict a loop over the
`n|E|` pairs of the history (`polyTimeComputable_iterate` with an accumulated conjunction of
`colVerify` checks). -/
theorem colVerifierRep_efficient {Com : List Bool → List Bool} (hCom : PolyTimeComputable Com)
    (ℓ : PolyExpr) : (colVerifierRep Com ℓ).Efficient :=
  ColProofs.colVerifierRep_efficient hCom ℓ

/-! ### Bounded prover messages (ruling G3-3 of gate 03) -/

/-- A vector of `q` commitments to `n`-bit values with `m`-bit randomness has at most
`q (2 C (2n + 3 + m)^c + 2)` bits when `C (|w| + 1)^c` bounds `|Com w|`
(`CommitmentLemmas.length_encodeMsgs_le`, `length_pairEncode`). -/
theorem length_multiCom_le {Com : List Bool → List Bool} {C c : ℕ}
    (hC : ∀ w, (Com w).length ≤ C * (w.length + 1) ^ c) {q n m : ℕ} (v : Fin q → Fin n → Bool)
    (r : Fin q → Fin m → Bool) :
    (multiCom Com v r).length ≤ q * (2 * (C * (2 * n + 3 + m) ^ c) + 2) := by
  unfold multiCom
  refine (CommitmentLemmas.length_encodeMsgs_le _ (C * (2 * n + 3 + m) ^ c)
    fun msg hmsg => ?_).trans (by simp)
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hmsg
  refine (hC _).trans (le_of_eq ?_)
  rw [length_pairEncode, List.length_ofFn, List.length_ofFn]
  ring_nf

/-- **The honest prover of one iteration sends polynomially bounded messages** (ruling G3-3 of
gate 03): for `C (|w| + 1)^c` bounding `|Com w|` and `n = (decGraph x).1 ≤ |x|`, the
commitment message has at most `n (2 C (2n + 3 + ℓ(n))^c + 2)` bits (`length_multiCom_le`),
the opening `3 ℓ(n) + 20` (`length_pairEncode`, `length_encColoring`) and the empty reply none;
`ℓ` is monotone (`PolyExpr.eval_mono`). The bound holds for every tape and history, since
`colCommit` and `colOpen` have a fixed shape. -/
theorem colProver_length_le {Com : List Bool → List Bool} (hCom : PolyTimeComputable Com)
    (ℓ : PolyExpr) : ∃ B : PolyExpr, ∀ x y r hist,
      ((colProver Com ℓ).next x y r hist).length ≤ B.eval x.length := by
  obtain ⟨C, c, hC⟩ := hCom.output_length_le
  refine ⟨.add (.mul .var (.add (.mul (.const 2) (.mul (.const C)
    (.pow (.add (.add (.mul (.const 2) .var) (.const 3)) ℓ) c))) (.const 2)))
    (.add (.mul (.const 3) ℓ) (.const 20)), fun x y r hist => ?_⟩
  have hn : (decGraph x).1 ≤ x.length := Nat.sqrt_le_self _
  have hℓ : ℓ.eval (decGraph x).1 ≤ ℓ.eval x.length := ℓ.eval_mono hn
  have hcom : (decGraph x).1 * (2 * (C * (2 * (decGraph x).1 + 3 + ℓ.eval (decGraph x).1) ^ c) + 2)
      ≤ x.length * (2 * (C * (2 * x.length + 3 + ℓ.eval x.length) ^ c) + 2) := by
    gcongr
  simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_pow,
    PolyExpr.eval_var, colProver]
  split
  · exact (length_multiCom_le hC _ _).trans (hcom.trans (Nat.le_add_right _ _))
  · split
    · simp only [colOpen, length_pairEncode, List.length_ofFn, encColor, length_encColoring]
      omega
    · simp

/-- **The honest provers of [PS10, Protocol 127.5] send polynomially bounded messages**, one
iteration and `n|E|`-fold, on every instance (ruling G3-3 of gate 03): the bound of
`colProver_length_le` from the commitment's polynomial-time evaluator; the repeated prover
runs `colProver` on a coin block or sends `[]`. -/
theorem colProtocol_proverBounded {Com : List Bool → List Bool} {ℓ : PolyExpr}
    (hC : Commitment Com ℓ) (R : List Bool → List Bool → Prop) :
    ∃ B : PolyExpr, (colProtocol Com ℓ).ProverBounded R B ∧
      (colProtocolRep Com ℓ).ProverBounded R B := by
  obtain ⟨B, hB⟩ := colProver_length_le hC.easy ℓ
  refine ⟨B, (Protocol.proverBounded_iff _ _ _).2 fun x y r hist _ => hB x y r hist,
    (Protocol.proverBounded_iff _ _ _).2 fun x y r hist _ => ?_⟩
  show ((colProverRep Com ℓ).next x y r hist).length ≤ B.eval x.length
  simp only [colProverRep]
  split_ifs <;> first | exact hB _ _ _ _ | exact Nat.zero_le _

/-! ### Proposition 127.6, interactive-proof half -/

section OneIteration

open ColMachines

/-! ### Unfolding the parties on a decoded instance -/

/-- The verifier's verdict on `[com, opn]`, on an input decoding to `⟨n, G⟩`. -/
private theorem colVerifier_next_two_of (Com : List Bool → List Bool) (ℓ : PolyExpr) {x : List Bool}
    {n : ℕ} {G : Graph n} (hx : decGraph x = ⟨n, G⟩) (z r com opn : List Bool) :
    (colVerifier Com ℓ).next x z r [com, opn] =
      [decide (colWellFormed x = true ∧ (edgeCount G = 0 ∨ (2 ≤ n ∧
        colVerify Com (ℓ.eval n) G (sampleEdgeIdx (edgeCount G) x.length r) com opn = true)))] := by
  show [decide (colWellFormed x = true ∧ (edgeCount (decGraph x).2 = 0 ∨ (2 ≤ (decGraph x).1 ∧
    colVerify Com (ℓ.eval (decGraph x).1) (decGraph x).2
      (sampleEdgeIdx (edgeCount (decGraph x).2) x.length r) com opn = true)))] = _
  rw [hx]

/-- The verifier's challenge on `[com]`, on an input decoding to `⟨n, G⟩`. -/
private theorem colVerifier_next_one_of (Com : List Bool → List Bool) (ℓ : PolyExpr) {x : List Bool}
    {n : ℕ} {G : Graph n} (hx : decGraph x = ⟨n, G⟩) (z r com : List Bool) :
    (colVerifier Com ℓ).next x z r [com] = edgeMsg (sampleEdgeIdx (edgeCount G) x.length r) := by
  show edgeMsg (sampleEdgeIdx (edgeCount (decGraph x).2) x.length r) = _
  rw [hx]

/-- The prover's commitments, on an input decoding to `⟨n, G⟩`. -/
private theorem colProver_next_nil_of (Com : List Bool → List Bool) (ℓ : PolyExpr) {x : List Bool}
    {n : ℕ} {G : Graph n} (hx : decGraph x = ⟨n, G⟩) (y r : List Bool) :
    (colProver Com ℓ).next x y r [] = colCommit Com n (ℓ.eval n)
      (fun i => samplePerm3 x.length (r.take (3 * x.length)) (decColoring n y i))
      (fun i j => r.getD (3 * x.length + i * ℓ.eval n + j) false) := by
  show colCommit Com (decGraph x).1 (ℓ.eval (decGraph x).1)
    (fun i => samplePerm3 x.length (r.take (3 * x.length)) (decColoring (decGraph x).1 y i))
    (fun i j => r.getD (3 * x.length + i * ℓ.eval (decGraph x).1 + j) false) = _
  rw [hx]

/-- The prover's opening, on an input decoding to `⟨n, G⟩` with at least one edge. -/
private theorem colProver_next_cons_of (Com : List Bool → List Bool) (ℓ : PolyExpr) {x : List Bool}
    {n : ℕ} {G : Graph n} (hx : decGraph x = ⟨n, G⟩) (hm : 0 < edgeCount G) (y r w : List Bool)
    (h : List (List Bool)) :
    (colProver Com ℓ).next x y r (w :: h) = colOpen
      (fun i => samplePerm3 x.length (r.take (3 * x.length)) (decColoring n y i))
      (fun (i : Fin n) (j : Fin (ℓ.eval n)) => r.getD (3 * x.length + i * ℓ.eval n + j) false)
      (edgeOf G ⟨edgeIdxOfMsg (edgeCount G) w % edgeCount G, Nat.mod_lt _ hm⟩) := by
  simp only [colProver]
  rw [hx]
  dsimp only
  rw [edgeAt_eq_some_of_pos G hm]

/-- The verdict of one iteration against any prover `P'`: the verifier's activation on the
two prover messages, the second being the reply to the challenge. -/
private theorem colProtocol_outV (Com : List Bool → List Bool) (ℓ : PolyExpr) (P' : Strategy)
    (x y z : List Bool) (r : (colProtocol Com ℓ).ExecCoins P' x) :
    (colProtocol Com ℓ).outV P' x y z r =
      (colVerifier Com ℓ).next x z (List.ofFn r.2)
        [P'.next x y (List.ofFn r.1) [],
          P'.next x y (List.ofFn r.1)
            [(colVerifier Com ℓ).next x z (List.ofFn r.2) [P'.next x y (List.ofFn r.1) []]]] := rfl

/-! ### Completeness -/

/-- **The honest execution accepts** on every pair of random tapes: for a proper colouring the
verdict is `[true]`. -/
private theorem colProtocol_outV_honest {Com : List Bool → List Bool} {ℓ : PolyExpr} {n : ℕ}
    {G : Graph n} {c : Fin n → Fin 3} (hc : ProperColoring G c) (z : List Bool)
    (r : (colProtocol Com ℓ).ExecCoins (colProtocol Com ℓ).P (encGraph G)) :
    (colProtocol Com ℓ).outV (colProtocol Com ℓ).P (encGraph G) (encColoring c) z r = [true] := by
  have hx : decGraph (encGraph G) = ⟨n, G⟩ := decGraph_encGraph G
  rw [colProtocol_outV]
  show (colVerifier Com ℓ).next _ _ _ [(colProver Com ℓ).next _ _ _ [], (colProver Com ℓ).next _ _ _
    [(colVerifier Com ℓ).next _ _ _ [(colProver Com ℓ).next _ _ _ []]]] = _
  rw [colVerifier_next_one_of Com ℓ hx, colProver_next_nil_of Com ℓ hx, colVerifier_next_two_of Com ℓ hx,
    colWellFormed_encGraph, decColoring_encColoring]
  by_cases hm : edgeCount G = 0
  · simp [hm]
  · have hpos := Nat.pos_of_ne_zero hm
    have he := sampleEdgeIdx_lt hpos (encGraph G).length (List.ofFn r.2)
    rw [colProver_next_cons_of Com ℓ hx hpos, decColoring_encColoring]
    simp only [edgeIdxOfMsg_edgeMsg he]
    rw [colVerify_honest Com hc _ _ (edgeAt_eq_some_of_pos G hpos _)]
    simp [ColProofs.two_le_of_edge hc hpos]

/-! ### Soundness -/

/-- **One-round soundness bound against a deterministic prover:** for a non-colourable graph
on `n ≥ 2` vertices, the verifier's check on a uniform edge index `e`, a fixed commitment
message and an opening depending on `e`, passes with probability at most `1 - 1/|E|`
(`uprob_col_cheat_le` at `k = 1`). -/
private theorem uprob_check_uniform_le {Com : List Bool → List Bool} {ℓ : PolyExpr}
    (hC : Commitment Com ℓ) {n : ℕ} (hn : 2 ≤ n) {G : Graph n} (hG : ¬ ThreeColorable G)
    (com : List Bool) (opn : ℕ → List Bool) :
    uprob (fun e : Fin (edgeCount G) => colVerify Com (ℓ.eval n) G e com (opn e) = true) ≤
      1 - 1 / (edgeCount G : ℝ) := by
  have h := uprob_col_cheat_le hC hn hG 1 (W := Unit) (fun _ _ _ => com)
    (fun i h _ => opn (h (Fin.last i)))
  rw [pow_one] at h
  refine le_trans ?_ h
  rw [← uprob_comp_equiv (ColProofs.finOneEquiv (edgeCount G))]
  apply uprob_mono
  intro e he i
  rw [Fin.fin_one_eq_zero i]
  exact he

/-- **Soundness of one iteration** [PS10, Proposition 127.6]: for `x ∉ 3COL` and any prover,
the verifier rejects with probability at least `1 - (1 - 1/|x| + (1/2)^{|x|})`. -/
private theorem colProtocol_sound {Com : List Bool → List Bool} {ℓ : PolyExpr} (hC : Commitment Com ℓ)
    (x : List Bool) (hx : x ∉ L3COL) (P' : Strategy) (z : List Bool) :
    1 - (1 - 1 / (x.length : ℝ) + (1 / 2 : ℝ) ^ x.length) ≤
      uprob (fun r : (colProtocol Com ℓ).ExecCoins P' x =>
        (colProtocol Com ℓ).outV P' x [] z r = [false]) := by
  have hs0 : (0 : ℝ) ≤ 1 - 1 / (x.length : ℝ) + (1 / 2 : ℝ) ^ x.length := by
    have h1 : 1 / (x.length : ℝ) ≤ 1 := by
      rcases Nat.eq_zero_or_pos x.length with h | h
      · rw [h]; simp
      · rw [div_le_one (by exact_mod_cast h)]; exact_mod_cast h
    have h2 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ x.length := by positivity
    linarith
  -- reduce to a bound on the acceptance probability
  suffices key : uprob (fun r : (colProtocol Com ℓ).ExecCoins P' x =>
      ¬ (colProtocol Com ℓ).outV P' x [] z r = [false]) ≤
        1 - 1 / (x.length : ℝ) + (1 / 2 : ℝ) ^ x.length by
    rw [uprob_not] at key
    linarith
  set n := (decGraph x).1 with hn_def
  set G := (decGraph x).2 with hG_def
  have hx' : decGraph x = ⟨n, G⟩ := rfl
  have hout : ∀ r : (colProtocol Com ℓ).ExecCoins P' x, (colProtocol Com ℓ).outV P' x [] z r =
      [decide (colWellFormed x = true ∧ (edgeCount G = 0 ∨ (2 ≤ n ∧
        colVerify Com (ℓ.eval n) G (sampleEdgeIdx (edgeCount G) x.length (List.ofFn r.2))
          (P'.next x [] (List.ofFn r.1) [])
          (P'.next x [] (List.ofFn r.1)
            [edgeMsg (sampleEdgeIdx (edgeCount G) x.length (List.ofFn r.2))]) = true)))] := by
    intro r
    rw [colProtocol_outV, colVerifier_next_one_of Com ℓ hx', colVerifier_next_two_of Com ℓ hx']
  by_cases hwf : colWellFormed x = true
  · have hxG : x = encGraph G := of_decide_eq_true hwf
    have hnc : ¬ ThreeColorable G := fun h => hx (hxG ▸ (encGraph_mem_L3COL_iff G).2 h)
    have hm : 0 < edgeCount G := edgeCount_pos_of_not_threeColorable hnc
    by_cases hn : 2 ≤ n
    · -- the acceptance event is the verifier's check
      have hacc : ∀ r : (colProtocol Com ℓ).ExecCoins P' x,
          (¬ (colProtocol Com ℓ).outV P' x [] z r = [false]) ↔
            colVerify Com (ℓ.eval n) G (sampleEdgeIdx (edgeCount G) x.length (List.ofFn r.2))
              (P'.next x [] (List.ofFn r.1) [])
              (P'.next x [] (List.ofFn r.1)
                [edgeMsg (sampleEdgeIdx (edgeCount G) x.length (List.ofFn r.2))]) = true := by
        intro r
        rw [hout r]
        simp [hwf, hm.ne', hn]
      -- fix the prover's coins
      obtain ⟨rP, hrP⟩ := (colProtocol Com ℓ).exists_proverCoins_le P' x [] z fun o => ¬ o = [false]
      refine hrP.trans ?_
      rw [OneWay.uprob_congr fun rV => hacc (rP, rV)]
      -- the sampled edge is close to uniform on the verifier's tape
      have hmx : edgeCount G ≤ x.length := by
        have h1 : x.length = n * n := by rw [hxG, length_encGraph]
        rw [edgeCount_eq G x (decGraph_apply x), h1]
        exact countTrue_le _ _
      have hle : x.length * Nat.size (edgeCount G) ≤ (colVerifier Com ℓ).coinLen x.length := by
        show x.length * Nat.size (edgeCount G) ≤ 1 * (x.length + 1) ^ 2
        have h1 : Nat.size (edgeCount G) ≤ x.length :=
          (Nat.size_le_size hmx).trans (Nat.size_le.2 Nat.lt_two_pow_self)
        calc x.length * Nat.size (edgeCount G) ≤ x.length * x.length := Nat.mul_le_mul_left _ h1
          _ ≤ 1 * (x.length + 1) ^ 2 := by nlinarith
      have hclose := (statClose_sampleEdgeIdx hm x.length).comp_pushesUniform
        (ColProofs.pushesUniform_castLE hle)
      have hbound := hclose.uprob_le_add fun e : Fin (edgeCount G) =>
        colVerify Com (ℓ.eval n) G e (P'.next x [] (List.ofFn rP) [])
          (P'.next x [] (List.ofFn rP) [edgeMsg e]) = true
      simp only [id] at hbound
      have hev : ∀ rV : (colVerifier Com ℓ).Coins x.length,
          (colVerify Com (ℓ.eval n) G (sampleEdgeIdx (edgeCount G) x.length (List.ofFn (rP, rV).2))
            (P'.next x [] (List.ofFn (rP, rV).1) [])
            (P'.next x [] (List.ofFn (rP, rV).1)
              [edgeMsg (sampleEdgeIdx (edgeCount G) x.length (List.ofFn (rP, rV).2))]) = true) ↔
          (colVerify Com (ℓ.eval n) G
            (sampleEdgeIdx (edgeCount G) x.length (List.ofFn fun i => rV (Fin.castLE hle i)))
            (P'.next x [] (List.ofFn rP) [])
            (P'.next x [] (List.ofFn rP)
              [edgeMsg (sampleEdgeIdx (edgeCount G) x.length
                (List.ofFn fun i => rV (Fin.castLE hle i)))]) = true) := by
        intro rV
        rw [← ColProofs.sampleEdgeIdx_ofFn_castLE hle rV]
      refine (le_of_eq (OneWay.uprob_congr hev)).trans (hbound.trans ?_)
      have hcheat := uprob_check_uniform_le hC hn hnc (P'.next x [] (List.ofFn rP) [])
        fun e => P'.next x [] (List.ofFn rP) [edgeMsg e]
      have hinv : 1 / (x.length : ℝ) ≤ 1 / (edgeCount G : ℝ) :=
        one_div_le_one_div_of_le (by exact_mod_cast hm) (by exact_mod_cast hmx)
      linarith
    · -- fewer than two vertices with an edge: the verifier rejects outright
      have hall : ∀ r : (colProtocol Com ℓ).ExecCoins P' x,
          ¬ ¬ (colProtocol Com ℓ).outV P' x [] z r = [false] := by
        intro r
        rw [hout r]
        simp [hm.ne', hn]
      rw [OneWay.uprob_congr fun r => iff_of_false (hall r) (not_false)]
      rw [uprob_false]
      exact hs0
  · have hall : ∀ r : (colProtocol Com ℓ).ExecCoins P' x,
        ¬ ¬ (colProtocol Com ℓ).outV P' x [] z r = [false] := by
      intro r
      rw [hout r]
      simp [hwf]
    rw [OneWay.uprob_congr fun r => iff_of_false (hall r) (not_false)]
    rw [uprob_false]
    exact hs0

end OneIteration


/-- `R_3COL` is a witness relation for `3COL` [PS10, Definition 191.11 for Theorem 124.1]:
witnesses have length `2n ≤ 2|x|`, and the relation is decided in polynomial time by
re-encoding the decoded graph and colouring and checking every edge.

**Proof sketch.** `mem_iff` is `mem_L3COL_iff`; `bounded` with `p := 2 · var`
(`length_encColoring`, `length_encGraph`, `n ≤ n²`); `decidable` with
`T ⟨x, y⟩ := decide (x = encGraph (decGraph x).2 ∧ y = encColoring (decColoring n y) ∧
ProperColoring (decGraph x).2 (decColoring n y))`, correct by `decGraph_encGraph` and
`decColoring_encColoring`, and polynomial-time by `polyTimeComputable_pairEq` on the
re-encodings (`polyTimeComputable_blockMap`, `polyTimeComputable_iterateEmit`) and a scan of
the `n²` entries for the colouring test (`polyTimeComputable_iterate` with an accumulated
conjunction). -/
theorem R3COL_witnessRelation : WitnessRelation L3COL R3COL := by
  refine ⟨mem_L3COL_iff, ⟨.mul (.const 2) .var, ?_⟩, ?_⟩
  · rintro x y ⟨n, G, c, rfl, rfl, -⟩
    rw [length_encColoring, length_encGraph, PolyExpr.eval_mul, PolyExpr.eval_const,
      PolyExpr.eval_var]
    nlinarith [Nat.zero_le n]
  · sorry

/-- **One iteration of [PS10, Protocol 127.5] is an interactive proof for `3COL` with
efficient prover and soundness error `1 - 1/|x| + (1/2)^{|x|}`** [PS10, Proposition 127.6,
one iteration: "a cheating prover is caught with probability `1/|E|`"] (Prop-127.6,
Claim-127.e, Claim-127.h).

**Deviation (D10):** the error `1 - 1/|E|` is stated through `|E| ≤ |x|`, plus the edge
sampler's failure term `(1/2)^{|x|}`; here `|E| = edgeCount G ≤ n² = |x|` counts ordered
pairs (run-3 audit P11-3), which is what makes `|E| ≤ |x|` immediate.

**Proof sketch.** Completeness for every witness: for `x = encGraph G`, `y = encColoring c`
with `c` proper, the transcript is `[com, opn]` with `com = colCommit (π ∘ c) r` and
`opn = colOpen (π ∘ c) r p` for `p = edgeAt G e` (`exec_succ` three times, `decGraph_encGraph`,
`decColoring_encColoring`, `edgeIdxOfMsg_edgeMsg` with `sampleEdgeIdx_lt`), and the verdict is
`[true]` by `colWellFormed_encGraph`, `colVerify_honest` when `E ≠ ∅` (then `n ≥ 2`: a graph
with an edge and a proper colouring has two distinct vertices) and outright when `E = ∅`, for
every value of `π` and `e` (`HardcoreBit.uprob_eq_one_of_forall`). Completeness of
`InteractiveProofErr` is the witness of `mem_L3COL_iff`. Soundness: for `x ∉ 3COL` either
`colWellFormed x = false` (verdict `[false]` always) or `x = encGraph G` with `¬ ThreeColorable G`
(`encGraph_mem_L3COL_iff`), so `0 < |E|` (`edgeCount_pos_of_not_threeColorable`); if `n < 2`
the verdict is `[false]`; otherwise fix the prover's coins (`Protocol.exists_proverCoins_le`),
replace the sampled edge by a uniform one (`statClose_sampleEdgeIdx`,
`StatClose.abs_uprob_sub_le_prod`, cost `(1/2)^{|x|}`), and apply `uprob_col_cheat_le` with
`k = 1`, `comF :=` the prover's first message and `opnF :=` its reply to `1^e`, giving
`Pr[accept] ≤ 1 - 1/|E| + (1/2)^{|x|} ≤ 1 - 1/|x| + (1/2)^{|x|}` (`|E| ≤ n² = |x|`), i.e. the
`[false]` probability is at least `1 - s |x|` (`uprob_not`). Efficiency:
`colProver_efficient`, `colVerifier_efficient` from `hC.easy`. -/
theorem col_efficientProverProofErr {Com : List Bool → List Bool} {ℓ : PolyExpr}
    (hC : Commitment Com ℓ) :
    EfficientProverProofErr (colProtocol Com ℓ) L3COL R3COL
      (fun N => 1 - 1 / (N : ℝ) + (1 / 2 : ℝ) ^ N) where
  efficientV := colVerifier_efficient hC.easy ℓ
  complete := by
    obtain ⟨B, hB, -⟩ := colProtocol_proverBounded hC R3COL
    refine ⟨B, fun x hx => ?_⟩
    obtain ⟨y, n, G, c, rfl, rfl, hc⟩ := (mem_L3COL_iff x).1 hx
    exact ⟨encColoring c,
      fun r hist => (Protocol.proverBounded_iff _ _ _).1 hB _ _ r hist ⟨n, G, c, rfl, rfl, hc⟩,
      fun z => HardcoreBit.uprob_eq_one_of_forall fun r => colProtocol_outV_honest hc z r⟩
  sound := fun x hx P' z => colProtocol_sound hC x hx P' z
  efficientP := colProver_efficient hC.easy ℓ
  boundedP := (colProtocol_proverBounded hC R3COL).imp fun _ h => h.1
  completeWitness := by
    rintro x y ⟨n, G, c, rfl, rfl, hc⟩ z
    exact HardcoreBit.uprob_eq_one_of_forall fun r => colProtocol_outV_honest hc z r

/-- **The `n|E|`-fold [PS10, Protocol 127.5] is an interactive proof for `3COL` with efficient
prover** [PS10, Proposition 127.6, "the probability of successfully cheating in all rounds is
`(1 - 1/|E|)^{n|E|} ≈ e^{-n}`"] (Prop-127.6, Claim-127.h, Claim-125.a).

**Deviation:** `n|E|` iterations inside `4|x|²` fixed moves (D8); the soundness error carries the
edge samplers' failure term `|x|² (1/2)^{|x|}` (D10); the text's "`|E|²` times" is the
protocol's `n|E|`.

**Proof sketch.** Completeness as in `col_efficientProverProofErr`, iteration by iteration
(the verifier's history is `[com_0, opn_0, …]` and the parity bookkeeping of `colProverRep`
/ `colVerifierRep` reproduces one iteration on each coin block, `exec_succ`; the empty
messages beyond `n|E|` iterations are ignored). Soundness with
`ε N := Real.exp (-(Nat.sqrt N)) + N² (1/2)^N + 2⁻¹^N` (strict clause): for `x = encGraph G`
not colourable with `n ≥ 2`, fix the prover's coins, condition on all `n|E|` edge samplers
being uniform (`statClose_sampleEdgeIdx` per block, `StatClose.prod` iterated,
`StatClose.abs_uprob_sub_le_prod`, union cost `n|E| (1/2)^{|x|} ≤ |x|² (1/2)^{|x|}`), and apply
`uprob_col_cheat_le` with `k = n|E|`, `comF i` the prover's commitment of iteration `i` (a
function of the earlier challenges through `exec`) and `opnF i` its opening: the acceptance
probability is at most `(1 - 1/|E|)^{n|E|} ≤ e^{-n}` (`one_sub_inv_pow_mul_le_exp`) with
`n = Nat.sqrt |x|` (`length_encGraph`, `Nat.sqrt_eq`). Negligibility:
`negligible_exp_neg_sqrt_div` with `C = 1`, `Negligible.mul_pow negligible_two_pow_neg 2`,
`negligible_two_pow_neg`, `Negligible.add`. Efficiency: `colProverRep_efficient`,
`colVerifierRep_efficient`. Bounded prover messages (and the bound in the completeness
clause): `colProtocol_proverBounded`. -/
theorem colRep_efficientProverProof {Com : List Bool → List Bool} {ℓ : PolyExpr}
    (hC : Commitment Com ℓ) : EfficientProverProof (colProtocolRep Com ℓ) L3COL R3COL := by
  sorry

/-- The `n|E|`-fold protocol is an interactive proof for `3COL` [PS10, Proposition 127.6]. -/
theorem colRep_interactiveProof {Com : List Bool → List Bool} {ℓ : PolyExpr}
    (hC : Commitment Com ℓ) : InteractiveProof (colProtocolRep Com ℓ) L3COL :=
  (colRep_efficientProverProof hC).toInteractiveProof

end TCSlib.Cryptography

## ===== briefs/pass-shelat/DESIGN.md =====

# FROZEN DESIGN — Pass–shelat Chapters 2–4 computational-model layer and workstream map

Run 1 synthesis (2026-10-27). Inputs: `inventory-ch{2,3,4}.md`, `design-reuse-max.md`,
`design-abstract-interface.md`, `design-faithful-tapes.md`, three judge reports. Output of
this file: (1) the frozen Lean signatures, (2) the final text of the foundation decisions,
(3) the workstream map covering every core inventory item exactly once, (4) the
consolidated list of source errors, (5) the open questions for the maintainer.

**Evidence.** Every signature in §2 is reproduced from
`briefs/pass-shelat/DESIGN-freeze-scratch.lean` (1252 lines, 205 declarations), compiled on
2026-10-27 with `lake env lean` against the worktree: **exit 0, 0 errors, 53 `declaration
uses 'sorry'` warnings**, every sorry being a theorem stub under a stated proof plan (the
inventory of the 53 stubs is in §9). The proved parts are `PolyExpr.eval_*`, `eval_subst`,
`eval_mono`, `eval_le`, `NUPPT.output_spec`, `computesFunInTime`, `polyTimeComputable_output`,
`output_eq_of_computesInTime`, `length_advInput`, `output_ofPolyTime`,
`ofPolyTimeUniform_uniform`, `NUPPT.nonempty`, `invProbOpt_le_invProb`, `invProbOpt_some`,
`hybrid_lemma`, `prfAdv_toOracleAdversary`.

**Verdict adopted.** REUSE-MAXIMAL is the base (all three judges rank it first). The panel's
mandatory repairs are applied (§3) and the recommended grafts are taken (§4): syntactic
`PolyExpr` lengths everywhere, distribution-level samplability, `∀ q` oracle budgets, a
first-mover field and a fixed-alternation execution, literal `[false]` soundness, `≤` advice
length, literal Def 26.1 / Def 69.4 forms next to the `1^n` forms with the bridging lemmas,
abort-form perfect ZK, rejection-sampled permutations and positions, non-vacuity theorems in
`Checks.lean`, and the repaired construction of the repetition lemma. ABSTRACT-INTERFACE's
bundled class and FAITHFULNESS-FIRST's coin tape, pair-form bridges, oracle machines and
`NUPPTSeq` equivalence are **not** on the critical path (the latter two survive as optional
modules with one named admission each).

---

## 1. Foundation decisions D1–D11 (final text for `PassShelatChapter2-4Plan.md`)

D1. **Base and branch.** Branch `cryptography/pass-shelat-ch2-4` from `cryptography/garg-ch1-3`;
    worktree `/Users/dehmelf/Research/tcslib-pass-shelat`. Verification by shell
    `lake build <module>` / `lake env lean <file>` (user-approved deviation from `AGENTS.md`),
    one Lean process at a time.

D2. **Two layers, as in the Garg plan.** Concrete reductions are reused verbatim from
    `TCSlib/Cryptography/{Foundations,OneWayFunctions,HardcoreBit,Pseudorandom}`; the
    asymptotic layer adds machines, negligible functions and closure. Every asymptotic theorem
    is proved as (i) instantiate the concrete reduction at each `n`, (ii) exhibit the reduction
    as a `Complexity.NUPPT` by `NUPPT.ofPolyTime` of a function obtained from the FP calculus of
    `ClassNP/PolyTimePairing.lean` with `NUPPT.polyTimeComputable_output` as a black box, plus
    the two new machine lemmas of D11, (iii) negligible-function arithmetic through
    `not_negligible_iff`. New concrete lemmas go into campaign-owned files, never into the
    frozen Garg files. *Exception* (gate 03a, ruling G3-7a, user 2026-11-05): the general
    helper `negligible_zero` moved from `Asymptotic/Ensembles.lean` into
    `Foundations/Negligible.lean`, full name `TCSlib.Cryptography.negligible_zero` unchanged; its
    copy `negligible_const_zero` (`ZeroKnowledge/Defs.lean`) is left to the duplicate clean-up
    (ruling G3-5).

D3. **Probabilistic machines.** One structure `Complexity.NUPPT` (file
    `TCSlib/Complexity/Randomized/PPT.lean`): a `Turing.FinTM Bool` that halts on **every** input
    `z` within `Ct * (|z| + 1) ^ ct` steps, an explicit coin polynomial `coins : PolyExpr`, an
    advice polynomial `adv : PolyExpr` and an advice function. The single semantic primitive is
    `output z` (the output tape when the budget expires); `output` is `PolyTimeComputable`
    (proved) and every `PolyTimeComputable` function gives an `NUPPT` (`ofPolyTime`, proved).
    A PPT ([PS10, Def 23.4]) is an `NUPPT` with empty advice (`Uniform`; `Complexity.PPT` is the
    subtype). The activation at security parameter `n` on argument `y` with coins `r` is
    `runAt n y r := output ⟨⟨⟨1^n, y⟩, advice n⟩, r⟩` with `r : Fin (coins.eval n) → Bool`; the
    random tape is part of the input, the time bound holds for every coin string
    ([PS10, Def 23.5], worst case), and "`A` computes `f` with probability 1" ([PS10, Def 24.6])
    is `Computes`: equality for every coin string. `Computes` does not require `Uniform`: Def
    24.6 (on the encodings `⟨1^n, y⟩`, which is all `Computes` constrains; gate 03a, round 2,
    R2-1) is the case `A.Uniform ∧ A.Computes f`; for a non-uniform `A` it is the advice
    analogue and holds for uncomputable `f` (advice `[h n]`), so `∃ A, A.Computes f` is not "a
    PPT computes `f`" (gate 03a, finding 1). Honest evaluators ("easy to compute") are
    stated as `PolyTimeComputable` string functions on `⟨1^n, x⟩`. Recorded deviations:
    totality on all inputs (behaviour class unchanged: a machine polynomial-time on well-formed
    inputs is clocked by `timed_universal`; the optional lemma `NUPPT.ofPartial` is not needed
    by any theorem); time measured in the machine-input length (a polynomial in `n + |y|`,
    so the classes coincide); advice and coins indexed by the parameter `n` read from `1^n`
    rather than by the input length (interdefinable in every experiment of the text, and what
    makes one random tape per `n` well-typed for the oracle and interactive layouts).

D4. **Non-uniform PPT** ([PS10, Def 26.8]) in the advice formulation: `advice n` of length
    `≤ adv.eval n`, run on `⟨⟨⟨1^n, y⟩, advice n⟩, r⟩`. The input-length-indexed activation
    `A_{|y|}(y)` of the text is `runLit y r := runAt |y| y r` (the prefix `1^{|y|}` carries no
    information); it is the layout of the literal forms of Def 26.1 and Def 69.4 (D5, D6). The
    machine-sequence formulation (`NUPPTSeq`, with `CodeTM.serialize` size) is an **optional**
    corollary module (`Randomized/Sequence.lean`) with the equivalence
    `nuppt_seq_iff_advice` as one named, non-blocking admission; it is not formalized in the
    core (Deviation recorded in the docstring of `NUPPT`).

D5. **Domains are typed at each parameter.** A function family is
    `FunFamily := ⟨inLen outLen : PolyExpr, f n : (Fin (inLen.eval n) → Bool) → (Fin (outLen.eval n) → Bool)⟩`;
    the textbook `f : {0,1}* → {0,1}*` is `FunFamily.ofString f p` (`inLen = var`; exact for
    length-regular `f`, `ofFn_ofString_f`, otherwise the `false`-padding is lossy). An
    inverter's output is decoded by `decodeFin` as an `inLen n`-bit string and a wrong length is
    a failure (`invProbOpt`, bridged to the concrete `invProb` by `invProbOpt_le_invProb` and
    `invProbOpt_some`). Adversaries receive `1^n` exactly where the text gives it
    (Defs 27.3, 28.4, 75.2, 96.1, …); where the text withholds it (Def 26.1: `A(f(x))`;
    Def 69.4: `D(t)`) the frozen definition is the literal one (`WorstCaseOneWay` with
    `inverterLit`, `Ensemble.IndistLit`), and the `1^n` form (`Ensemble.Indist`) is the headline
    form of the theorems, related by `Indist.toLit` (always) and `IndistLit.toIndist`
    (injective `ℓ`, i.e. every ensemble of the text; for constant `ℓ` the two forms coincide
    as well, by point tests, which is not formalized: gate 03a, note 14). The two are never
    unified silently.

D6. **Ensembles** ([PS10, Def 69.3]) are `Ensemble ℓ := ⟨σ : ℕ → Type, Fintype, X n : σ n → (Fin (ℓ.eval n) → Bool)⟩`
    with arbitrary finite seed types (the uniform ensemble has seeds `Fin (ℓ n) → Bool`, the
    random-function oracle has function tables). "Efficiently samplable" is the predicate
    `Samplable` at the **distribution level**: a polynomial-time sampler from `s.eval n` uniform
    bits whose output law equals `X n` (`StatClose … 0`). Lemma 71.5 is `Indist.push` (image
    under an `NUPPT`, padded to an explicit `ℓ' : PolyExpr`), the multicopy corollary
    `Indist.copies` takes `Samplable X`, `Samplable Y`, and the hybrid lemma is the concrete
    `exists_hybrid_gap`. Deviation: every samplable distribution is dyadic; non-dyadic
    distributions of the text (primes, `Z_q`, permutations) appear only as *ideal* distributions
    in experiments and are approximated by rejection samplers within `StatClose` error (D10).

D7. **Oracle adversaries** ([PS10, Def 96.1]) are next-query machines: an `NUPPT` activated once
    per query on the encoded history of (query, answer) pairs with one random tape per `n`, and
    an explicit query budget `q : PolyExpr` quantified universally in the definition
    (`∀ D q`); `NUPPT.toOracleAdversary n ℓ₁ ℓ₂ (q.eval n)` builds the concrete `QueryTree`
    (`OracleAdversary`), `toOracleAdversary_boundedBy` supplies `BoundedBy q` for
    `ggm_prfAdv_le`/`exists_ggmBits_dist`. No oracle tapes (the library's `OracleTM` is a
    language oracle); the bridge `exists_queryTree` from `OracleTM`-level machines is an optional
    module. Deviation recorded.

D8. **Interactive protocols** ([PS10, §4.4]). A `Strategy` is a next-message function
    `next x z r received` with an explicit random-tape polynomial `coins : PolyExpr`; its value
    on the complete history is the party's output. A `Protocol` is `⟨P, V, rounds, verifierFirst⟩`
    where `rounds : PolyExpr` is the number of messages exchanged and `verifierFirst` the first
    mover (GNI: verifier; GI, 3COL: prover). `exec` is the fixed alternation of
    `rounds.eval |x|` moves; the verifier's verdict is `V.next` on the complete history
    (`outV`), so it is always defined and the literal `out_V = 0` is `outV = [false]`.
    `Strategy.Efficient` = one activation of a uniform `NUPPT` at parameter `|x|` on
    `⟨⟨x, z⟩, messages⟩` with the whole random tape (time polynomial in the total input,
    Deviation from the text's `t(|x|)`). Soundness quantifies `∃ ε` before `∀ x ∉ L ∀ P' ∀ z`
    over arbitrary strategies `P'` (unbounded provers; polynomial coin tapes lose nothing by
    averaging). Zero knowledge: `∀ V* efficient, ∃ S uniform NUPPT, ∀ Lz D, ∃ ε, ∀ x y z`,
    `R x y → |z| ≤ Lz.eval |x| → distAdv ≤ ε |x|` — strict PPT simulators, auxiliary inputs
    bounded by an arbitrary polynomial quantified after the simulator (the class a `t(|x|)`-time
    verifier can read; required for the non-uniform reduction of Prop 128.8). Statistical ZK
    (`StatZK δ`, sup-over-test-sets `StatClose`), `PerfectZK := StatZK 0` and Goldreich's abort
    form `PerfectZKAbort` are stated; GI and 3COL are proved statistically (truncated
    simulators, rejection-sampled permutations). Deviations: fixed number of moves (a halting
    party is modelled as sending `[]`; all protocols of the text are fixed-round), strict
    simulators, statistical instead of perfect ZK, `|z|` polynomially bounded.
    **Erratum (2026-11-06, gate 03e round 2, finding 1, and gate 03g, finding 6; the frozen text
    above is unchanged).** Only GI is proved statistically (`gi_statZK`: `StatZK` with
    negligible δ, truncated simulator, rejection-sampled permutations). 3COL is proved
    computationally ZK (`col_zk`, by `Commitment.multiHiding`; the truncation and sampling errors
    are statistical terms inside a computational bound), its simulator stopping after `n|E|`
    attempts as the text's does. It cannot be statistical: with a perfectly binding commitment
    the real views of two colourings outside one colour-permutation orbit are statistically far
    apart, and the simulator does not see the witness.

D9. **Lengths are syntax.** Every length or budget that depends on the parameter (coins,
    advice, input/output lengths of families and ensembles, stretch, query budgets, rounds,
    auxiliary-input bounds) is a `Complexity.PolyExpr` (`const/var/add/mul/pow`, `eval`,
    `subst`, `eval_subst`, `eval_mono`, `eval_le`, `normal C c = C(n+1)^c`). Time bounds of
    machines stay in the normal form `Ct (n+1)^ct` (the shape of `PolyTimeComputable`).
    `polyTimeComputable_unaryPoly p : x ↦ 1^{p(|x|)}` is proved by induction with the new
    primitive `computesFunInTime_unaryMul`, never through the repetition lemma. Abstract
    `ℕ → ℕ` lengths appear only as hypotheses of theorems with a `PolyExpr` majorant
    (`exists_reparam_advice`), never in a definition.

D10. **Sampling device.** `TCSlib/Cryptography/Asymptotic/Sampling.lean` owns
    `StatClose` (with `distAdv_le_of_statClose`, `StatClose.prod`, `StatClose.map`),
    `rejectionSample m k T` (`T` trials of `k` bits; uniform on `Fin m` conditioned on `some`,
    failure `(1 - m/2^k)^T`) and `permFromCoins` (Fisher–Yates with rejection-sampled offsets).
    Experiments use ideal uniform distributions (as the text); honest parties and reductions
    sample by rejection with `2^{-n}`-close laws and the theorems carry the explicit
    statistical term. This one device serves Theorem 35.1's uniform position (`m = 2nq(n)` is
    kept literal), SamplePrime/`Z_q`/`Z_N^*`/`QR_N` (Q3), and Chapter 4's permutations, edges
    and colour permutations (DQ1 option A at the concrete level).

D11. **Admissions policy.** `Complexity.polyTimeComputable_iterateFind`
    (`Randomized/Repetition.lean`) is the single machine lemma that may remain admitted at the
    end of run 4; every theorem that repeats an adversary depends on it and on nothing else
    admitted. The two new primitives (`pairSplitAt`, `unaryMul`) are built in the `Build/`
    style in the campaign-owned `Randomized/Primitives.lean`. `NUPPTSeq`'s equivalence,
    `NUPPT.ofPartial` and `exists_queryTree` are optional modules, each with its own named
    admission, off every critical path. Number-theoretic machine facts (binary `mul`,
    `add`, `sub`, `divMod`, `xgcd`, `modExp`, comparison, bit length, primality; run-3
    audit P7-1 added `add`/`sub`/bit length) are explicit hypotheses
    (`Candidates/Arithmetic.lean` bundle), never axioms; `#print axioms` of every headline must
    show `[propext, Classical.choice, Quot.sound]` plus, at most, the admissions named here.
    *Status* (gate 03a, note 20; decision log 2026-10-28): run 3b proved
    `polyTimeComputable_iterateFind`, so the permitted machine admission is unused.
    `NUPPT.ofPartial` was never written; the only machine-layer `sorry` is the optional bridge
    `NUPPT.decides_of_decidesWithAdviceInTime` (`Randomized/NonUniform.lean`), whose sketch does
    `ofPartial`'s clocking inline. It is the named admission of that optional module (open
    question 5, ruled outside the core on 2026-10-27).

---

## 2. Frozen Lean signatures

All code below is verbatim from `DESIGN-freeze-scratch.lean` (compiled). Namespaces:
`Complexity` for the machine layer (`open Turing`), `TCSlib.Cryptography` for everything
else (`open Complexity Turing`). Each file's `## References` lists `[PS10]`, `[Gar26]`, `[AB09]`.
Docstrings in the skeleton must begin with the natural-language statement, then the
`[PS10, …]` citation, then the Deviation notes quoted in §5.

### 2.1 `TCSlib/Complexity/Randomized/PolyExpr.lean`

```lean
namespace Complexity

inductive PolyExpr : Type
  | const : ℕ → PolyExpr
  | var : PolyExpr
  | add : PolyExpr → PolyExpr → PolyExpr
  | mul : PolyExpr → PolyExpr → PolyExpr
  | pow : PolyExpr → ℕ → PolyExpr
  deriving DecidableEq, Repr

namespace PolyExpr
def eval : PolyExpr → ℕ → ℕ                       -- structural
def subst : PolyExpr → PolyExpr → PolyExpr          -- p[q/n]
def normal (C c : ℕ) : PolyExpr := mul (const C) (pow (add var (const 1)) c)
@[simp] theorem eval_const (c n : ℕ) : (const c).eval n = c := rfl       -- likewise eval_var/add/mul/pow
theorem eval_normal (C c n : ℕ) : (normal C c).eval n = C * (n + 1) ^ c := rfl
theorem eval_subst (p q : PolyExpr) (n : ℕ) : (p.subst q).eval n = p.eval (q.eval n)   -- proved
theorem eval_mono (p : PolyExpr) : Monotone p.eval                                       -- proved
theorem eval_le (p : PolyExpr) : ∃ C c : ℕ, ∀ n, p.eval n ≤ C * (n + 1) ^ c               -- proved
end PolyExpr

/-- `1^{p(|x|)}` is polynomial-time computable. Proof: induction on `p`; `const` =
`polyTimeComputable_const`, `var` = `polyTimeComputable_unary`, `add` = `PolyTimeComputable.append`,
`mul` = `computesFunInTime_unaryMul` (§2.4) composed with `PolyTimeComputable.pairEncode` of the
two unary strings, `pow p c` = induction on `c` through `mul`. -/
theorem polyTimeComputable_unaryPoly (p : PolyExpr) :
    PolyTimeComputable fun x => List.replicate (p.eval x.length) true
end Complexity
```

### 2.2 `TCSlib/Complexity/Randomized/PPT.lean` — the structure and its primitive

```lean
namespace Complexity
open Turing

/-- NUPPT [PS10, Def 26.8, advice formulation]; PPT [PS10, Def 23.4] = `Uniform`. -/
structure NUPPT where
  M : FinTM Bool
  Ct : ℕ
  ct : ℕ                                  -- M halts within Ct (|z|+1)^ct on EVERY input z
  coins : PolyExpr                        -- coins.eval n uniform coins at parameter n
  adv : PolyExpr                          -- |advice n| ≤ adv.eval n
  advice : ℕ → List Bool
  advice_length : ∀ n, (advice n).length ≤ adv.eval n
  halts : ∀ z : List Bool, ∃ out : List Bool, M.ComputesInTime z out (Ct * (z.length + 1) ^ ct)

namespace NUPPT
variable (A : NUPPT)
def timeBound (m : ℕ) : ℕ := A.Ct * (m + 1) ^ A.ct
def coinLen (n : ℕ) : ℕ := A.coins.eval n
def adviceLen (n : ℕ) : ℕ := A.adv.eval n
def output (z : List Bool) : List Bool :=
  (A.M.tm.runFrom (A.M.tm.initCfg z) (A.timeBound z.length)).output
theorem output_spec (z) : A.M.ComputesInTime z (A.output z) (A.timeBound z.length)      -- proved
theorem computesFunInTime : A.M.ComputesFunInTime A.output A.timeBound                   -- proved
theorem polyTimeComputable_output : PolyTimeComputable A.output                          -- proved
theorem output_eq_of_computesInTime {z w t} (h : A.M.ComputesInTime z w t) : A.output z = w  -- proved
def advInput (n : ℕ) (y : List Bool) : List Bool := pairEncode (List.replicate n true) y   -- ⟨1^n, y⟩
theorem length_advInput (n y) : (advInput n y).length = 2 * n + 2 + y.length                -- proved
abbrev Coins (n : ℕ) : Type := Fin (A.coinLen n) → Bool
def runAt (n : ℕ) (y : List Bool) (r : A.Coins n) : List Bool :=
  A.output (pairEncode (pairEncode (advInput n y) (A.advice n)) (List.ofFn r))
def runAtL (n : ℕ) (y r : List Bool) : List Bool :=
  A.output (pairEncode (pairEncode (advInput n y) (A.advice n)) r)
theorem runAt_eq (n y r) : A.runAt n y r = A.runAtL n y (List.ofFn r) := rfl
/-- `A_{|y|}(y)` of [PS10, Def 26.8]: activation at the input length. -/
def runLit (y : List Bool) (r : A.Coins y.length) : List Bool := A.runAt y.length y r
def Uniform : Prop := ∀ n, A.advice n = []
/-- [PS10, Def 24.6]. -/
def Computes (f : List Bool → List Bool) : Prop := ∀ n y (r : A.Coins n), A.runAt n y r = f (advInput n y)
noncomputable def ofPolyTime {f} (hf : PolyTimeComputable f) (coins adv : PolyExpr)
    (advice : ℕ → List Bool) (hα : ∀ n, (advice n).length ≤ adv.eval n) : NUPPT
theorem output_ofPolyTime … : (ofPolyTime hf coins adv advice hα).output = f                -- proved
noncomputable def ofPolyTimeUniform {f} (hf : PolyTimeComputable f) (coins : PolyExpr) : NUPPT
theorem ofPolyTimeUniform_uniform … : (ofPolyTimeUniform hf coins).Uniform                  -- proved
end NUPPT

def PPT : Type 1 := {A : NUPPT // A.Uniform}
theorem NUPPT.nonempty : Nonempty NUPPT                                                       -- proved
end Complexity
```

### 2.3 `TCSlib/Complexity/Randomized/NonUniform.lean` — Def 26.8 material

Contents: the docstring of Def 26.8 (both formulations, the advice one frozen), `runLit` lemmas
(`runLit_eq_runAt`), `Uniform` lemmas (`ofPolyTime` with empty advice; `Uniform.advice_eq`),
the sanity bridge to the library's advice machines, and the optional `NUPPTSeq`:

```lean
/-- Optional sanity bridge (needs the clocking construction `NUPPT.ofPartial`; off the
critical path). -/
theorem NUPPT.decides_of_decidesWithAdviceInTime (M : FinTM Bool) (L : Language Bool)
    (α : ℕ → List Bool) (C c Ca ca : ℕ) (hα : ∀ n, (α n).length = Ca * (n + 1) ^ ca)
    (h : M.DecidesWithAdviceInTime L α (fun n => C * (n + 1) ^ c)) :
    ∃ A : NUPPT, ∀ x (r : A.Coins x.length),
      A.runAt x.length x r = [MultiTapeTM.indicator (L : Set (List Bool)) x]
```

Optional module `Randomized/Sequence.lean` (owner: machine-core, deferred): `NUPPTSeq`
(FAITHFUL §2.1 verbatim with `CodeTM.serialize`) and `nuppt_seq_iff_advice` (⇒ conditional on
`PolyBound c.canonizerTime` as in `TMSAT_mem_NP`; ⇐ via the hard-wiring construction), one
named admission; no theorem of chapters 2–4 depends on it.

### 2.4 `TCSlib/Complexity/Randomized/Primitives.lean` — two new machines

```lean
namespace Turing.FinTM
/-- NEW: `⟨u, b⟩ ↦ ⟨b.take |u|, b.drop |u|⟩` (coin splitting at a unary length). -/
theorem computesFunInTime_pairSplitAt :
    ∃ (M : FinTM Bool) (c : ℕ), M.ComputesFunInTime
      (fun z => match pairDecode z with
        | some (u, b) => pairEncode (b.take u.length) (b.drop u.length) | none => [])
      fun n => c * (n + 1)
/-- NEW: unary multiplication `⟨1^a, 1^b⟩ ↦ 1^{a·b}`. -/
theorem computesFunInTime_unaryMul :
    ∃ (M : FinTM Bool) (c : ℕ), M.ComputesFunInTime
      (fun z => match pairDecode z with
        | some (u, v) => List.replicate (u.length * v.length) true | none => [])
      fun n => c * (n + 1) ^ 2
end Turing.FinTM

theorem Complexity.polyTimeComputable_pairTakePoly (p : PolyExpr) :
    PolyTimeComputable fun z => (pairSndD z).take (p.eval (pairFstD z).length)
theorem Complexity.polyTimeComputable_pairDropPoly (p : PolyExpr) :
    PolyTimeComputable fun z => (pairSndD z).drop (p.eval (pairFstD z).length)
```

Construction sketches. `pairSplitAt`: the buffered aligned parser of `computesFunInTime_pairFst`
(reads the doubled prefix `u` onto a work tape without emitting), then a copy scan of `b` that
emits the doubled bit `bb` while the work head walks across `u`, then the separator `01`, then
the remainder verbatim; linear, two work tapes (≈ 300–500 lines). `unaryMul`: copy `1^b` onto a
work tape (the parser of `pairSnd`), then for each token of `u` replay the work tape onto the
output (`emitAction`-style) and rewind; `O(ab + a + b)` steps, ≈ 300–500 lines. Fallback for
`unaryMul` only: an instance of `polyTimeComputable_iterateEmit` (state `⟨1^{rest}, 1^b⟩`,
`emit = pairSndD`, step pops one token) — acceptable only after `iterateFind` is closed.
`pairTakePoly p` = `pairFstD ∘ pairSplitAt ∘ pairEncode (unaryPoly p ∘ pairFstD) pairSndD`
by `polyTimeComputable_of_linear`, `PolyTimeComputable.pairEncode`, `.comp`.

**As-built note (2026-11-05, gate 03l; the sketch above is unchanged).** The `pairSplitAt`
machine (`Randomized/Build/PairSplit.lean`) uses one work tape, not two: the parser stores `u`,
and the copy scan of `b` doubles each bit while the work head walks across the stored `u`. Its
buffered aligned parser is public (`Turing.PairParse`) and is shared by the `unaryMul` machine
(`Randomized/Build/UnaryMul.lean`), which stores `u` and replays it once per symbol of `v`.

### 2.5 `TCSlib/Complexity/Randomized/Closure.lean` — closure catalogue

Every lemma is `NUPPT.ofPolyTime` of an FP function built from
`A.polyTimeComputable_output`, `PolyTimeComputable.comp/.pairEncode/.append`,
`polyTimeComputable_const/_prepend/_unary/_pairFstD/_pairSndD/_iterate_pairFstD/_pairConcat/_pairSwap/_ite/_and/_lenLe/_lenEq`,
`polyTimeComputable_unaryPoly` and `pairTakePoly/DropPoly`; the equation is `output_ofPolyTime`
+ `pairDecode_pairEncode` + `funext`. `Uniform` is preserved whenever the advice is `A.advice`
or `[]`.

```lean
theorem NUPPT.exists_comp (A : NUPPT) {pre post} (hpre : PolyTimeComputable pre) (hpost : PolyTimeComputable post) :
    ∃ B : NUPPT, B.coins = A.coins ∧ B.adv = A.adv ∧ B.advice = A.advice ∧
      ∀ n y r, B.runAtL n y r = post (A.runAtL n (pre y) r)
theorem NUPPT.exists_reparam (A : NUPPT) (p : PolyExpr) :                        -- n ↦ p(n), uniform
    ∃ B : NUPPT, B.coins = A.coins.subst p ∧ (A.Uniform → B.Uniform) ∧
      ∀ n y r, B.runAtL n y r = A.runAtL (p.eval n) y r
theorem NUPPT.exists_reparam_advice (A : NUPPT) (φ : ℕ → ℕ) (p : PolyExpr) (hφ : ∀ n, φ n ≤ p.eval n) :
    ∃ B : NUPPT, B.coins = A.coins.subst p ∧
      ∀ n y r, B.runAtL n y r = A.runAtL (φ n) y (r.take (A.coinLen (φ n)))      -- 1^{φ n}, advice (φ n) hard-wired
theorem NUPPT.exists_withAdvice (A : NUPPT) (β : ℕ → List Bool) (b : PolyExpr) (hβ : ∀ n, (β n).length ≤ b.eval n) :
    ∃ B : NUPPT, B.coins = A.coins ∧ ∀ n y r, B.runAtL n y r = A.runAtL n (pairEncode y (β n)) r
theorem NUPPT.exists_split (A : NUPPT) (p : PolyExpr) :                          -- extra coins as data
    ∃ B : NUPPT, B.coins = .add p A.coins ∧ B.advice = A.advice ∧
      ∀ n y r, B.runAtL n y r = A.runAtL n (pairEncode y (r.take (p.eval n))) (r.drop (p.eval n))
theorem NUPPT.exists_seq (A B : NUPPT) :                                          -- sunglass composition
    ∃ C : NUPPT, C.coins = .add A.coins B.coins ∧ (A.Uniform → B.Uniform → C.Uniform) ∧
      ∀ n y r, C.runAtL n y r =
        B.runAtL n (pairEncode y (A.runAtL n y (r.take (A.coinLen n)))) (r.drop (A.coinLen n))
```

| Lemma | Raw function on `⟨⟨⟨1^n, y⟩, α⟩, r⟩` | Supplier |
| --- | --- | --- |
| `exists_comp` | re-pair with `pre y`, apply `A.output`, apply `post` | `pairFstD`, `pairSndD`, `pairEncode`, `comp`, `A.polyTimeComputable_output` |
| `exists_reparam p` | advice `A.advice (p n)` (length `A.adv.subst p` by `eval_subst`); machine replaces `1^n` by `1^{p n}` (`unaryPoly p` on `pairFstD (pairFstD (pairFstD z))`) and re-pairs | `unaryPoly`, `pairEncode`, `comp` |
| `exists_reparam_advice φ p` | advice `⟨1^{φ n}, A.advice (φ n)⟩` (length `2p+2+A.adv.subst p`); coins `A.coins.subst p ≥ A.coins.eval (φ n)` (`eval_mono`); the machine cuts `1^{A.coins.eval (φ n)}` coins (`unaryPoly A.coins` on the advice's `1^{φ n}`, then `pairSplitAt`) | `pairSplitAt`, `unaryPoly`, `eval_mono` |
| `exists_withAdvice` | advice `⟨A.advice n, β n⟩`, length `2·A.adv + 2 + b`; re-pair `y` with `β n` | pairing calculus |
| `exists_split p` | cut `r` at `1^{p n}`; pass the head as data | `pairTakePoly p`, `pairDropPoly p` |
| `exists_seq` | cut at `1^{A.coinLen n}`; run `A.output` on the first part, then `B.output` on `⟨⟨⟨1^n, ⟨y, a⟩⟩, α_B⟩, r₂⟩`; advice `⟨α_A, α_B⟩` | both outputs, `pairTakePoly/DropPoly`, pairing |
| negation / `[true]` normalisation | `computesFunInTime_ifEq` via `exists_comp` | Composition.lean |
| branching | FP-level `polyTimeComputable_ite`, `computesFunInTime_cond` | PolyTimePairing, Build/Wrappers |
| length tests | `polyTimeComputable_lenEq/_lenLe` | PolyTimePairing |
| loop fuel | `computesFunInTime_polyBits` (normal form) and `unaryPoly` + `computesFunInTime_lengthBits` (general `PolyExpr`) | Build/Primitives |

### 2.6 `TCSlib/Complexity/Randomized/Repetition.lean` — the load-bearing lemma, repaired

```lean
theorem polyTimeComputable_iterateFind {g} (hg : PolyTimeComputable g)
    {acc : List Bool → Bool} (hacc : PolyTimeComputable fun s => [acc s])
    {out} (hout : PolyTimeComputable out) (R P : PolyExpr)
    (horbit : ∀ x i, i ≤ R.eval x.length → (g^[i] x).length ≤ P.eval x.length) :
    PolyTimeComputable fun x =>
      match (List.range (R.eval x.length + 1)).find? (fun i => acc (g^[i] x)) with
      | some i => out (g^[i] x) | none => []
theorem polyTimeComputable_iterate {g} (hg) (R P) (horbit) : PolyTimeComputable fun x => g^[R.eval x.length] x
theorem polyTimeComputable_iterateEmit {g emit} (hg) (hemit) (R P) (horbit) :
    PolyTimeComputable fun x => (List.range (R.eval x.length + 1)).flatMap fun i => emit (g^[i] x)
theorem polyTimeComputable_majority : PolyTimeComputable fun w => [decide (w.length < 2 * w.count true)]
theorem polyTimeComputable_pairXor : PolyTimeComputable fun z => List.zipWith xor (pairFstD z) (pairSndD z)
theorem polyTimeComputable_pairEq : PolyTimeComputable fun z => [decide (pairFstD z = pairSndD z)]
theorem polyTimeComputable_blockMap (b : PolyExpr) {g} (hg) :
    PolyTimeComputable fun z => (List.range ((pairSndD z).length / b.eval (pairFstD z).length)).flatMap fun i =>
      g (((pairSndD z).drop (i * b.eval (pairFstD z).length)).take (b.eval (pairFstD z).length))
```

**Construction of `iterateFind` (instance of `exists_loopFindTM`, Loop.lean:2633), with the
three panel repairs built in.**

1. *State word carries the input.* `s0 x := pairEncode x x` (the second component is the
   current orbit point). Loop data: `stepF x w := if |pairSndD w| ≤ P|x| then pairEncode x (g (pairSndD w)) else w`
   (**length-guarded**), `acceptF x w := acc (pairSndD w)`, `out x w := out (pairSndD w)`,
   `Inv x w := pairFstD w = x ∧ (pairSndD w).length ≤ P.eval x.length`. `hInv0` is
   `pairDecode_pairEncode`; `hInvStep` holds because the guard fixes the state once the bound
   is exceeded and otherwise `|g s| ≤ …` is **not** needed: the guarded step keeps the second
   component unchanged when it is already too long, so `Inv` is closed under `stepF` for every
   `w` (refutation J1-7/J2-15/J3-5). On the orbit `i ≤ R|x|`, `horbit` shows the guard is never
   taken, so `(stepF x)^[i] (s0 x) = pairEncode x (g^[i] x)` and the `find?` of the conclusion
   is the statement's (a 40-line pure lemma `iterate_guard_eq`).
2. *Modules.* From `hg`, `hacc`, `hout` build three clean-call modules over the state word:
   `C₁ := exists_installCallTM` for `w ↦ pairEncode [acc (pairSndD w)] w` (verdict as the first
   cell of the installed word: `pairEncode [b] w = [b, b, false, true] ++ w`, no scan needed),
   `C₂ := exists_installCallTM` for `w ↦ stepF' (pairSndD w)` where `stepF'` is the guarded step
   on the pair (FP: `polyTimeComputable_ite` with `polyTimeComputable_lenLe` on
   `⟨pairSndD w, 1^{P|pairFstD w|}⟩` by `unaryPoly P ∘ pairFstD`), `C₃ := exists_emitCallTM` for
   `w ↦ out (pairSndD (pairSndD w))`. Each module promises first-visit-to-exit from the clean
   seam over an arbitrary native input (Loop.lean:5645/5691) and `0 < C.k`.
3. *Gluing without overriding `exit`.* Body state `Unit ⊕ (C₁.State ⊕ C₂.State ⊕ C₃.State) ⊕ Fin 3`;
   the tape counts are equalised with idle tapes (`leftAction`/`leftCfg_run`, Simulation.lean).
   **The anchor is the fresh state `inl ()`** whose transition is stationary into `C₁.entry`
   (refutation J2-16/J3-6: no module-internal state is the anchor). The module tables are
   copied with every transition *targeting* `Cᵢ.exit` **redirected** to a fresh branch state
   (`inr (inr k)`), so the module's own table at `exit` is never consulted and the case
   `entry = exit` is harmless: the first positive visit of `exit` promised by the contract is
   exactly the first entry into the branch state, with the clean seam on the tapes. Branch
   states: after `C₁`, read tape-0 cell 0 — `true` → `C₃.entry`, `false` → `C₂.entry`; after
   `C₂` → anchor (one stationary step); after `C₃` → halt.
4. *`hstart`.* From `initCfg x`, install `s0 x = pairEncode x x` on tape 0: this is one more
   `exists_installCallTM` module for `pairDup` (`computesFunInTime_pairDup`) applied to the
   argument word `x` itself, which must first be on tape 0: a one-state copy scan of the native
   input onto tape 0 plus `timed_rewind` (≈ 100 lines; precedent: the startup phases of
   `computesFunInTime_splitSolveWith`). No anchor visit before the seam.
5. *`hround`.* From `Cfg.ofWords anchor (stateWord K w)` with `Inv x w`: one step into
   `C₁.entry`; `C₁` to its first exit (`t₁ ≤ c₁ (T_acc(|w|) + 2|w| + 5)`), branch; accepting
   clause: `C₃` to its first exit emitting `out (pairSndD w)` and halt; advancing clause: `C₂`
   to its first exit installing `stepF x w`, one step to the anchor. Anchor exclusion inside
   the round is syntactic (the anchor is `inl ()`, entered only from the post-`C₂` branch
   state). Budget `T n := c (T_g(Q n) + T_acc(Q n) + T_out(Q n) + Q n + 8)` with
   `Q n := 2 n + 2 + P.eval n + 4` (length of the state word), a normal-form majorant by
   `eval_le`.
6. *Fuel.* `hF` from `computesFunInTime_polyBits` for a normal-form majorant of `R`, or
   `unaryPoly R` + `computesFunInTime_lengthBits` for exact `R` (the `find?` range must be
   exactly `R|x| + 1`: use the exact form).
7. *Conclusion.* `exists_loopFindTM` gives `E` within `c (T n + 1)(R n + 2)`; package as
   `PolyTimeComputable`. `iterate` threads a unary counter in the state
   (`acc := lenEq cnt 1^{R|x|}` against `unaryPoly R` of the retained input);
   `iterateEmit` threads an accumulator; the derived string functions are instances
   (REUSE-MAX §7.4, unchanged).

Estimated size 1 200–1 800 lines; private precedent for the module gluing: `satClean_install`,
`satStopTM`, `sat_run_agree` in `ClassNP/SAT.lean` (private copies, not edits). If the lemma is
not closed in run 4 it is the single named admission of D11.

**As-built erratum (2026-11-05, gate 03l, minor 2; the frozen text above is unchanged).** The
machine of `polyTimeComputable_iterateFind` (`Randomized/Build/IterateFind.lean`, with
`Randomized/Build/IterateFindHost.lean` and the public host `TuringMachine/Build/ModuleHost.lean`)
departs from steps 1–5 and 7 as follows. The frozen signatures and decisions are unchanged.
- *Step 1: the guard and the invariant.* The guard tests the **new** point:
  `stepF x w := if |g (pairSndD w)| ≤ P|x| then pairEncode x (g (pairSndD w)) else w`. The guard
  on the old length written above does not close `Inv`: for `x = []`, `P = var` and
  `g s = true :: s`, the word `⟨[], []⟩` satisfies `Inv`, passes the guard `0 ≤ 0`, and steps to
  `⟨[], [true]⟩`, which does not. The machine's invariant is the actual-pair invariant
  `Inv x w := ∃ s, w = pairEncode x s ∧ |s| ≤ P|x|`, which, unlike `pairFstD w = x ∧ …`, excludes
  malformed words and gives the length bound `|w| ≤ 2|x| + 2 + P|x|` that the budget needs.
  (`Repetition.lean`'s `guardedStep` is the same step; its `LoopInv` is the pure invariant above,
  not the machine's.)
- *Steps 2–3: the gluing.* No transition is redirected. A release flag halts each clean-call
  module one silent step after its first positive exit, and the run is cut at its first halt
  (the clean-module contract `Turing.ModuleHost.Clean`, `clean_install`, `clean_emit`). The
  modules are padded to a common bank of tapes and run in one finite host with states
  `Fin 3 ⊕ Σ i, (M i).State` over five modules (copier, startup install `x ↦ ⟨x, x⟩`, verdict
  install, step install, payload emit): the anchor `inl 0`, the branch `inl 1` and the halt
  `inl 2`. This host is now the public clean-module host `Turing.ModuleHost.hostTM`
  (`machine-library-design.md` §14, row H14), harvested on 2026-11-05 from `ClassNP/SAT.lean`'s
  private module layer and this machine's copy of it.
- *Step 4: the startup.* The input is copied onto tape 0 by a two-state copier (`copyTM`: copy and
  turn, then rewind both heads), not by a one-state scan and `timed_rewind`.
- *Step 5: the budget.* Every request has length at most `2n + 6 + P n`, and the common budget is
  `T n = A·(2n + 7 + P n)^D` (`IterateFind.lean`), with `A` and `D` collected from the modules'
  budgets and the fuel machine.
- *Step 7.* `iterate`'s counter test is `R|x| ≤ |cnt|` (`StateLoop.IterLoop.acc`), not `lenEq`.

### 2.7 `TCSlib/Cryptography/Asymptotic/Sampling.lean`

```lean
def StatClose {σ τ γ} [Fintype σ] [Fintype τ] (X : σ → γ) (Y : τ → γ) (δ : ℝ) : Prop :=
  ∀ T : γ → Prop, |uprob (fun s => T (X s)) - uprob (fun t => T (Y t))| ≤ δ
theorem distAdv_le_of_statClose … (h : StatClose X Y δ) (D : γ → ρ → Bool) : distAdv X Y D ≤ δ
theorem StatClose.prod … (h : StatClose X X' δ) (h' : StatClose Y Y' δ') :
    StatClose (fun z : σ × σ' => (X z.1, Y z.2)) (fun z : τ × τ' => (X' z.1, Y' z.2)) (δ + δ')
theorem StatClose.map … (h : StatClose X Y δ) (g : γ → γ') : StatClose (fun s => g (X s)) (fun t => g (Y t)) δ
def bitsToNat {k : ℕ} (b : Fin k → Bool) : ℕ
def uniformFromBits (m k : ℕ) (b : Fin k → Bool) : Option (Fin m)
def rejectionSample (m k T : ℕ) (b : Fin T → Fin k → Bool) : Option (Fin m)
theorem rejectionSample_uniform_of_some (m k T) (hm : 0 < m) (hk : m ≤ 2 ^ k) (i j : Fin m) :
    uprob (fun b => rejectionSample m k T b = some i) = uprob (fun b => rejectionSample m k T b = some j)
theorem uprob_rejectionSample_none (m k T) (hm) (hk) :
    uprob (fun b => rejectionSample m k T b = none) = (1 - (m : ℝ) / 2 ^ k) ^ T
theorem statClose_rejectionSample (m k T) (hm) (hk) (d : Fin m) :
    StatClose (fun b => (rejectionSample m k T b).getD d) (id : Fin m → Fin m) ((1 - (m : ℝ) / 2 ^ k) ^ T)
```

**Run-3 repair (audit P2-1, pack P2).** `uprob_permFromCoins_none_le` is stated with the
provable bound `n * (1 - 1/2^k)^T` (the frozen `n (1/2)^T` is false: the last position has
range `1` and fails with probability `(1 - 1/2^k)^T`). The permutation section moved to
`Asymptotic/Permutations.lean` (file-size limit), which also owns the campaign parameters and
the closed form:
```lean
def permBits (n : ℕ) : ℕ := Nat.size n            -- n ≤ 2^k ≤ 2n
def permTrials (n : ℕ) : ℕ := 2 * n * n
theorem statClose_permFromCoins (n k T) (hk : n ≤ 2 ^ k) (d : Equiv.Perm (Fin n)) :
    StatClose (fun b => (permFromCoins n k T b).getD d) id (n * (1 - 1 / 2 ^ k : ℝ) ^ T)
theorem uprob_permFromCoins_none_le_two_pow (n) :
    uprob (fun b => permFromCoins n (permBits n) (permTrials n) b = none) ≤ n * (2 : ℝ)⁻¹ ^ n
theorem statClose_permFromCoins_two_pow (n) (d) :
    StatClose (fun b => (permFromCoins n (permBits n) (permTrials n) b).getD d) id (n * (2 : ℝ)⁻¹ ^ n)
```
with the general `statClose_getD_of_uniform_of_some` (a sampler uniform conditioned on
success, made total by a default, is `StatClose` to uniform within its failure probability),
`StatClose.comp_pushesUniform` and `one_sub_inv_pow_le_half` (`(1 - 1/m)^m ≤ 1/2`, Bernoulli)
in `Sampling.lean`; all proved except `permFromCoins_uniform_of_some` (fill).

Proof sources: `distAdv_le_of_statClose` transposes `abs_sum_sub_le_statDist`'s argument
(average over the distinguisher's coins; each coin string is one test set; `uprob_prod`);
`StatClose.prod` by `uprob_prod` (Fubini) and the triangle inequality; the rejection lemmas by
`uprob_prod` over trials, `OneWay.uprob_pi_forall` for the all-fail event, and the bijection
`bitsToNat : (Fin k → Bool) ≃ Fin (2^k)` (`finFunctionFinEquiv`) for uniformity of one trial.
This file also hosts the ch. 2 concrete lemmas C4 (`first_hit_uniform` = `rejectionSample_uniform_of_some`),
C5 (`pushesUniform_of_card_fiber`) and C10 (statistical switch = `StatClose.map` + `distAdv_le_of_statClose`).

### 2.8 `TCSlib/Cryptography/Asymptotic/Adversary.lean`

```lean
def decodeFin (ℓ : ℕ) (w : List Bool) : Option (Fin ℓ → Bool)       -- wrong length = failure (D5)
def padFin (ℓ : ℕ) (w : List Bool) : Fin ℓ → Bool                   -- pad/truncate (samplers)
def Complexity.NUPPT.inverter (A : NUPPT) (n ℓ m : ℕ) : (Fin m → Bool) → A.Coins n → Option (Fin ℓ → Bool)
def Complexity.NUPPT.inverterLit (A : NUPPT) (ℓ m : ℕ) : (Fin m → Bool) → A.Coins m → Option (Fin ℓ → Bool)
def Complexity.NUPPT.distinguisher (A : NUPPT) (n m : ℕ) : (Fin m → Bool) → A.Coins n → Bool
def Complexity.NUPPT.distinguisherL (A : NUPPT) (n : ℕ) : List Bool → A.Coins n → Bool
def Complexity.NUPPT.predictor (A : NUPPT) (n m : ℕ) : (Fin m → Bool) → A.Coins n → Bool
noncomputable def invProbOpt {α β ρ} [Fintype α] [Fintype ρ] (f : α → β) (A : β → ρ → Option α) : ℝ
theorem invProbOpt_le_invProb [Inhabited α] (f) (A) : invProbOpt f A ≤ invProb f (fun y r => (A y r).getD default)  -- proved
theorem invProbOpt_some (f) (A : β → ρ → α) : invProbOpt f (fun y r => some (A y r)) = invProb f A           -- proved
```

### 2.9 `TCSlib/Cryptography/Asymptotic/OneWay.lean`

```lean
structure FunFamily where
  inLen : PolyExpr
  outLen : PolyExpr
  f : ∀ n, (Fin (inLen.eval n) → Bool) → (Fin (outLen.eval n) → Bool)

namespace FunFamily
def Easy (𝓕 : FunFamily) : Prop :=                                         -- [26.1(1), 27.3(1)]
  ∃ F, PolyTimeComputable F ∧ ∀ n (x : Fin (𝓕.inLen.eval n) → Bool), F (NUPPT.advInput n (List.ofFn x)) = List.ofFn (𝓕.f n x)
noncomputable def invProbAt (𝓕) (A : NUPPT) (n : ℕ) : ℝ := invProbOpt (𝓕.f n) (A.inverter n (𝓕.inLen.eval n) (𝓕.outLen.eval n))
structure StrongOneWay (𝓕 : FunFamily) : Prop where                        -- [PS10, Def 27.3]
  easy : 𝓕.Easy
  hard : ∀ A : NUPPT, Negligible fun n => 𝓕.invProbAt A n
structure WeakOneWay (𝓕 : FunFamily) : Prop where                          -- [PS10, Def 28.4]
  easy : 𝓕.Easy
  hard : ∃ q : PolyExpr, (∀ n, 0 < q.eval n) ∧ ∀ A : NUPPT, ∃ n₀, ∀ n ≥ n₀, 𝓕.invProbAt A n ≤ 1 - 1 / (q.eval n : ℝ)
structure WorstCaseOneWay (𝓕 : FunFamily) : Prop where                     -- [PS10, Def 26.1], 1^n form (headline; run-3 audit P3-2)
  easy : 𝓕.Easy
  hard : ¬ ∃ A : NUPPT, ∀ n (x : Fin (𝓕.inLen.eval n) → Bool),
    uprob (fun r : A.Coins n =>
      ∃ x', A.inverter n (𝓕.inLen.eval n) (𝓕.outLen.eval n) (𝓕.f n x) r = some x' ∧ 𝓕.f n x' = 𝓕.f n x) = 1
structure WorstCaseOneWayLit (𝓕 : FunFamily) : Prop where                  -- [PS10, Def 26.1], literal (A gets f(x) only)
  easy : 𝓕.Easy
  hard : ¬ ∃ A : NUPPT, ∀ n (x : Fin (𝓕.inLen.eval n) → Bool),
    uprob (fun r : A.Coins (𝓕.outLen.eval n) =>
      ∃ x', A.inverterLit (𝓕.inLen.eval n) (𝓕.outLen.eval n) (𝓕.f n x) r = some x' ∧ 𝓕.f n x' = 𝓕.f n x) = 1
theorem FunFamily.WorstCaseOneWay.toLit {𝓕} (h : 𝓕.WorstCaseOneWay) : 𝓕.WorstCaseOneWayLit          -- always (proved)
theorem FunFamily.WorstCaseOneWayLit.toParam {𝓕} (hinj : Function.Injective 𝓕.outLen.eval)
    (h : 𝓕.WorstCaseOneWayLit) : 𝓕.WorstCaseOneWay                                                 -- injective outLen (proved)
def strOutLen (f : List Bool → List Bool) (n : ℕ) : ℕ
def ofString (f : List Bool → List Bool) (p : PolyExpr) : FunFamily        -- inLen = var, outLen = p
def LengthRegular (f) (p : PolyExpr) : Prop := ∀ x, (f x).length = p.eval x.length
def blocks (q ℓ : ℕ) : (Fin (q * ℓ) → Bool) ≃ (Fin q → Fin ℓ → Bool)
def prod (𝓕 : FunFamily) (q : PolyExpr) : FunFamily                        -- inLen = q·inLen, f' = prodFun blockwise
end FunFamily

theorem weak_to_strong {𝓕} (h : FunFamily.WeakOneWay 𝓕) : ∃ q : PolyExpr, FunFamily.StrongOneWay (𝓕.prod q)   -- [35.1]
theorem strong_prod_two {𝓕} (h : FunFamily.StrongOneWay 𝓕) : FunFamily.StrongOneWay (𝓕.prod (.const 2))      -- [35.2]
theorem FunFamily.StrongOneWay.weak {𝓕} (h : 𝓕.StrongOneWay) : 𝓕.WeakOneWay                                   -- sanity
theorem not_strongOneWay_id : ¬ FunFamily.StrongOneWay (FunFamily.ofString id .var)                           -- non-vacuity

structure PermFamily where f : ∀ n, (Fin n → Bool) ≃ (Fin n → Bool)        -- the single OWP of 79.4/126.4
def PermFamily.toFunFamily (P : PermFamily) : FunFamily
def OneWayPermutation (P : PermFamily) : Prop := P.toFunFamily.StrongOneWay
```

Theorem 35.1 plan (REUSE-MAX §3.3 with the sampling repair). `q := mul (const 2) (mul var q_w)`
(the text's `m = 2nq(n)`, literal). The reduction machine `A*` hard-wires in its advice
`⟨A'.advice n, 1^{m n}, 1^{T n}, 1^{inLen n}, 1^{A'.coinLen n}⟩` (all `PolyExpr`, so advice is
optional and the reduction is in fact `Uniform`-preserving) and iterates
(`polyTimeComputable_iterateFind`, `T n := 2 n m(n) n^c` rounds) the step: cut a coin segment
(`pairTakePoly`), sample the position `i` by `rejectionSample (m n) k n` with `k := clog`-free
`k n := m n` bits (`2^{m n} ≥ m n`, failure `≤ 2^{-n}` per trial), evaluate `F` blockwise
(`blockMap inLen`), plant `y` (`blockSelect`), call `A'.output` on the re-paired layout, test
`F ⟨1^n, z_i⟩ = y` (`pairEq`), emit `z_i` (or `0^{inLen n}` on exhaustion so that the machine is
`yaoInverter` *including its default*). Functional identity: `A*.inverter n _ _ y r = some (yaoInverter (𝓕.f n) (B n) (T n) y (coinsEquiv n r))`
on the event that every position trial succeeds, which has probability `≥ 1 − T n · 2^{-n}`;
`StatClose.prod`/`distAdv_le_of_statClose` move `invProb` by at most that. Then
`yao_amplification_exp` with `α' := 1/q_w(n)`, `μ₀ := 1/n^c − T n 2^{-n}`, and
`not_negligible_iff` as in REUSE-MAX steps 8–9.

### 2.10 `TCSlib/Cryptography/Asymptotic/Collections.lean`

```lean
structure Collection where                      -- [PS10, Def 41.1]; Gen(1^n) = ⟨i, t⟩, t ignored by plain collections
  D : List Bool → Type
  [fintypeD : ∀ i, Fintype (D i)]  [inhabitedD : ∀ i, Inhabited (D i)]
  encD : ∀ i, D i → List Bool
  decD : ∀ i, List Bool → Option (D i)
  decD_encD : ∀ i x, decD i (encD i x) = some x
  encD_decD : ∀ i w x, decD i w = some x → encD i x = w                     -- canonical decoding; gate 03b, G3-1
  f : ∀ i, D i → List Bool
  gen : NUPPT     gen_uniform : gen.Uniform
  sample : NUPPT  sample_uniform : sample.Uniform
  eval : List Bool → List Bool   eval_poly : PolyTimeComputable eval
  eval_spec : ∀ i x, eval (pairEncode i (encD i x)) = f i x
  sample_spec : ∀ n (r : gen.Coins n) (s : sample.Coins n), ∃ x,          -- [41.1 (2), membership]; run-3 audit P3-1
    decD (pairFstD (gen.runAt n [] r)) (sample.runAt n (pairFstD (gen.runAt n [] r)) s) = some x ∧
    eval (pairEncode (pairFstD (gen.runAt n [] r)) (sample.runAt n (pairFstD (gen.runAt n [] r)) s)) = f (pairFstD (gen.runAt n [] r)) x
namespace Collection
def index (F) (n) (r : F.gen.Coins n) : List Bool := pairFstD (F.gen.runAt n [] r)
def trap  (F) (n) (r : F.gen.Coins n) : List Bool := pairSndD (F.gen.runAt n [] r)
def SampleClose (F) (δ : ℕ → ℝ) : Prop := ∀ n r, StatClose (fun s : F.sample.Coins n => F.decD (F.index n r) (F.sample.runAt n (F.index n r) s)) (fun x : F.D (F.index n r) => some x) (δ n)
noncomputable def invProbAt (F) (A : NUPPT) (n) : ℝ :=        -- i ← Gen; x ← D_i uniform (ideal); uexp over Gen's coins
  uexp fun r : F.gen.Coins n => uprob fun z : F.D (F.index n r) × A.Coins n =>
    ∃ x', F.decD _ (A.runAt n (pairEncode (F.index n r) (F.f _ z.1)) z.2) = some x' ∧ F.f _ x' = F.f _ z.1
structure OneWay (F : Collection) : Prop where
  sampleClose : ∃ δ, Negligible δ ∧ F.SampleClose δ
  hard : ∀ A : NUPPT, Negligible fun n => F.invProbAt A n
def HardCore (F : Collection) (h : ∀ i, F.D i → Bool) : Prop := …          -- Def 78.3 for collections (uexp/uprob form)
end Collection
structure PermCollection extends Collection where perm : ∀ i, D i ≃ D i; f_perm : ∀ i x, f i x = encD i (perm i x)   -- [55.1]
structure TrapdoorCollection extends PermCollection where                                                                -- [56.1]
  inv : NUPPT  inv_uniform : inv.Uniform
  inv_spec : ∀ n (r : gen.Coins n) (y : D (pairFstD (gen.runAt n [] r))) (s : inv.Coins n),
    decD _ (inv.runAt n (pairEncode (pairSndD (gen.runAt n [] r)) (encD _ y)) s) = some ((perm _).symm y)
theorem Collection.OneWay.exists_strongOneWay {F} (h : F.OneWay) : ∃ 𝓕 : FunFamily, 𝓕.StrongOneWay            -- [42.2 ⇒]
```

The dependent domain is handled by `uexp` over the generator's coins of the inner `uprob` on
`D i × ρ` (the uniform-on-`Σ` trap of the inventory is avoided). The (⇐) direction of Thm 42.2
(`StrongOneWay 𝓕 → (collection with Gen = 1^n).OneWay`) is stated alongside.

Run-3 audit (P3-1): the field `sample_spec` was added — without it Thm 42.2 (⇒) is unprovable
(nothing ties the sampler's outputs to `D_i` off the canonical encodings); `exists_strongOneWay`
is now proved from the explicit `owfFamily_strongOneWay` (sorried under its sketch), and every
instance discharges `sample_spec` (`FunFamily.toCollection`, `factoringCollection` by the
canonical default pair, `Collection.glPad m henc` — which now takes `henc` — by `F.sample_spec`,
the RSA/Rabin/Blum/exponentiation candidates by sorried `*Sampler_spec` stubs;
`expCollection H G hV` takes the validity bridge and its generator outputs `dlDefaultIndex`
below `n₀`). Run-3 audit (P3-5): the literal `Inv(1^n, ⟨⟨i, t⟩, y⟩)` form of Def 56.1 (6) was
not adopted; the Deviation is recorded on `TrapdoorCollection`, `rsaGen` and `blumGen`.

Gate 03b (finding 1, ruling G3-1): the field `encD_decD` (canonical decoding) was added. Without
it the sampler's and the trapdoor inverter's outputs were pinned only up to a possibly lenient
decoder, so `eval` and a hard-core evaluator (constrained on encodings) could misbehave on them.
Every instance discharges it by a decoder lemma (`ofFn_of_decodeFin_eq_some` for
`FunFamily.toCollection` and the padding of `Collection.glPad`; `expEnc_of_expDec`,
`encodeDistinctPrimes_of_decode`, `rsaEnc_of_rsaDec`; inline for `rabinCollection` and
`rabinBlumTrapdoor`). Derived: `Collection.decD_eq_some_iff`, `apply_of_decD`, `eval_of_decD`,
`sample_eq_encD`, `HardCore.evaluator`, `TrapdoorCollection.inv_eq_encD`, `eval_inv`,
`Collection.HardCore.nonempty_predEvaluator` and the evaluator-free
`TrapdoorCollection.OneWay.exists_glPad_singleBitSecure`. The helpers of Thm 42.2
(`NUPPT.withIndexParam`, `NUPPT.runLenPoly`, `splitCoins`, the marker padding) moved, names
unchanged, to `Asymptotic/CollectionsHelpers.lean`, which `Collections.lean` imports.

### 2.11 `TCSlib/Cryptography/Asymptotic/Ensembles.lean`

```lean
structure Ensemble (ℓ : PolyExpr) where                 -- [PS10, Def 69.3]
  σ : ℕ → Type
  [fintype : ∀ n, Fintype (σ n)]
  X : ∀ n, σ n → (Fin (ℓ.eval n) → Bool)
namespace Ensemble
def uniform (ℓ : PolyExpr) : Ensemble ℓ
def Samplable (X : Ensemble ℓ) : Prop :=                 -- distribution level, D6
  ∃ (s : PolyExpr) (S : List Bool → List Bool), PolyTimeComputable S ∧
    ∀ n, StatClose (fun r : Fin (s.eval n) → Bool => padFin (ℓ.eval n) (S (NUPPT.advInput n (List.ofFn r)))) (X.X n) 0
def Indist (X Y : Ensemble ℓ) : Prop :=                  -- [69.4], D receives 1^n (headline)
  ∀ D : NUPPT, Negligible fun n => distAdv (X.X n) (Y.X n) (D.distinguisher n (ℓ.eval n))
def IndistLit (X Y : Ensemble ℓ) : Prop :=               -- [69.4] literal: D receives t only
  ∀ D : NUPPT, Negligible fun n => distAdv (X.X n) (Y.X n) (D.distinguisher (ℓ.eval n) (ℓ.eval n))
def Pseudorandom (X : Ensemble ℓ) : Prop := Indist X (uniform ℓ)                                  -- [74.1]
def push (M : NUPPT) (ℓ' : PolyExpr) (X : Ensemble ℓ) : Ensemble ℓ'                               -- {M(X_n)}
def copies (t : PolyExpr) (X : Ensemble ℓ) : Ensemble (.mul t ℓ)
end Ensemble
theorem Ensemble.Indist.toLit (h : X.Indist Y) : X.IndistLit Y
theorem Ensemble.IndistLit.toIndist (hℓ : Function.Injective ℓ.eval) (h : X.IndistLit Y) : X.Indist Y
theorem Ensemble.Indist.refl (X) : X.Indist X                                                      -- non-vacuity
theorem Ensemble.Indist.symm (h : X.Indist Y) : Y.Indist X
theorem Ensemble.Indist.push {ℓ ℓ'} {X Y : Ensemble ℓ} (h : X.Indist Y) (M : NUPPT) : (X.push M ℓ').Indist (Y.push M ℓ')   -- [71.5]
theorem hybrid_lemma {m} (hm : 0 < m) (X : ℕ → σ → γ) (D) : ∃ i < m, distAdv (X 0) (X m) D / m ≤ distAdv (X i) (X (i+1)) D  -- [71.6], proved
theorem Ensemble.Indist.trans (h₁ : X.Indist Y) (h₂ : Y.Indist Z) : X.Indist Z
theorem Ensemble.Indist.copies (h : X.Indist Y) (hX : X.Samplable) (hY : Y.Samplable) (t : PolyExpr) : (X.copies t).Indist (Y.copies t)
def mixEnsemble (X₀ X₁ : Ensemble ℓ) (n) : Bool × (X₀.σ n × X₁.σ n) → Bool × (Fin (ℓ.eval n) → Bool)
theorem predict_eq … : uprob (fun z => D (if z.1.1 then X₁ z.1.2.2 else X₀ z.1.2.1) z.2 = z.1.1) = 1/2 + (acceptProb X₁ D - acceptProb X₀ D)/2   -- Claim 73.a
theorem prediction_lemma (X₀ X₁ : Ensemble ℓ) (D : NUPPT) (μ) (h : ∀ n₀, ∃ n ≥ n₀, μ n < distAdv …) :
    ∃ A : NUPPT, ∀ n₀, ∃ n ≥ n₀, 1/2 + μ n/2 < uprob fun z => A.predictor n (ℓ.eval n) (mixEnsemble X₀ X₁ n z.1).2 z.2 = (mixEnsemble X₀ X₁ n z.1).1   -- [73.8]
```

**Run-3 repair (audit P2-2, pack P2).** `Ensemble` has the additional instance field
`[nonempty : ∀ n, Nonempty (σ n)]` (an empty seed type is not a distribution; without it
`NextBitUnpredictable` was vacuous for an empty-seed ensemble and `prediction_lemma`,
`NextBitUnpredictable.pseudorandom` were unprovable as frozen). Every ensemble of the
campaign fills it by instance resolution (including `ddhReal`/`ddhRandom` of
`Candidates/ElGamal.lean`, whose seeds are products of coin types since the run-3 repair
P8-1). `prediction_lemma` and
`NextBitUnpredictable.pseudorandom` have exactly the frozen shapes above (the run-2 ad hoc
hypotheses `h₀ h₁`, `hσ` were dropped); `predict_eq` carries `[Nonempty σ₀] [Nonempty σ₁]
[Nonempty ρ]`, discharged automatically for ensemble seeds and machine coins.

Proof plans: 71.5 — `D' := exists_seq M D` (coins `M.coins + D.coins`), then
`distAdv_sunglassRed` with `P t c := padFin (ℓ' n) (M.runAt n (ofFn t) c)` gives equal advantages
after `acceptProb_comp_equiv` on the coin split (`Fin.appendEquiv`-style equivalence
`(Fin (a+b) → Bool) ≃ (Fin a → Bool) × (Fin b → Bool)`); `ℓ' : PolyExpr` makes the padding
computable (`unaryPoly ℓ'`). `toLit`: a literal distinguisher at length `ℓ n` is a `1^n`
distinguisher via `exists_reparam_advice ℓ.eval ℓ` with the advice carrying `α(ℓ n)` and
ignoring `1^n`; `toIndist` (injective `ℓ`): a `1^n` distinguisher `D` becomes a literal one with
advice `⟨1^n, D.advice n⟩` at length `ℓ n` (`Classical.choose` of the preimage; `[]` off the
image), coins `D.coins` evaluated at `ℓ n ≥ n` (`eval_mono`) and cut to `D.coinLen n`
(`exists_reparam_advice` with `φ := ℓ⁻¹`). `copies`: for every `n` take a maximising hybrid
index `k_n` (`exists_multicopyRed_ge`, `Finset.exists_max_image`) into the advice, sample the
other coordinates with the `Samplable` evaluators (`iterateEmit` over `t n` positions,
`StatClose … 0` lifts to the product law by `StatClose.prod`), plant the challenge; then
`Negligible.mul_pow`. `prediction_lemma`: `A := D` or `D` negated (`exists_comp` with
`computesFunInTime_ifEq`), chosen by pigeonhole on the infinite set; `predict_eq` is proved
once with `uprob_bool_prod`.

### 2.12 `Asymptotic/{Pseudorandom,NextBit,HardCore}.lean` — definition shapes

(The collection form of Thm 87.3, `Collection.glPad` … `goldreich_levin_coll`, moved unchanged to
`Asymptotic/HardCoreCollection.lean`, which `HardCore.lean` imports; gate 03c, finding 11.)

```lean
structure PRG where                                           -- [PS10, Def 77.1], length-regular
  stretch : PolyExpr
  G : ∀ n, (Fin n → Bool) → (Fin (stretch.eval n) → Bool)
  expands : ∀ n, n < stretch.eval n                           -- every n, n = 0 included: 2n, n^c excluded (§5.25; gate 03c, G3-2)
def PRG.Easy (P : PRG) : Prop := ∃ F, PolyTimeComputable F ∧ ∀ n (s : Fin n → Bool), F (List.ofFn s) = List.ofFn (P.G n s)
def PRG.ensemble (P : PRG) : Ensemble P.stretch               -- seeds Fin n → Bool
def PRG.Secure (P : PRG) : Prop := P.Easy ∧ P.ensemble.Pseudorandom

noncomputable def nextBitProb {ℓ} (X : σ → Fin ℓ → Bool) (i : Fin ℓ) (A : (Fin i → Bool) → ρ → Bool) : ℝ :=
  uprob fun z : σ × ρ => A (fun j => X z.1 (Fin.castLE i.isLt.le j)) z.2 = X z.1 i
def Ensemble.NextBitUnpredictable (X : Ensemble ℓ) : Prop :=   -- [PS10, Def 75.2], i < ℓ n, A gets 1^n and the prefix
  ∀ A : NUPPT, ∃ ε, Negligible ε ∧ ∀ n (i : Fin (ℓ.eval n)), nextBitProb (X.X n) i (A.predictor n i) ≤ 1/2 + ε n
theorem Ensemble.NextBitUnpredictable.pseudorandom (h : X.NextBitUnpredictable) : X.Pseudorandom   -- [75.4]; the source's statement (hℓ : ∀ n, 0 < ℓ.eval n dropped at gate 03c, G3-7b)

def HardCore (𝓕 : FunFamily) (h : ∀ n, (Fin (𝓕.inLen.eval n) → Bool) → Bool) : Prop :=   -- [PS10, Def 78.3]
  (∃ H, PolyTimeComputable H ∧ ∀ n x, H (NUPPT.advInput n (List.ofFn x)) = [h n x]) ∧
  ∀ A : NUPPT, ∃ ε, Negligible ε ∧ ∀ n, predProb (𝓕.f n) (h n) (A.predictor n (𝓕.outLen.eval n)) ≤ 1/2 + ε n
```

Theorem shapes of the HardCore file (statement phase): `owp_hardcore_prg (P : PermFamily) (h) : OneWayPermutation P → HardCore P.toFunFamily h → (PRG with G n s = f n s ‖ h n s).Secure`
(79.4, via `exists_owpPredictorBits`); `prg_expand (P : PRG) (ℓ : PolyExpr) : P.Secure → (prgExtBits-based PRG of stretch ℓ).Secure`
(80.5, via `exists_prgExtBitsRed_ge`, hybrid index as advice, `iterate` for the evaluator; **as shipped**
(gate 03c, finding 4): `prg_expand (G : ∀ n, (Fin n → Bool) → (Fin (n + 1) → Bool)) (ℓ : PolyExpr)
(hℓ : ∀ n, n < ℓ.eval n) (h : (PRG.oneBit G).Secure) : (PRG.expand G ℓ hℓ).Secure`, the one-bit input of the
text's Lemma 80.5 ("Let `G : {0,1}^n → {0,1}^{n+1}` be a PRG"); a general secure `P : PRG` reaches it through
`PRG.truncate` with `PRG.Secure.truncate : (PRG.oneBit P.truncate).Secure` in `Asymptotic/PRF.lean`, and `hℓ`
carries the cost of §5.25);
`cor_81_7` (closed form `prgExt_succ`); `goldreich_levin (𝓕) : StrongOneWay 𝓕 → StrongOneWay (glPad 𝓕) ∧ HardCore (glPad 𝓕) glBit`
(87.3, via `invProb_guessInverter`, `k(n) := ⌈log₂(2n^{2c+1}+1)⌉` hard-wired, `iterateFind`
for the `n(2^k−1)` calls, `majority`, `pairXor`); `goldreich_levin_coll (F : Collection) …`
(87.3.coll, `half_le_uprob_threshold` over `i`).

### 2.13 Encryption shapes — `Asymptotic/Encryption.lean`, `Asymptotic/PublicKey.lean`, `ZeroKnowledge/Encryption.lean`

```lean
structure PrivateKeyScheme where                               -- [PS10, Def 24.7]
  gen enc dec : NUPPT
  gen_uniform : gen.Uniform   enc_uniform : enc.Uniform   dec_uniform : dec.Uniform
  correct : ∀ n (m : Fin n → Bool) (rg : gen.Coins n) (re : enc.Coins n) (rd : dec.Coins n),
    decodeFin n (dec.runAt n (pairEncode (gen.runAt n [] rg) (enc.runAt n (pairEncode (gen.runAt n [] rg) (List.ofFn m)) re)) rd) = some m
def PrivateKeyScheme.encDist (S) (n) (m : Fin n → Bool) : S.gen.Coins n × S.enc.Coins n → List Bool
def PrivateKeyScheme.SingleMessageSecure (S) : Prop :=        -- [91.1]
  ∀ D : NUPPT, ∃ ε, Negligible ε ∧ ∀ n (m₀ m₁ : Fin n → Bool), distAdv (S.encDist n m₀) (S.encDist n m₁) (D.distinguisherL n) ≤ ε n
def PrivateKeyScheme.multiEncDist (S) (n q : ℕ) (m : Fin (q+1) → Fin n → Bool) : S.gen.Coins n × (Fin (q+1) → S.enc.Coins n) → List Bool
def PrivateKeyScheme.MultiMessageSecure (S) : Prop :=         -- [93.1], q n + 1 messages
  ∀ (D : NUPPT) (q : PolyExpr), ∃ ε, Negligible ε ∧ ∀ n (m m' : Fin (q.eval n + 1) → Fin n → Bool),
    distAdv (S.multiEncDist n (q.eval n) m) (S.multiEncDist n (q.eval n) m') (D.distinguisherL n) ≤ ε n
def PrivateKeyScheme.ZeroKnowledge (S) : Prop :=               -- [111.1]
  ∃ Sim : NUPPT, Sim.Uniform ∧ ∀ D : NUPPT, ∃ ε, Negligible ε ∧ ∀ n (m : Fin n → Bool),
    distAdv (S.encDist n m) (Sim.runAt n []) (D.distinguisherL n) ≤ ε n
theorem PrivateKeyScheme.singleMessageSecure_iff_zeroKnowledge (S) : S.SingleMessageSecure ↔ S.ZeroKnowledge   -- [112.2]

structure PublicKeyScheme where                                -- [PS10, Def 102.1]; clause (4) dropped (Deviation)
  gen enc : NUPPT   dec : List Bool → List Bool
  gen_uniform : gen.Uniform   enc_uniform : enc.Uniform   dec_poly : PolyTimeComputable dec
  correct : ∀ n (m : Fin n → Bool) (rg : gen.Coins n) (re : enc.Coins n),
    decodeFin n (dec (pairEncode (pairSndD (gen.runAt n [] rg)) (enc.runAt n (pairEncode (pairFstD (gen.runAt n [] rg)) (List.ofFn m)) re))) = some m
def PublicKeyScheme.pkEncDist (S) (n) (m) : S.gen.Coins n × S.enc.Coins n → List Bool    -- ⟨pk, Enc_pk(m)⟩
def PublicKeyScheme.Secure (S) : Prop := ∀ D : NUPPT, ∃ ε, Negligible ε ∧ ∀ n m₀ m₁, distAdv (S.pkEncDist n m₀) (S.pkEncDist n m₁) (D.distinguisherL n) ≤ ε n   -- [102.2]
```

`MultiMessageSecure` for PKE, `SingleBitSecure` (message space `Bool`, encoded as `[b]`), the
bitwise scheme (103.f) and Alg 104.3 (`gen := TDP gen`, `enc := ⟨f_i(r), b_i(r) ⊕ m⟩`) follow the
same shapes in `PublicKey.lean`. Alg 92.1 and Alg 99.1 are `PrivateKeyScheme` values built with
`ofPolyTimeUniform` of FP functions (`pairXor` for the one-time pad).

### 2.14 `TCSlib/Cryptography/Asymptotic/PRF.lean`

```lean
structure OracleEnsemble (ℓ₁ ℓ₂ : PolyExpr) where              -- [PS10, Def 96.1]
  σ : ℕ → Type   [fintype : ∀ n, Fintype (σ n)]
  O : ∀ n, σ n → (Fin (ℓ₁.eval n) → Bool) → (Fin (ℓ₂.eval n) → Bool)
def OracleEnsemble.random (ℓ₁ ℓ₂ : PolyExpr) : OracleEnsemble ℓ₁ ℓ₂            -- RF_n, seed = table
def OracleEnsemble.keyed {ℓ₁ ℓ₂} (F : ∀ n, (Fin n → Bool) → (Fin (ℓ₁.eval n) → Bool) → (Fin (ℓ₂.eval n) → Bool)) : OracleEnsemble ℓ₁ ℓ₂
inductive OracleMove (ℓ₁ : ℕ) | query (x : Fin ℓ₁ → Bool) | ret (b : Bool)
def decodeOracleMove (ℓ₁ : ℕ) (w : List Bool) : OracleMove ℓ₁                 -- ⟨[false], x⟩ query; [true, b] verdict
def encodeHist {ℓ₁ ℓ₂} (h : List ((Fin ℓ₁ → Bool) × (Fin ℓ₂ → Bool))) : List Bool
def buildTree {ℓ₁ ℓ₂} (next : List (…) → OracleMove ℓ₁) : ℕ → List (…) → QueryTree (Fin ℓ₁ → Bool) (Fin ℓ₂ → Bool) Bool
def Complexity.NUPPT.toOracleAdversary (D : NUPPT) (n ℓ₁ ℓ₂ q : ℕ) : OracleAdversary (D.Coins n) (Fin ℓ₁ → Bool) (Fin ℓ₂ → Bool)
theorem Complexity.NUPPT.toOracleAdversary_boundedBy (D) (n ℓ₁ ℓ₂ q) : (D.toOracleAdversary n ℓ₁ ℓ₂ q).BoundedBy q
def OracleEnsemble.Indist (O O' : OracleEnsemble ℓ₁ ℓ₂) : Prop :=               -- ∀ D, ∀ q
  ∀ (D : NUPPT) (q : PolyExpr), Negligible fun n => distAdv (O.O n) (O'.O n) (oracleDist (D.toOracleAdversary n (ℓ₁.eval n) (ℓ₂.eval n) (q.eval n)))
theorem OracleEnsemble.Indist.refl (O) : O.Indist O                                                     -- non-vacuity
structure PRF (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool)) : Prop where                 -- [PS10, Def 96.2]
  easy : ∃ E, PolyTimeComputable E ∧ ∀ n (s x : Fin n → Bool), E (pairEncode (List.ofFn s) (List.ofFn x)) = List.ofFn (F n s x)
  pseudorandom : (OracleEnsemble.keyed (ℓ₁ := .var) (ℓ₂ := .var) F).Indist (OracleEnsemble.random .var .var)
theorem prfAdv_toOracleAdversary (F) (D : NUPPT) (n q : ℕ) :
    distAdv ((keyed F).O n) ((random .var .var).O n) (oracleDist (D.toOracleAdversary n n n q)) = prfAdv (F n) (D.toOracleAdversary n n n q) := rfl
```

Theorem 97.3 plan: REUSE-MAX §5 unchanged (the hybrid indices `(i_n, j_n)` from
`exists_ggmBits_dist` into the advice; the PRG distinguisher hosts `D`'s next-query function
in an `iterateFind` loop over at most `q n + 1` activations with the lazily sampled table in the
state; functional identity with `evalLazy`/`noteQuery` by induction on the tree;
`Negligible.mul_pow` for `n · q n`). Theorem 99.2's oracle adversary is a chain of `q n + 1`
`query` nodes built by `buildTree` from an FP next-query function with the messages as advice.

### 2.15 Chapter 4 — `ZeroKnowledge/{Interaction,InteractiveProofs,Defs,Commitment,GraphIsomorphism}.lean`

```lean
structure Strategy where
  next : List Bool → List Bool → List Bool → List (List Bool) → List Bool     -- x z r received ↦ message / output
  coins : PolyExpr
namespace Strategy
def coinLen (S) (n) : ℕ := S.coins.eval n
abbrev Coins (S) (n) : Type := Fin (S.coinLen n) → Bool
def encodeMsgs (h : List (List Bool)) : List Bool := h.foldr pairEncode []
def ofNUPPT (A : NUPPT) : Strategy :=   -- one activation at parameter |x| on ⟨⟨x, z⟩, messages⟩, whole random tape
  { next := fun x z r hist => A.runAtL x.length (pairEncode (pairEncode x z) (encodeMsgs hist)) r, coins := A.coins }
def Efficient (S : Strategy) : Prop := ∃ A : NUPPT, A.Uniform ∧ S.coins = A.coins ∧ ∀ x z r hist, S.next x z r hist = (ofNUPPT A).next x z r hist
end Strategy

def moverIsV (vFirst : Bool) (k : ℕ) : Bool := if vFirst then decide (k % 2 = 0) else decide (k % 2 = 1)
/-- Messages received by (P, V) after k moves. -/
def exec (P V : Strategy) (vFirst : Bool) (x zP zV rP rV : List Bool) : ℕ → List (List Bool) × List (List Bool)
  | 0 => ([], [])
  | k + 1 => let e := exec P V vFirst x zP zV rP rV k
             if moverIsV vFirst k then (e.1 ++ [V.next x zV rV e.2], e.2) else (e.1, e.2 ++ [P.next x zP rP e.1])
structure View where (x z r : List Bool) (received : List (List Bool))
def View.encode (v : View) : List Bool := pairEncode (pairEncode v.x v.z) (pairEncode v.r (Strategy.encodeMsgs v.received))
structure Protocol where (P V : Strategy) (rounds : PolyExpr) (verifierFirst : Bool)    -- rounds = number of messages
namespace Protocol
abbrev ExecCoins (π) (P' : Strategy) (x) : Type := P'.Coins x.length × π.V.Coins x.length
def withV (π) (V' : Strategy) : Protocol := { π with V := V' }
def transcriptWith (π) (P') (x y z) (r : π.ExecCoins P' x) : List (List Bool) × List (List Bool) :=
  exec P' π.V π.verifierFirst x y z (List.ofFn r.1) (List.ofFn r.2) (π.rounds.eval x.length)
def outV (π) (P') (x y z) (r) : List Bool := π.V.next x z (List.ofFn r.2) (π.transcriptWith P' x y z r).2
def outP (π) (x y z) (r) : List Bool
def viewV (π) (x y z) (r : π.ExecCoins π.P x) : View := ⟨x, z, List.ofFn r.2, (π.transcriptWith π.P x y z r).2⟩
def viewP (π) (x y z) (r) : View
end Protocol

structure InteractiveProof (π : Protocol) (L : Language Bool) : Prop where            -- [PS10, Def 116.1]
  efficientV : π.V.Efficient
  complete : ∀ x ∈ L, ∃ y, ∀ z, uprob (fun r : π.ExecCoins π.P x => π.outV π.P x y z r = [true]) = 1
  sound : ∃ ε, Negligible ε ∧ ∀ x ∉ L, ∀ (P' : Strategy) z, 1 - ε x.length < uprob (fun r : π.ExecCoins P' x => π.outV P' x [] z r = [false])
structure InteractiveProofErr (π) (L) (s : ℕ → ℝ) : Prop where                        -- soundness error s
  efficientV …  complete …
  sound : ∀ x ∉ L, ∀ P' z, 1 - s x.length ≤ uprob (fun r => π.outV P' x [] z r = [false])
structure WitnessRelation (L : Language Bool) (R : List Bool → List Bool → Prop) : Prop where   -- Appendix B
  mem_iff : ∀ x, x ∈ L ↔ ∃ y, R x y
  bounded : ∃ p : PolyExpr, ∀ x y, R x y → y.length ≤ p.eval x.length
  decidable : ∃ T : List Bool → Bool, PolyTimeComputable (fun z => [T z]) ∧ ∀ x y, T (pairEncode x y) = true ↔ R x y
structure EfficientProverProof (π) (L) (R) : Prop extends InteractiveProof π L where    -- [PS10, Def 119.5]
  efficientP : π.P.Efficient
  completeWitness : ∀ x y, R x y → ∀ z, uprob (fun r => π.outV π.P x y z r = [true]) = 1
structure EfficientProverProofErr (π) (L) (R) (s) : Prop extends InteractiveProofErr π L s where …

def Complexity.NUPPT.simulate (S : NUPPT) (x z : List Bool) (r : S.Coins x.length) : List Bool := S.runAt x.length (pairEncode x z) r
def HVZK (π) (R) : Prop :=                                                               -- [121.1]
  ∃ S : NUPPT, S.Uniform ∧ ∀ (Lz : PolyExpr) (D : NUPPT), ∃ ε, Negligible ε ∧ ∀ x y z, R x y → z.length ≤ Lz.eval x.length →
    distAdv (fun r => (π.viewV x y z r).encode) (S.simulate x z) (D.distinguisherL x.length) ≤ ε x.length
def ZK (π) (R) : Prop :=                                                                 -- [121.2]
  ∀ V' : Strategy, V'.Efficient → ∃ S : NUPPT, S.Uniform ∧ ∀ (Lz : PolyExpr) (D : NUPPT), ∃ ε, Negligible ε ∧
    ∀ x y z, R x y → z.length ≤ Lz.eval x.length →
      distAdv (fun r => ((π.withV V').viewV x y z r).encode) (S.simulate x z) (D.distinguisherL x.length) ≤ ε x.length
def StatZK (π) (R) (δ : ℕ → ℝ) : Prop :=
  ∀ V', V'.Efficient → ∃ S : NUPPT, S.Uniform ∧ ∀ x y z, R x y → StatClose (fun r => ((π.withV V').viewV x y z r).encode) (S.simulate x z) (δ x.length)
def PerfectZK (π) (R) : Prop := StatZK π R (fun _ => 0)
def PerfectZKAbort (π) (R) : Prop :=                                                     -- Goldreich Def 4.3.1, ⊥ = []
  ∀ V', V'.Efficient → ∃ S : NUPPT, S.Uniform ∧ ∀ x y z, R x y →
    uprob (fun r : S.Coins x.length => S.simulate x z r = []) ≤ 1/2 ∧
    ∀ T : List Bool → Prop, uprob (fun r => T (view r)) * uprob (fun r => S.simulate x z r ≠ []) = uprob (fun r => S.simulate x z r ≠ [] ∧ T (S.simulate x z r))
theorem StatZK.zk (hδ : Negligible δ) (h : StatZK π R δ) : ZK π R
theorem StatZK.hvzk (hδ : Negligible δ) (hV : π.V.Efficient) (h : StatZK π R δ) : HVZK π R

structure Commitment (Com : List Bool → List Bool) (ℓ : PolyExpr) : Prop where          -- [PS10, Def 126.3], binding repaired
  easy : PolyTimeComputable Com
  binding : ∀ n v₀ v₁ r₀ r₁, v₀.length = n → v₁.length = n → r₀.length = ℓ.eval n → r₁.length = ℓ.eval n → v₀ ≠ v₁ →
    Com (pairEncode v₀ r₀) ≠ Com (pairEncode v₁ r₁)
  hides : ∀ D : NUPPT, ∃ ε, Negligible ε ∧ ∀ n (v₀ v₁ : Fin n → Bool),
    distAdv (fun r : Fin (ℓ.eval n) → Bool => Com (pairEncode (List.ofFn v₀) (List.ofFn r)))
            (fun r : Fin (ℓ.eval n) → Bool => Com (pairEncode (List.ofFn v₁) (List.ofFn r))) (D.distinguisherL n) ≤ ε n
```

**As-built note (2026-11-06, gate 03g, finding 6; the frozen block above is unchanged).** Ruling
G3-3 changed two signatures. `InteractiveProof(Err).complete` is
`∃ B : PolyExpr, ∀ x ∈ L, ∃ y, (∀ r hist, (π.P.next x y r hist).length ≤ B.eval x.length) ∧ ∀ z, uprob (…) = 1`,
and `EfficientProverProof(Err)` has the field `boundedP : ∃ B : PolyExpr, π.ProverBounded R B`
(`Protocol.ProverBounded`, `Interaction.lean`). See §5 item 8.

Graph isomorphism (compiled expressibility check): `Graph n := Fin n → Fin n → Bool`,
`permGraph G π u v := G (π.symm u) (π.symm v)`, `encGraph`/`decGraph` (adjacency matrix, `n²`
bits, `Nat.sqrt`), `encPerm`/`decPerm` (relation matrix, `Fin.find`, `Equiv.ofBijective`),
`fisherYates n c`, `permFromCoins n k T : (Fin n → Fin T → Fin k → Bool) → Option (Equiv.Perm (Fin n))`
with `permFromCoins_uniform_of_some` and `uprob_permFromCoins_none_le (hk : n ≤ 2^k) : … ≤ n (1/2)^T`;
`giProver` (coins `normal 1 2`; `π` by `permFromCoins n n n`, identity on failure; message 1
`encGraph (π(G₀))`, message 3 `encPerm (if b then π * σ⁻¹ else π)`), `giVerifier` (coins
`const 1`; on `[H]` sends `[b]`, on `[H, γ]` outputs `[decide (encGraph (permGraph G_b (decPerm n γ)) = H)]`),
`giProtocol := ⟨giProver, giVerifier, const 3, false⟩` (three messages, prover first; the
verdict is the fourth activation), `Liso`, `Riso`, `Riso_witnessRelation`,
`gi_sim_H_dist`/`gi_sim_half` (Lemma 123.5, exact over `Equiv.Perm (Fin n)`),
`gi_efficientProverProofErr : EfficientProverProofErr giProtocol Liso Riso (fun _ => 1/2)` (Prop 120.7,
one iteration), `gi_statZK : ∃ δ, Negligible δ ∧ StatZK giProtocol Riso δ` (Theorem 122.3,
`δ n = 2^{-n} + 2 n (1/2)^n` from the truncated simulator and the rejection sampler),
`giProtocolRep := ⟨giProverRep, giVerifierRep, mul (const 3) var, false⟩` with
`InteractiveProof giProtocolRep Liso` (Lemma 120.d), and the sanity
`npProtocol_interactiveProof : EfficientProverProof (npProtocol T) L R` (P sends `y`).

**Run-3 repair (audit P2-1, pack P2).** The permutation-sampler parameters above are
superseded: the honest parties sample by
`samplePerm n r := (permFromCoins n (permBits n) (permTrials n) (coinTable n (permTrials n) (permBits n) r)).getD 1`
(`permBits n = Nat.size n`, `permTrials n = 2n²`, `Asymptotic/Permutations.lean`) with
`permCoinLen n := n * permTrials n * permBits n ≤ (N + 1)²` whenever `2n² ≤ N`
(`permCoinLen_le`; every encoded instance has length `3n² + 2`, so the coin polynomials
`normal 1 2` are kept), `permFailBound n := n * (2 : ℝ)⁻¹ ^ n` (`statClose_samplePerm` and
`negligible_mul_permFailBound` proved from the shared lemmas; the run-2 `permFailBound_le_exp`
removed), and `polyTimeComputable_encPermFromCoins` (`ZeroKnowledge/Encoding.lean`) is stated
at the same parameters, GI's private `polyTimeComputable_encSamplePerm` being derived from
it. `gi_statZK`'s planned error becomes `δ n = 2^{-n} + (n + 1) · n · 2^{-n}`.

**Run-3 repair (audit P10-1/P10-2, pack P10).** The exact-probability engines of the
adaptive-prover bounds, `uprob_adaptive_guess` (Lem-119.c) and `uprob_gni_rep_cheat`
(Lem-119.b), assume the auxiliary coin type nonempty (`[Nonempty W]`, `[Nonempty ρ]`): `uprob`
on an empty type is `0`, so the run-2 statements specialised to `Empty` at `m = 0` read
`0 = 1`. Every consumer instantiates the coin type with a tape `Fin k → Bool`, so no
downstream statement changes; `uprob_gi_rep_cheat_le` (Lem-120.d, an inequality) keeps its
statement and is reproved by a case split on `ρ`. Audit P10-3 (divergent sampler copies) is
resolved by the P2-1 repair above: `polyTimeComputable_encSamplePerm` is derived from the
shared `polyTimeComputable_encPermFromCoins` at the one set of parameters.

---

## 3. Disposition of every panel refutation

| # | Refutation (judge) | Disposition |
| --- | --- | --- |
| 1 | REUSE-MAX `iterateFind`: `Inv x s := ∃ i ≤ R|x|, s = g^[i] x` not closed under `stepF` (J1-7, J2-15, J3-5) | **Fixed** (§2.6): length-guarded step on a state word carrying the input, `Inv x w := pairFstD w = x ∧ |pairSndD w| ≤ P|x|`; `horbit` shows the guard is inactive on the orbit. The statement is unchanged. |
| 2 | REUSE-MAX anchor exclusion / `entry = exit` and overriding the module table at `exit` (J2-16, J3-6) | **Fixed** (§2.6 step 3): fresh anchor state `inl ()` stepping into `C₁.entry`; transitions *into* `exit` are redirected to fresh branch states, the module table at `exit` is never overridden. |
| 3 | REUSE-MAX `Indist.push` without `hℓ'` (J1-8, J2-17, J3-7) | **Fixed**: `ℓ' : PolyExpr`; the bound is intrinsic (`eval_le`) and `1^{ℓ' n}` is computed (`unaryPoly`). |
| 4 | REUSE-MAX `Indist.copies` without `Samplable` (J1-8, J3-7) | **Fixed**: hypotheses `hX : X.Samplable`, `hY : Y.Samplable` (§2.11). |
| 5 | REUSE-MAX `Samplable` as a seed bijection is unsatisfiable for `U_n` and pushed ensembles (J2-14) | **Fixed**: distribution-level `Samplable` (`StatClose … 0` from `s.eval n` bits, `s : PolyExpr`); `U_n` has `s = var`, `S = pairSndD`. |
| 6 | REUSE-MAX GI `rounds = 3` leaves `outB = none`; `CR(n+1)^cR ≠ 3` (J1-9); FAITHFUL `rounds = 1` gives the coin bit (J1-14, J3-?) | **Fixed**: `rounds : PolyExpr := const 3` counts messages; the verdict is `V.next` on the complete history (fourth activation), always defined. |
| 7 | REUSE-MAX abstract `ℕ → ℕ` lengths (`inLen/outLen`, `Ensemble ℓ`, `push ℓ'`, `copies t`) against the brief (J1-10, J3-8) | **Fixed**: all are `PolyExpr`; `InLenPoly` and `Lin` disappear (`polyTimeComputable_unaryPoly`). |
| 8 | REUSE-MAX `1^n` given to Def 26.1 / 69.4 adversaries (J1-10, graft from FAITHFUL) | **Fixed**: `WorstCaseOneWayLit` literal (`inverterLit`), `IndistLit` literal; `WorstCaseOneWay`/`Indist` (headline, `1^n` form) related by `toLit`/`toParam`, `toLit`/`toIndist` (D5; run-3 audit P3-2 made the `1^n` form the headline of Def 26.1 as well). |
| 9 | REUSE-MAX power-of-two block count in 35.1 (J2 graft `pow2log`, J1 fallback R2) | **Rebutted/replaced**: no `pow2log` constructor; the text's `m = 2nq(n)` is literal and the uniform position is rejection-sampled with the D10 device (statistical term `T·2^{-n}` absorbed in `μ₀`). |
| 10 | REUSE-MAX `Samplable` claims and `prediction_lemma` advice (J1 critique) | `prediction_lemma` uses no advice (pigeonhole, `exists_comp`); `copies` uses advice for `k_n`. |
| 11 | ABSTRACT `WeakOWF` vacuous, `weak_to_strong` false (J1, J2, J3) | **Guarded**: `WeakOneWay.hard` carries `∀ n, 0 < q.eval n`; `weak_to_strong` stated for the guarded notion. |
| 12 | ABSTRACT `iterate`/`mem_iter` unsatisfiable without a growth bound (J1, J2, J3) | **Avoided**: every iteration lemma carries `horbit`; no interface fields. |
| 13 | ABSTRACT don't-care runs outside the declared coin length (`oracleAdv`, `coinsP/coinsV` at `z = []`, `PRF` unsatisfiable) (J1, J2, J3) | **Not applicable**: `NUPPT` is total; `runAt n` fixes one coin type per `n`; strategies use the whole tape at parameter `|x|`; oracle adversaries use `runAt n` on the growing history. |
| 14 | ABSTRACT `gi_sim_statDist` ill-typed (`FinDist` needs `Fintype`) (J2, J3) | **Avoided**: `StatClose` sup-over-test-sets form; `distAdv_le_of_statClose`. |
| 15 | ABSTRACT `exec` hardcodes verifier-first (J1) | **Fixed**: `Protocol.verifierFirst`, `moverIsV`. |
| 16 | ABSTRACT `exists_stepCallTM` extends private Loop.lean machinery (J1, J2) | **Avoided**: `iterateFind` uses only the public `exists_loopFindTM`, `exists_installCallTM`, `exists_emitCallTM`. |
| 17 | FAITHFUL `runCoins_eq_of_take` false at `t = 0` (J2) | **Not applicable** (no coin tape); the "extra coins unread" device is the `r.take` clause of `exists_reparam_advice`, a statement about FP functions. |
| 18 | FAITHFUL `Poly.eval = C(n+1)^c` cannot express `n`, `2n` (J1, J2) | **Fixed by `PolyExpr`** (`var`, `mul (const 2) var`). |
| 19 | FAITHFUL `FunFamily.str` conflates parameter and input length (J1, J2) | **Avoided**: `Easy` evaluates on `⟨1^n, x⟩`. |
| 20 | FAITHFUL `∃ N` after `∀ x y z` in `HVZK`/`ZK`/`hide` (J1, J2, J3) | **Avoided**: no coin budget variable; distinguisher at parameter `|x|`, `Lz` universally quantified before `ε`. |
| 21 | FAITHFUL `nuppt_seq_iff_advice` conditional on `PolyBound canonizerTime`; `one_work_tape_binary` not at the seam (J1, J2, J3) | **Off the critical path**: `NUPPTSeq` optional module with one named admission (D4, D11). |
| 22 | FAITHFUL `Strategy.IsPPT` run cut at the deadline; `encodeView` sorried (J3) | **Not applicable**: total machines; `View.encode` is defined. |
| 23 | FAITHFUL `exists_handlerSim` possibly prohibitive (J1) | **Not needed**: D7 next-query machines; GGM's reduction hosts the adversary's next-query function in `iterateFind`. |
| 24 | FAITHFUL `forall_of_uprob_eq_one` namespace (J1, J3) | Recorded: `TCSlib.Cryptography.HardcoreBit.forall_of_uprob_eq_one` (HardcoreBit/Basic.lean:107), `uprob_eq_one_of_forall` (:120). |
| 25 | FAITHFUL/J2: `distAdv_sunglassRed` is at Indistinguishability.lean:130 | Recorded. |
| 26 | J3: `1^n` vs `|x|` indexing, time in machine-input length, totality must be in the decision log | **Recorded** in D3 with the interdefinability argument. |

Issues found in this synthesis and resolved here (not raised by the panel):

* The text's "a round ends with the active machine halting — in which case the protocol ends"
  makes the literal `Pr[out_V = 0]` unsatisfiable against the immediately-halting prover
  (the verifier never outputs). The fixed-alternation model with the verdict on the complete
  history is the reading under which the literal `[false]` soundness clause is satisfiable
  (D8, Deviation recorded).
* With total machines, a verifier `V*` and a distinguisher `D` read all of an unbounded `z`,
  so the non-uniform reduction of Prop 128.8 (which hard-wires the worst `(x, y, z)`) needs
  `|z|` polynomially bounded; hence the `∀ Lz` clause (D8). The text's own model (time `t(|x|)`)
  implies the same bound implicitly.
* `exists_reparam_advice` is the one place an abstract `φ : ℕ → ℕ` appears; it is a theorem
  hypothesis with a `PolyExpr` majorant (needed by Lemma 64.3's `m(n) = n − ⌊log₂ n⌋` and by
  `IndistLit.toIndist`), consistent with the brief.

## 4. Grafts adopted (source → where)

| Graft | From | Where it lands |
| --- | --- | --- |
| Syntactic `PolyExpr` for every length/budget | ABSTRACT | `Randomized/PolyExpr.lean`; all structures |
| `∀ q : PolyExpr` oracle budget | ABSTRACT | `OracleEnsemble.Indist` |
| First-mover field; padded/explicit per-parameter coin types | ABSTRACT | `Protocol.verifierFirst`; coins at parameter `|x|` |
| Non-vacuity theorems | ABSTRACT, FAITHFUL | `NUPPT.nonempty`, `not_strongOneWay_id`, `StrongOneWay.weak`, `Indist.refl`, `OracleEnsemble.Indist.refl`, `npProtocol_interactiveProof` + `Checks.lean` prints |
| Power-of-two index discipline for exact uniformity; definable `NESubset k ≃ Fin (2^k − 1)` | ABSTRACT | GL inverter packaging (HardCore workstream) |
| Literal Def 26.1 and Def 69.4 forms, never unified silently | FAITHFUL, J1–J3 | `WorstCaseOneWay`, `IndistLit`, `toLit`/`toIndist` |
| `advice_length ≤` | FAITHFUL | `NUPPT.advice_length` |
| Literal `[false]` soundness; `∃ ε` before `∀ x P' z`; arbitrary provers | FAITHFUL | `InteractiveProof.sound` |
| Abort-form perfect ZK; non-dyadic permutation finding | FAITHFUL, J2 | `PerfectZKAbort`; `permFromCoins`; `gi_statZK` |
| "Extra coins unread" transport instead of Σ-types | FAITHFUL | `exists_reparam_advice`'s `r.take`; `StatClose.prod` |
| `NUPPTSeq`, `exists_queryTree`, `ofPartial` as optional modules with named admissions | FAITHFUL, J1 | D4, D7, D11 |
| Statistical-switch device for non-dyadic samplers (Q3), shared by Thm 35.1, candidates and ch. 4 | inventory-ch2 F4/C10, J2 | `Asymptotic/Sampling.lean` (D10) |
| Distribution-level `Samplable` | J2 | `Ensemble.Samplable` |
| Closure lemmas preserve `Uniform` | J2, ABSTRACT | `exists_reparam`, `exists_seq`, `ofPolyTimeUniform` |
| Repaired `iterateFind` construction (guarded step, carried input, fresh anchor) | J1–J3 | §2.6 |

## 5. Deviations register (docstring text, one line each)

1. `NUPPT`: totality on all inputs (behaviour class unchanged via clocking); time in the
   machine-input length; advice and coins indexed by the parameter `n` read from `1^n`.
2. `NUPPT`: Def 26.8's machine-sequence formulation not formalized in the core (optional module).
3. `FunFamily.Easy`: deterministic polynomial-time evaluator on `⟨1^n, x⟩` instead of a PPT
   computing with probability one (equivalent by `Computes` + `ofPolyTimeUniform`).
4. `inverter`: wrong-length output = failure (D5); verdict `= [true]` (normalisable by `ifEq`).
5. `Ensemble`: dyadic samplable distributions; `Indist` gives `D` the input `1^n` (literal form
   `IndistLit`, equivalent for every `PolyExpr ℓ`: proved for injective `ℓ`, the constant case
   by point tests, not formalized; gate 03a, note 14).
6. `WeakOneWay`: `0 < q n` made explicit; Theorem 35.1 with the text's `m = 2nq(n)` and a
   rejection-sampled position (statistical term absorbed).
7. `OracleEnsemble.Indist`: next-query machines with an explicit universally quantified
   budget; no oracle tapes; forced verdict `false` after `q n` queries.
8. `Protocol`: fixed number of messages `rounds.eval |x|`, verdict on the complete history
   (halting = sending `[]`); `Efficient` time polynomial in the total input length. The honest
   messages are polynomially bounded in `|x|` (`Protocol.ProverBounded`, in
   `InteractiveProof(Err).complete` and the field `EfficientProverProof(Err).boundedP`): for
   Definition 119.5 the source's p.p.t. prover writes at most `t(|x|)` bits; for Definition
   116.1, whose prover is unbounded, it is a normal form (a verifier of time `t(|x|)` reads at
   most `t(|x|)` bits of each message; gate 03e round 2, finding 7). Against a cheating prover the verifier's
   work is polynomial in the message length, not in `|x|` (gate 03e, finding 1; ruling G3-3).
9. Soundness `1 − ε < Pr[out = [false]]` literal; provers have polynomial coin tapes (no loss by
   averaging); completeness `uprob = 1` (every coin pair).
10. `ZK`/`HVZK`: strict PPT simulators; auxiliary inputs bounded by `∀ Lz : PolyExpr`;
    simulator and distinguisher at parameter `|x|`; views encoded as `⟨⟨x, z⟩, ⟨r, msgs⟩⟩`.
11. GI: statistical ZK with negligible δ (`gi_statZK`; truncated simulator, rejection-sampled
    permutations). 3COL: computational ZK (`col_zk`; `Commitment.multiHiding`, with the
    statistical errors of the `n|E|`-attempt simulator and of the rejection-sampled edges, colour
    pairs and colour permutations absorbed); not statistical, since with a perfectly binding
    commitment two inequivalent colourings give statistically distinct views (gate 03e round 2,
    finding 1; gate 03g, finding 6). One-iteration ZK; the `n`-fold protocols get soundness only
    (sequential composition is §7.2.1, out of scope). `PerfectZK` and `PerfectZKAbort` are
    stated, but no source protocol attains them under D8/D10; `PerfectZKAbort.statZK` turns the
    abort form into statistical ZK with error `2^{-|x|}` (gate 03e, finding 2; ruling G3-4).
12. `Commitment`: binding clause with `v₀ ≠ v₁` (source error); `n` an explicit argument,
    colours padded to `n` bits (DQ4).
13. `PublicKeyScheme`: clause (4) (message enumerator) dropped; `0^n` is the canonical message.
14. `Collection`: `Gen(1^n) = ⟨i, t⟩`; domain samplers within negligible statistical distance of
    uniform (`SampleClose`), hardness on the ideal uniform `x ← D_i` (`uexp` over `Gen`'s coins).
15. Candidates: `A` receives `1^n` in Assumptions 30.1/52.2/53.1; `Π_n` throughout; `p ≠ q`
    (odd / Blum) in RSA and Rabin; expected time replaced by strict PPT with `2^{-n}` failure.
16. `WorstCaseOneWayLit` (run-3 audit P3-2; reworded at gate 03b, finding 9): when `outLen` is
    constant, so that `|f(x)|` does not determine `n`, the literal form can hold for families
    that are trivially invertible given `1^n` (e.g. the constant family, or `f n b = b ⊕ [n odd]`
    on one bit), an artefact of D5's typed inverse; the `1^n` form `WorstCaseOneWay` is the
    headline, and `toParam` applies whenever `outLen` is non-constant (for `PolyExpr`,
    injective ⇔ non-constant).
17. `TrapdoorCollection.inv_spec` (run-3 audit P3-5): the inverter receives `⟨t, y⟩` without the
    index. The classes coincide (gate 03b, finding 6): a text TDP becomes one of this shape with
    `t' := ⟨i, t⟩` (`Gen'` outputs `⟨i, ⟨i, t⟩⟩`; the trapdoor never reaches the adversary), and
    this shape is a text TDP whose `Inv` ignores `i`. RSA's trapdoor is `⟨N, d⟩` (text: `d`) and
    Rabin's inverter recomputes `N = pq`.
18. `Collection.glPad m henc`, `expCollection H G hV` (run-3 audit P3-1): the encoding-length
    hypothesis resp. the validity bridge are arguments of the definitions; `expGen` outputs the
    fixed valid instance `dlDefaultIndex` below the instance generator's threshold `n₀`. Cost of
    `henc` (gate 03c, finding 3; ruling G3-7c): a non-constant `PolyExpr` is strictly
    increasing, so an index generated at two parameters forces `m` constant, and no candidate of
    the library satisfies `henc` as parametrized (`rsaTrapdoor`: `2·max(n, 2)`-bit elements,
    `rabinBlumTrapdoor`: `2·max(n, 3)`, `expCollection`: `dlDefaultIndex` below `n₀`); Thm 104.4's
    reading "from trapdoor permutations" (`glPad_hardCore`, `exists_glPad_singleBitSecure`) holds
    for TDPs whose generated indices encode elements in exactly `m(n)` bits. A per-index form
    (`|encD_i x| = |encD_i default| ≤ m(n)`) would admit the candidates; not formalized.
19. Theorem 63.1 (run-3 audit P3-4): `theorem_63_1`, `fUniversal_*` are conditional on an
    encoding scheme with `CanonizerExp c`; no instance proved (`exists_canonizerExp`).
20. `ddhReal`/`ddhRandom` (run-3 audit P8-1): the DDH exponents `a, b, z` are read from
    `n · n`-bit seed blocks by rejection (`ddhExpo`, within `2^{-n}` of uniform, D10) — product
    seeds, never a dependent sum (uniform-on-`Σ` tilts the instance law by the fibre sizes).
21. `ExpGroupGen.FullLengthExcept δ` (run-3 audit P8-2): full-length primes except on a set of
    the generator's coins of probability `δ n`; `fullDLCollection_hardCore` and `elGamal_secure`
    take `∃ δ, Negligible δ ∧ G.FullLengthExcept δ` (full length on every coin string is not
    known to be achievable in polynomial time).
22. `uprob_adaptive_guess`, `uprob_gni_rep_cheat` (run-3 audit P10-1/P10-2): the auxiliary coin
    type (`W`, `ρ`) is assumed nonempty — `uprob` on an empty type is `0`, so the exact `2^{-m}`
    fails for `Empty`; every consumer passes a tape type `Fin k → Bool`.
23. Thms 35.1, 35.2 and Claim 38.2 (gate 03b, finding 8): the direct products are families at
    parameter `n` whose adversaries receive `1^n` (the text: `1^{n·m(n)}`, `1^{2n}`;
    interderivable, so negligibility in `n` and in `n·m(n)` coincide); Claim 38.2 runs
    `T(n) + 1 = 2n·m(n)·n^c + 1` rounds with Garg's threshold `μ₀/(2m)` (the text: `2nm²p(n)`
    rounds, threshold `1/(2m²p(n))`), with the margin `(T + 1)·2^{-n}` for the rejection-sampled
    positions.
24. `Collection.encD_decD` (gate 03b, finding 1; ruling G3-1): decoders are canonical — a string
    decodes only if it is the encoding of its value — so the outputs of the sampler and of the
    trapdoor inverter are encodings ([PS10, Defs 41.1 (2), 56.1 (6)]: "an element of `D_i`",
    "computes `f_i^{-1}(y)`"); every decoder of the library is canonical.
25. `PRG.expands` (gate 03c, finding 1; ruling G3-2): expansion at every seed length, `n = 0`
    included (Def 77.1 (2)'s `|G(x)| > |x|` read literally at `x = ε`). A `PolyExpr` stretch has
    coefficients in ℕ, so stretches with `ℓ(0) = 0` (exactly `2n`) or `ℓ(1) = 1` (`n^c`) are not
    `PRG`s, although the text uses them (the length-doubling `G` of Alg 92.1 and Thm 97.3; Lem 80.5's
    "for any polynomial `ℓ`"); `PRG.expand`/`prg_expand` take the same `hℓ : ∀ n, n < ℓ(n)`. Thm 97.3
    uses the separate predicate `DoublingPRG`, produced from any secure `PRG` by `PRG.doubling`
    (`PRG.Secure.doubling`, `Asymptotic/PRF.lean`); elsewhere `2n + 1`, `n^c + 1` are reached by
    `prg_expand` from the one-bit truncation `PRG.truncate`, and shorter outputs by truncation
    (`PRG.Secure.truncateTo_easy`/`_negligible`). Alg 92.1 needs only `n ≤ ℓ(n)`. "PRGs exist" has the
    same meaning under every reading (truncate to `n + 1` bits, change below `n₀`), and no statement
    of ch. 2–8 is vacuous by it.

---

## 6. Workstreams, ownership, coverage, build order

Every **core** item of the three inventories appears exactly once (68 + 82 + 69 = 219 ids).
Optional/deferred items are listed in §6.2 for information. Paths are relative to the
worktree. New files not in the plan's layout are marked (new).

| WS | Name | Owned files | Inventory ids covered | Depends on |
| --- | --- | --- | --- | --- |
| M1 | machine-core | `TCSlib/Complexity/Randomized/PolyExpr.lean` (new), `TCSlib/Complexity/Randomized/PPT.lean`, `TCSlib/Complexity/Randomized/NonUniform.lean`, `TCSlib/Complexity/Randomized.lean` (facade), `TCSlib/Cryptography/Asymptotic/Adversary.lean` (new) | Def-23.4, Def-23.5, Def-24.6, Def-26.8 | — |
| M2 | machine-primitives-closure | `TCSlib/Complexity/Randomized/Primitives.lean` (new), `TCSlib/Complexity/Randomized/Closure.lean` | Claim-26.3 | M1 |
| M3 | machine-repetition | `TCSlib/Complexity/Randomized/Repetition.lean` | Inf-4.3 | M1, M2 |
| S | sampling | `TCSlib/Cryptography/Asymptotic/Sampling.lean` (new) | (concrete lemmas C4, C5, C10 of inventory-ch2 §4; DQ1-A) | M1 |
| C2a | onewayfunctions | `TCSlib/Cryptography/Asymptotic/OneWay.lean` | Def-26.1, Def-27.3, Def-28.4, Thm-35.1, Thm-35.2, Claim-38.2 | M1, M2, M3, S |
| C2b | collections | `TCSlib/Cryptography/Asymptotic/Collections.lean` | Def-41.1, Thm-42.2, Def-55.1, Def-56.1, Def-78.3.coll | C2a, S |
| C2c | universal-owf | `TCSlib/Cryptography/Asymptotic/Universal.lean` | Thm-63.1, Alg-64.2, Lem-64.3, Claim-65.1, Claim-65.2 | C2a, M2, M3 |
| NT | number-theory | `TCSlib/Cryptography/NumberTheory.lean` (facade), `TCSlib/Cryptography/NumberTheory/Chebyshev.lean`, `…/Euclid.lean`, `…/ModExp.lean`, `…/Units.lean`, `…/Primality.lean`, `…/QuadraticResidues.lean` | Def-29.3, Thm-31.3, Claim-33.1, Alg-43.2, Claim-43.3, Claim-44.5, Alg-45.5, Claim-47.2, Cor-48.12, Thm-54.3, Def-49.1, Alg-49.13, Thm-49.14, Lem-50.15a, Alg-50.16, Lem-51.17, Def-57.0, Lem-57.1, Thm-58.2, Def-59.3, Thm-59.4, Thm-60.5, Cor-60.6, Claim-60.7, Claim-62.1, Claim-63.1 | S (Lem-51.17 closeness), M3 (Lem-51.17(iii) only) |
| Cand1 | candidates-factoring | `TCSlib/Cryptography/Candidates.lean` (facade), `TCSlib/Cryptography/Candidates/Arithmetic.lean` (new), `…/Concrete.lean` (new), `…/Factoring.lean` | Def-29.1, Asm-30.1, Thm-33.5, Alg-33.6, Claim-34.1, Thm-36.3, Claim-36.2, Alg-37.4, Thm-51.1 | C2a, C2b, NT, S |
| Cand2 | candidates-rsa-rabin | `TCSlib/Cryptography/Candidates/RSA.lean`, `…/Rabin.lean` | Asm-53.1, Thm-53.2, Thm-55.2, Alg-55.3, Thm-57.2, Thm-61.7, Thm-61.8, Alg-62.9, Claim-62.2, Thm-63.10 | Cand1, NT, C2b |
| Cand3 | candidates-dl-elgamal | `TCSlib/Cryptography/Candidates/DiscreteLog.lean`, `…/DiscreteLogHardcore.lean` (new), `…/ElGamal.lean` (new) | Asm-52.2, Thm-52.3, Lem-84.1, Lem-84.1.0, Lem-84.1.1, Alg-84.2, Alg-85.a, Lem-84.1.3, Lem-84.1.4, Lem-84.1.5, Asm-105.1, NT-105.a, Alg-106.2, Claim-107.a, Thm-107.3 | C2b, NT, C3a, C3f, M3 |
| C3a | ensembles | `TCSlib/Cryptography/Asymptotic.lean` (facade), `TCSlib/Cryptography/Asymptotic/Ensembles.lean` | Def-69.3, Def-69.4, Lem-71.5, Lem-71.6, Claim-73.a, Lem-73.8, Claim-73.b, Ineq-189.a | M1, M2, M3, S |
| C3b | pseudorandom-nextbit | `TCSlib/Cryptography/Asymptotic/Pseudorandom.lean`, `TCSlib/Cryptography/Asymptotic/NextBit.lean` (new) | Def-74.1, Def-75.2, Rem-75.3, Thm-75.4, Thm-75.4.c, Thm-75.4.1, Thm-75.4.2, Alg-76.5, Def-77.1 | C3a |
| C3c | hardcore | `TCSlib/Cryptography/Asymptotic/HardCore.lean` | Def-78.3, Thm-79.4, Lem-80.5, Cor-81.7, Thm-87.3, Thm-87.3.a, Thm-87.3.b, Thm-87.3.c, Thm-87.3.1, Thm-87.3.2, Thm-87.3.3, Fact-88.4, Alg-88.5, Alg-89.6, Thm-87.3.6, Thm-87.3.7, Thm-87.3.8, Thm-87.3.9, Thm-87.3.coll | C3b, C2a, C2b, M3 |
| C3d | encryption | `TCSlib/Cryptography/Asymptotic/Encryption.lean`, `TCSlib/Cryptography/ZeroKnowledge/Encryption.lean` | Def-24.7, Def-91.1, Alg-92.1, Claim-92.a, Thm-92.2, Def-93.1, Thm-94.2, Def-111.1, Thm-112.2, Thm-112.2.i, Thm-112.2.ii | C3b, M2 |
| C3e | prf-multimessage | `TCSlib/Cryptography/Asymptotic/PRF.lean`, `TCSlib/Cryptography/Asymptotic/MultiMessage.lean` (new) | Def-95.a, Claim-95.b, Def-96.1, Claim-96.b, Def-96.2, Cor-97.a, Constr-97.b, Claim-97.c, Thm-97.3, Thm-97.3.1, Thm-97.3.2, Thm-97.3.3, Alg-99.1, Thm-99.2, Thm-99.2.1, Thm-99.2.2, Thm-99.2.3 | C3c, C3d, M3 |
| C3f | publickey | `TCSlib/Cryptography/Asymptotic/PublicKey.lean` | Def-102.1, Def-102.2, Def-103.c, Thm-103.d, Def-103.e, Thm-103.f, Alg-104.3, Lem-104.a, Thm-104.4 | C2b, C3c, C3a |
| C4a | zk-model | `TCSlib/Cryptography/ZeroKnowledge.lean` (facade), `TCSlib/Cryptography/ZeroKnowledge/Interaction.lean`, `…/InteractiveProofs.lean`, `…/Defs.lean`, `…/Encoding.lean` (new) | Def-114.a, Def-114.b, Def-115.a, Def-115.b, Def-115.c, Def-115.d, Def-116.a, Def-116.b, Def-116.1, Def-117.a, Def-119.5, Def-121.1, Def-121.2, Def-122.a, Def-191.11, Inf-4.1, Inf-4.2, Inf-4.4 | M1, M2, S |
| C4b | zk-graph-isomorphism | `TCSlib/Cryptography/ZeroKnowledge/GraphIsomorphism.lean`, `…/GraphIsomorphismZK.lean` | Def-117.e, Def-118.a, Prot-118.3, Lem-119.a, Lem-119.b, Lem-119.c, Lem-119.d, Prop-118.4, Prot-120.6, Lem-120.a, Lem-120.b, Lem-120.c, Lem-120.d, Prop-120.7, Thm-122.3, Thm-122.3.hv, Thm-122.3.trunc, Alg-123.4, Lem-123.5, Claim-123.b, Claim-123.d | C4a, M3, S |
| C4c | zk-commitment | `TCSlib/Cryptography/ZeroKnowledge/Commitment.lean` | Def-126.3, Claim-126.a, Thm-126.4, Alg-127.a, Claim-127.b, Claim-127.c, Claim-127.d | C4a, C3c, C3a |
| C4d | zk-3col-np | `TCSlib/Cryptography/ZeroKnowledge/ThreeColoring.lean` (split into `ThreeColoring/Protocol.lean` and `ThreeColoring/Simulator.lean` if > 600 lines), `TCSlib/Cryptography/ZeroKnowledge/NP.lean` | Def-124.f, Claim-125.a, Prot-127.5, Claim-127.e, Lem-127.f, Lem-127.g, Claim-127.h, Prop-127.6, Alg-128.7, Claim-128.a, Prop-128.8, Claim-129.a, Lem-129.b, Claim-129.c, Claim-129.d, Thm-124.1, Def-124.a, Claim-124.d | C4c, C4a, M3, S |
| A | audit-integration | `audits/pass-shelat/Checks.lean` (append only), facade registration in `TCSlib.lean`/`TCSlib/ComputationalModels.lean` (integrator) | — (sanity prints: `NUPPT.nonempty`, `not_strongOneWay_id`, `StrongOneWay.weak`, `Indist.refl`, `OracleEnsemble.Indist.refl`, `npProtocol_interactiveProof`, and every headline theorem) | all |

### 6.1 Build order (run 2 statement phase)

1. **M1** (serial; everything imports it) — then **M2 and M3 statements** (serial; their fills
   are the machine agent's run-4 work and may lag).
2. **S** (small; concrete) in parallel with the statement skeletons of **C2a, C3a, C4a, NT**.
3. **C2b, C3b, C4b, Cand1, C2c**.
4. **C3c, C3d, C4c, Cand2**.
5. **C3e, C3f, Cand3, C4d**.
6. **A** after each workstream lands (append its `#print axioms` lines) and at closure.

Fill-phase critical path: `pairSplitAt` → `unaryMul` → `Closure.lean` → `iterateFind`
→ {Thm 35.1, `Indist.copies`, GL, GGM, GI/3COL simulators} in parallel.

### 6.2 Optional / deferred items (not counted; for information)

Ch. 2: Def-21.x, Rem-22.1, Def-27.2, Rem-28.1, Claim-32.4, Claim-44.4, Thm-45.6, Def-46.x,
Thm-46.8, Claim-47.1, Thm-47.10, Cor-48.11, Ex-*, Def-52.1, Rem-52.2, Claim-53.1, Claim-53.2,
Claim-58.1, Thm-58.3, Claim-59.1, App-A.*, Thm-189.9, Def-191.10, Def-191.11 (ch. 2 copy);
deferred: Rem-24.2, Rem-26.2 (optional module `Randomized/Sequence.lean`), Rem-27.1, Rem-29.2,
Rem-33.2 (hypothesis in `Candidates/Arithmetic.lean`), Rem-43.6, Rem-48.2, Lem-50.15b,
Rem-49.3, Rem-50.2, Ex-58.3, Thm-188.7, Lem-189.8, Def-192.12.
Ch. 3: optional Claim-67.a, Rem-72.7, Claim-72.a, Ex-72.b, Thm-75.4.conv, Constr-77.a,
Claim-78.a, Claim-78.b, Claim-79.a, Claim-96.a, Claim-96.c, Claim-103.a, Claim-103.b,
Constr-104.a, Claim-106.a, Claim-106.b, Def-107.b, Claim-107.c, Thm-188.7, Lem-189.8;
deferred Claim-78.c, Constr-82.a/b, Constr-83.a/b, Claim-83.c, Claim-107.d.
Ch. 4: optional Def-111.a, Def-111.b, Claim-112.a, Claim-112.b, Def-117.b, Claim-117.c,
Claim-118.b, Def-119.e, Claim-122.b, Def-191.10, Def-192.12; deferred Claim-117.d,
Claim-118.c, Claim-119.f, Def-121.a, Claim-122.c, Claim-123.a, Claim-123.c, Claim-124.b,
Claim-124.c, Claim-124.e.

---

## 7. Consolidated errors and gaps in the source text

Outright errors (to replace the plan's seeded list):

**Chapter 2.**
1. Algorithm 64.2 / Theorem 63.1: `f_universal(⟨M, x⟩) = M(x)` omits the machine description
   from the output; the proof is invalid. Corrected definition outputs `⟨M, M(x)⟩`.
2. §2.6.5, `L_N`: "`N = u2^j`" should be `N − 1 = u·2^j`; the condition stated with `i = j`
   only is vacuous; intended `∀ i < j, α^{u2^{i+1}} = 1 → α^{u2^i} = ±1`.
3. Claim 32.4 is false as a strict inequality (`x = 1, p = 2`); correct form
   `p^{ν_p(C(2x,x))} ≤ 2x` (`Nat.pow_factorization_choose_le`).
4. §2.6.6 (p. 50): prime probability "exceeds `1/n`"; Theorem 31.3 gives `1/(2n)`.
5. Theorems 60.5, 61.7, 61.8, 63.10 and Corollary 60.6 need `p ≠ q` odd primes (`Π_n` contains
   2 and allows `p = q`); `Φ(pq) = (p−1)(q−1)` (p. 47) and Assumption 53.1 need `p ≠ q`.
6. Theorem 61.8 (⇐) needs square roots modulo arbitrary primes; only `p ≡ 3 (mod 4)` is proved
   (Theorem 58.2); Theorem 63.10's `Gen` needs the density of primes `≡ 3 (mod 4)` (not in
   Mathlib; explicit hypothesis).
7. Theorem 59.4: "`zinQRq`" typo; the `⇒`/`⇐` labels of the proof are swapped.
8. Theorem 52.3: `R_i = G_p`, `f_{p,g}` should be `G_q`, `f_{q,g}`; Assumption 52.2 gives `A`
   only `g^x` (needs `q, g`); `G_q` unspecified.
9. Theorem 53.2's proof samples `e ← Z_N^*` (should be `Z*_{Φ(N)}`).
10. Definition 56.1(5): `≤ e(k)` should be `e(n)`.
11. Definition 41.1(4): "p.p.t. `A`" contradicts the nuPPT convention; `f(A(1^n, i, y)) = y`
    should read `f_i`; `R_i` unconstrained; `D_i` must be finite.
12. Theorem 42.2 proof idea: "`I = {0}`, `D_0 = ℕ`" — the domain must depend on `n`.
13. §2.4.3 proof: "for each `j ∈ [1, n]`" should be `[1, m]`; the bound chain with the extra
    factor `m` is garbled.
14. Algorithm 33.6 line 7: `A(1^n, z′)` should be `A(1^{2n}, z′)`; Algorithm 37.4 must output a
    verified factor.
15. Lemma 189.8 garbled ("`1 − 2??`"), proof unfinished; Theorem 188.7's threshold `ε` should be `εn`.
16. §2.3 attack `A(z) = (2, z/2)` returns a preimage of a different input length.
17. Claim 43.3 case 2: "`b > 2^n`" should be `b ≥ 2^n`; the precondition allows `b = 0`.
18. p. 61 example `N = 77`: numbers garbled.
19. Theorem 63.1 proof: "hardness amplification from §2.3" should be §2.4; budget `|y|^3`
    becomes `(|y|+1)^3`.
20. Theorem 49.14: "with probability `1 − 2^{−t}`" should be "at least". (Lemma 50.15's "`N > 2`
    composite" is right as stated: for even `N > 2` the liars also form a proper subgroup, since
    `(−1)^{N−1} = −1`; the formal lemma restricts to odd `N` only for convenience. Corrected on gate
    03f2, F01.)
21. p. 27: "NP ⊄ BPP ⟺ worst-case OWFs exist" mixes uniform BPP with non-uniform inverters.
22. Theorem 45.6 / p. 46: the remark that Euler's theorem "removes the restriction `x < N`"
    refers to a restriction Algorithm 45.5 does not have.
23. Theorem 31.3 proof: "each term is greater than 2" — the term `(x+x)/x` equals 2.
24. Theorems 61.8 / 55.2 mix `n` and `k`; Theorem 61.7 writes `Z_n^*`; Theorem 51.1's `D_i`
    uses exactly-`i/2`-bit primes while Assumption 30.1 uses `Π_n`.
25. Theorem 35.1's `m = 2nq(n)` is kept, but the uniform position of Algorithm 38.5 is not
    exactly samplable by a bit-coin PPT unless `m` is a power of two (D10).

**Chapter 3.**
26. Theorem 87.3 says `⟨x, r⟩` is hard-core "for `f`"; it is for `g(x, r) = (f(x), r)`.
27. Lemma 84.1 vs Assumption 52.2: the assumption is for prime-order `G_q`, the lemma and
    Algorithm 84.2 use `Z_p^*` (even order); `x ← Z_p` should be `x ← Z_{p−1}`; "`ε = s(n)`"
    should be `1/s(n)`; the range reduction "as we will show later" is never shown; the
    good-instance averaging over `(p, g)` is missing; the p. 86 analysis bounds
    `Pr[noinc | low]` by `1/2 − ε/2`, the complementary event of its own increment rule (`lo`
    counts disagreements `b_i ≠ half(r_i)`). (Run-3 audit P8-3: line 11's root selection is
    consistent with `half`'s convention, and the strict `half_m(x) := [2x < m]` of the
    formalization is a harmless variant, not needed by the halving invariant.)
28. Theorem 107.3 / Algorithm 106.2: El Gamal with `m ∈ Z_p^*` is insecure under DDH on `G_q`
    (Legendre symbol of `c_2`); correct with message space `G_q`; `Gen` draws `g ∈ Z_p` (may be
    `0, ±1`); the square-vs-generator sampling term `1/q` is missing.
29. Definition 75.2 quantifies `i ∈ [0, ℓ(n)]` (bit `t_{ℓ(n)+1}` does not exist).
30. Definition 78.3 mixes `k` and `n`.
31. Definition 96.1: `{O'_n} ≈ {O'_n}` typo.
32. Theorem 104.4 omits the hard-core bit from its hypothesis; its proof writes `D` for `A`.
33. Algorithm 76.5 draws `U_{ℓ(n)−1}` (should be `U_{ℓ(n)−i}`); Theorem 75.4's proof defines
    `H̃^i` with a stray `u_{l(m)}`, mixes 0/1-indexing, and its last display has `A(t) = 1` for
    `A(t) = b`.
34. Lemma 80.5's proof: `m(n)`/`ℓ(n)` interchanged; hybrids must start at `i = 0`; `M(y)` reads
    bit-then-seed against the construction's seed-then-bit.
35. Theorem 99.2's collision bound `C(q(n), 2) 2^{−n}` should be `C(q(n)+1, 2) 2^{−n}`.
36. Theorem 92.2's proof: hybrid `H²` mislabelled ("`m_1`"); gap `1/(3p(n))`, not `1/(4p(n))`.
37. Theorem 87.3's final constant: text `ε^3/(32n)` (with `ε' = ε/2`) versus the concrete
    layer's stronger `ε^3/(16n)` (the plan's seeded `ε^3/(4n)` note compares `ε'` with `ε`).
38. Lemma 71.6: the proof gives `ε/(m−1)`, the statement `ε/m` (harmless); Corollary 81.7 lists
    `ℓ(n)+1` bits.

**Chapter 4.**
39. Proposition 120.7 says "for `L_niso`"; it is for `L_iso`; its proof reverses the maps
    (`π(H) = G1`, `σ(π(H))`) and renames the graphs.
40. Definition 126.3, binding: omits `v₀ ≠ v₁`; as printed unsatisfiable.
41. Proposition 127.6's proof: "repeated `|E|^2` times" vs the protocol's `n|E|`.
42. Protocol 127.5: witness listed as `c_0 … c_m` (should be `c_1 … c_n`); Simulator 128.7:
    "`k ∈ [m] \ {i', j'}`" should be `[n]`.
43. Protocol 127.5's verifier "accepts iff `c'_i ≠ c'_j`" without checking the openings — unsound;
    undefined for `E = ∅`; `Com` on 2-bit colours has security parameter 2 (pad to `n`).
44. Theorem 122.3 claims perfect ZK for the `n`-iteration protocol; the proof covers one
    iteration and relies on §7.2.1; with bit-coin parties perfect completeness and perfect ZK
    cannot both be literal (`n!` is not dyadic); same for Protocol 118.3's `σ` and 127.5's
    colour permutation.
45. Definitions 121.1/121.2 and Proposition 128.8 bound by `e(n)` with `n` undefined
    (`n = |x|`); Definition 121.2 relies on expected polynomial time.
46. Proposition 128.8's proof: hybrid count `2n|E|` vs `n|E|` attempts; "`S̃_{e+1}` … `S̃_{e+1}`"
    typo; the `6|E|` sub-hybrid is unnecessary; p. 129 prints "If we assume that `S′` never
    outputs fail" and "`S′` fails with probability …" for `S″` (gate 03g, M2).
47. §4.7 step 2: "Cook's reduction applied to the witness" needs a Levin reduction (never
    defined); "execute `(P, V)` on `x'`" should be `(P', V')`; Theorem 126.4 needs a hard-core
    predicate (Theorem 87.3) and uses a single OWP, not Definition 55.1's collection.
48. Appendix B, Definition 191.11: "`R_L(x) = {y : (x, y) ∈ L}`" should be `∈ R_L`.
49. Proposition 118.4's proof uses `G1, G2` for `G0, G1`; "the prover runs in exponential time"
    is only an upper bound; the adaptive-prover argument is hidden.
50. §4.4: a round ends when the active machine *halts* ("the protocol ends"), which makes the
    literal `Pr[out_V = 0]` of Definition 116.1 unsatisfiable against a prover that halts at
    once; time complexity `t(|x|)` "regardless of messages" leaves the simulator's call to `V*`
    on long `z` ill-defined (D8 reading).
51. Definition 121.2 read literally (`∀ z ∈ {0,1}*`, the distinguisher polynomial-time in its
    input) fails for the 3-colouring protocol 127.5 of Proposition 128.8: with `|z|` exponential,
    the distinguisher, whose input (the view) contains `z`, opens the perfectly binding
    commitments by exhaustive search, and on a graph with two proper colourings outside one
    colour-permutation orbit it separates the two real views, which the witness-blind simulator
    cannot match (protocols with exactly simulable views are not affected; gate 03e round 2,
    finding 6). So the bound `∀ Lz : PolyExpr` on `|z|`, and
    indexing the distinguisher's advice by `|x|` rather than by its input length, are necessary,
    not only convenient (gate 03e, finding 9; `ZeroKnowledge/Defs.lean`'s module docstring).

Gaps the formalization fills (not errors): Theorem 42.2 (⇒) and Theorem 57.2 ("exercises");
the PKE single ⇒ multi-message theorem and the bitwise theorem (p. 103); Theorem 107.3
("exercise") with the `1/q` term; Lemma 84.1's range reduction and averaging; the square-root
algorithm for `p ≡ 1 (mod 4)` (restricted to `3 (mod 4)` instead); Miller–Rabin's composite
case (proved: `two_mul_card_mrLiars_le`, `uprob_millerRabin_le`); Chernoff (replaced by Chebyshev for pairwise independence); Theorem 112.2's
message sampler (`0^n`); Theorem 124.1's string-level Levin reduction to 3COL (hypothesis).

---

## 8. Open questions for the maintainer (everything else is decided above)

1. **Conditional candidates.** Every number-theoretic candidate theorem (Thms 33.5, 36.3, 51.1,
   52.3, 53.2, 55.2, 57.2, 61.7, 61.8, 63.10, 107.3, Lem 84.1) is stated with the hypothesis
   bundle `Candidates/Arithmetic.lean` (polynomial-time machines for binary `mul`, `add`,
   `sub`, `divMod`, `xgcd`, `modExp`, comparison, bit length, primality — the three fields
   `add`, `sub`, `size` added by the run-3 audit repair P7-1, since the generators and
   reductions of §2.9–§2.12 decrement, add, subtract modulo `N` and read bit lengths) because
   the library has no binary-arithmetic
   machines (inventory F1/F6). `#print axioms` stays clean but the theorems are conditional.
   Confirm this is acceptable as the campaign's headline form, or fund the arithmetic machines
   (research-level, ≥ 5k lines).
2. **Theorem 124.1 ("ZK for NP").** Core form (A): every `(L, R_L)` with a Levin reduction to
   3COL, the reduction being an explicit hypothesis; the "every `L ∈ NP`" form needs a
   string-level Levin reduction `SAT3 → 3COL` (the repository's is graph-level with a private
   witness map). Confirm form (A) as the headline or fund the string reduction.
3. **Rabin/RSA scope.** Rabin results restricted to Blum integers (`p ≠ q`, `p ≡ q ≡ 3 (mod 4)`)
   with the density of primes `≡ 3 (mod 4)` as an explicit hypothesis of Theorem 63.10's `Gen`
   clause; RSA and factoring assumptions restricted to `p ≠ q`. Lemma 84.1's asymptotic form
   restricts `Gen_DL` to `p ≡ 3 (mod 4)` (square roots). Confirm these restrictions.
4. **Lemma 84.1 deliverable.** The concrete statement (Classical roots, `p ≡ 3 (mod 4)`) is
   core; is the asymptotic wrapper (the hardest ch. 3 fill) mandatory for closure, or may it
   remain sorried under its sketch if the fill stalls?
5. **Optional literal modules.** `NUPPTSeq` (Def 26.8 verbatim), `exists_queryTree`
   (`OracleTM` bridge) and `NUPPT.ofPartial` are specified as optional modules with one named
   admission each; confirm they are out of the mandatory core (they are not needed by any
   chapter 2–4 theorem). **Ruled** (decision log 2026-10-27): outside the mandatory core.
   The one admission in this area is the optional bridge
   `NUPPT.decides_of_decidesWithAdviceInTime` (decision log 2026-10-28; see D11).
6. **Encoding scheme for Theorem 63.1 (run-3 audit P3-4).** `theorem_63_1` and `fUniversal_*`
   are stated for schemes with an at most exponential canonizer (`CanonizerExp c`); the only
   scheme in the library (`Turing.exists_effectiveMachineCode`) has no bound on its canonizer,
   so the headlines are conditional. Ratified as an explicit hypothesis like `ArithmeticFP`
   (D11); the open problem `exists_canonizerExp` (a `Build/`-style parser-and-reserializer
   canonizer) is stated and sorried. Confirm, or fund the canonizer construction.

---

## 9. Appendix — the 53 statement stubs of the compiled scratch (owner workstream)

M1: `polyTimeComputable_unaryPoly` (needs M2's `unaryMul`), `NUPPT.decides_of_decidesWithAdviceInTime` (optional).
M2: `computesFunInTime_pairSplitAt`, `computesFunInTime_unaryMul`, `polyTimeComputable_pairTakePoly`,
`polyTimeComputable_pairDropPoly`, `NUPPT.exists_comp`, `exists_reparam`, `exists_reparam_advice`,
`exists_withAdvice`, `exists_split`, `exists_seq`.
M3: `polyTimeComputable_iterateFind`, `iterate`, `iterateEmit`, `majority`, `pairXor`, `pairEq`, `blockMap`.
S: `distAdv_le_of_statClose`, `StatClose.prod`, `StatClose.map`, `rejectionSample_uniform_of_some`,
`uprob_rejectionSample_none`, `statClose_rejectionSample`, `permFromCoins_uniform_of_some`,
`uprob_permFromCoins_none_le` (the last two may move to C4a/Encoding).
C2a: `weak_to_strong`, `strong_prod_two`, `StrongOneWay.weak`, `not_strongOneWay_id`.
C2b: `Collection.OneWay.exists_strongOneWay`.
C3a: `Indist.toLit`, `IndistLit.toIndist`, `Indist.refl`, `Indist.symm`, `Indist.push`, `Indist.trans`,
`Indist.copies`, `predict_eq`, `prediction_lemma`.
C3b: `NextBitUnpredictable.pseudorandom`.
C3d: `singleMessageSecure_iff_zeroKnowledge`.
C3e: `toOracleAdversary_boundedBy`, `OracleEnsemble.Indist.refl`.
C4a: `StatZK.zk`, `StatZK.hvzk`, `npProtocol_interactiveProof`.
C4b: `Riso_witnessRelation`, `gi_sim_H_dist`, `gi_sim_half`, `gi_efficientProverProofErr`, `gi_statZK`.

Compile command and outcome: `lake env lean briefs/pass-shelat/DESIGN-freeze-scratch.lean`
→ exit 0, 0 errors, 53 sorry warnings (2026-10-27).

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/resolutions-03e-r1.md =====

# Gate 03e (interaction, proof systems, ZK definitions, commitments, NP layer): round 1 resolutions

- **Round 1:** findings `findings/gate03e-findings.md`, verbatim, SHA-256
  `8af18f12965eb01b594de42d60e567b4ad5cb2810652a94f70f7daf0aef0a7e3`; head
  `a3c5fa8b72e50939822f22364647dc844a3914a0`. Counts: **0 blockers, 2 majors (#1, #2), 4 minors,
  11 notes.**
- **Review:** `review/gate03e-review.md`: no finding false; by its tables 15 true (#6 (c) left
  unverified) and 2 partly true (#5, #16). No severity change (2 majors, 4 minors, 11 notes).
  Corrections to the auditor's proposed fixes for #1, #5 (c), #12, #13 and the pack labels. Ten
  items missed by the auditor (M1–M10 below).
- **Rulings (user, 2026-11-05;** `QUEUE.md:116–129`; decision log rows "Gate 03 rulings G3-1 to
  G3-4" and "G3-5 to G3-8"**):** G3-3 (A) = R-03e-1 option 1, `Efficient` plus bounded honest
  messages in the definitions (#1); G3-4 (A) = R-03e-2 option 1, keep the perfect forms, state the
  cost, prove `PerfectZKAbort.statZK` (#2); G3-6 (A) = R-03e-3, approve the 15 `@[simp]` (#17);
  G3-7 (d) = R-03e-4, `InteractiveProofErr.seqRep` in prong C (#3); G3-5 (A) for the copy
  `negligible_const_zero` (DL-13). Q-1 (no cap on `V*`) stands (#7).
- **Repair:** worker commit `30f90d36ab23d8f6b9ac99e4608c38174f3bfcb1` (on `a3c5fa8b…`), merged
  with #198's head as `b925421ece04d3189f5fc8c6ed4c6884e5caae49` = PR #199's head, merged into
  `cryptography/pass-shelat-ch2-4` by `af91d53a414cdad6bbb61cecdc13f5e0e956d0b1`. Evidence
  `evidence-repairs/03e/` (31 downstream modules on the stacked state; `Checks` 328 prints, 57
  `sorryAx`); the prints below are also in `evidence-repairs/03ac/checks-axioms.log` at #201's head
  (`0c348ff94cacf24d96d99078c9dd9e328530c8d2`, which contains #199). Line numbers are at #201's head;
  Lean paths are under `TCSlib/Cryptography/ZeroKnowledge/`.
- **Outside ch. 2–4:** G3-7 (d) is prong C commit `9e6f08bb28b2fcebfa845d47a9fd6e1ed281f951`; prong
  C's re-sync to G3-3 and G3-4 is in gate 06's integration to-do
  (`gates/06-ch5-8-statements/PLAN.md:55–57`).

| Finding | Severity (after review) | Resolution |
|---|---|---|
| 1 | major | **Fixed** (G3-3). `Protocol.ProverBounded` is in `Interaction.lean:331–337`; `InteractiveProof(Err).complete` bounds the honest messages (`InteractiveProofs.lean:126–128, 149–151`), `EfficientProverProof(Err)` has `boundedP` (:346, :361), with bound lemmas (`InteractiveProofs.lean:466`, `NP.lean:273`, `GraphIsomorphism.lean:926, 930, 935`, `ThreeColoring/Protocol.lean:562, 580, 605`), the "PPT" docstrings replaced, statements re-proved unchanged, prints standard. **Fixed (records, after #201 merged):** DESIGN §5 item 8 (`briefs/pass-shelat/DESIGN.md:1009–1014`) now states the bounded-message convention; the 03e repair had not amended (review §1.1); prong C's local `ProverBounded` is **Scheduled** for gate 06 integration. |
| 2 | major | **Fixed** in ch. 2–4 (G3-4); prong C scheduled. The cost is stated on `PerfectZK` and `PerfectZKAbort` (`Defs.lean:173–180, 189–196`) and in the module docstring (:50–57); `PerfectZKAbort.statZK` (error `2^{-\|x\|}`), `.zk` and `perfectZK_zeroRounds` are proved (:535, :596, :269), and `GraphIsomorphismZK.lean:43–48` cross-references. **Fixed (records, after #201 merged):** DESIGN §5 item 11 (`DESIGN.md:1019–1023`) no longer says "`PerfectZKAbort` stated as the perfect form": no source protocol attains the perfect forms; GI is `StatZK`. **Fixed (records):** the Thm-175.1 row of `inventory-ch5-8.md`. **Scheduled:** prong C's `SequentialZK.lean` (:41–45, `PerfectZKAbort.seqRep` through `statZK`) at gate 06 integration; the `inventory-ch5-8.md:130` row is not named there. |
| 3 | minor | **Fixed.** Titles retitled to "a zero-knowledge protocol with soundness error …" (`NP.lean:563–581, 595–607`); tied forms `exists_commitment_zk_proof_of_owp_levinReduction`, `zk_proof_of_witnessRelation(_of_owp)` (:625–634, :679, :698); the text's Thm 124.1 recorded as debt for ch. 7 (:575–576). The debt's discharge (G3-7 (d)): `InteractiveProofErr.seqRep` is in prong C (`9e6f08bb…`); the 3-colouring corollary is **Scheduled** for gate 06 integration (decision log, G3-7d row). |
| 4 | minor | **Fixed.** `zk_proof_of_witnessRelation` holds for every witness relation (`NP.lean:679`); `zk_proof_of_mem_NP` (:729) is its corollary, statement unchanged. |
| 5 | minor (partly true) | **Fixed.** (a) The `sorryAx` prints are annotated with the stubs they reach, `colRep_efficientProverProof` and `col_zk` (`audits/pass-shelat/Checks.lean:321–324`); (b) the five prints (:418–423), standard at #201's head. **Fixed (records):** (c)'s record fixes, an erratum on `audits/pass-shelat/run3-audit-summary.md:17` (it meant `Complexity/Randomized/Build/*`; of the 22 non-ZK `sorry` warnings in 03e's closure, 21 are `main`'s and one is `NonUniform`'s optional admission). (Committed in `dd492eac`; the 22 are round 1's 358-module closure. Stale drafting text removed on gate 03e round 2, finding 3.) |
| 6 | minor | **Fixed** in ch. 2–4; prong C scheduled. (a) `[Gol01]` in `Defs.lean:68, 102, 184` and `GraphIsomorphismZK.lean:87, 289`; (b) the p. 116 misquotes paraphrased (`Interaction.lean:46–48, 160–162`); (c) `[AB09, §2.3]` (`NP.lean:114–115`). **Scheduled:** the tag in prong C's `Composability/SequentialZK.lean:85`, now in gate 06's integration to-do (`gates/06-ch5-8-statements/PLAN.md`). |
| 7 | note | **Fixed.** `ZK`'s deviation records Q-1 (no cap on `V*`) and why the view is still bounded (`Defs.lean:146–152`). |
| 8 | note | **Fixed.** The dummy-move repetition convention, with its users, in `Interaction.lean:39–43`. |
| 9 | note | **Fixed.** The necessity argument for `Lz` and for advice indexed by `\|x\|` is in `Defs.lean:42–47`. **Fixed (records, after #201 merged):** the source issue is DESIGN §7 item 51, beside item 50. |
| 10 | note | **Fixed.** `perfectZK_zeroRounds` (`Defs.lean:269`); `gi_statZK` named as the substantive instance in the module docstring (:53–56). |
| 11 | note | **Fixed.** `WitnessRelation`'s docstring states the daylight with Def 191.11 (`InteractiveProofs.lean:239–249`). |
| 12 | note | **No change** needed (already met: `colVerify` checks the lengths); the optional sentence is added to `Commitment` (`Commitment.lean:107–110`). |
| 13 | note | **Fixed.** `exists_commitment_of_owp`, the text's Thm 126.4 (`Commitment.lean:905–911`); its print is standard. |
| 14 | note | **Fixed.** The padding remark now says "assumed" (`NP.lean:35, 131`); the pointer belongs to 03g. |
| 15 | note | **Fixed (records).** Both limits (Barak–Lindell on black-box strict-PPT simulation; everything indexed by `\|x\|`) are recorded in `SPINE-DESIGN.md` §S1, "Two limits of the interaction model D8 for ch. 5–8". |
| 16 | note (partly true) | **Fixed in the closing-round pack** (pack text): Thm-124.1 and Claim-124.d are owned by 03g and listed in 03e's pack as "(also 03g)". |
| 17 | note | **Recorded** (G3-6, `QUEUE.md:125`): the 15 are approved and unchanged: `encodeMsgs_nil/cons`, `moverIsV_true/false`, `exec_zero`, `withV_V/P/rounds/verifierFirst/self` (`Interaction.lean`), `mem_witnessLanguage`, `mem_witnessSet` (`InteractiveProofs.lean`), `bitCom_castSucc/last`, `owpComLen_eval` (`Commitment.lean`). |
| M1 | (review) a prefix cap does not give `ProverBounded` | **No change:** informed G3-3's option 1, which bounds the honest messages directly. |
| M2 | (review) the 3-colouring parties are not prefix-reading | **No change:** option 1 needs no redefinition; `colProtocol_proverBounded` (`ThreeColoring/Protocol.lean:605`) comes from `Com`'s polynomial time. |
| M3 | (review) the bound must sit in the completeness clause | **Fixed** (`InteractiveProofs.lean:126–128, 149–151`). |
| M4 | (review) the perfect-ZK obstruction is inherent | **Fixed:** both arguments (`n! ∤ 2^c`; dyadic simulator laws) are in `Defs.lean:173–180, 189–196` and `GraphIsomorphismZK.lean:43–48`. |
| M5 | (review) misleading text in DESIGN §5 item 11 and `SequentialZK.lean` | **Fixed** for DESIGN (§5 item 11, records); **Scheduled** for `SequentialZK.lean:41–45, 397–399` at gate 06 integration (`PLAN.md`). See #2. |
| M6 | (review) no soundness amplification for `seqRep` | **Fixed** in prong C (G3-7 (d), `9e6f08bb…`: `InteractiveProofErr.seqRep`, `EfficientProverProofErr.seqRep`); the 3-colouring corollary is **Scheduled** (gate 06 integration). |
| M7 | (review) pack labels; 03e's scope line | **Fixed in the closing-round pack:** 03g is 3-colouring and 03k graph isomorphism (`03e-pack.md:39` had them swapped). 03g's re-staged pack (`b13af7af`) points at the rulings. |
| M8 | (review) #12 met, #13's premise outdated, #5 (c) reconciled | **No change**; #5 (c)'s record correction is done (`run3-audit-summary.md:17`, `dd492eac`; corrected on gate 03e round 2, finding 3). |
| M9 | (review) "PPT strategy" field docstrings; second misquote | **Fixed:** no "PPT strategy" remains in `InteractiveProofs.lean`; `Interaction.lean:46–48` paraphrases. |
| M10 | (review) removing the 15 `@[simp]` breaks proofs | **No change** (G3-6 approves them). |

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/03e-pack-r2.md =====

# Gate 03e ([PS10] ch. 2–4, interaction, proof systems, ZK definitions, commitments, NP layer), round 2: external closing audit pack

**What is audited:** the repairs of round 1, on `cryptography/pass-shelat-ch2-4` at
`e79397eaf68b156b9db091f464741f6eb75b9c28` (the branch after #201 merged; its Lean files are #201's head `0c348ff9`).
- **Round 1** audited `a3c5fa8b72e50939822f22364647dc844a3914a0` and found **0 blockers, 2 majors (#1, #2), 4 minors and 11 notes**; no severity change in the review (`gate03e-findings.md`, in the bundle,
  verbatim).
- **The repair:** the 03e repair commit (G3-3: bounded honest messages; G3-4: the perfect forms' cost and `PerfectZKAbort.statZK`; minors and notes), merged in #199; the DESIGN records it missed (§5 items 8 and 11, §7 item 51) were committed after #201 merged. The full delta is `evidence-r2/03e/repair.diff.txt`; each round 1
  row's resolution is in `resolutions-03e-r1.md` (both in the bundle). The maintainer's review of
  round 1 is `review/gate03e-review.md` (in the bundle).
- **The deliverable:** **`gate03e-r2-findings.md`**.

The bundle holds this pack, then every file named below under a `## ===== <path> =====` header.
**The source is attached separately:** [PS10], 3rd ed., January 2010 (PDF; book page = PDF page −
12).

## Errata to the round 1 pack (review of round 1)

- **Scope line** (M7): pack 03g is 3-colouring and 03k graph isomorphism (round 1's line 39 had
  them swapped).
- **Inventory** (#16): Thm-124.1 and Claim-124.d are owned by pack 03g (its inventory list); this
  pack audits `NP.lean`'s forms of them as well ("also 03g").
- **Q-1** stands as ruled (no cap on `V*`; finding 7).

## Brief for the auditor

Round 2 does two things.
1. **It verifies the round 1 resolutions.** For each row of `resolutions-03e-r1.md` (the
   findings and the review's missed items `M1`, …) say whether the resolution is adequate:
   - **fixed**: the defect is gone, and the fix introduces no new one;
   - **recorded** or **scheduled**: accepted as declared, or deferred to a named PR or gate, and
     the record is accurate;
   - **not resolved**: say why.
2. **It audits the changed surface afresh** (section A of `evidence-r2/03e/repair.diff.txt`):
   - restate every new public declaration listed below in your own words, and say whether its
     statement is what its docstring claims;
   - check every changed statement and docstring;
   - look for regressions: anything round 1 accepted that the repair broke.

Pack 03a's brief and severity guide apply (03a's pack is in the bundle). Attempt at least
**three adversarial instantiations** against the changed surface. Do not give a blanket
approval.

## What changed

- **Statements:** `InteractiveProof(Err)`'s completeness carries a message bound `B` (`ProverBounded`), and `EfficientProverProof(Err)` has the new field `boundedP`. `zk_proof_of_mem_NP` and `_of_owp` become corollaries of the witness-relation forms; the `_owp_` Levin-reduction forms tie the commitment and the protocol together (`∃ Com ℓ, Commitment Com ℓ ∧ …`).
- **New public declarations:**
- `Protocol.ProverBounded` (def), `ProverBounded.mono`, `ProverBounded.pullback`,
  `ProverBounded.exists_complete`, `npProtocol_proverBounded`;
- `InteractiveProof.exists_accept`, `InteractiveProofErr.exists_accept` (the old completeness, for
  consumers);
- `PerfectZKAbort.statZK` (error `2^{-|x|}`), `PerfectZKAbort.zk`, `perfectZK_zeroRounds`, and the
  retry construction `AbortRetry.attempt`, `retry`, `attempt_poly`, `retry_poly`,
  `statClose_retry`, `exists_retrySimulator`, `firstHit_map_getD_eq`, `uprob_not_ne_nil_le`;
- `exists_commitment_of_owp` (`Commitment.lean`);
- `zk_proof_of_witnessRelation`, `zk_proof_of_witnessRelation_of_owp`,
  `exists_commitment_zk_proof_of_owp_levinReduction` (`NP.lean`).
- Consumers re-proved by the repair (graph isomorphism, 3-colouring) are in packs 03k and 03g; they are context here (section B of the diff).

## Scope

| Item | Where |
|---|---|
| Round 1 findings, review, resolutions, repair diff | `findings/gate03e-findings.md`, `review/gate03e-review.md`, `resolutions-03e-r1.md`, `evidence-r2/03e/repair.diff.txt` |
| Under audit (the changed surface), at the pin | `TCSlib/Cryptography/ZeroKnowledge/{Interaction, InteractiveProofs, Defs, Commitment, NP}.lean` |
| Context | `03e-pack.md` (round 1), `03a-pack.md` (common brief), `policy.md`, `briefs/pass-shelat/DESIGN.md`, the duplication ledger (scheduled rows) |
| Out of scope | tactic proofs; the scheduled clean-up (G3-5, DL-9 onward) beyond checking that its record is accurate |

## Attestations (maintainer execution claims; evidence under `evidence/e2/` in the bundle)

### Attestation results at `e79397eaf68b156b9db091f464741f6eb75b9c28` (evidence under `evidence/e2/`)

1. **Elaboration** (`replay.log`): the closure of this pack's files, 126 modules, each
   checked alone into a fresh olean tree by `scripts/lean_check_tree.sh`: all pass, 0 errors;
   21 `sorry` warnings in the closure.
2. **Axioms** (`axioms.log`): 116 prints of every public theorem and lemma in this pack's files:
   109 use only the standard axioms, and 7 depend on `sorryAx`; any other axiom is listed
   in the log.
3. **Admissions** (`admissions.txt`): 0 declarations in this pack's files contain `sorry`.
4. **Lint** (`lint.log`): `scripts/style_lint.py` on this pack's files: 0 findings in 5 files.

The replay is the 416-module replay at `af91d53a` overlaid with the re-check of the 98 modules
downstream of #201's changes (`evidence-repairs/03ac/replay.log`); each line of `replay.log` is the
newest check of its module, and the Lean files at the pin equal #201's head.

## Findings format (auditor fills)

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Plus one line per round 1 row: `<row>: fixed / recorded / scheduled / not resolved — <reason>`.

Severity guide: **blocker** (a downstream phase would build on a wrong statement); **major**
(fixable but materially misleading, or debt that needs explicit acknowledgment); **minor** (an edge
case, naming or attribution); **note** (no change required). The gate closes at **0 blockers and 0
majors**.

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/03e-pack.md =====

# Gate 03e ([PS10] ch. 2–4, interaction and ZK definitions): external statement audit pack

**Status: ready to dispatch** (staged 2026-11-05 at the merged head after #192 and #193; the evidence is under `evidence/e/`).

**What is audited:** the asymptotic layer of [PS10] ch. 2–4 on `cryptography/pass-shelat-ch2-4`, at
`a3c5fa8b72e50939822f22364647dc844a3914a0`. This pack covers the interaction model (strategies, executions, views, protocols), interactive proofs, the zero-knowledge definitions, commitments, and the NP layer used by Thm 124.1.
- **Gate type:** an external **statement gate** (`workflow.md` §3; user's ruling of 2026-11-05),
  over a layer written in another campaign (Frederick Dehmel's, now closed). That layer had only
  an internal audit (run 3a, summary in the bundle).
- **The deliverable:** **`gate03e-findings.md`**.

The bundle holds this pack, then every file named below under a `## ===== <path> =====` header.
**The source is attached separately:** [PS10], 3rd ed., January 2010 (PDF). Book page = PDF
page − 12. This pack needs §4.4–§4.7 (book pp. 114–127) and the appendix definition Def 191.11.

## Brief for the auditor

Pack 03a's brief applies unchanged (its pack is in the bundle): the trusted surface, the six
things to hunt for, the inventory check, restating every definition in your own words, and 1–3
sentences per theorem. Attempt at least **three adversarial instantiations**, for example:
- a verifier that is efficient but reads exponentially long messages;
- a "proof" whose soundness holds only because the verifier's verdict is ill-defined;
- a simulator that is efficient only because the auxiliary input is bounded.

Check the run-3a repairs in scope instead of re-finding them. Do not give a blanket approval.

## Scope

| Item | Where |
|---|---|
| Under audit | `TCSlib/Cryptography/ZeroKnowledge/{Interaction, InteractiveProofs, Defs, Commitment, NP}.lean` |
| The common brief | `briefs/pass-shelat-ch5-8/gates/03-ch2-4/03a-pack.md` (for its brief and severity guide; its questions are not this pack's) |
| Context, not under audit | packs 03a–03d's files: earlier packs of this gate |
| Design record | `briefs/pass-shelat/DESIGN.md` (§1 D1–D11, §2.15 the frozen ch. 4 signatures (with D8, the interaction reading), §5 the deviations register) |
| Inventory | `briefs/pass-shelat/inventory-ch4.md`: Def-114.a, Def-114.b, Def-115.a–d, Def-116.a, Def-116.b, Def-116.1, Def-117.a, Def-117.b, Claim-117.c, Def-119.5, Def-119.e, Def-191.11, Def-121.1, Def-121.2, Def-122.a, Claim-122.b, Def-124.a, Def-126.3, Claim-126.a, Thm-126.4, Alg-127.a, Claim-127.b–d |
| Internal audit record | `audits/pass-shelat/run3-audit-summary.md` |
| Source | [PS10] as above (PDF attached) |
| Standards | `policy.md` |
| Out of scope | tactic proofs; the protocols and their proofs (graph isomorphism, 3-colouring: packs 03g and 03k) |

## Attestations (maintainer execution claims; evidence under `evidence/` in the bundle)

### Attestation results at `a3c5fa8b72e50939822f22364647dc844a3914a0` (evidence under `evidence/e/`)

1. **Elaboration** (`replay.log`): the closure of this pack's files, 358 modules, each
   checked alone into a fresh olean tree by `scripts/lean_check_tree.sh`: all pass, 0 errors;
   25 `sorry` warnings in the closure.
2. **Axioms** (`axioms.log`): 26 headline prints from `audits/pass-shelat/Checks.lean` for
   declarations in this pack's files: 22 use only the standard axioms, and
   4 depend on `sorryAx`.
3. **Admissions** (`admissions.txt`): 0 declarations in this pack's files contain `sorry`.
4. **Lint** (`lint.log`): `scripts/style_lint.py` on this pack's files: 0 findings in 5 files.

Pack-specific notes (as drafted):
- elaboration (a fresh replay of the closure);
- the axiom prints for this pack's headline theorems (`audits/pass-shelat/Checks.lean`);
- admissions: none in these five files;
- lint;
- interface use. The declarations cited by ch. 5–8 are `Strategy`, `View`, `Protocol`, `InteractiveProof`, `ZK`, `PerfectZK`, `PerfectZKAbort` and
  `Commitment`. **Context for the auditor:** ch. 5–8 runs protocols in a new framework, through a
  bridge to these definitions (`Party.exec`, under D8's reading). The ruling of 2026-11-05 carries
  D8's strict or truncated simulators into the sequential composition of ch. 7.

## Specific questions

1. **The interaction model (Defs 114.a–116.b; D8).**
   - Is the fixed-alternation reading of D8 (the next-message function on the complete history is
     the output; a halting party sends `[]`) benign for every use in ch. 4?
   - Is the verdict convention (P9-3: the verifier's last message is its verdict when it moves
     last) a restriction that excludes any protocol of the source?
2. **Efficiency (Def 116.b).**
   - `Strategy.Efficient` is polynomial in the total input length, with `ReadsPrefix` restoring
     the bound in `|x|`. Is that faithful to "time `t(|x|)` regardless of messages"?
   - Is `ReadsPrefix` required wherever the source needs it?
   - **Known consequence (maintainer, 2026-11-05).** `ZK` quantifies over `Strategy.Efficient`
     verifiers without `ReadsPrefix`. Such a verifier may double its messages from activation to
     activation, so over polynomially many rounds, against an honest prover that echoes it, its
     view can grow exponentially, and no strict-PPT simulator can output it. Ch. 5–8's sequential
     composition (Thm 175.1) therefore assumes bounded honest-prover messages
     (`Protocol.ProverBounded`). Does any ch. 2–4 ZK theorem depend on this gap? The honest
     provers of the graph protocols have fixed message lengths. Should `ZK` itself require
     `ReadsPrefix` of `V*`? (Queued for the user as Q-1.)
3. **Interactive proofs (Def 116.1).** Are completeness and soundness stated against every
   (unbounded) prover, with the source's error bounds?
4. **Zero knowledge (Defs 121.1, 121.2, 122.a).**
   - Are `ZK` (every n.u.p.p.t. `V*` with auxiliary input), `PerfectZK` and the statistical form
     faithful?
   - D8 uses strict PPT simulators where the source has expected polynomial time. Is
     `PerfectZKAbort` (truncation with abort) an adequate stand-in for the source's perfect ZK
     protocols?
5. **Commitments (Def 126.3, Thm 126.4, Alg 127.a).** Are hiding and binding at the source's
   strength (computational hiding, perfect binding), and is the OWP-based scheme stated correctly?
6. **NP and Levin reductions (Def 124.a, Def 191.11; `NP.lean`).** Is the NP relation (efficient
   verifier, polynomially bounded witness) and the witness-preserving reduction the one
   Thm 124.1's form (A) needs?

## Findings format (auditor fills)

As in pack 03a: one table, `# | Severity | File · declaration | Claim | Evidence / counterexample |
Proposed fix`, with the same severity guide. The pack closes at **0 blockers and 0 majors**.

## ===== briefs/pass-shelat-ch5-8/gates/03-ch2-4/03a-pack.md =====

# Gate 03a ([PS10] ch. 2–4, machines and probability): external statement audit pack

**Status: ready to dispatch** (staged 2026-11-05 at the merged head after #192 and #193; the evidence is under `evidence/a/`).

**What is audited:** the asymptotic layer of [PS10] ch. 2–4 on `cryptography/pass-shelat-ch2-4`, at
`a3c5fa8b72e50939822f22364647dc844a3914a0`. This pack covers the machine model and the probability
notions on which the rest of the layer, and ch. 5–8, are stated.
- **Gate type:** an external **statement gate** (`workflow.md` §3; user's ruling of 2026-11-05).
  The layer was written in another campaign (Frederick Dehmel's, now closed). It had an internal
  adversarial statement audit (run 3a, summary in the bundle), but never an external one.
- **The deliverable:** **`gate03a-findings.md`**.

The bundle holds this pack, then every file named below under a `## ===== <path> =====` header.
**The source is attached separately:** [PS10] R. Pass, a. shelat, *A Course in Cryptography*, 3rd
ed., January 2010 (PDF). Book page = PDF page − 12; item numbers carry the book page. This pack
needs §2.1 and Definition 27.2 (book pp. 21–27), and §3.1 (book pp. 69–73).

## Brief for the auditor

You are auditing the **trusted surface**: definitions, theorem statements, docstrings and proof
sketches. Most proofs are machine-checked; do not review tactic scripts. Hunt for:
1. **Infidelity to the source:** a definition or statement that differs from [PS10]'s, other than
   by a deviation declared in its docstring and in `DESIGN.md` (§1 decisions D1–D11, §5 the
   deviations register). Check that each declared deviation is benign, or that its cost is stated.
2. **Wrong semantics:** a definition that does not compute what its docstring says.
3. **Trivialization:** vacuous or unsatisfiable hypotheses; definitions satisfiable for
   degenerate reasons (for example, a machine class that is empty, or that contains every function).
4. **Wrong strength:** a theorem weaker or stronger than its docstring claims; boundary cases
   (`n = 0`, empty coin strings, length-0 advice).
5. **Fitness for the layer's use:** these declarations are the interface that every later
   statement of ch. 2–4 and of ch. 5–8 cites. A definition that cannot express its later uses is a
   finding.
6. **Attribution:** `policy.md` §2.

**Checking against the inventories.** For every row of `inventory-ch2.md` and `inventory-ch3.md`
whose location is one of this pack's files, state whether the item is formalized faithfully. For
**every definition**, restate it in your own mathematical English before reading its docstring,
and report any daylight. For **every theorem**, say in 1–3 sentences whether its statement is what
the docstring claims. Attempt at least **three adversarial instantiations** (a degenerate machine,
a degenerate ensemble, an adversary exploiting the advice). The run-3a summary lists the internal
audit's findings and repairs: check that its repairs hold, and do not re-report a finding it
resolved unless the resolution is wrong. Do not give a blanket approval.

## Scope

| Item | Where |
|---|---|
| Under audit | `TCSlib/Complexity/Randomized/{PolyExpr, PPT, Primitives, Closure, Repetition, NonUniform}.lean`, `TCSlib/Cryptography/Asymptotic/{Adversary, Sampling, Ensembles}.lean`, and the new bridge `TCSlib/Cryptography/Asymptotic/SamplingFinDist.lean` (`StatClose` of samplers is `EpsClose` of their laws; duplication-ledger item DL-4) |
| Context, not under audit | `TCSlib/Cryptography/Foundations/Negligible.lean` (audited in the Garg ch. 1–3 campaign) |
| Design record (states the intent and the declared deviations) | `briefs/pass-shelat/DESIGN.md` |
| Inventories | `briefs/pass-shelat/inventory-ch2.md`, `briefs/pass-shelat/inventory-ch3.md` |
| Internal audit record | `audits/pass-shelat/run3-audit-summary.md` |
| Source | [PS10] §2.1, Def 27.2, §3.1 (PDF attached) |
| Standards | `policy.md` |
| Out of scope | tactic proofs; the machine constructions of `Complexity/Randomized/Build/` (pack 03l), whose statements this pack's files use |

## Attestations (maintainer execution claims; evidence under `evidence/` in the bundle)

### Attestation results at `a3c5fa8b72e50939822f22364647dc844a3914a0` (evidence under `evidence/a/`)

1. **Elaboration** (`replay.log`): the closure of this pack's files, 323 modules, each
   checked alone into a fresh olean tree by `scripts/lean_check_tree.sh`: all pass, 0 errors;
   22 `sorry` warnings in the closure.
2. **Axioms** (`axioms.log`): 41 headline prints from `audits/pass-shelat/Checks.lean` for
   declarations in this pack's files: 40 use only the standard axioms, and
   1 depend on `sorryAx`.
3. **Admissions** (`admissions.txt`): 1 declarations in this pack's files contain `sorry`.
4. **Lint** (`lint.log`): `scripts/style_lint.py` on this pack's files: 2 findings in 11 files.
   Both are in `SamplingFinDist.lean`, the dedup's new bridge (the maintainer's file): a missing
   `set_option maxHeartbeats 0` and a missing `## Main definitions` heading. Style only; fixed with
   gate 03's repairs.

Pack-specific notes (as drafted):
1. **Elaboration:** a fresh replay of the closure.
2. **Axioms:** the prints for this pack's headline theorems, from `audits/pass-shelat/Checks.lean`.
3. **Admissions:** the one `sorry` in scope, `NUPPT.decides_of_decidesWithAdviceInTime`
   (`NonUniform.lean`), an optional bridge outside the mandatory core (Frederick's open question 5).
4. **Lint.**
5. **Interface use:** the declarations of this pack cited by ch. 5–8 (S1 note, point 3) are
   `Complexity.NUPPT`, `Complexity.PPT`, `NUPPT.Uniform`, `NUPPT.runAt`, `NUPPT.Computes`,
   `NUPPT.ofPolyTime`, the closure calculus, `Negligible`, `Ensemble`, `Ensemble.Indist`,
   `Ensemble.Samplable` and `StatClose`.

## Specific questions

1. **The machine model.**
   - Do `PPT` and `NUPPT` capture [PS10] Defs 23.4, 23.5 and 26.8?
     - The coins are an explicit polynomial-length input.
     - The advice has length `Cα (n+1)^cα`, and the machine runs on `⟨⟨x, α |x|⟩, r⟩`.
     - The time bound is polynomial in what?
   - Is `NUPPT.Uniform` the uniform class?
   - Does the D4 reading of "|A_i| < d(i)" (advice in place of a sequence of machines) lose
     anything?
2. **Computing with probability 1** (Def 24.6). Does `NUPPT.Computes` require the same output on
   every coin string, and is that the source's notion?
3. **Polynomials.** Does `PolyExpr` (explicit polynomial expressions) cover every bound the layer
   needs? Is anything stated "for some polynomial" where the source quantifies differently?
4. **The closure calculus** (Claim 26.3).
   - Is each closure lemma of `Closure.lean` and `Repetition.lean` what the reductions of ch. 2–4
     need: pre- and post-composition, pairing, hard-wiring, polynomially many calls with fresh coins?
   - Is any hypothesis stronger than the uses can meet?
5. **Statistical closeness** (`Sampling.lean`, `SamplingFinDist.lean`). Is `StatClose` the source's
   statistical distance, or an equivalent form, for samplers? Is it preserved by the operations
   stated? Does `statClose_iff_epsClose_map` make it exactly `main`'s `EpsClose` ([PS10, Def 181.1])
   on finite sample spaces?
6. **Ensembles and indistinguishability** (Defs 69.3, 69.4; Lems 71.5, 71.6).
   - Is `Ensemble.Indist` "for every n.u.p.p.t. distinguisher, the advantage is negligible", with
     the source's quantifier order?
   - Is the advice of the distinguisher handled as the source does?
   - Are the hybrid lemma and the closure under efficient operations stated at the right strength?
7. **Adversaries** (`Adversary.lean`). Is the adversary interface faithful to how [PS10] quantifies
   over adversaries in ch. 2–3?
8. **The one admission.** Is `decides_of_decidesWithAdviceInTime` true as stated, and correctly
   labelled optional?

## Findings format (auditor fills)

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | blocker / major / minor / note | | | | |

Severity guide:
- **blocker:** a downstream statement (in ch. 2–4 or ch. 5–8) would build on a wrong definition or
  statement;
- **major:** fixable but materially misleading as it stands, or debt that needs explicit human
  acknowledgment;
- **minor:** an edge case, or a naming or attribution defect;
- **note:** an observation; no change required.

The pack closes at **0 blockers and 0 majors**.

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

**Definitions land with their lemmas** (user, 2026-10-16). Every new public `def` is published,
in the same PR and beside the definition, with the lemmas that let a consumer read it without
unfolding:
- a structure-valued definition (a contract, a configuration, zone contents): its field
  equations, generated by `simps` with `(config := { isSimp := false })` and explicit
  projections (`simps!` where the body is another constructor's result);
- any other definition: an equation lemma `<name>_eq` (by `rfl` where that holds), or case
  lemmas that together cover every input (`_of_lt`/`_of_le`, `_true`/`_false`, one per
  constructor);
- a predicate: an `_iff` characterization;
- a machine: its run or contract lemma, the only way consumers read a machine.

None carries `@[simp]` unless a gate approves it, and each docstring states its formula. Consumers
never unfold another file's definition (the no-unfolding rule of the briefs, user 2026-10-16). The
rule binds TCSlib's own definitions: core and Mathlib definitions may reduce in a `rfl`, `decide`
or `show` step, but are never passed to `simp`, `rw` or `unfold`; use their equation lemmas
(`Bool.toNat_true`, not `simp [Bool.toNat]`) (user, 2026-10-23).
**Reducible abbreviations are notation** (user, 2026-10-26). Lean unfolds a TCSlib `abbrev` (such
as `Turing.Cfg.Halted`, `cfg.state = none`) at every step, and the standard seal cannot cover it:
under Lean's default reducibility validation, `attribute [local irreducible]` fails on a reducible
declaration (only the unsafe override `set_option allowUnsafeReducibility true`, which the
campaign's seals do not use, lifts the check). So reading an abbreviation through its body,
for example `¬ c.Halted` as `c.state ≠ none`, is allowed and is not a definitional closure. A
consumer names it in `simp`, `rw` or `unfold` only through a published lemma where one exists, and
a new public `abbrev` still lands with its `_iff` or `_eq` lemma.
They read the machine model's primitives (`MultiTapeTM.step`, `runFrom`, `Action.apply`,
`Cfg.mapState`) through the existing lemmas. The style lint's check 8 reports, per file, every
public `def` with no lemma named after it and no `simps` attribute, so a head-against-base diff
of the lint shows any new definition that lacks one. Definitions that predate the rule are listed
by the same check and covered as consumers need them.

**Construction reuse.** Machines are built from the verified construction layers, not from
scratch: the combinators and routine catalog of `TCSlib/Complexity/TuringMachine/Build/`
(conventions, wrappers, loops, primitives, embeddings, seams, and the catalog rows —
`machine-library-design.md` is the registry), the registered hosts (**Hosts come first**,
below), and the program layers (`LogProg.ARM`, `CounterProg`, and the general programming
layer of `machine-library-design.md` §15 once it lands) where a program-level description
suffices. Before writing a transition
table by hand, check the registry; a routine that exists is cited, not re-derived. A routine
that *almost* exists is the interesting case: do not write a third private variant — either
consume the general form, or commission the missing form into the shared layer (during a
fill batch: a `private` local copy plus a "requested shared lemma" in the report, promoted
at the next shared-file window). A hand-built machine is acceptable only when no layer
covers the need, and its docstring must say so and name what was missing — that sentence is
what turns the gap into the next catalog row. The chapter-1/2 files that predate this layer
re-derived the same bank/relocation/dispatch/frame families four times over (`emitterBank*`,
`clBank*`, `clSlot*`, …); the retrofit paying that debt back is the standing cautionary
tale. The same discipline applies to circuit construction once `CircuitComplexity`'s gadget
layer exists: gadgets, wiring combinators, and size/depth ledgers get one shared home and a
registry, and new circuits are assembled from it.

**Hosts come first.** A *host* is a control structure that drives other routines rather than
computing one value: a search or traversal (BFS, DFS, backtracking, an odometer over
assignments), a recursion or evaluation scheme (AND/OR evaluation, Savitch's midpoint
recursion), an interpreter or simulation step block, a clocked or windowed runner, a dispatcher
over a data structure (tables, records), or an input device. Any routine whose natural contract
does not depend on its first consumer counts as a host; leaf rows (copy, compare, seek,
arithmetic) do not. **A host is never built `private` inside the proof that first needs it.**
Its public contract is designed, statement-gated and placed in the shared construction layer
first, generic in the parts its consumers vary (the leaf test, the step relation, the data
domain), with time and space (head-envelope) clauses. Consumers cite it, under the campaign's
proved-modulo rule while its own fill is still running. The host registry is
`machine-library-design.md` §14. A private host already in the tree is harvested into the
shared layer before a second consumer is briefed against it. The rule exists because private
hosts were the main way the library overfitted to single proofs: four configuration encodings,
three reachability notions and a private search host per theorem, each to be re-derived by the
next consumer (assessment of 2026-10-12, recorded in the design document). (User, binding,
2026-10-12.)

**Duplication.** Some duplication is mechanically forced by the campaign discipline —
exclusive file ownership, the statement freeze, and `private` visibility leave a fill batch
no other legal way to use another file's unexported machinery — and occasionally it is the
right engineering call. It is never silently acceptable: **every instance of duplicated
proved material must be human-approved.** A fill batch discloses each copy in its report;
the maintainer's integration ledger totals copied material per file (`workflow.md` §4); and
the audit template treats accumulated duplication as a major finding that a gate cannot
close over without the human maintainer explicitly accepting the debt and naming where and
when it is paid back (the registry's dedup/refactor queue). Duplication that was never
disclosed is a freeze violation, not debt.

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
(`<name>.raw.md` + `<name>.md`) so these citations are possible: put the PDF under
`blueprint/src/references/` in the change that formalizes it and run
`python3 scripts/dataset_pipeline.py --yes`, which ingests it, matches every text the
blueprint does not cite yet, and carries the new statements into the dataset
(`python3 scripts/sources.py add TAG=<pdf or md>` does the ingest and match alone, with
the docstring tag above; `python3 scripts/sources.py` shows which texts are attached and
which are still missing; see `dataset/INSTRUCTIONS.md`). The dataset builder does not
search outside that directory for sources; an unattached text leaves the theorems with
informalized proof notes instead of citations.

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
8. No new private host: every search, recursion, interpreter, runner or input device the
   change introduces is a registered public host, or cites one (§1, **Hosts come first**).
