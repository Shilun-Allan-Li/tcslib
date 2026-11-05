# Gate 02 / S2a, round 2 — external API audit findings

Audited: [TCSlib PR #185](https://github.com/Shilun-Allan-Li/tcslib/pull/185), frozen head `586510c1416afa21881b9a42b5a8d0578c9bd749`.

**Disposition:** the original execution, first-message logging, and first-bad-transition defects have been repaired under the declared execution convention. I found **no remaining blocker or major within that ruled S2a scope**. There are **six open minor findings**: round 1 #8 and M2 remain partly unresolved, and Table 2 adds four minors. Table 2 also contains two notes. This is not a certification of literal PS10 execution/view equivalence, the S2b bridges, or source-general expected-time ZK composition.

The fifteen resolution verdicts are **9 fixed, 4 recorded, 2 not resolved**. “Fixed” below addresses the identified round 1 defect; the narrower source-fidelity qualifications in the new findings still apply.

Verification and scope:

- `gate02-s2a-r2-bundle.md`: SHA-256 **`c5b0668c69191852672000db0f1edf1f1a627b417188b330a9efa93a39570344`**, exact match; **28** section headers.
- `Pass–Shelat.pdf`: SHA-256 **`7624556077a7a272ba0b3ddb7cd47b96574fb0b4b4947a25467d1f91bb61bda8`**, exact match. References below use book pages; PDF page = book page + 12. I read the relevant source definitions, §4.4, Lemma 71.6, and the continuation of Thm 175.1; I also visually checked book pp. 115 and 156.
- All seven extracted Lean files match the new Git blob prefixes in `repair.diff.txt`; the reverse patch applies cleanly. This checks the supplied diff against the supplied files, not the maintainer's execution environment. The [root export at the frozen head](https://github.com/Shilun-Allan-Li/tcslib/blob/586510c1416afa21881b9a42b5a8d0578c9bd749/TCSlib.lean) independently includes `import TCSlib.Cryptography.Games`.
- I restated the changed definitions from comment-stripped bodies before comparing their declaration docstrings. The audit covers **14 new/body-changed/documentation-changed definitions or types**, **19 new/changed/documentation-changed theorem statements** including the private helper, the three execution sanity examples, the module prose, and unchanged interfaces for regressions. Tactic proofs were not reviewed.
- The supplied evidence records 9/9 module checks, clean lints, and standard axioms for 75 public theorems. I did **not** rerun Lean, the repository lints, or the repository-wide name screen. Independently, exact-rational transcriptions of the executor and a separate event-driven scheduler agreed in **720 small execution cases**, including outcome erasure, message-count and alternation checks. The targeted examples below were also checked. These are corroborating models, not Lean certificates.

Locations below are individual-file line numbers. Unqualified Lean filenames are under `TCSlib/Cryptography/Games/`.

## Table 1 — round 1 resolutions

| Round 1 # | Verdict (fixed / recorded / not resolved) | Evidence |
|---|---|---|
| 1 | fixed | `Protocols.lean:83,110,117,130`: `finish` is removed. `close` stops at the first forbidden send; `endWith` reports `sentAfterEnd`; `exec` separately reports an exhausted message budget. The extra final activation is now explicitly a deviation from literal PS10 and is authorized by the recorded ruling. No arbitrary drain can manufacture `done` after observing a forbidden send. This does **not** establish the stronger “D8 except for early returns” claim: see new finding 1 and Q2. |
| 2 | fixed | `Protocols.lean:169,199,209–211,252`: `execT` prepends the first delivered message to the second mover's received list, records both parties' draws including closing draws, and retains both outputs in the same sample. The secret-bit example now gives Bob `received = [x]`, even when Bob immediately returns. `execT_outcome` is the correct erasure statement. The distinct full-random-tape qualification is new finding 2; this repair fixes the missing-message defect, not an unconditional ITM-view equivalence. |
| 3 | fixed | `Hopping.lean:220,301,326,338`: agreement now concerns the unnormalized good-successor law of the **reply/state pair**. The crossing-call example has equal good mass and differing bad replies, so it now satisfies the premise. A discarded singleton draw no longer obstructs agreement. Both stickiness premises remain; `hagree_of_eq` and sampled initialization have the advertised statements. See Q4 for source-relevant instantiations and necessary qualifications. |
| 4 | recorded | The design's synchronization paragraph and inventory row `Thm-175.1` explicitly restrict the target to strict simulators or truncation with abort. PS10 Def 121.2, Algorithm 123.4 and Thm 175.1, book pp. 121, 123, 175–176, still permit expected-time retrying. The restriction is accurately declared; it is not a proof of equivalence with that source generality. The `Q·2^-k` claim requires a uniform per-session abort bound on the auxiliary inputs/histories actually used, as detailed in Q6. |
| 5 | fixed | `Protocols.lean:130–150`: only a delivered message decreases fuel. Two immediate returns succeed with fuel 0; one send followed by both returns succeeds with fuel 1; a further reply with no fuel yields `outOfFuel`. Closing never silently spends further sends. The new zero-fuel docstring nevertheless omits its return branch; that is new finding 3. |
| 6 | fixed | `OracleComp.lean:17–19` now says well-founded tree, finite when answer types are finite. This includes infinitely branching examples with unbounded finite branch lengths without claiming that the whole tree is finite. `ProbComp` remains finitely branching and finite for each fixed computation. |
| 7 | fixed | `Probability.lean:71–80` and `Simulate.lean:135–152` now carry the four missing VCVio tags, identifying `uniformFin`, `QueryImpl.compose`, and `simulateQ_compose`. The corrected author list agrees with the six named module headers at VCVio commit `9054989327a7185ff19ef9ff0f119cccea479501`, independently retrieved. The composition attribution is a design adaptation with explicit state threading, not a claim that the two theorem types are identical. |
| 8 | not resolved | **Minor; partly repaired.** The PS10 correction to Lemma 71.6 and the telescoping description are right. The incorrect Shoup location was deleted, but the requested pinned revision/precise location was not supplied: `Hopping.lean:46–48,126–127,288` still uses an unpinned `[Sho04]` and a session-access explanation. The directly inspected author-hosted revision is **18 January 2006, §1.1, Lemma 1**, p. 3. Cite that revision and location. This retains the original attribution severity; it does not dispute the difference inequality. |
| 9 | fixed | `Advantage.lean:70–71` says only nonnegativity; `Hopping.lean:100–103` explicitly states the support-restricted expectation inequality. Both now match their statements. |
| 10 | fixed | `Advantage.lean:6,98–111` imports the concrete probability layer and specializes `abs_sub_le_sum_hybrids` and `exists_hybrid_gap` to acceptance probabilities. The requested reuse is present, rather than merely listed as future work. The imported module has only Mathlib imports. The two statements are correct; the source's slightly weaker indexing/constant should be disclosed as in new finding 4. |
| 11 | recorded | `resolutions-r1.md` explicitly retains the distinction between abstract finite uniform sampling and bounded fair-bit implementation, with dyadic sampling or truncated rejection in S2b. Exact `sampleFin 2` is still not implemented by a bounded fair-bit sampler; nothing in S2a claims that it is. |
| 12 | recorded | The facade and design §8 continue to defer the machine/efficiency and protocol bridges. B1/B2 progress and B3 drafts are reported as work on a separate S2b branch, not as results supplied by this bundle. B4 remains unproved. No closure theorem or ZK equivalence is inferred from `simulate_comp` or a query bound. |
| M1 | fixed | `Hopping.lean:21–24,150–161` now scopes the collision estimate to one fresh draw after a bounded list. The adaptive nonce bound is explicitly scheduled. The quantified program shape enforces that the list is selected first; duplicates and `q > card T` do not invalidate the inequality. |
| M2 | not resolved | **Minor; partly repaired.** `prob_mem_le` now has an appropriate supporting tag. However, `Advantage.lean:149–151` newly says that PS10 uses both guessing and distinguishing forms at §3.1 and Def 168.1. The formal definitions there are distinguishing definitions: Def 168.1 defines two experiments for **fixed** `b`, not a uniform hidden-bit guessing-success experiment. State that the guessing game is a standard equivalent reformulation, with the factor-two identity proved here; do not attribute both formal conventions to these locations. The informal guessing motivation in §3.1 does not supply the missing formal definition. |
| M4 | recorded | The design has a current precedence paragraph naming `Games`, `CostBoundedBy`, `ExecOutcome`, `execT`, semantic good-law agreement and the simulator restriction. It explicitly labels the remaining sketches as pre-gate drafts. Thus the record discloses, rather than silently endorses, stale material such as `Option (α × β)`, views from party logs, `IsQueryBound`, and the old namespace. This is an adequate historical record, but not a literal synchronization of all snippets. New source-facing statements should use the current declarations. |

## Table 2 — new findings

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | minor | `Protocols.lean:20–26,125–129` · `Party.exec`; facade `Games.lean:42–43`; pack Q2 | Early returns are the only distinction from the bundled D8 execution model. | D8 uses the same deterministic `next` on the same full history/tape to compute the last sender's final message and output; they must be equal (`Interaction.lean:277–282`). With exactly one allowed message, let Alice send `false` and return `true` after closure, and Bob return `false`. `Party.exec 1` returns `done true false` and Bob receives `[false]`. No party ended before the prescribed message count, yet this transcript/output pair cannot arise from a one-message D8 protocol. | Describe the executor as a broader coroutine model with a separate return value as well as early termination. State D8 agreement only for induced strategies satisfying its verdict convention, and preserve that obligation in B4. The extra expressiveness is not an execution bug. |
| 2 | minor | `Protocols.lean:28–33,167–173,195–198` · `Party.Obs`, `Party.execT` | These observations, plus input/auxiliary parameters, automatically recover the literal PS10/D8 view. | `Obs.coins` records draws actually executed, not a separately specified full random tape. A source machine with a one-bit tape that ignores its tape has two possible source views but the same no-draw `Party.Obs` and fixed inputs. No deterministic function of those observations recovers the omitted bit. Nonbinary finite draws also are not intrinsically bit tapes. | Call the generic object a received-message/draw trace. For the exact PS10/D8 view, specify that the induced party samples its entire bounded tape and retains it, or supply a suitable padding/encoding equivalence with its hypotheses. This is expressible with the present API; Q6 gives the construction. Do not assert a generic deterministic full-tape projection without that convention. |
| 3 | minor | `Protocols.lean:138–140` · `Party.exec_zero` | With zero fuel the execution ends at the first mover's first send. | The theorem also includes the immediate-return branch, which runs `endWith`; for example `exec 0 (pure a) (fun _ => pure b) = pure (done a b)`. The waiting party may even draw coins before returning or triggering `sentAfterEnd`. The statement is correct; the prose omits a substantive branch. | Say: run the first party to a return or attempted send; close the waiting party on return, and report `outOfFuel` on an attempted send. |
| 4 | minor | `Advantage.lean:106–111` · `exists_advantage_hybrid_gap` | The displayed version is attributed to PS10 Lemma 71.6 without describing its sharper constant. | PS10 book pp. 71–72 uses `m` distributions and the weaker threshold `ε/m`. Here `G 0,…,G n` contains `n+1` games and `n` gaps, and the bound is the exact endpoint advantage divided by `n`. The statement and arithmetic are valid; it sharpens the cited formulation. | Add that this is the sharp concrete form, using the number of gaps and the actual endpoint advantage. This meets `policy.md`'s requirement to disclose strengthened/source-reformulated constants. |
| 5 | note | `Protocols.lean:199,252` · `Party.execT`, `execT_outcome` | Outcome erasure is the appropriate consistency result, but does not certify the contents of the observations. | An executor with every observation replaced by empty lists would satisfy the same erasure equation. The present recurrence does record the observations correctly in the checks below. Useful missing statements are total received length at most fuel, the alternation relation, exact length on `outOfFuel`, and the D8 view projection on the induced class. | Add the trace invariants stated in Q3 and the full-view bridge in S2b. Their absence is not itself a false theorem or an S2a blocker. |
| 6 | note | `pack-r2.md` attestation 2; `evidence-r2/axioms.log`; `Hopping.lean:194` | The log describes “all 75 theorems.” | There are **75 public named theorems plus one private named helper**, `expect_ite_one_split`. The 75 public names are represented in the log; the private helper has no separate printed entry. Standard-axiom results for public theorems are still transitive dependency checks. | Say “all 75 public theorems”; optionally print the private helper separately. I found no contradictory axiom evidence. |

## Answers to the six questions

**Q1 — Resolutions.** Table 1 gives a verdict for all twelve original findings and M1, M2, M4. No accepted simulator or machine-layer deviation has been silently upgraded to a proved equivalence.

**Q2 — Execution and adversarial boundaries.** The alternating routing is correct: a permitted send delivers its message to the waiting party, swaps roles, and decreases the budget by one. A return costs no message; closing receives a single `none` and permits draws but no further send. This is the expressly ruled closure convention, not literal PS10 stopping at the first active halt. Its relationship to D8 has the additional return-value distinction in new finding 1.

For the following calculations, `return a` means `.pure a`, and `send(m,k)` means the exchange query `.query (.inl ()) m k`.

1. **Zero messages, both return:**
   \[
   \operatorname{exec}\,0\,(\operatorname{return}a)\,(\lambda\_.\operatorname{return}b)
   =\operatorname{return}(\operatorname{done}(a,b)).
   \]
   The outcome is not spuriously truncated. Both received lists and both draw lists are empty.
2. **Zero messages, an attempted send:**
   \[
   \operatorname{exec}\,0\,(\operatorname{send}(m,k))\,B
   =\operatorname{return}(\operatorname{outOfFuel}).
   \]
   Neither `B (some m)` nor `k none` is executed. The blocked message is not logged as delivered. Draws before the attempt remain in the active party's trace.
3. **The last allowed message:** with `k = fun _ => return a` and `B = fun _ => return b`,
   \[
   \operatorname{exec}\,1\,(\operatorname{send}(m,k))\,B
   =\operatorname{return}(\operatorname{done}(a,b)).
   \]
   Alice receives `[]`; Bob receives `[m]`. Substituting a secret bit for `m` repairs the exact round 1 privacy counterexample.
4. **One more reply:** if Bob instead sends a reply after receiving `m`, the same one-message budget yields `outOfFuel`. Bob retains `[m]`, Alice receives no reply, and no output pair is reported. With budget two and immediate returns after that reply, both messages are delivered and the execution succeeds.
5. **Send after an immediate end:** for any fuel, Alice returning immediately and Bob attempting a send on `none` yields `sentAfterEnd`. Increasing fuel cannot turn that forbidden send into success.
6. **The original first mover misbehaves after a role swap:** Alice sends `m`; Bob returns; Alice's continuation attempts another send on `none`. The result is again `sentAfterEnd`, including when `m` consumed the last unit of fuel. Thus the check is not restricted to the initially waiting party.
7. **Randomized closing:** Alice returns; Bob draws a fair bit on closure, returning on one value and attempting a send on the other. The result has probability `1/2` each of `done` and `sentAfterEnd`. Bob's closing bit is recorded on both branches. It is not averaged away into a successful output.
8. **Coin order across both swaps:** Alice draws `u` from `Fin 2`, sends it, then draws `v` from `Fin 3` after Bob's reply and returns `(u,v)`. Bob draws from `Fin 1`, replies, then draws `w` from `Fin 2` during closure and returns `w`. Each `(u,v,w)` has probability `1/12`. Alice's coin indices are `[1,2]`, Bob's `[0,1]`, in that order; outputs remain `((u,v),w)` in the original party order. This specifically tests the `p.2 ++ r.2.2.coins` concatenation and `closeT` branch.
9. **D8 restriction:** Alice's single message `false` and later return `true` give the successful counterexample in new finding 1, with no premature return relative to the one-message schedule.

Consequently, an **executed** forbidden send or attempted message beyond the remaining budget cannot be hidden inside `done`. The outcomes do not identify the offender or retain partial outputs on failure; their specification does not promise that. The budget is a message budget, not a running-time/randomness budget, and behavior after the first reported failure is not executed.

**Q3 — Views.** The received-message and draw sequences are correctly routed and ordered. The current recursion records the initial message to Bob even though that message is passed as an argument; it then records all later delivered messages. `stepT` and `closeT` prepend each draw before their recursively returned draws. At a role swap, the original active party's earlier draws are concatenated before its later draws, and the other party's initial received message is prepended to its later messages. The source view separates the tape and received-message sequence, so an explicit global interleaving field is not required.

Inputs and auxiliary inputs can be attached from the fixed parameters of the party family. This is a construction a consumer must make; the type `Party` does not itself label those parameters. For **draw-trace views**, these data suffice. For a literal source full-tape view, the unconditional answer is **no** without the representation convention in finding 2. Sampling the full bounded tape inside the induced party remedies it, including bits that its subsequent deterministic strategy ignores. The two interpretations must be distinguished when stating B4.

`execT_outcome` is the right conservativity statement: discarding observations gives equality of `ProbComp` trees, not merely equality of outcome probabilities. It proves neither source fidelity nor trace completeness by itself. In particular, write `M_A` and `M_B` for the two received lists returned on a run. The following are useful missing sanity theorems, for **every possible output** of `execT fuel A B`:

\[
\begin{aligned}
|M_A|+|M_B|&\le\mathrm{fuel},\\
|M_B|&\in\{|M_A|,\ |M_A|+1\},\\
\mathrm{outcome}=\mathrm{outOfFuel}
&\Longrightarrow |M_A|+|M_B|=\mathrm{fuel}.
\end{aligned}
\]

The inequalities follow by induction on fuel: a terminal/blocked-send branch adds zero delivered messages; a recursive send branch adds exactly one message to the receiver and swaps the two lists. The alternation relation swaps accordingly. These are mathematical statements justified by the defining equations and the independent finite checks, **not additional Lean results present in the submission**. A successful run need not use all available fuel.

**Q4 — The new identical-until-bad premise.** It is equality of **unnormalized** measures restricted to good successor pairs, including both the answer and the entire state. It is stronger than equality of conditional answer distributions given goodness. Taking `g = 1` already forces equal total good mass, hence equal bad mass because each handler is normalized.

More explicitly, let `μ₀, μ₁` be the finite laws of a particular pair of handlers at a good entry state. The premise is

\[
\sum_{y,s':\neg\mathrm{bad}(s')}\mu_0(y,s')g(y,s')
=\sum_{y,s':\neg\mathrm{bad}(s')}\mu_1(y,s')g(y,s')
\quad\text{for every }g.
\]

Indicator tests for individual successor pairs show that this is equality of their good restricted laws. `hagree_of_eq` follows immediately by substituting equal handler computations into each expectation; it recovers the old stronger premise.

The statement and sketch have the standard constant-one conclusion. By induction on the adversary computation, stickiness makes the probability of “output in the event and final state good” zero from a bad successor. On good successors the inductive probabilities agree, so the displayed premise gives equality of the two good-event probabilities. Taking the output event to be always true also gives equal final-bad probabilities. If `a` is the common good-event probability, `b₀,b₁` the two bad-event contributions, and `B` the common final-bad probability, then

\[
0\le b_0,b_1\le B,\qquad
\left|(a+b_0)-(a+b_1)\right|=|b_0-b_1|\le B.
\]

The new premise survives the following adversarial instantiations:

- **First divergence inside the crossing call.** Initially the flag is false. Draw a fair bit `b`; handler 0 returns `(false,b)`, handler 1 returns `(b,b)`, where the second coordinate is the new flag. Both good restricted laws put mass `1/2` on `(false,false)`. For a one-call adversary returning the reply, the acceptance probabilities are `0` and `1/2`, and both bad probabilities are `1/2`. From a bad entry state retain the flag. Thus all premises hold, with equality in the bound, although the old whole-computation equality fails.
- **Equal law, unequal syntax.** `return (false,s)` and `sampleFin 0 >>= fun _ => return (false,s)` have the same law. Every tested expectation agrees although the roots are different constructors. This formerly excluded case is now covered.
- **Repeated nonce, as used in Thm 168.2.** Use a shared state containing a sticky flag and a lazily sampled table. On a fresh nonce, both handlers sample the same law for a fresh pad and store it in the same table; on a repeated nonce, both set the flag, after which one may reuse the old pad while the other samples a fresh one. Their good restricted successor laws agree for every entry state. A two-nonce example with cached pad `0` at nonce `0` gives bad probability `1/2`; the event “reply is nonce `0` with pad `1`” has probabilities `0` and `1/4`. The full good reply/cache laws agree, not just the event probabilities.
- **Necessary representation qualification for that hop.** If the state instead contains a complete fixed random-function table, returning its fixed value at a fresh nonce versus drawing a new pad need not satisfy the premise at that state. Sampling the table in `init` does not remove this pointwise obligation. The source application therefore needs the usual proved lazy-sampling/relabeling step and a synchronized good state; it is not a direct application to every eager representation. For CCA1, the table/bad event must also account for relevant pre-challenge decryption queries. This is compatible with, but not a replacement for, the scheduled adaptive analysis.
- **CCA2 challenge query.** Keep the challenge and key in the shared state. Away from the challenge, use equal handlers. On the challenge, set the flag in both games, then allow one to decrypt and the other to return `⊥`; retain the flag thereafter. There is no good successor on that branch, so the new premise permits the different replies. An adversary deliberately asking the challenge can make bad probability **one**. The lemma consequently does not justify accepting challenge-decryption queries in the definition or treating them as negligibly rare; the source's refusal rule must remain.
- **Rejection tests.** Equal conditional good laws with good probabilities `1/2` and `1/4` fail `hagree` already at `g = 1`. Raising a flag, diverging, and then clearing it can give output gap one and final-bad probability zero; that example fails the retained stickiness premise. Neither is a counterexample to the submitted theorem.

`identical_until_bad_init` covers a sampled key: put the key and initially clear flag in `init`. Its hypothesis is `init.AllOutputs (fun s => ¬ bad s)`. Every leaf of a `ProbComp` has positive weight, since a path weight is a finite product of positive reciprocals; therefore, here probability-one goodness also implies that all possible leaves are good. Averaging the pointwise bounds gives

\[
\left|\mathbb E_{s\leftarrow\mathrm{init}}p_0(s)
-\mathbb E_{s\leftarrow\mathrm{init}}p_1(s)\right|
\le\mathbb E_s|p_0(s)-p_1(s)|
\le\mathbb E_s\Pr_0[\mathrm{bad}\mid s].
\]

The last expression is precisely the theorem's bad probability for the initialized game. It does not cover an initialization which is bad with positive probability, nor does it weaken agreement on good entry states. The semantic deviation from BR06 is accurately described.

**Q5 — Hybrid reuse.** Both statements match their numerical docstrings. With `p_i = accept (G i)`,

\[
|p_0-p_n|\le\sum_{i=0}^{n-1}|p_i-p_{i+1}|.
\]

For `n > 0`, if every summand were smaller than `|p₀-pₙ|/n`, their sum would be smaller than `|p₀-pₙ|`, contradicting the inequality. For `n=0`, the first theorem is the valid `0 ≤ 0`; the second theorem correctly excludes that case. Lemma **71.6**, book pp. 71–72, is the correct PS10 tag. Finding 4 concerns disclosure of the sharper concrete constant, not its validity. The two wrappers invoke the concrete layer's existing statements with `fun i => accept (G i)`; no probability bridge is needed for this specialization.

**Q6 — Expressiveness.** At a fixed security parameter, both requested constructions are expressible, with the following explicit conventions and still-deferred proofs.

For **Def 155.1**, give each induced party its input and auxiliary input as fixed parameters. At its first activation, sample its full bounded bit tape (a finite type), retain that tape in its continuation, and thereafter compute the next messages/output deterministically from it and the received history. Alternatively sample the prescribed number of individual bits before proceeding. All tape bits, including unused ones, then appear in `Obs.coins` with a known decoding. In the second mover, the initial message is additionally present in `received` independently of that sampling.

On a successful sample `(done a b, obsA, obsB)`, deterministic projections give

\[
((x,z_A,r_A,M_A),b),\qquad ((y,z_B,r_B,M_B),a),
\]

or omit auxiliary inputs in the source definition's simpler presentation. Both are derived from the **same** run, preserving the correlations with the other party's output. One must prove successful termination for the honest protocol, or explicitly retain an abort symbol and account for its probability; conditioning on success and silently discarding failures is not the source experiment. The repaired trace has enough data for this construction. The corresponding Lean view projections and B4 equivalence are not yet supplied.

A concrete embedding of the bundled **D8 fixed-round protocols** is also possible: pre-sample each strategy's tape; maintain its received history and the prescribed turn count; send `next` on scheduled turns; after all scheduled messages, return `next` on the complete history. After the last handoff the receiver returns, and closing causes the last sender to return. For that sender the history has not changed since its last send, so its returned value equals its final message, exactly as D8 requires. This establishes why finding 1 is a scope/documentation defect, not an inability to represent D8 protocols. The source correspondence still needs its promised Lean theorem.

For **Thm 175.1 under the ruling**, a fixed `Q(n)`-session execution and its strict/truncated simulator can be expressed by finite recursion and bind. Preserve the malicious verifier's state and one full random tape across sessions; sample the honest parties' session randomness independently as specified. The simulator can sample that verifier tape once, retain the prior transcripts, and feed the tape/history as auxiliary input to each session simulator, just as the source's proof does. Merely rerunning independent malicious verifiers would not express the required theorem.

For the truncation variant, if every session at every relevant auxiliary input/history has abort/error contribution at most `2^-k`, then

\[
\Pr[\text{some session aborts}]
\le\sum_{i=1}^{Q(n)}\Pr[\text{session }i\text{ aborts}]
\le Q(n)\,2^{-k}.
\]

An exact conditional simulation off abort can consequently give statistical error bounded by this quantity; computational composition also carries the underlying computational hybrid errors. The parameter choice must make the displayed error negligible if that is the target claim. Truncation does not yield perfect ZK automatically, and an arbitrary expected-polynomial simulator does not automatically have this particular exponential tail. The unbounded retrying algorithm in PS10 is still outside the finite `ProbComp` syntax; that is the recorded restriction, not a newly proved bridge.

The unchanged search-game and phased-oracle interfaces still express the concrete experiments in Defs 134.2, 136.2, 140.1, 168.1 and 172.6: output types need not be Boolean, state persists across phases, query logging supports message freshness, and a challenge-equality test can return rejection. The executor changes do not alter those interfaces. Efficient-adversary quantification and asymptotic conclusions remain S2b obligations.

## Declaration-by-declaration comparison

The following are the blind mathematical restatements and subsequent docstring comparisons. A changed citation or docstring is included even where the defining body is unchanged.

Definitions and types:

- **`ExecOutcome` (`Protocols.lean:83`):** a disjoint choice between two returned values, an attempted send without remaining message budget, and a send encountered while closing after the other party has returned. Its constructors match this meaning; errors retain no partial output or party identity.
- **`ExecOutcome.swap` (`:92`):** exchange the two returned values, leaving each error unchanged. The docstring matches.
- **`Party.close` (`:110`):** pass through draws until a return or send; return `some a` on the former and `none` on the latter without running its continuation. The docstring matches, provided its “pending send already answered” phrase is read as the caller's convention rather than something the function itself does.
- **`Party.endWith` (`:117`):** invoke the waiting continuation on `none`, close it, and either pair its return with the active party's return or report `sentAfterEnd`. The docstring matches, including activation of the second party if the first returned before any message.
- **`Party.exec` (`:130`):** execute local draws, finish on a return using `endWith`, or consume one unit per permitted handoff and exchange roles; at zero fuel reject a handoff. The operational description matches. The claimed relationship to D8 needs finding 1's qualification.
- **`Party.Obs` (`:169`):** two ordered lists, one of delivered incoming messages and one of sampling-oracle indices with their finite answers. Its declaration docstring is accurate. It does not independently contain source inputs or unused tape bits; the stronger module claim needs finding 2.
- **`Party.stepT` (`:176`):** return the same return/send boundary as `step`, together with all draws before it in execution order. The docstring matches.
- **`Party.closeT` (`:184`):** return `close`'s optional value and the draws up to its return/first forbidden send, in execution order. The docstring matches.
- **`Party.endWithT` (`:191`):** return `endWith`'s outcome and the waiting party's closing draws. The docstring matches; it does not claim to include the earlier active party's draws.
- **`Party.execT` (`:199`):** execute with the same fuel/closure rules as `exec`, returning the original party order and the two correctly routed observations. Its local trace claim matches; `[PS10]` needs the full-tape convention in finding 2. A blocked send is not delivered and is not added to a received list.
- **`ProbComp` (`Probability.lean:73`):** specialize the well-founded query syntax to positive finite uniform-selection answers. The docstring and new VCVio tag match; the finite probabilistic semantics is supplied by `expect`, not by arbitrary external answers to this syntax.
- **`ProbComp.sampleFin` (`:80`):** issue one sampling query with exactly `m+1` possible answers and return that answer. It is uniform under `expect`, and the new `uniformFin` attribution is appropriate.
- **`QueryImpl.comp` (`Simulate.lean:140`):** implement a source call by running the first handler under the second, retaining both updated states in their original state order. Its description and new VCVio composition tag match.
- **`guessGame` (`Advantage.lean:117`):** draw a uniform Boolean, run the corresponding Boolean-output game, and return whether its output equals that bit. Its operational prose matches. Its connection to Def 168.1 is a reformulation of the fixed-bit experiment, as explained in the unresolved M2 row.

Unchanged supporting definitions were also checked for regressions: `exchangeSpec` returns `Option In`; `Party` is the union of exchange and sampling effects; `step` runs only to the next return/send; the query monad, costs, probability interpretation, simulation and logging remain unchanged. The generic `OracleComp` tree wording is now accurate as described in resolution 6.

Theorem statements, one assessment per changed declaration:

- **`accept_nonneg` (`Advantage.lean:71`):** it asserts the lower bound only, exactly as the repaired prose now says.
- **`advantage_hybrid` (`:102`):** it bounds the endpoint difference by the sum over precisely `n` adjacent gaps, including the empty chain. The docstring accurately identifies the telescoping inequality from the source proof and its concrete-layer specialization.
- **`exists_advantage_hybrid_gap` (`:109`):** for a nonempty chain of gaps, it provides an adjacent gap at least the endpoint gap divided by the number of gaps. The prose matches; disclose the source sharpening in finding 4.
- **`guessAdv_eq_half_advantage` (`:152`):** it states the exact factor-two relation for the absolute guessing-bias convention. The numerical statement/prose and the elementary algebra are correct; the new claim about which two formal conventions PS10 uses is the remaining M2 attribution defect.
- **`expect_mono_of_allOutputs` (`Hopping.lean:102`):** the assumed support predicate confines the required pointwise inequality to possible outputs. The revised docstring says precisely this.
- **`abs_prob_sub_le_of_agree` (`:131`):** events agreeing outside the bad event in one common probability space have difference bounded by bad probability. The statement and indicator/expectation sketch match; resolution 8 identifies the outstanding citation repair.
- **`prob_mem_le` (`:158`):** it bounds one new uniform draw's membership in a previously sampled list of bounded length. The revised statement prose and fixed-list averaging sketch are accurate; this is not already an adaptive birthday theorem.
- **`expect_ite_one_split` (`:194`, private):** it writes the expectation of “one on bad, `f` elsewhere” as the bad probability plus the off-bad expectation of `f`. The short docstring describes that split accurately, using normalization of `ProbComp`.
- **`prob_eq_until_bad` (`:220`):** it concludes equality of the good-output-event masses and equality of final-bad probabilities from a good start. The revised prose and induction sketch match the semantic premise; “same law” must include the whole reply/state pair and its unnormalized good mass.
- **`identical_until_bad` (`:301`):** it bounds the absolute output-event gap by the first game's final-bad probability. The prose, semantic deviation and three-step sketch match; the preceding theorem also makes the second game's bad probability equal.
- **`hagree_of_eq` (`:326`):** equality of the complete handlers at good entry states implies equality of every tested off-bad expectation. This is exactly the old-premise implication advertised, not an equivalence of the two premises.
- **`identical_until_bad_init` (`:338`):** the same bound holds after a common sampled initialization all of whose possible states are good. Its docstring and averaging sketch match, including the good-initial-support restriction.
- **`exec_zero` (`Protocols.lean:139`):** the statement includes both return/closure and blocked-send branches. Its short docstring only describes the latter, as in finding 3.
- **`exec_succ` (`:145`):** after one available handoff, the recurrence executes the receiver against the sender's continuation with one less fuel and swaps the result back; on return it closes instead. This is what the docstring describes.
- **`stepT_fst` (`:214`):** projecting away the draw list recovers `step` as an equality of computations. This matches its projection docstring.
- **`closeT_fst` (`:227`):** projecting away the draw list recovers `close`, including failure at a forbidden send. This matches its projection docstring.
- **`endWithT_fst` (`:240`):** projecting away the waiting party's closing draws recovers `endWith`. This matches its docstring.
- **`execT_outcome` (`:252`):** projection to the outcome recovers `exec` for every fuel and party pair. The generalized-fuel induction sketch explains this correctly; the result does not make an assertion about view contents.
- **`simulate_comp` (`Simulate.lean:152`):** nested simulation equals simulation by the composed handler after the explicit reassociation of both final states. Its unchanged statement/sketch and new VCVio design citation agree.

The three added unnamed examples assert the zero-message successful run, a one-message successful run, and a closing-send failure. Their mathematical statements are correct, but the second and third do not replace the role-swap, randomized-closing, or trace checks above.

## Source and evidence qualifications

PS10 references are to the hash-verified supplied PDF. The audit does not adopt every prose claim of the source: in particular, it preserves the declared expected-time restriction and the inventory's public-key reading of Def 172.6.

The VCVio attribution checks used the pinned [oracle computation](https://github.com/Verified-zkEVM/VCVio/blob/9054989327a7185ff19ef9ff0f119cccea479501/VCVio/OracleComp/OracleComp.lean), [oracle specification](https://github.com/Verified-zkEVM/VCVio/blob/9054989327a7185ff19ef9ff0f119cccea479501/VCVio/OracleComp/OracleSpec.lean), [query](https://github.com/Verified-zkEVM/VCVio/blob/9054989327a7185ff19ef9ff0f119cccea479501/VCVio/OracleComp/OracleQuery.lean), [probabilistic constructors](https://github.com/Verified-zkEVM/VCVio/blob/9054989327a7185ff19ef9ff0f119cccea479501/VCVio/OracleComp/ProbComp/Basic.lean), [composition](https://github.com/Verified-zkEVM/VCVio/blob/9054989327a7185ff19ef9ff0f119cccea479501/VCVio/OracleComp/SimSemantics/QueryImpl/Compose.lean), and [logging](https://github.com/Verified-zkEVM/VCVio/blob/9054989327a7185ff19ef9ff0f119cccea479501/VCVio/OracleComp/QueryTracking/LoggingOracle/Core.lean) modules. The named construction correspondences and headers were checked; authorship history and the assertion that no code was transcribed were not independently reconstructed.

For Shoup, the inspected [author-hosted PDF](https://www.shoup.net/papers/games.pdf) is dated 18 January 2006; its difference lemma is §1.1, Lemma 1, p. 3. For Bellare–Rogaway, the [author publication record](https://www.cs.ucdavis.edu/~rogaway/papers/games.html) confirms the EUROCRYPT 2006 provenance; the indexed primary [full version, ePrint 2004/331](https://eprint.iacr.org/2004/331.pdf), dated 27 November 2008, identifies Lemma 2 and the standard bound. Direct retrieval of that full PDF and the proceedings PDF failed in this audit, so no new exact proceedings section number is certified. The semantic inequality used in Q4 was checked independently above.

## Notation glossary

- `return a`, `send(m,k)`: `.pure a` and the message-exchange query carrying `m` with continuation `k`.
- `A,B`, `a,b`, `m,k`: locally specified parties, their returned values, a message, and a continuation; in the truncation bound `k` instead denotes the accuracy/repetition parameter. In the crossing-call example `b` denotes its freshly drawn bit.
- `M_A,M_B`, `|M_A|,|M_B|`: the original first and second movers' received-message lists and their lengths.
- `u,v,w`: the three nontrivial sample values in the two-message coin-order test.
- `μ₀,μ₁`, `g`, `y,s'`: the two finite one-call reply/state laws, a real test function, a reply, and a successor state.
- `a,b₀,b₁,B` in the bad-event calculation: common good-event probability, the two bad-event contributions, and common bad probability; these are local to that calculation.
- `p_j(s)`, `p_i`, `Pr_j`, `E`: initialized-state output-event probabilities in game `j`; hybrid acceptance probabilities; probability in game `j`; expectation. Their contexts are separate.
- `x,y,z_A,z_B,r_A,r_B`: source inputs, auxiliary inputs and full random tapes in the view construction.
- `n,Q(n),ε,m` in source comparisons: security parameter or number of hybrid gaps as specified locally; number of sessions; source distinguishing threshold; number of source hybrid distributions.
