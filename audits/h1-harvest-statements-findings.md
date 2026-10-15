SHA-256: `1b294f312a89211072a0dcaf42a445c0e2ae10338fe7e798adcfba3ab373a596`.

Exactly **66 sections** match `## ===== <repository path> =====`. Both checks match the request.

**Verdict: PASS — 0 blockers, 0 majors, 4 minors.** The proposed public contracts satisfy C1 ruling 5. The actual companion edit preserves the remaining statements and removes the private assembly as disclosed. The findings concern evidence checks, one negative control, and a stale documentation reference; none demonstrates a false public statement or a missing contract needed for R's loop phase.

This is the **statement-gate verdict**, not certification that the proposed modules have landed or that their downstream build has passed. Apply or explicitly dispose of the minors and perform the planned merged-base replay before landing. Homes, names, and the other design choices below remain the user's decisions.

I read the three definition bodies in the unit with comments removed before comparing their docstrings. I independently reconstructed the supplied module, overlay, replay probe, and companion landing; applied the supplied diff separately; checked the declaration changes; and ran adversarial controls against the Python/shell checks. **I did not run Lean:** this environment has neither a Lean executable nor the complete dependency/olean snapshot. Elaborations, axiom sets, and the maintainer's re-check at `1b6b972c` remain supplied execution evidence, distinguished below from reproduced source facts. I did not review tactic proofs for correctness.

Locations below are repository-relative. Unit locations refer to `audits/evidence/h1harv/H1Harvest.lean.txt`; source line numbers exclude the bundle's presentation fences. The immutable input was not edited.

## Findings

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| H1-1 | minor | `scripts/decls.py.txt` · `cmd_freeze`, `cmd_movemap`, `cmd_refs` | Exit zero certifies the stated freeze, move, and private-reference checks. | Three independent checker-level false passes: an extra `ChoiceReplay` import in the proposed `CodeSimulator` still gives `FREEZE OK`; changing the moved `loopRoundTime_spec` bound from `50` to `51` still gives `MOVEMAP OK`; appending `#check Turing.StepBlock.loopRoundTime` still gives `REFS OK`. The outside-declaration delta is printed but not asserted; unchanged-spec equality is not enforced; the reference regex excludes identifiers preceded by a dot. These mutations are scratch controls, not defects found in the supplied landing. | Assert the permitted outside-declaration delta and surviving declaration order; enforce the expected kinds, visibility, and unchanged signatures for the fixed move-map entries; recognize qualified references, including their final name components. Add these controls, each requiring nonzero exit. Keep actual cross-module elaboration as a separate landing check. |
| H1-2 | minor | `scripts/runall.sh.txt` · §6; pack's “fails closed” description | Every check contributes to failure status. | The three elaborations in the cited-name section are not passed to `expect` or `check`; unexpected unresolved names are printed without an asserted allowlist. In an isolated execution of the actual §6 shell text with deliberately failing elaborator responses, the section printed `Turing.exists_ndInterpreterCore ... 1 errors`, left `CHECKS=0`, `FAILS=0`, and returned success. This is a test of failure accounting, not a Lean run or a reproduction of the full runner. | Check each elaborator's expected status and diagnostics, assert the allowed unresolved-name sets, and increment failures on discrepancies. Treat errors outside the generated `#check` lines as failures. Audit other informational/preparation commands before describing the entire runner as fail-closed; alternatively describe precisely which checks gate its exit. |
| H1-3 | minor | `scripts/neg/neg2_tail.lean.txt` · its `example` | This is a negative control for deleting the counter-width term from the actual exit-time bound. | The conclusion is only `∃ T, ∀ t' ≤ t, ... → T ≤ t' * B + 4 * t'`. It contains **no run equation or exit requirement**. It is true by choosing `T = 0`; the reported failure shows that the supplied proof does not close, not that the statement is false. | Retain the actual run endpoint and first-exit requirement when forming the negative statement. Use the large-borrow example below to test the missing width term, or label the existing file merely as a failed proof-reuse test. |
| H1-4 | minor | Unit:319 · `loopTM_run` proof sketch; landed module:283 | The represented-run argument is identified by its available helper. | The sketch still calls it `h1Clock_orbit`, although that declaration is deleted and the generalized helper is `loopOrbit_rep`. The old overlay context can resolve the historical name, so taking the union of overlay and replay name checks hides this stale reference. | Write `loopOrbit_rep` here, optionally followed by “formerly `h1Clock_orbit`.” Validate current citations in the landing context; separately allow references explicitly labelled historical. |

The checking defects are minors because the submitted source facts were independently verified and the proposed statements have no identified substantive defect. H1-1 does **not** claim that its mutations evade every combined elaboration/axiom check.

For H1-3, the current conclusion has the immediate witness

```lean
by
  exact ⟨0, fun _ _ _ => Nat.zero_le _⟩
```

This displayed replacement was not compiled here; its mathematical content is simply `0 ≤ t' * B + 4 * t'`.
A genuine counterexample to the width-free **exit** bound uses a fixed machine that halts on its first transition and counter word

\[
w=\underbrace{[\mathrm{false},\ldots,\mathrm{false}]}_{B+2\text{ entries}}
  \mathbin{++}[\mathrm{true}],\qquad t=2^{B+2}.
\]

The first decrement alone takes

\[
2(B+2)+2=2B+6>B+4.
\]

The simulated round begins only afterward. Thus the actual first escape cannot satisfy the proposed width-free bound at `t' = 1`. This follows from the supplied decrement-cost definition and loop sequencing; it is not an additional machine-checked probe supplied by this audit.

## Definition restatements and comparison

| Definition | Independent reading of its body | Comparison |
|---|---|---|
| `loopTM k` (unit:133) | Apply the binary counter-loop constructor to `roundTM k`, using `exit k true` as its round anchor and `exit k false` as its designated escape. Its work tapes are the block's `k + 2` tapes followed by the counter; its control is the counter-loop state over the block's state. | Matches the docstring. A decrement precedes each simulated step; a returning round triggers another decrement, and the final underflow selects `done`. The machine program depends on `k`, not on the represented table or deadline. |
| `hostedLoopTM k` (unit:141) | Apply the emitting virtual-input transformer to `loopTM k`. This adds a first input-buffer tape and pairs the loop control with a Boolean boundary tag. | Matches the docstring. Z1 supplies the frozen native head and forwards physical emissions; the block/loop contract supplies silence during the represented simulation. The transformer itself is not being asserted silent on arbitrary malformed configurations. |
| `loopRoundTime d` (unit:150, private) | Take the least **strictly positive** time at which `roundTM k`, started at `d`, reaches either flagged exit. Return zero if there is no such time. | Matches the intended proof index. Starting at the entry marker does not make the selected duration zero. The docstring could mention the fallback explicitly, but its specification correctly excludes that fallback at represented live entries. |

The companion's `h1HostedVerdictTM` is also faithful: outside the two loop exits it keeps the hosted transition; at either exit it performs one stationary halting emission. It emits `true` precisely at `escape` with summary cell `some true`, and emits `false` otherwise. Its body is unchanged after replacing the old machine name by `hostedLoopTM`; this is a check of the existing wrapper, not a new machine design.

These are implementation refinements of bounded universal simulation, not verbatim AB09 theorems. The exact constant `50`, representation relation, binary countdown, and live exits come from the library's previously gated interfaces. Independent retrieval of the author-hosted draft supports the bounded-simulation motivation in its universal-machine discussion and §3.1; I could not retrieve the published 2009 pages for a fresh edition-specific check. The draft has different numbering in places, so I do not present it as verification of the 2009 theorem numbering. Sources: [author-hosted book draft](https://theory.cs.princeton.edu/complexity/book.pdf), [author-hosted excerpt](https://theory.cs.princeton.edu/complexity/excerpt.pdf).

## Public contracts: meaning, non-vacuity, and consumer sufficiency

**`loopTM_run` (unit:330).** The statement runs the actual public machine from the prescribed counter configuration and identifies its endpoint with a represented source run at the deadline; `done` means that source run is still live, and `escape` means it has halted by then. The same existential time satisfies the full bound, every applicable early bound, endpoint output preservation, the counter frame, and the two strict-prefix exclusions. Its hypotheses are satisfiable for every live source configuration: construct the canonical mirrored bank, table, and summary/state tape, choose entry control, and install any translated delimited counter word. This is exactly the native loop interface needed by the hosted theorem and recovers the old private effect statement by the disclosed specialization.

**`hostedLoopTM_run` (unit:458).** This is the same run and same bounds under Z1, with any valid initial tag, arbitrary native input/head, and arbitrary physical prefix. `Rep` equates the source and block input positions, so the tag hypothesis is the one required by the virtual-input lockstep; the endpoint gives a valid, existential arrival tag rather than assuming it is unchanged. Non-vacuity follows from the preceding construction and choosing the boundary-compatible tag, and `pre ++ e.output = pre ++ d.output` follows from the stated equality. The cut excludes **every** tag at both exits, which permits a caller to replace all verdict-exit transitions without changing the strict-prefix run.

**`hostedLoop_read` (unit:522).** This is a structural reading lemma, valid at any represented body configuration and any supplied live loop control, rather than a claim that arbitrary data have been reached by a run. The summary tape has original index `k + 1`; `castSucc` preserves that index when the counter is appended, and `vhostBank` increases it to host index `k + 2`, as required. `Rep` puts that tape's head at zero and its zero cell at `outputSummary c'.output`, so `outputSummary_true` identifies exactly the singleton `[true]`. Its hypotheses are satisfiable by the canonical frame, and together with the hosted endpoint it gives precisely the control, native head, physical output, and cell needed for a one-step verdict transition; no tag-validity hypothesis is needed for this structural identity.

The body configuration's `state` field is intentionally not uniquely determined by the public endpoint: `counterLoopCfg` replaces it, and `Rep` leaves control free. This is benign. The **actual host control and actual transported tape/head/output fields** are pinned by the run equation, so the existential body is not a freely chosen verdict witness.

The private theorem statements were checked as well:

| Helper | Ruling |
|---|---|
| `loopOrbit_succ` | Exactly the successor equation of `roundOrbit` through the abbreviation. Its one-line proof needs no separate proof sketch under policy §3. |
| `loopRoundTime_spec` | Same signature as the renamed private specification: positive bounded duration, correct one-step represented endpoint, silence, and an interior cut. The live-entry hypotheses are precisely those of the previously gated step block. |
| `loopOrbit_rep` | Correct generalized invariant. The separate initial liveness hypothesis is needed at round zero; at positive rounds, the strict-prefix liveness condition permits the final round itself to halt. Specializing `c` to `M.initCfg x` recovers the old statement. |
| `loopOrbit_round` | Correctly requires source liveness through round `r`, thereby supplying the next positive round and its interior cut. Initial liveness follows from its hypothesis at zero; no additional hidden initial-state assumption is introduced. |

## Adversarial instantiations

| Test | Result |
|---|---|
| `t = 0`, `w = []` | `M.runFrom c 0 = c` is live, so the selected exit is `done`, even if the next transition would halt. No source round runs. Empty-counter underflow takes two steps, consistent with `T ≤ 2`. |
| `t = 0`, `w = [false,false]` | Again `done`; underflow scans and returns across the two counter cells, costing `2·2 + 2 = 6`. Padded zero does not cause a simulated transition. |
| First source halt exactly at `t > 0` | The state at the deadline is `none`, hence `escape`. Substituting `t' = t` gives `T ≤ t·B + 4t + 2|w|`; the escape round index is `t - 1 < t`. There is no final underflow charge. |
| First transition halts, any `t ≥ 1` | Absorption gives `M.runFrom c t = M.step c`; clause (ii) at `t' = 1` gives `T ≤ B + 4 + 2|w|`. At deadline one the hosted endpoint is `some (.escape,b')`, not `none`; the tighter escape bound is `B + 6` for `[true]`, while S4's general `B + 8` also covers timeout. |
| Arbitrary represented start and endpoint | The S0 construction works for every source configuration, including the replay start with a preinstalled stream and arbitrary mirrored tapes/heads. Its physical output can be chosen independently. The actual run equation and summary relation prevent choosing an unrelated accepting endpoint. |
| Drop `live` | Take a halted source configuration, `t = 0`, and `w = []`. The early clause at `t' = 0` would force `T ≤ 0`, while the endpoint would require `escape`; the state at time zero is `.dec .run`. Thus the generalized statement without `live` is false, without needing any assumption about how the block handles the empty state word. |
| Drop `hb` | At the left blank, `c.inputPos = 0`, the valid tag is `false`. For a left move, `virtualMove false none (-1) = 0`, but the wrong tag gives `virtualMove true none (-1) = -1`: the physical buffer head moves from `-1` to `-2` instead of staying at `-1`. The endpoint representation can therefore fail. |
| `k = 0`, one state, empty input, immediate emitting halt, counter `[true,false,true]` | The counter value is `1 + 0·2 + 1·4 = 5`; the zero-tape mirrored bank is empty but the auxiliary tapes remain. The first round escapes with summary `some true`, and the early bound is `B + 4 + 2·3 = B + 10`, exactly S5's claim. |
| Output summaries | `[] ↦ none`, `[true] ↦ some true`, `[true,true] ↦ some false`, `[false] ↦ some false`. Acceptance also requires `escape`; a live source that has already emitted `[true]` is still rejected on timeout. |
| Shifted counter and arbitrary external cells | The closed delimiter hypothesis includes `cp - 1` and `cp + |w|`; the modified interval is half-open. Both delimiters and every external cell are preserved. The same statement allows negative `cp`; at width zero the entire counter tape is framed. |
| Nonempty physical prefix; arbitrary valid tag | The output is exactly `pre ++ d.output`, independent of the simulated output summary. Interior virtual positions admit either tag; boundary positions constrain it. The arrival tag may change, and the cut covers both tags, including at time zero. |
| Choice stream longer than `t` | The replay theorem equates each prefix of length `t' ≤ t` with the branch along `s.take t'`. No suffix after that prefix affects state or output. The probe retains the whole tape in the representation but does not scan or clear its unused suffix. |

The distinct initial and exit constructors exclude a zero-time exit witness. The supplied S0–S5 probes support these checks, but the negative-control failures themselves are not proofs of false statements; H1-3 is the concrete instance of that distinction.

## R's consumer fit and time calculation

The replay probe chooses the constant **before** quantifying over the input, deadline, stream, frame, and native head:

\[
B=50\bigl(|\operatorname{tableBitsK}(N.\operatorname{replayTM}.\mathrm{tr})|+1\bigr),
\qquad C=B+6.
\]

This is one constant per decoded machine, hence per code. `CodeNDTM` has two work tapes and `Fin (numStates + 1)` states; its replay machine has three tapes and the same states, exactly the harvest's parameter shape.

For every `t' ≤ t`, the supplied replay and locality statements give

\[
\begin{aligned}
&(N.\operatorname{replayTM}.\operatorname{runFrom}
 (\operatorname{withChoiceTape}(N.\operatorname{initCfg}(x.\operatorname{take}t))
 (\operatorname{bufferTape}s)\,0)\,t').\mathrm{state}\\
&\hspace{2em}=(N.\operatorname{runWith}(s.\operatorname{take}t')
 (N.\operatorname{initCfg}x)).\mathrm{state},
\end{aligned}
\]

and the same equality for output. The needed length hypothesis follows from `t' ≤ t ≤ |s|`; locality applies because `|s.take t'| ≤ t`. The valid initial tag is `true`, including the empty input window.

The full bound follows step by step from `|bits t| ≤ t`:

\[
\begin{aligned}
T&\le tB+4t+2|\operatorname{bits}t|+2\\
 &\le tB+6t+2\\
 &\le (B+6)(t+1)=C(t+1).
\end{aligned}
\]

If the branch has halted by `t' ≤ t`, the **same** time satisfies

\[
\begin{aligned}
T&\le t'B+4t'+2|\operatorname{bits}t|\\
 &\le (B+6)(t'+|\operatorname{bits}t|+1)\\
 &\le C(t'+|x|+|\operatorname{bits}t|+1).
\end{aligned}
\]

The summary reading then gives
`(q = escape ∧ cell = some true) ↔ (branch.state = none ∧ branch.output = [true])`.
The general consumer probe also explicitly states `q = done ∨ q = escape`; the replay probe omits that conjunct but instantiates the theorem's actual conditional exit, so no public guarantee is missing.

**Still R's fill obligations:** parse the header; construct/install the replay table and initial unary state; copy and rewind `x.take t`; preserve the already installed choice stream; establish the exact `Rep`/Z1/counter seam; implement distinct live accept/reject states with their cut; and add the setup, dispatch, and verdict costs to both ledgers. In particular, the unused stream suffix must not be traversed. The harvest proves the loop phase, not those setup/composition obligations. Its absence of space/head-trajectory clauses does not obstruct this time consumer; future space consumers need the separately disclosed adapter or companion contracts.

## Landing, freeze, and duplication

The supplied diff applies to the bundled `CodeSimulator.lean` with **zero fuzz** and produces exactly the bytes regenerated by `mkposth.py`. The disclosed eight removals are:

| Removed private declaration | Destination |
|---|---|
| `h1ClockTM` | public `loopTM`; same body, explicit type |
| `h1HostedClockTM` | public `hostedLoopTM`; same body after renaming, explicit type |
| `h1RoundTime` | private `loopRoundTime`; same body/signature after renaming |
| `h1RoundTime_spec` | private `loopRoundTime_spec`; same signature |
| `h1Clock_orbit` | private `loopOrbit_rep`; arbitrary live start |
| `h1Clock_round` | private `loopOrbit_round`; arbitrary start |
| `h1Clock_effect` | public `loopTM_run`; disclosed generalizations |
| `h1HostedClock_effect` | public `hostedLoopTM_run`; disclosed generalizations |

The removals total **269 lines including their docstrings**. `CodeSimulator` changes from **105 to 97 declarations**, with **11 public declarations before and after**, and from **3,290 to 3,010 lines**. All surviving signatures, visibility, and declaration order are preserved. Only `h1HostedVerdictTM` and `h1HostedVerdict_effect` change executable bodies; the former is identical after the machine-name replacement, and the latter's statement is unchanged. **`h1HostedVerdict_accepts` is byte-unchanged**: “three re-pointings” describes the retained client group, not three textual body edits.

The changed declaration docstrings are exactly those of `h1HostedVerdictTM` and `exists_uniformSimulator`. Outside declarations, the actual delta is the import and disclosed module-status text. Both old headline admissions remain. The new module contains exactly five public and five private declarations; `hostedLoop_read` and the private successor helper are the two new declarations beyond the eight moved/generalized ones.

The eight deleted declarations are absent from the landing's executable code. An independent token search that also recognizes qualified names found no reference there to any of the new module's five private helpers. No new instance, notation, or simplification attribute is introduced by the unit. The one-file rehearsal plus this inspection is adequate **statement-gate evidence** of the current split, but is not a substitute for compiling the actual module boundary before landing.

**Duplication ledger:** accepted. Production has a move, not a second copy. The three disclosed overlaps are replaced by the public first-exit uniqueness lemma, the core orbit-successor lemma, and `hostedLoop_read`. Overlay/probe copies are evidence, not production debt. The probe-only bits-value proof remains evidence; do not transplant it privately into R. No new unacknowledged production-copy family was found. O7's future round adapter, the summary-encoding family, U-1's constant/device work, and the other inherited H2 items are not closed by this gate.

## Rulings on the brief's eleven points

| Point | Ruling |
|---|---|
| 1. Ruling 5 | **Satisfied item by item.** Arbitrary represented live starts include the stream-installed replay start; clause (ii) quantifies over every qualifying `t' ≤ t` for one exit time; live exits, exact transported endpoint, every-tag cut, frame, and summary reading are supplied. |
| 2. Native loop | **Approved.** Halt-at-deadline selects escape; absorption identifies the endpoint; both delimiters are framed; output is preserved; time zero is off both exits. |
| 3. Hosted loop | **Approved.** Correct initial-tag premise, existential valid arrival tag, unchanged native head, arbitrary prefix, and all-tag cut. |
| 4. Reading | **Approved.** The summary host tape is index `k + 2`, and `some true` characterizes exactly `[true]`. |
| 5. Consumer fit | **Approved for the loop phase.** Both time clauses and the correct full-input branch verdict follow; the remaining setup/seam/verdict/ledger work is listed above. |
| 6. Landing and freeze | **Actual supplied edit approved.** Eight deletions, two changed retained bodies, unchanged third client, and no other surviving signature change. Repair the checker overclaims in H1-1; actual cross-module replay remains a landing obligation. |
| 7. MIG-0b and PRs | **Approved with the stated evidence limits.** Public signatures contain no orbit or duration function. The successor helper uses `roundOrbit_succ`, and the deleted old invariant includes MIG-0b's unfolding token. The newer maintainer note supersedes the old open-PR status; include `SelfUniversal` in the merged-base replay and rebase the facade. The complete PR diffs/build graph are not independently available here. |
| 8. Homes/names/registry | **Recommend the proposed choices.** A separate `Build/StepBlockLoop` expresses the composition without forcing counter/virtual-input dependencies on bare-step-block clients. `Turing.StepBlock` and the five public names are coherent; H2-L avoids confusion with the registry's unrelated H1. |
| 9. Adversarial instances/debt | **Attempted above.** No public-contract counterexample found. H1-3 identifies the vacuous negative control; no new production duplication debt found. |
| 10. Documentation/policy | **Approved subject to H1-4 and the planned sketch update.** Required module sections and public prose are present; all nontrivial helper/public proofs have literal proof-sketch paragraphs. The successor's one-line proof is exempt. New-module/probe lines are at most 100 characters; the unchanged old 102-character canonizer line moves from 1134 to 1137. File size is not a reason to split this harvest. |
| 11. Other claims | **Bounded as in the evidence record below.** Source fidelity is independently reproduced; historical commit identity, complete closure/name inventories, and kernel execution are not upgraded from supplied claims to new measurements. |

## Recommendations on the seven open questions

1. **Home:** keep `Build/StepBlockLoop.lean` in namespace `Turing.StepBlock` for the stated layering reason.
2. **Registry:** add H2-L directly after H2; mark it landed only when the landing actually occurs.
3. **Names:** retain `loopTM`, `hostedLoopTM`, `loopTM_run`, `hostedLoopTM_run`, and `hostedLoop_read`.
4. **Order:** the pack's newer note says #92 and #93 are merged. Land against that merged base, with the nine-module replay including `SelfUniversal`; retain its existing facade additions. I did not independently query Git history.
5. **Gate/fill:** no separate proof-fill brief is needed for these ten proved declarations. Use the single maintainer landing PR and replay, then have R's brief cite the public contracts.
6. **Bits value:** recommend a public `Turing.counterValue_bits (t : ℕ) : counterValue t.bits = t` beside `counterValue`, with a small separately reviewable proof. Reuse or move the word-value bridge rather than copying it into another consumer, and avoid importing an interpreter module into the counter layer merely to access the private proof. The generalized harvest itself does not require this extra theorem.
7. **R's sketch:** update it at landing to name `hostedLoopTM_run` and `hostedLoop_read`; remove the stale “private”/“harvested with H2's promotion” wording. The public early bound now supplies the consumer estimate directly, without making R depend on a private exact-duration function.

## Independent evidence record

Removing only the presentation fences/separator blank line where appropriate reproduces the recorded unit and diff hashes. In particular:

| Artifact | Lines | Independently computed SHA-256 |
|---|---:|---|
| Unit | 540 | `3b46ca085ed4a7ff7129a8283c22f546cb3af34ab01398470fe08956a94b90e3` |
| Landing `StepBlockLoop.lean` | 504 | `f0dc162f717c3de5a12a3cdd7cb64f7764e49b51868699fabef71c7d96d54845` |
| Landing `CodeSimulator.lean` | 3010 | `d3ee752604cb1ba801d7fae1014b0ad48c13eb8c0d8725575e666760403b0bc6` |
| Supplied companion diff | 417 | `602490e6e18bfbda5904df6ee796db72dfeae1f35c4d40b76ce6d5142960a450` |

- The overlay begins with exactly the bundled base's **167,148 bytes**, then a newline. The base's computed Git blob hash is `aceb849bc4af87ce3a6b4dab79938bf8b7e955c4`, matching the transcript. This checks the bytes against the logged hash, not the commit's existence independently.
- Regenerating the standalone module, full overlay, and replay probe yields byte-identical supplied files. The generated cut has the three declared imports and the same nonblank content as the landing module. The five corollary theorem statements are extracted from the old declarations; the three definition-equality probes accompany them.
- The admissions census reproduces zero `sorry`/`axiom` declarations in the harvest and exactly the two retained headline sorries in the landing `CodeSimulator`. The ten standard-axiom prints and zero-error elaborations are internally consistent **supplied transcripts**, not fresh kernel results from this audit.
- The supplied library sources show the intended dependency directions. The full 716/721-module graphs, complete name inventory, missing transitive sources, and both olean trees are not in this environment, so I do not independently certify the exact whole-tree closure/name/replay counts or snapshot completeness. The pack already labels snapshot completeness inferred and downstream replay pending.
- The maintainer note identifies the three newer bundled files and reports the merged-base re-check. Nothing inspected contradicts it; the absent post-merge raw build artifacts prevent independent verification of that execution claim.

**Notation used:** `B` is the per-round table bound `50·(|tableBitsK M.tr| + 1)` (with `M = N.replayTM` in the replay calculation); `C = B + 6` is the probe's per-machine loop constant; `T` is physical loop time; `t` is the simulated deadline; `t'` is a tested prefix length; `w` is the little-endian counter word; `cp` is its starting head position; `|·|` denotes list length; `++` denotes list concatenation. All follow the pack's notation.
