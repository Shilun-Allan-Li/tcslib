# §12.6 framed catalog contracts — statement-gate findings

**Verdict: PASS — 0 blockers, 0 majors, 0 minors; notes below.** The five statements are mathematically sound as written and sufficient for the selected framed routine calls. Their hypotheses are sufficient but not all minimal. This closes the **statement gate**, not the proof-fill gate or either zone-machine construction.

Audit date: 2026-10-10. Evidence: the supplied `s12-framed-bundle.md`, SHA-256 `5ae388dc2f33f884646b4f513f80ec5783e4ee38fe3d4185cf7ac3345a6a1634`. Source line numbers below refer to the extracted attachments, not the bundle. All five signatures were extracted with Lean comments removed, and the restatements were recorded before reading their theorem docstrings.

## Standard findings table

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| F1 | note | `Build/Catalog.lean:1341` · `transferTM_run_ofCfg` | No findings: exact transfer, frame, first return, and trajectory are correct. | Forward copy, blank turn, backward erasure, blank return take exactly `2*length w+2`. Cases T1–T3 include empty input, a stored `false`, negative coordinates, and occupied destination delimiters. | None. Prove the generalized trace once in Catalog. |
| F2 | note | `Build/Catalog.lean:1373` · `copyTM_run_ofCfg` | No findings: source preservation and arbitrary destination are correct. | Destination reads never select a transition; the intact source guides both passes. Cases C1–C3 also cover equal coordinates on distinct tapes. | None. |
| F3 | note | `Build/Catalog.lean:1404` · `clearTM_run_ofCfg` | No findings: the erased interval and both boundary cells are correct. | Erasure occurs only on the return pass, at nonblank interior cells. Cases E1–E3 include the minimum one-tape instance. Exact interior Boolean values are stronger than needed. | None; retain the common word-based interface. |
| F4 | note | `Build/Catalog.lean:1437` · `incrementTM_run_succ_ofCfg` | No findings: width, exact carry cost, both exit exclusions, and the shorter trajectory bound are correct. | `incFixed` preserves width on success; the first false bit is the turning cell. Cases S1–S3 cover zero carry, carry through the last word cell, and an untouched suffix. | None. The right-blank premise is deliberately redundant; maintain it between counter calls. |
| F5 | note | `Build/Catalog.lean:1470` · `incrementTM_run_overflow_ofCfg` | No findings: empty and nonempty overflow both satisfy the literal contract. | Overflow is exactly the all-true case, including `[]`; the output is stored false bits, not blanks. Cases O1–O3. | None. |
| F6 | note | Five contracts · hypothesis minimality | The common hypotheses are sufficient, not a minimal characterization of every literal conclusion. | Successful increment does not read the right delimiter; clear only tests interior nonblankness; the copy formula also works with aliased indices. The transfer formula with aliased indices describes a clear because its source branch has priority. | No gate repair. Keep distinctness for the advertised two-tape transfer/copy use; do not call every premise logically necessary. |
| F7 | note | `Build/Zone.lean:1109,1145` · consumer fitness | The interface gap is closed; the full uniform controllers remain to be proved. | Boundary preservation, ascending treatment of left-side words, and increment-to-overflow navigation fit the stated zone bounds; details below. These routines exit at live anchors, not genuine halt. | Carry these obligations into the zone fill brief. No additional catalog contract is forced by the selected route. |
| F8 | note | Pack · verification attestations | Source and semantic checks support the gate; repository compilation and historical freeze attestations were not independently replayed. | The attached Catalog has exactly five `sorry` tokens after comment stripping. The supplied Lean harness/log contains 63 passing fixtures and a rejected wrong-time control. Independent semantic-model checks pass, but are not Lean executions. No checker script, build environment, downstream logs, lint log, or pre-change machine baseline accompanies the pack. | Retain the maintainer's compilation evidence for the fill handoff. Do not describe this audit as a kernel replay or a historical byte comparison. |

## Blind restatements

Write $n=\texttt{w.length}$ and $p=\texttt{(w.takeWhile id).length}$. The common tape premise means precisely: at the selected initial head, the next $n$ cells hold the Boolean word `w`, and the cells at relative offsets $-1$ and $n$ are blank. `some false` is a nonblank cell. All configurations, outer tape contents, input positions, and output prefixes are otherwise arbitrary.

1. **Transfer.** For distinct `src` and `dst`, starting in `sweep`, the machine reaches `done` at time $2n+2$. It blanks the source interval and overwrites the destination interval with `w`, each interval measured from that tape's own initial head. Every other cell and every final head, input position, and output prefix is preserved. There is no earlier `done`; through the exit both selected heads stay in their translated $[-1,n]$ intervals and all other heads stay fixed. There is no destination-content premise.
2. **Copy.** With the same source-window and start-state premises, only the destination interval is overwritten with `w`. The source is preserved in full; the exact time, final preserved fields, first-return condition, and head bounds are the same as for transfer.
3. **Clear.** Starting in `sweep` with a delimited `w` at tape `i`'s head, the machine blanks exactly its length-$n$ interval and reaches `done` at $2n+2$. The final remaining fields and cells are preserved, `done` is absent earlier, the selected head stays in its translated $[-1,n]$ interval, and all other heads stay fixed.
4. **Successful increment.** Assuming `incFixed w = some v`, the machine starts in `run` and reaches `done true` at $2p+2$. Its selected length-$n$ interval is replaced by `v`; other cells and final fields are preserved. Neither Boolean exit anchor occurs earlier. Its head stays in the translated $[-1,p]$ interval through the exit, and every other head stays fixed.
5. **Overflow increment.** Assuming `incFixed w = none`, the machine starts in `run` and reaches `done false` at $2n+2$. Its selected interval contains exactly $n$ stored false bits afterward; all remaining cells and final fields are preserved. Neither exit anchor occurs earlier, the selected head stays in the translated $[-1,n]$ interval, and other heads stay fixed.

The transfer signature also matches `RequestedSharedLemma.lean.txt`: the local `T` and `finish` definitions are expanded, and the nested tape-index/interval tests are flattened without changing their values under `hne`. The exact time, record fields, earlier-exit exclusion, and trajectory quantifiers are unchanged.

These restatements agree with the five docstrings. They assert first arrival at a **live** exit state, not halting. No reachability assumption on `d`, finite-support assumption on its tapes, or restriction on the native input is needed.

## Transition-based justification

The relevant definitions are `Catalog.lean:137–219,260–283`, `Convention.lean:77–79,119–122`, `Simulation.lean:494–509`, and `Configuration.lean:197–207`. `Action.apply` writes at the old head before moving. Every transition of these routines has input movement zero and no output; every inactive tape receives `(none, 0)`. Thus the input position, output, inactive heads, and inactive tapes are preserved at every step, including input-boundary positions.

### Transfer, copy, and clear

Induct on the number of executed transitions. At time $t$, for $0\le t\le n$, the state is `sweep` and every selected head has relative offset $t$. Transfer/copy have overwritten exactly the destination prefix $[0,t)$; the source is intact. Clear has not yet written anything.

At $t=n$, the source's right blank causes one left move and enters `rewind`. After another $r$ return transitions, $0\le r\le n$, the time and relative head offset are

\[
t=n+1+r,\qquad \text{offset}=n-1-r.
\]

Transfer/clear have erased exactly the source suffix $[n-r,n)$; copy has preserved the source. Transfer/copy already hold the full destination word. If $r<n$, the next source cell is still an original nonblank interior cell, so the next transition extends the erased suffix, or merely moves left for copy. If $r=n$, the head reads the unchanged left blank, moves right, and enters `done`. Therefore

\[
T=n+1+n+1=2n+2.
\]

No preceding state is `done`, and no delimiter is written. This establishes the exact record updates, including the destination's unmodified boundary cells and arbitrary outer frame. It also covers $n=0$: the two delimiter transitions give offsets $0,-1,0$, with no word writes.

### Increment

The three defining clauses of `incFixed` give, by list induction,

\[
\begin{aligned}
\texttt{incFixed w = some v}
&\Longrightarrow
\exists\,\text{rest},\quad
w=\texttt{replicate }p\ \texttt{true}\mathbin{++}(\texttt{false}::\text{rest}),\\
&\hspace{47mm}
v=\texttt{replicate }p\ \texttt{false}\mathbin{++}(\texttt{true}::\text{rest}),\\
&\hspace{47mm}
p<n,\quad |v|=n;\\[2pt]
\texttt{incFixed w = none}
&\Longleftrightarrow w=\texttt{replicate }n\ \texttt{true}.
\end{aligned}
\]

For the induction: the empty list returns `none`; a leading false returns a word of the same length with that bit set; a leading true prepends one false to a recursive success and propagates a recursive overflow. In the last case the initial true-prefix length increases by one. These cases prove both displayed characterizations and width preservation.

On success, after $t\le p$ transitions the head is at relative offset $t$, the first $t$ true bits have become false, and the rest of the tape is unchanged. The next transition at $p$ writes true, moves left, and enters `rewind true`; the word is now exactly `v`. The $p$ return transitions cross nonblank false cells, then the left blank supplies the final right step: $T=p+1+p+1=2p+2$. Neither exit occurs sooner, and nothing to the right of offset $p$ is visited.

On overflow, the same induction changes all $n$ true bits to false before reading the right blank. That blank selects `rewind false`; $n$ return transitions and the left-blank step finish at $2n+2$. In particular `incFixed [] = none` gives the two-step empty overflow, not a zero-step exit.

### Every-time trajectory and frame

Set $m=n$ for the three sweep contracts and overflow, and $m=p$ for successful increment. The preceding inductions give the following relative head position at **every** integer time through exit:

| Time | Relative offset | Phase |
|---|---:|---|
| $0\le t\le m$ | $t$ | `sweep` or `run` |
| $m+1\le t\le 2m+1$ | $2m-t$ | `rewind`, with the fixed verdict for increment |
| $t=2m+2$ | $0$ | the claimed `done` anchor |

Consequently $-1\le\text{offset}\le m$ at every such time, independently of the sign of the initial coordinate. In the finish expressions, `q - d.workTapePos j` is the relative offset, so negative absolute coordinates do not cause a spurious `Int.toNat` truncation. The induction also shows every write lies in the claimed word intervals. All `done` actions are stationary self-loops, so the standalone machines continue preserving the final configuration afterward; the contracts themselves only require the bounds through exit.

These are mathematical induction arguments on the attached transition tables. They have not been submitted as Lean proofs, and the five admissions remain admissions.

## Adversarial instantiations

The following 15 cases were executed in an independent transcription of those transitions. The source is nonblank outside its two required delimiters; transfer/copy destinations have periodic arbitrary contents, including occupied delimiters. The native input is `[true,false]`, with initial input position `0` and existing output `[true,false]`. Three-tape cases also contain a nonblank inactive tape with a displaced head. Every row checks the complete final configuration, every earlier exit state, and all through-exit head bounds.

| Case | Contract | Word and initial head(s) | Exact time | Checked result |
|---|---|---|---:|---|
| T1 | Transfer | `[]`; `src=-4`, `dst=6`; two tapes | 2 | No tape writes; both relative paths are $0,-1,0$. |
| T2 | Transfer | `[false]`; `src=-4`, `dst=6`; two tapes | 4 | Source cell erased; destination receives a nonblank false bit. |
| T3 | Transfer | `[true,false,true]`; `src=3`, `dst=-2`; three tapes | 8 | Source erased and destination correct; its left/right boundary cells `some false`/`some true` are preserved. |
| C1 | Copy | `[]`; `src=-4`, `dst=6`; two tapes | 2 | No writes, despite occupied outer frames. |
| C2 | Copy | `[false]`; both coordinates `0` on distinct tapes | 4 | Equal coordinates do not alias tapes; source false retained and destination false written. |
| C3 | Copy | `[true,false,true]`; `src=3`, `dst=-2`; three tapes | 8 | Whole source and destination frame preserved; inactive tape/head unchanged. |
| E1 | Clear | `[]`; head `-5`; one tape | 2 | Both boundary cells remain blank; no writes. |
| E2 | Clear | `[false]`; head `-5`; one tape | 4 | Stored false is erased; the next outer nonblank cells survive. |
| E3 | Clear | `[true,false,true]`; head `3`; three tapes | 8 | Exactly three cells erased; other tapes and heads unchanged. |
| S1 | Success | `[false,true,true]`; head `-3`; one tape; $p=0$ | 2 | Result `[true,true,true]`; offsets $0,-1,0$; suffix never visited. |
| S2 | Success | `[true,true,false]`; head `-3`; one tape; $p=n-1=2$ | 6 | Result `[false,false,true]`; offsets $0,1,2,1,0,-1,0$. |
| S3 | Success | `[true,false,true]`; head `3`; three tapes; $p=1$ | 4 | Result `[false,true,true]`; offset 2 and both inactive tapes untouched. |
| O1 | Overflow | `[]`; head `-3`; one tape | 2 | `done false`, unchanged tapes; offsets $0,-1,0$. |
| O2 | Overflow | `[true]`; head `-3`; one tape | 4 | Result `[false]`, not a blank interval. |
| O3 | Overflow | `[true,true,true]`; head `3`; three tapes | 8 | Result `[false,false,false]`; right delimiter visited, never written. |

An empty **successful** increment is impossible for the legitimate reason `incFixed [] = none`; this does not make the success theorem vacuous on nonempty inputs. `Fin k` supplies an actual selected tape, while distinct `src,dst` supply two tapes; no additional positivity hypothesis is missing.

Additional executed coverage:

| Contract | Supplied fixture patterns reproduced in the semantic model | All words of lengths 0–6, three framed configurations |
|---|---:|---:|
| Transfer | 14 | 381 |
| Copy | 21 | 381 |
| Clear | 14 | 381 |
| Increment success | 8 | 360 |
| Increment overflow | 6 | 21 |
| **Total** | **63** | **1,524** |

The additional configurations vary negative/positive/equal coordinates, tape-index order, destination background, input positions `0`, `2`, `3`, and a nonempty output prefix. Tape comparison uses normalized finite updates over identical infinite background functions, not a sampled interval. All cases pass. The supplied wrong-time pattern, copy at $2n+1$, is rejected. This is independent executable evidence, not an execution of the attached Lean `#eval` file or a universal proof.

## Necessity and sufficiency of the hypotheses

| Premise | Assessment and adversarial check |
|---|---|
| Start phase | Necessary for the claimed first-return discipline. Starting at the stated `done` anchor violates the no-earlier-exit clause already at time 0; the advertised times are always positive. Starting halted also cannot produce the claimed live finish. |
| Left delimiter | Needed in all five contracts. For the sweep routines and empty overflow, take `w=[]` and change offset `-1` to `some true`: at time 2 the head is at offset `-2` in `rewind`, not at the exit. For success take `w=[false]` and the same mutation: time 2 is again a leftward rewind, not the claimed finish. These mutations were rejected by the checker. |
| Right delimiter | Needed for transfer/copy/clear and overflow: with `w=[]`, replacing offset 0 by `some false` prevents the claimed two-step exit; increment even selects the success verdict. Not needed on success because $p<n$ and the head never reaches $n$. The successful case `[true,true,false]` still passes after its right delimiter is made nonblank. |
| Interior source contents | Transfer/copy need the specified bits to produce the specified destination. Clear needs a contiguous nonblank interval but not its Boolean values; flipping both bits of `[false,true]` still satisfies the conclusion after dropping that part of the premise. An interior blank can cause premature termination. |
| Unvisited success suffix | Still needed for the **whole-word finish equality**, although not for control flow. For `w=[false,true]`, change the physical second bit to false. The machine leaves that cell false, whereas the asserted `v=[true,true]` requires true; the weakened-premise test fails. |
| `incFixed` result | Correctly selects the branch and output. It excludes empty success, forces all-true overflow, and supplies the width equality used by the success record update. |
| Distinct indices | Appropriate for the intended transfer between two tapes. It is not logically minimal for the displayed formulas: self-copy changes nothing, and self-transfer clears the word because the final source branch wins. Both literal alias behaviors were tested. A nonempty self-transfer cannot satisfy the prose intention that its source is erased while its destination retains `w`; retaining `hne` prevents that interpretation. |
| Destination contents/delimiters | No premise needed. The transition tables branch only on the source read. Destination word cells are overwritten; destination delimiters are visited without writes. |

The common hypotheses are jointly sufficient by the trace inductions. Their deliberate excess does not burden this consumer: word windows and counter buffers can be delimited once for their relevant lifetime. Reinstalling and restoring the far counter delimiter on **every** increment would introduce an avoidable width-dependent cost and is not justified by the carry ledger.

## Canonical specialization

For each row instantiate `d := Cfg.ofWords …` and use the corresponding canonical word at the selected index. All heads become zero; `hstate` and `hw` follow from the definitions. The framed final record is extensionally equal to the canonical `Cfg.ofWords` finish:

| Canonical theorem | Witness time | Final word family |
|---|---:|---|
| `transferTM_run` | $2n+2\le3n+3$ | Source updated to `[]`, destination updated to its original source word; reinstate the canonical blank-destination premise. |
| `copyTM_run` | $2n+2\le3n+3$ | Destination updated to the source word; reinstate the canonical blank-destination premise. |
| `clearTM_run` | $2n+2$ | Selected word updated to `[]`. |
| `incrementTM_run_succ` | $2p+2\le2n+2$ | Selected word updated to `v`, using `v.length = n`. |
| `incrementTM_run_overflow` | $2n+2$ | Selected word updated to `List.replicate n false`. |

For transfer/copy, the old destination being globally blank ensures no old suffix survives beyond the new word. For clear, the old source was already blank outside its word. For both increment branches, equal width makes the unchanged exterior agree with the new global buffer. The framed no-earlier-exit conjunct is precisely the canonical cut, with conjunctions reordered. Thus all five canonical rows follow with their existing statements unchanged; the proof dependency order may need rearrangement because the framed rows currently appear later in the file.

## Fitness for the zone consumer

**Boundary preparation is feasible with two tapes.** Each saved boundary value lies in `Option Bool`, so saving two delimiters requires only nine possible symbol pairs in finite control, independently of the zone level and word length. The controller must locate those cells, save their values, install blanks, return to the word's starting head, invoke the routine, and restore the saved values afterward. The machines never write the delimiter cells; the contracts preserve them at exit and return the heads exactly, including for empty words. Coordinates are recovered by the navigation procedure; no unbounded coordinate is stored in finite control. Protect the other scratch intervals, including the unary level word, as part of the outer frame.

The attached regression was reconstructed: a bare transfer from data head 6 consumes ten physical bits, exits at 22, and erases cell 14. Saving cells 5 and 14, installing blanks, and transferring the intended eight-bit donor instead exits at 18; restoring the saved cells preserves both cells 14 and 15. This validates the purpose of the stronger source-window premise without claiming to implement the complete shift.

**Left-side orientation needs explicit bookkeeping.** `zoneStage_leftWindow` reads away from home in decreasing coordinates, whereas these routines sweep toward increasing coordinates. Starting at the leftmost occupied physical cell therefore supplies `reverse (zoneStageWord false …)` to the framed contract. The controller must account for that reversal when staging and placing words. A reflected-machine contract is not required if both calls use the appropriate ascending physical representation; the existing left-window lemma alone is not a reflected-run theorem.

**Spatial bounds fit.** `zoneStage_window_bounds` covers both oriented windows and their delimiter cells inside the zone row's permitted data-head interval. The framed trajectory clause therefore supplies the routine portion of that obligation. The attached `MultiTapeTM.spaceUsedByTape_le_card_Icc` yields $n+2$ visited cells per touched tape, or $p+2$ on success. Boundary preparation/restoration and navigation paths still require their own bounds.

**Carry-sensitive time supplies the geometric ledger.** Use an $i$-bit zero counter and stop on its first overflow after $2^i$ increments. For increment number $r<2^i$, the old word has exactly $v_2(r)$ initial true bits; at $r=2^i$, the overflow cost is also $2v_2(r)+2=2i+2$. Counting multiples of each power of two gives

\[
\begin{aligned}
\sum_{r=1}^{2^i} v_2(r)
&=\sum_{j=1}^{i}\left\lfloor\frac{2^i}{2^j}\right\rfloor
=\sum_{j=1}^{i}2^{i-j}=2^i-1,\\
\sum_{r=1}^{2^i}(1+v_2(r))
&=2^{i+1}-1<2^{i+1},\\
\sum_{r=1}^{2^i}(2v_2(r)+2)
&=2^{i+2}-2.
\end{aligned}
\]

This includes $i=0$: the empty counter overflows in two steps. A constant amount of controller work and a data-head movement per increment preserve the geometric bound. The counter delimiters should remain installed across the run; initialization, later cleanup, and restoration are charged separately. Increment-to-overflow can implement the required distance countdown without a new decrement contract. The consumer must still prove that its actual counter schedule, rather than an arbitrary sequence of counter resets, has this cost.

**Remaining consumer obligations, not missing catalog statements:** uniform finite control independent of `i`; window location; source-boundary preparation/restoration; left-side word orientation; the guarded identity branch; exact unary-scratch restoration; composition and first-return transport; and an explicit transition to genuine halt. The five contracts close the stated local routine gap and do not themselves discharge those obligations.

## Attestations and fill handoff

- Confirmed textually: the attached Catalog has exactly the five audited admissions. The audited addition contains no new machine or proof-helper implementation and no copied proof bodies. This is a scoped statement audit, not a reopening of the historical Catalog duplication census.
- Checked the attached execution harness: its count is $14+21+14+14=63$, with increment split into 8 success and 6 overflow inputs. Its actual tape comparison samples cells $-10,\ldots,19$, and its initial input position/output remain canonical. The stronger independent tests above exercise noncanonical preserved fields and complete symbolic tapes. Neither finite test family proves the general statements.
- Not independently replayed: Lean elaboration, downstream compilation, lint, the original kernel boundary proof, and historical byte identity of the machine definitions. The source-level audit and semantic reconstruction do not substitute for those checks.
- During fill, generalize the existing traces in their shared home and derive the canonical rows by specialization. Preserve theorem statements; avoid parallel private copies of the same traces. Useful kernel sanity checks are the 15 concrete cases above, width preservation, the `incFixed` branch characterizations, and explicit canonical-specialization proofs. They are validation suggestions, not additional statement-gate blockers.

## Notation

- $n$: length of `w`.
- $p$: length of the initial true prefix of `w`.
- $m$: forward-pass length, equal to $n$ except on successful increment, where it is $p$.
- `rest`: the suffix following the first false bit in a successful increment.
- $t$: elapsed transitions; $r$: return-pass count or increment number, as specified locally; $j$: summation index in the carry calculation.
- $v_2(r)$: exponent of two dividing the positive integer $r$.
- Intervals describe integer tape coordinates or relative offsets; word intervals are half-open, trajectory intervals inclusive. Other identifiers retain their meanings in the Lean statements.
