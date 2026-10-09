External audit — §12 routine layer, epoch F2

**Verdict: PASS — 0 blockers, 0 majors, 1 minor.** The F2 fill gate closes under the supplied rule. The minor concerns a startup proof sketch; it does not weaken a statement or invalidate a space ledger. Explicit “no findings” rows below record the other checks.

Audited packet: `routine-f2-bundle.md`, supplied for commit `41a06e08`, branch `complexity/arora-barak-ch3-4`. Audit date: 2026-10-09. Independently computed bundle SHA-256:

```text
72861b805fcbe8f368905149e21d39aa827a6b3c052809582709438d874a8004
```

I extracted all 24 attachments, read the new declaration bodies/signatures with comments suppressed before comparing their descriptions and the agents’ role tables, and inspected the proof routes where needed to check the binding ledgers. This is a surface and contract-fidelity audit, not a new kernel replay. Locations below are line numbers in the attached final `Build/Catalog.lean`, unless another file is named.

**Findings table**

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| F2-1 | minor | `Catalog.lean:7025` · sketch of `f2_loopHost_start` | The sentence “The no-anchor prefix includes time zero” needs a positive-time qualification. Zero-time startup is permitted and actually used. | The premise is `∀ u < t, … ≠ some anchor`; at `t = 0` it is vacuous. Take a split body at its genuine empty-candidate anchor: `f2_splitBody_start` supplies `hend` with `s = []`, `t = 0`, while its initial state **is** the anchor. The formal proof correctly executes the stop and release in two steps, using `f2_loopHost_anchor_return` with `release = false`; no erroneous positive-startup premise enters either export. | Qualify the sentence with “when the startup time is positive”; add that a zero-time startup already occupies the anchor and takes the two administrative steps directly. Change prose only. |
| F2-2 | note | All 45 `a2_*` declarations; forwarding and loop exports | **No findings** in their statements, definitions, or use of the inherited ledgers. | Individual restatements and calculations below establish coefficient-one payload containment, the fixed loop interval, correct seams, both empty-input clamps, and halted tails. | None. |
| F2-3 | note | F2A’s 306 private declarations and 17 filled rows | **No findings** beyond F2-1. | All declarations are covered by the family inventory below; the witness machines and principal contracts/space engines are restated individually. R5, R8, split-search reuse, and W3 are respected. | Apply only F2-1’s prose correction. |
| F2-4 | note | `f2_space_of_time` and its six call sites | **No findings**: this is an all-time visited-image argument, used only with sufficiently sharp time bounds. | Source lines 3951, 4003, 4028, 4076, 4203, 4595 are the complete call-site inventory. Counter width, unary-bank reuse, split seams, and conditional source banks use separate invariants. | None. |
| F2-5 | note | `a2_mapTM`, finite-sum copies, loop copies, deduplication | **No findings** in the declared design anomalies. Literal historical-copy verification has the evidence limits stated below. | The true mode is the exported map witness; false-mode stationarity is used to identify setup’s first seam. The two finite-sum copies and the supplied Wrappers copies match. The loop’s administrative allowance is local to each canonical call. | Keep the recorded per-theme refactor and the Wrappers trajectory projection queued; no shared-file change is needed to accept these fills. |
| F2-6 | note | Both patch series; all frozen declarations and docstrings | **No findings**: the supplied source and patches support the freeze and inventory attestations. | Exact patch reversal/replay, direct declaration comparisons, preserved old docstrings, and the counts below. A2 removes exactly two `sorry` lines. | None. |
| F2-7 | note | Integration/axiom/style evidence; excluded environment shim | **No findings** in the integrated source dependency surface. Execution and archive claims remain appropriately attributed. | No shim reference, foreign hook, new axiom, unsafe declaration, native proof evaluation, or admission appears in integrated Catalog code. Final supplied logs have zero errors/sorry warnings, both exit codes zero, and 20 standard-triple axiom records. Original archives, toolchain tree, and fresh artifact metadata were not supplied. | None; retain the independent maintainer replay evidence. |

**Integrity and evidence**

| Check | Independently established from this packet |
|---|---|
| Reconstructed pre-F2A source | 1,851 lines; 72 source declarations; 19 `sorry` bodies; Git blob `b239b4089759c6ce10ff71bec7ba0682e7dfab42`. |
| Reconstructed post-F2A/pre-A2 source | 9,404 lines; 378 declarations; exactly the loop and map `sorry` bodies; blob `f4b449b2769d64c5e512c51e55f3197fcf5e5bbf`. |
| Supplied final source | 10,876 lines; 423 source declarations: 39 public, 384 private; no code-level `sorry`; blob `798fb8ac16fcddeb2a5e7456e44238ad5febcade`. |
| Patch reconstruction | Reversed A2’s patches in reverse order, then F2A; applied all three forward again. The result is byte-identical to the supplied final Catalog. Blob identities agree with the patch metadata. |
| F2A freeze | All 72 old declaration heads remain verbatim and in order. All 55 nonfilled old declaration bodies remain verbatim, including the two frontier admissions. Existing docstrings, imports, options, and namespace transitions are preserved. The 54 raw removed diff lines do not imply 54 substantive removals. |
| A2 freeze | All 378 old heads remain verbatim and in order; all 376 nonfilled bodies are unchanged. Exactly two removed lines, each `  sorry`. Existing docstrings are unchanged. |
| Added inventory | Exactly 306 `f2_*` and 45 `a2_*` source declarations, all private. Independent enumeration matches each report’s complete ordered inventory. Compiler-generated constructors, recursors, and instances are not separately counted as source declarations. |
| Path scope | Every patch touches only `TCSlib/Complexity/TuringMachine/Build/Catalog.lean`. |
| Interim evidence | The F2A sweep contains zero `error:` diagnostics and two sorry warnings. Its 20 axiom records have `sorryAx` on precisely the two frontier rows; the other 18 are clean, including F1 W2. |
| Final evidence | The A2 sweep contains zero errors and zero sorry warnings, `catalog_exit=0`, `facade_exit=0`. All 20 final axiom records are exactly `[propext, Classical.choice, Quot.sound]`. |
| Style | The supplied final log reports 0 FAIL and three file-size WARNs: Catalog, Loop, Primitives. Catalog’s recorded split justification is present in the packet’s resolutions/design. |

These checks establish consistency of the supplied files, not independent execution of Lean or authentication of the repository commit. I did not rerun Lean, the toolchain bootstrap, or a repository build. The delivery ZIPs, `SHA256SUMS`, git bundles, full repository trees, and fresh `.olean` timestamps are absent; the 14/14 and 20/20 checksums, bundle validity, integration commits, full-tree identity, and freshness remain maintainer attestations. Embed/Seam’s earlier closure is inherited from the attached F1 resolutions; these patches do not change them.

The module header and old public docstrings still use historical skeleton/fill-pending wording. That text is frozen and unchanged; it is not a newly introduced F2 defect or evidence of a remaining admission.

**The loop ledger**

Fix input `x`, set `n = x.length`, `ℓ = (Nat.bits (R n)).length`, and use the actual witness `E = f2_loopHost body F anchor false`. The proof establishes, for every time and every physical work tape, the single bound

\[
-B\le\text{head}\le B,\qquad B=S(n)+4\ell+8.
\]

1. `hstart` selects an actual startup endpoint at most `T n`. `hround` selects an actual positive round endpoint at most `T n`; acceptance is cut back to the **first actual halt**. Therefore every source prefix used by `a2_call_prefix` is within the supplied `hstartSpace`/`hroundSpace` budget. No assertion about an unbounded uninterrupted source execution is substituted.
2. All body heads begin each call at zero. `a2_source_radius` proves that the integer interval between zero and a head’s position is contained in that tape’s visited set. Its cardinality is at most that tape’s space, which is at most total source space `S n`. Thus each body head lies in `[-S n,S n]`. `a2_call_run` transfers the actual prefix; `a2_call_heads` projects body, flag, counter, fuel, and capture positions separately.
3. `a2_loop_prepare` applies `hFspace` to every fuel prefix, retains the actual halted fuel configuration with heads in `[-S n,S n]`, and threads that same configuration through subsequent calls. Fuel-bank coordinates are never translated by a round index.
4. Output-length monotonicity and the one-bit-per-step rule give `ℓ ≤ T n`. Preparation’s capture prefix has radius at most `S n + ℓ`; installation adds at most `3ℓ+4` steps, giving `S n+4ℓ+4`. The input rewind preserves every work head. `f2_loopDebit_iterate_length` preserves exactly `ℓ` cells through successful debit and underflow.
5. Startup and returning rounds end with output `[]`, so every preceding output is empty. An accepting round ends with `[true]`, so every output prefix has length at most one. At a new call, counter and capture heads start at zero; rejecting calls do not leave an accumulating output log. Acceptance requires no subsequent round.
6. Startup adds two administrative steps. An accepting round is bounded within radius `S n+1+5`; a rejecting round within `S n+2ℓ+5`, conservatively stated as `S n+2ℓ+6`. Each lies in the same `B`. `a2_segments` passes this **unchanged** `B` to the remaining chain and freezes every halted suffix. It never recurs with `B` plus another allowance.

Consequently, for every horizon `t`,

\[
\begin{aligned}
\operatorname{space}_E(x,t)
&\le E.k(2B+1)\\
&=E.k\bigl(2S(n)+8\ell+17\bigr)\\
&\le19E.k\bigl(S(n)+T(n)+1\bigr)\\
&\le(c_0+19E.k)\bigl(S(n)+T(n)+1\bigr).
\end{aligned}
\]

Here `c₀` is the coefficient supplied by `f2_loopHost_contracts` (its witness is 10). The exported coefficient is exactly `c₀ + 19*E.k`, multiplying `S n + T n + 1` **jointly**. The time argument independently combines startup and `R n+1` candidate segments:

\[
c_0(T(n)+1)+(R(n)+1)c_0(T(n)+1)
=c_0(T(n)+1)(R(n)+2).
\]

Enlarging that coefficient preserves the frozen time clause. `R n` contributes to space only through the fuel width, which is absorbed by `T n`; it never multiplies a spatial interval. The existence/termination argument is not replaced by the space-only segment lemma: `a2_loop_halted_run` supplies the correct Boolean output and finite time.

**The forwarding ledger**

The witness is `a2_mapTM Mg true`, with exactly two administrative tapes plus `Mg.k` payload tapes. The constructor’s payload action contains the original `a.workTapes` and `a.output`; there is no payload-output capture action. The refuted `pairMapTM` is absent from the new proof and its controller dependencies.

For valid `pairDecode x = some (a,b)`, `a2_map_launch` gives the first payload entry `u ≤ 5(n+1)`, with source configuration precisely `Mg.tm.initCfg b` and physical output `pairEncode a []`. For source elapsed time `v`, `a2_mapVirtual_run` identifies the complete host configuration at `u+v`: payload tapes and heads equal the source’s, output is `pairEncode a [] ++ source.output`, first-buffer head is `|a|`, and second-buffer head is `source.inputPos - 1`.

The virtual-step proof invokes `virtualMove_correct` under `VirtualTag`, identifies the buffered symbol with `c.inputSymbol`, and preserves that predicate in its successor. In particular, its head equation is the source’s **clamped** input move expressed in buffer coordinates. There is no `b ≠ []` premise. On empty `b`, buffer position `0` represents the source’s right boundary and `-1` its left boundary: an outward move stays at that boundary, and an inward move reaches the other boundary. The source’s halting action is executed before the mapped control becomes `none`; later configurations remain fixed.

For a host horizon `t`, the proof of each payload visited-set inclusion sends a visited time `v` to source time zero if `v ≤ u`, otherwise to `v-u`. Both indices are at most `t`. Hence, tape by tape,

\[
\text{host payload visited set at }t
\subseteq\text{source visited set on }b\text{ at }t.
\]

`a2_map_space` sums those source cardinalities once. It does not multiply `Sg` by the payload tape count. For the two administrative tapes put `D = 5(n+1)`: setup’s unit-step bound lies in `[-D,D]`; afterwards their positions are `|a|` and an element of `[-1,|b|]`, respectively. Thus

\[
\begin{aligned}
\operatorname{space}_{\rm host}(x,t)
&\le Sg(|b|)+2(2D+1)\\
&=Sg(|b|)+20(n+1)+2\\
&\le Sg(n)+22(n+1),\\
\operatorname{time}_{\rm host}(x)
&\le u+Tg(|b|)\\
&\le5(n+1)+Tg(n)\\
&\le22(n+1+Tg(n)).
\end{aligned}
\]

The length inequalities follow from the exact pair encoding; the budget comparisons use precisely `hSg` and `hTg`. For malformed input, `a2_map_reject` gives an empty-output halt by `5(n+1)` and equality of the true/false-mode trajectories at **all** times. Payload heads stay at zero; the source bank’s origin cells are charged using `hgs x t`. The same administrative interval includes the halted tail. The single exported constant is 22.

The false mode is an auxiliary machine with an absorbing **live** payload state, not a claimed implementation of the exported total function. It permits choosing the first entry without trusting a padded endpoint. Prefix agreement transfers only times through that entry on valid inputs; all later behavior comes from true-mode lockstep. No false-mode liveness or freezing property is used as a false claim about the exported payload execution.

**The F2A routes and `f2_space_of_time` discipline**

| Filled row | Verified witness/route and actual space accounting |
|---|---|
| `id` | `f2_idTM`, no work tapes; time `n+1`, space 0; exported constant 1. |
| `const` | `f2_constTM w`, finite emission chain, no work tapes; fixed time `w.length+1` fits `(w.length+1)*(n+1)`. |
| `prepend` | `f2_catalogPrefixTM w`, finite prefix followed by input scan; time `w.length+n+1`, space 0. |
| `pairEncodeFixed` | Prepend the fixed doubled first component and `01`; same zero-tape witness family. |
| `pairValid` | `f2_pairValidTM`, pending/alignment bit in finite control; time `n+1`, space 0. |
| `pairDup` | `f2_pairDupTM`, doubled input pass, input rewind, suffix copy; time `4(n+1)`, space 0. |
| `incFixed` | `f2_incFixedTM`, silent overflow test followed by carry/output scan; time `3(n+1)`, space 0, including width zero. |
| `pairFst` | `f2_pairExtractTM true false`; one prefix buffer, verified halting time `5(n+1)` gives all-time space at most `5(n+1)+1 ≤ 6(n+1)`. |
| `pairSnd` | Same parser/buffer with flags `false,true`; malformed and valid runs satisfy the same sharp halting bound and constant 6. |
| `pairConcat` | Flags `true,true`; same sharp halting bound, same constant 6. |
| `polyUnary` | Exponent zero takes the constant family. For `e=d+1`, the fixed `d+1` unary banks satisfy a phase invariant; space `5(d+1)(n+1)`, independently of output length. Exported constant `C+10(d+1)+4` covers both clauses. |
| `polyBits` | **First** split `C=0`, then `e=0`, using constant output. Only the positive case buffers unary output and runs the direct counter. Its actual time is `K(n+1)^e`, so all-time space fits the value bound since `(n+1)^e ≤ C(n+1)^e`. The public time exponent remains `e+1`. |
| `lengthBits` | `f2_counterTM`; potential/carry argument gives time `5(n+1)`, separate head invariant gives space `5(Nat.size n+1)`. No opaque `timeConstructible_id` witness is used. |
| `pairLenCheck` | First-component extraction, sharp unary generator, then `f2_pairCountTM`. Actual time `K((n+1)^e+n+1)` already fits the space envelope. The retained linear term covers zero coefficient/exponent and malformed parsing. |
| `stripLast` | `f2_strip_linear` assembles the suffix-marker guard, raw stripping of the original input, and empty-output failure branch. It proves `a(n+1)` **before** the quadratic time weakening, yielding space at most `M.k(a(n+1)+1)`. |
| `splitSolve` | Explicit prepare/count/restore/emit body, then `f2_exists_loopFind_space`. Fixed segment radius, not total loop time, gives degree `e+1` space; candidate count produces degree `e+2` time only. |
| `cond` | `f2_timedCondTM`; disjoint source visited-set containment yields exactly decider space plus selected branch space, idle origins, and two capture cells. Constant `7+M₁.k+M₂.k` preserves coefficients one on both supplied budgets. |

For `f2_space_of_time`, a genuine `ComputesInTime x y T` hypothesis supplies a halted configuration at time `T`. A visited time at most `T` maps to itself; a later visited time maps to `T`, by halt absorption. Therefore, for each tape and every horizon, its visited set is contained in the image of the `T+1` source times `0,…,T`. Cardinality and summation give `M.k*(T+1)`. This uses the **entire finite trajectory**, not a bound on the final head alone.

| Call site | Time premise used before weakening | Why it fits |
|---|---|---|
| 3951, positive `polyBits` | `K(n+1)^e` | Positive `C,e` absorb this into a constant times `C(n+1)^e+1`. |
| 4003, `pairFst` | `5(n+1)` | One tape; `5(n+1)+1 ≤ 6(n+1)`. |
| 4028, `pairSnd` | `5(n+1)` | Same. |
| 4076, `pairConcat` | `5(n+1)` | Same. |
| 4203, `pairLenCheck` | `K((n+1)^e+n+1)` | Exactly the desired space envelope up to a fixed factor. |
| 4595, `stripLast` | `a(n+1)` | Linear bound is retained locally before public quadratic weakening. |

The direct counter’s separate proof bounds each increment from a returned origin using its carry length and the final binary width; it includes emission and halt. Unary generation uses a preserved state-dependent head invariant after setup. Split search uses `f2_segment_heads`/`f2_seamed_space`, with a terminal bound and early-halt case. W3 uses `f2_cond_ledger`/`f2_cond_space`. None substitutes the full elapsed time for a sharper required space bound.

For W3, the precise intermediate statement is

\[
\operatorname{space}_{\rm host}(x,t)
\le\operatorname{space}_{D}(x,T_0(n))
+\operatorname{space}_{\rm branch}(x,t)+2.
\]

`f2_branch_space` identifies branch space as the selected source’s space plus exactly the other machine’s tape count. At every host time `u`, `f2_cond_ledger` supplies a decider time at most its budget, a branch time at most `u`, and capture coordinate in `{0,1}`. Thus taking unions does not enlarge either source coefficient. Native input rewind has stationary work heads; no monotonicity hypothesis is added.

For split search, `f2_loopHost_contracts` supplies seam heads within radius `T(n)`, segment/startup duration at most `c₀(T(n)+1)`, and a halted terminal within radius `T(n)+c₀(T(n)+1)`. `f2_segment_heads` preserves that radius through any finite number of segments, including early acceptance. Substituting `T(n)=(A+a)(n+1)^(e+1)` gives the claimed spatial exponent, whereas `R(n)=n` supplies the extra time factor. Accepted payload capture/replay is included in the individual segment duration; the completed fuel bank remains in the same interval. A synthetic exhaustion terminal in the already-accepting last-candidate case is harmless: that case halts in its accepting segment and never follows an edge to the synthetic terminal.

**A2: all 45 individual blind restatements**

These restatements were derived from the formal surface with comments suppressed, then compared with the descriptions. “Radius B” means every physical work head is in the integer interval `[-B,B]`. A configuration predicate alone is not a trajectory claim; the rows distinguish them. Unless stated otherwise, the map setup lemmas concern `forward = false`.

| # | Declaration · line | Restatement from the body/signature; comparison |
|---|---|---|
| A2-01 | `a2_MapState` · 4624 | Finite-control alternatives are parsing with an optional pending bit; copying the suffix; rewinding the second and first buffers; emitting the first component, its repeated bit, and the separator; and running a payload state with a Boolean boundary tag. The parameter stores a payload **state**, not an arbitrary input or output word. Derived equality has the corresponding equality assumption on the payload state. Matches. |
| A2-02 | `a2_mapStateFintype` · 4630 | A finite payload-state type gives a finite type for the preceding control alternatives. No uniform bound on the number of payload states is asserted. Matches. |
| A2-03 | `a2_mapAct` · 4634 | Construct an action on `1+(1+M.k)` tapes with the supplied native-input motion, independent first/second tape actions, supplied output and next state, and no write or movement on any payload tape. Matches. |
| A2-04 | `a2_mapTM` · 4644 | Start in empty-pending parse state. Equal bit pairs append one bit to buffer A; `01` starts copying the unrestricted suffix to B; `10`, end without a delimiter, or an incomplete pair halts silently. Rewind B then A; emit doubled A followed by `01`. At payload entry, true mode forwards the payload’s work actions and output while B simulates its bounded input; false mode repeats an action that preserves the entire configuration. Exactly two extra work tapes; no payload-output buffer. Matches the commissioned witness in true mode. |
| A2-05 | `a2_mapCfg` · 4686 | Explicit administrative configuration with supplied control, native input position, output, A/B buffer words and heads; every payload tape is blank and every payload head is zero. It does not itself assert reachability or well-formed control. Matches. |
| A2-06 | `a2_mapVirtual` · 4697 | Embed an arbitrary source configuration on virtual input `y`: map its live state to `run q tag`, preserve its payload bank, hold native input at supplied `p`, store A and `y` on the two buffers, place their heads at `A.length` and `source.inputPos−1`, and prepend the supplied output prefix. A halted source maps to a halted host. The definition alone imposes no validity on `tag`; lockstep supplies that premise. Matches. |
| A2-07 | `a2_mapCfg_read` · 4707 | At native position `i+1`, for `i ≤ x.length`, the administrative configuration reads `x[i]?`, including `none` at the right blank. Matches. |
| A2-08 | `a2_map_move` · 4714 | Applying an administrative action with no writes updates the native position by bounded input motion, adds each administrative displacement to its head, appends the optional emitted bit, and sets the supplied state. All tape contents and payload heads remain as specified. Matches. |
| A2-09 | `a2_map_first` · 4736 | With unread input beginning in bit `b`, one parse step records `b`, advances native input once, and leaves buffers and empty output intact. Matches. |
| A2-10 | `a2_map_block` · 4758 | Two parse steps on `bc` either append `b` when `b=c`, halt silently on `10`, or enter suffix-copy on `01` with A’s head at `A.length−1`. The last subtraction is an integer, so empty A gives head `−1`. Matches. |
| A2-11 | `a2_map_suffix` · 4795 | From a partially filled B at the start of remaining suffix `rest`, `rest.length+1` steps append that suffix, finish at the native right blank, enter B rewind, and put B’s head at its final length minus one. Output stays empty. Matches. |
| A2-12 | `a2_map_backB` · 4849 | Starting in B rewind at integer head `j−1`, with `j ≤ B.length`, exactly `j+1` steps reach A rewind with B’s head zero. Native input, tape contents, A head and empty output are preserved. Includes `j=0`. Matches. |
| A2-13 | `a2_map_backA` · 4884 | The analogous `j+1`-step rewind of A, with `j ≤ A.length`, reaches A emission with both administrative heads zero. Includes empty A. Matches. |
| A2-14 | `a2_map_emit` · 4923 | If A is `pre ++ rest` and its head is `pre.length`, exactly `2*rest.length+2` steps append doubled `rest` and `01` to the existing output, then enter the live initial payload state with tag true, A head at its full length, and B head zero. Matches. |
| A2-15 | `a2_map_finish` · 4976 | From suffix-copy with A already decoded and B initially empty, copying suffix `b`, both rewinds, and prefix emission take exactly `3*A.length+2*b.length+5` steps. The endpoint is the virtual embedding of the genuine payload initialization on `b`, with output `pairEncode A []`. Matches. |
| A2-16 | `a2_map_parse` · 5004 | From parse state with stored A and unread `rest`, some time at most `3*rest.length+3*A.length+5` either reaches the initialized virtual payload for `pairDecode rest = some (d,b)`, with first component `A++d`, or halts with empty output when decoding fails. Covers arbitrary stored A; no valid-encoding premise is hidden. Matches. |
| A2-17 | `a2_map_setup` · 5075 | From genuine initialization, false mode reaches the exact virtual payload seam for valid input, or halts silently for malformed input, within `5*(x.length+1)`. This is a bounded endpoint result, not a statement that false mode eventually computes `g`. Matches. |
| A2-18 | `a2_mapVirtual_step` · 5103 | For any source configuration and valid boundary tag, one true-mode host step is the virtual embedding of one source step, for a new valid tag. Native input and both buffer contents are fixed; source actions and output are preserved, including a halting action. Includes already halted configurations and empty virtual input. Matches. |
| A2-19 | `a2_mapVirtual_run` · 5152 | Iterate the preceding equality for any natural number of steps, retaining a valid endpoint tag and full configuration equality. No source halting or input-length positivity premise is required. Matches. |
| A2-20 | `a2_mapEntered` · 5169 | A configuration is “entered” exactly when its state is `some (run q tag)` for some payload state/tag. It asserts neither reachability nor a buffer invariant. That intentionally weak predicate suffices for the mode comparison. Matches. |
| A2-21 | `a2_mapSetup_stationary` · 5174 | Every false-mode configuration satisfying `a2_mapEntered` is fixed by every subsequent run, in every field. This is live stationarity, not halting. Matches. |
| A2-22 | `a2_mapSetup_step` · 5189 | On any configuration not satisfying `a2_mapEntered`, true and false mode take the same step; this includes halted configurations. Matches. |
| A2-23 | `a2_mapSetup_run` · 5202 | If the initialized false run has not entered at any time strictly before `t`, initialized true and false runs agree at time `t`. The endpoint may itself be the entry. Matches. |
| A2-24 | `a2_mapSetup_head_step` · 5214 | One false-mode step preserves each payload work-head position for an arbitrary configuration, including entered and halted configurations. Matches. |
| A2-25 | `a2_mapSetup_heads` · 5253 | Every payload work head remains zero at every time in the genuinely initialized false run. This is the trajectory fact used for setup’s contribution to payload visited sets. Matches. |
| A2-26 | `a2_map_launch` · 5264 | Valid input has a true-mode seam time `u ≤ 5*(x.length+1)` with exactly the initialized virtual payload and encoded first-component prefix; true and false configurations agree at every time through `u`. The construction selects first entry, although the statement need not expose minimality. Matches. |
| A2-27 | `a2_map_reject` · 5298 | Malformed input has a true-mode silent halt within the same setup bound, and the initialized true/false runs agree at **every** time. False-mode entry cannot occur: its stationarity would contradict the established halt. Matches. |
| A2-28 | `a2_mapSumEquiv` · 5331 | Bijection from the disjoint union of the first `a` and next `b` finite indices to `Fin (a+b)`, with inverse split at index `a`. Includes empty banks. Matches. |
| A2-29 | `a2_map_sum` · 5354 | Summing a natural-valued function over the concatenated finite bank equals the sum over its two injected banks, each once. No inequality or multiplicative loss occurs. Matches. |
| A2-30 | `a2_map_space` · 5365 | At horizon `t`, assume both administrative heads stay in `[-D,D]` through `t`; every payload head occurrence corresponds to a source occurrence on the same tape at a time at most `t`; and source space through `t` is at most `S`. Then host space is at most `S+2*(2*D+1)`. This is a conditional containment lemma, not a claim that arbitrary host configurations already simulate the source. Matches. |
| A2-31 | `a2_source_radius` · 10243 | For a source starting with all work heads zero, total visited space at time `t` at most `B` forces each endpoint head into `[-B,B]`. The argument uses the traversed interval, not the final configuration alone; quantifying its application over prefix times gives the trajectory bound. Matches. |
| A2-32 | `a2_heads` · 10278 | Predicate that every physical work head of one configuration lies in `[-B,B]`. No assertion about prior visits, tape contents, control, input head or output. Matches. |
| A2-33 | `a2_heads_mono` · 10283 | A configuration satisfying radius `A` also satisfies radius `B` when `A≤B`. Matches. |
| A2-34 | `a2_heads_steps` · 10292 | From radius `A`, any run of at most `B` steps ends in radius `A+B`, because each work head moves by at most one per step. Matches. |
| A2-35 | `a2_heads_join` · 10301 | Two consecutive inclusive prefixes, both bounded by the **same** radius `B`, concatenate to a prefix bounded by `B`; the radii are not added. Matches. |
| A2-36 | `a2_heads_halted` · 10313 | If a run halts at time `a` and every configuration through `a` has radius `B`, all subsequent times have radius `B` as well. Matches. |
| A2-37 | `a2_call_heads` · 10327 | A loop-call embedding has radius `B` when its body and retained fuel configurations do and the body’s output length is at most `B`. Body/fuel heads are copied, the counter and flag heads are zero, and the capture head equals body-output length. The counter **word length** is not a head displacement at this seam. Matches. |
| A2-38 | `a2_fuel_heads` · 10354 | The captured-fuel configuration has radius `B` when the fuel’s heads and output length are bounded by `B`; the other source bank and administrative heads are zero. Matches. |
| A2-39 | `a2_call_run` · 10376 | A live body call follows the exact captured source run through time `t`, provided strict earlier times are live and avoid the anchor except for the initially released occurrence. The release bit persists only at `t=0`; the stop flag becomes true exactly when the endpoint source is halted. Applies to either loop mode and either startup flag. Matches. |
| A2-40 | `a2_call_prefix` · 10399 | For decision mode, the preceding guarded source call, zero starting body heads, source-space bound at every prefix, retained fuel radius `B`, and endpoint output length at most `B` imply radius `B` at every host call prefix through `t`. Monotonic output length bounds all capture prefixes. Matches. |
| A2-41 | `a2_loop_prepare` · 10424 | Given a fuel machine computing `bits(R(n))` within `T(n)` and all-time fuel space `S(n)`, obtain an actual halted fuel configuration and host-ready time at most `5*T(n)+7`; retained fuel heads have radius `S(n)`, and the entire preparation prefix has radius `S(n)+4*bits(R(n)).length+4`. Matches. |
| A2-42 | `a2_loop_start_prefix` · 10508 | Given a startup that first reaches the canonical anchor at time `t`, source space at every prefix at most `B`, and retained fuel radius `B`, every host prefix through `t+2` from ready has radius `B+2`. Time zero startup is permitted. Matches; this corroborates the edge case behind F2-1 in the older F2A helper’s sketch. |
| A2-43 | `a2_loop_round` · 10537 | For a positive guarded source round ending either with halt/output `[true]` or an exact canonical next-state return, with source prefix space and fuel radius at most `B`, the host either reaches a halted endpoint or successfully debits the counter and reaches the exact next canonical call. In either case its whole chosen prefix has radius `B+2*word.length+6`. This lemma exposes **no duration bound**; time is obtained separately from the loop phase contracts. Matches. |
| A2-44 | `a2_segments` · 10634 | For a positive finite number `N` of configurations, suppose each indexed segment stays within one fixed radius `B` and ends either halted or at the next index strictly inside `N`. Every time in the run from configuration zero then has radius `B`. The last segment must halt, zero-duration transitions are allowed, and finite index progress supplies the induction. It proves neither a numerical time bound nor an output value. Matches. |
| A2-45 | `a2_loop_halted_run` · 10665 | A chain of `N` candidate segments, each taking at most `B` steps and either halting with `[true]` when its Boolean acceptance flag is true or reaching the next configuration otherwise, followed by a halted `[false]` terminal, halts from the start within `N*B` with the Boolean `any` of the first `N` flags. Includes `N=0`. Matches the stated chain/time role. |


**F2A: complete family coverage**

The following 30 disjoint families contain exactly 306 new private source declarations. Each inventory entry gives its final Catalog line. Supporting configuration, arithmetic, and phase lemmas are restated jointly here; the machines and contracts that carry the conclusions are separated in the next table. Descriptions were compared after the blind reading. All match, subject to F2-1.

**F2A-01: Zero-tape identity/constants/prefix (8 declarations).** Zero-work-tape identity scans and forwards each bit; a fixed-word machine emits a word held in finite control; prefixing emits that word and then copies the native input. The explicit configuration and prefix/copy lemmas identify every finite emission/copy stage and the final halt.

Inventory: `f2_idTM` (1311), `f2_idTM_run` (1323), `f2_constTM` (1358), `f2_catalogPrefixTM` (1365), `f2_catalogPrefixCfg` (1378), `f2_catalogPrefixTM_emit` (1384), `f2_catalogPrefixTM_copy` (1403), `f2_catalogPrefixTM_computes` (1434).

**F2A-02: Scan, duplication, fixed increment (13 declarations).** Explicit zero-tape scan configurations track native position and accumulated output. Generic scan lemmas copy input or emit one true per scanned symbol. Duplication emits each bit twice, rewinds native input, emits the separator, and copies the input again. Fixed-width increment classifies the first zero or the all-ones case and uses finite control/native rescanning, without a work bank.

Inventory: `f2_scanCfg` (1447), `f2_scanCfg_read` (1452), `f2_scanCopy_run` (1466), `f2_scanCopy_finish` (1490), `f2_pairDupTM` (1507), `f2_pairDup_double` (1529), `f2_pairDup_computes` (1567), `f2_scanCopy_suffix` (1609), `f2_scanTrues_run` (1648), `f2_incFixed_cases` (1678), `f2_incFixedTM` (1696), `f2_incFixed_computes` (1723), `f2_scanStep_right` (1789).

**F2A-03: Pair validity (4 declarations).** A finite parser reads equal doubled bits until 01; 10, a missing delimiter, and an incomplete pair are invalid. It emits exactly the resulting validity bit and halts. Block and whole-input lemmas cover all parse outcomes; no suffix grammar restriction is imposed after 01.

Inventory: `f2_pairValidTM` (1805), `f2_pairValid_block` (1818), `f2_pairValid_run` (1843), `f2_pairValid_computes` (1887).

**F2A-04: Pair extractors (12 declarations).** A one-tape parser buffers the first component before producing output. Its keep-first/keep-second flags select replay of that buffer, native suffix copying, or both. Read, block, rewind, replay, suffix, finish, and whole-input statements describe full configurations and bounded halts, including silent malformed rejection.

Inventory: `f2_pairExtractTM` (1902), `f2_extractCfg` (1931), `f2_extractCfg_read` (1937), `f2_extract_first` (1943), `f2_extract_block` (1959), `f2_extract_rewind` (1987), `f2_extract_replay` (2021), `f2_extract_replay_finish` (2048), `f2_extract_suffix` (2065), `f2_extract_finish` (2109), `f2_extract_run` (2139), `f2_pairExtract_computes` (2197).

**F2A-05: Unary generator (20 declarations).** Finite control encodes setup, nested loop levels, rewinds, advances, and a fixed-size emission counter. Each of d+1 work tapes receives n+1 true symbols. Explicit tapes/configurations, single-bank motion, and setup/copy/loop lemmas describe nested reuse of these fixed words to emit C*(n+1)^(d+1) true symbols. The recursive cost and its upper bound account for moves and emissions; output is on the output channel.

Inventory: `f2_CatalogPolyControl` (2217), `f2_catalogPolyControlFintype` (2225), `f2_catalogPolyControlDecidableEq` (2229), `f2_catalogPolyTape` (2233), `f2_catalogPolyMove` (2237), `f2_catalogPolyUnaryTM` (2244), `f2_catalogPolyCfg` (2274), `f2_catalogPolyMove_apply` (2280), `f2_catalogPoly_emit` (2294), `f2_catalogPoly_rewind` (2316), `f2_catalogPoly_advance` (2349), `f2_catalogPolyCost` (2359), `f2_catalogPoly_loop` (2371), `f2_catalogPolyTape_write` (2476), `f2_catalogPolyCost_le` (2489), `f2_catalogPolyCopyCfg` (2508), `f2_catalogPoly_copy` (2513), `f2_catalogPoly_setup` (2548), `f2_catalogPoly_start` (2572), `f2_catalogPoly_unary_computes` (2606).

**F2A-06: Unary trajectory (5 declarations).** A state-sensitive post-setup predicate bounds all d+1 head coordinates; different inequalities distinguish loop, rewind, advance, emit, and halt. Its transition preservation and the generic unit-motion bound cover setup, all later computation, and absorbed halted tails. Summed interval cardinalities give linear-in-input space, regardless of emitted polynomial length.

Inventory: `f2_polyHeads` (2646), `f2_polyHeads_bounds` (2656), `f2_poly_step` (2671), `f2_head_steps` (2794), `f2_poly_space` (2812).

**F2A-07: Direct binary counter (23 declarations).** Little-endian increment and initial carry length satisfy a popcount potential identity and preserve the intended binary numeral. A direct one-tape four-state machine increments once per native input bit, rewinds its counter after each increment, then emits its final digits. Explicit tape reads/writes, carry, rewind, counting, and emission contracts prove amortized linear time. Separate prefix and all-time head bounds depend on final numeral width, not total count time.

Inventory: `f2_counterInc` (2858), `f2_counterCarry` (2864), `f2_counterInc_potential` (2870), `f2_counterInc_bits` (2882), `f2_counterInc_length` (2898), `f2_counterBump` (2907), `f2_counterTM` (2914), `f2_counterTape` (2935), `f2_counterCfg` (2939), `f2_counterTape_read` (2944), `f2_counterTape_write` (2954), `f2_counter_carry_step` (2975), `f2_counter_carry` (3000), `f2_counter_rewind` (3031), `f2_counter_start` (3066), `f2_counter_increment` (3095), `f2_counter_count` (3117), `f2_counter_emit_run` (3146), `f2_counter_emit` (3174), `f2_counter_computes` (3195), `f2_counter_count_space` (3228), `f2_counter_heads` (3279), `f2_counter_space` (3323).

**F2A-08: Captured length checker (13 declarations).** Run and capture a supplied machine, rewind the native input, parse the pair prefix, and compare suffix length with the captured output length by walking its buffer. The output values themselves are immaterial to the comparison. Invalid grammar emits false. Action/configuration/parse/suffix contracts and the bounded rewind establish the exact length-test function within source time plus linear input time. Pair inversion connects successful parsing to the encoding.

Inventory: `f2_lenAction` (3340), `f2_pairCountTM` (3348), `f2_lenCfg` (3378), `f2_lenCfg_read` (3389), `f2_lenAction_apply` (3396), `f2_lenSuffix_run` (3415), `f2_lenParse_first` (3471), `f2_lenParse_block` (3488), `f2_lenParse_run` (3521), `f2_catalogRewind` (3582), `f2_lenStart` (3612), `f2_pairCount_computes` (3669), `f2_catalogPair_inverse` (3690).

**F2A-09: Time-to-space (1 declarations).** A genuinely halted time-bounded computation has all later configurations equal to its endpoint, so every all-time visited work cell already occurs at one of times 0 through T. Each tape therefore contributes at most T+1 cells.

Inventory: `f2_space_of_time` (3716).

**F2A-10: Sharp unary and grammar bounds (2 declarations).** A separate unary witness retains the sharp time envelope a*((n+1)^e+n+1), including constant cases. The grammar lemma bounds the decoded first component, defaulting to empty on malformed input, by the original input length.

Inventory: `f2_unary_sharp` (4100), `f2_first_length` (4119).

**F2A-11: Guarded stripping (15 declarations).** The raw one-tape machine copies, removes trailing false bits and the last true marker, rewinds, and replays the retained prefix, or emits empty if no marker exists. The zero-tape guard detects a true bit. A suffix-only guard prevents the pair delimiter from being mistaken for a payload marker; composition and conditional selection yield the actual stripping function in linear time before later weakening.

Inventory: `f2_rawStripTM` (4217), `f2_stripCfg` (4237), `f2_catalogBuffer_erase` (4242), `f2_rawStrip_copy` (4253), `f2_rawStrip_rewind` (4279), `f2_rawStrip_replay` (4312), `f2_rawStrip_finish` (4334), `f2_rawStrip_erase` (4346), `f2_rawStrip_trim` (4365), `f2_rawStrip_computes` (4392), `f2_anyTrueTM` (4412), `f2_anyTrue_run` (4425), `f2_anyTrue_computes` (4458), `f2_catalogMarker_cases` (4474), `f2_strip_linear` (4495).

**F2A-12: Loop arithmetic and decrement (27 declarations).** Generic source facts give live/silent strict prefixes, first actual halts, orbit invariance, output length bounded by time, and bounded native rewind. Fixed-width little-endian debit, its borrow position and numerical value, preserve width and detect underflow. Buffer identities and a one-tape decrement machine realize the same operation, returning its head to zero after successful debit or underflow.

Inventory: `f2_loop_live_prefix` (5571), `f2_loop_silent_prefix` (5582), `f2_loop_first_halt` (5596), `f2_loop_orbit_inv` (5619), `f2_loop_fuel_width` (5629), `f2_loop_input_move_le` (5636), `f2_loop_input_run_le` (5650), `f2_loop_output_length_le` (5666), `f2_loop_rewind_bounded` (5683), `f2_loopDebit` (5715), `f2_loopBorrowPos` (5721), `f2_loopBorrowPos_le` (5726), `f2_loopDebit_length` (5732), `f2_loopValue` (5738), `f2_loopValue_bits` (5743), `f2_loopDebit_value` (5754), `f2_loopDebit_success` (5768), `f2_loopDebit_iterate_length` (5779), `f2_loopDebit_iterate_value` (5789), `f2_loopBuffer_read` (5803), `f2_loopBuffer_write` (5811), `f2_loopDebitTM` (5832), `f2_loopDebitCfg` (5848), `f2_loopBorrow_step` (5855), `f2_loopBorrow_run` (5881), `f2_loopBorrow_rewind` (5906), `f2_loopBorrow_correct` (5940).

**F2A-13: Stop/release body wrapper (6 declarations).** A body wrapper adds a one-cell result flag and a one-step release bit: an unreleased anchor causes a silent stop with false flag; source halt gives true flag; all other source actions proceed. The step/run contracts use explicit live/no-anchor guards. Capturing this wrapper preserves its work bank and records emitted payload.

Inventory: `f2_loopBodyTM` (5958), `f2_loopBodyCfg` (5981), `f2_loopBody_stop` (5993), `f2_loopBody_step` (6011), `f2_loopBody_run` (6058), `f2_loopBody_capture` (6086).

**F2A-14: Loop host and capture (10 declarations).** The loop host is a finite sum of fuel-source states, body-call states, and 14 administrative phases. Padded source machines put body, flag, counter, fuel, and capture on disjoint banks. Fuel/body lockstep and genuine initialization identify their trajectories; controller idle and native-input rewind facts preserve all work heads.

Inventory: `f2_LoopHostState` (6109), `f2_loopFuelSource` (6113), `f2_loopBodySource` (6121), `f2_loopControlAction` (6128), `f2_loopHost` (6152), `f2_loopHost_body_capture` (6229), `f2_loopHost_fuel_capture` (6243), `f2_loopHost_init` (6255), `f2_loopControl_idle` (6264), `f2_loopHost_input_rewind` (6272).

**F2A-15: Controller frames and replay (9 declarations).** Explicit controller frames retain body/fuel configurations and give separate counter/capture tapes and heads. A frame update writes only its declared administrative cells. A replay machine reads a fixed buffered word and emits it, with exact step/run identities. Payload projection connects those identities to the host replay phase.

Inventory: `f2_loopFrame` (6289), `f2_loopWrite` (6309), `f2_loopControl_apply` (6316), `f2_loopReplayTM` (6352), `f2_loopReplayCfg` (6362), `f2_loopReplay_step` (6368), `f2_loopReplay_run` (6392), `f2_loopControl_payload` (6408), `f2_loopHost_replay` (6428).

**F2A-16: Fuel installation (18 declarations).** Fuel execution is captured; its emitted counter word is rewound, copied into the counter tape, and erased from capture. Copy-tape read/erase/endpoint identities and phase contracts return counter/capture heads to zero, retain the halted fuel bank, rewind native input, and reach a ready body configuration. The setup has a fixed bound depending on fuel time and counter width.

Inventory: `f2_loopFuelCfg` (6465), `f2_loopFuel_run` (6474), `f2_loopFuel_init` (6487), `f2_loopFrame_payload` (6504), `f2_loopFrame_counter` (6514), `f2_loopHost_fuel_rewind` (6526), `f2_loopCopyTape` (6576), `f2_loopCopy_read` (6580), `f2_loopCopy_erase` (6585), `f2_loopCopy_initial` (6598), `f2_loopCopy_final` (6606), `f2_loopHost_fuel_copy` (6620), `f2_loopHost_fuel_return` (6671), `f2_loopHost_fuel_setup` (6726), `f2_loopFuelCaptured` (6757), `f2_loopReady` (6764), `f2_loopFuelCaptured_frame` (6776), `f2_loopHost_prepare` (6835).

**F2A-17: Body calls and seams (10 declarations).** Padded body and call configurations describe every physical bank and control flag. Guarded source replay reaches the first anchor, performs a stop, then releases it for the next call; separate contracts cover source halt and the startup seam. Frame/reframe identities expose the precise administrative state used next. Startup may take zero source steps; F2-1 records the sole prose mismatch.

Inventory: `f2_loopBodyPadded` (6882), `f2_loopCall` (6892), `f2_loopBodySource_run` (6902), `f2_loopHost_anchor_return` (6917), `f2_loopReady_call` (6958), `f2_loopHost_release` (6997), `f2_loopHost_start` (7028), `f2_loopHost_halt_return` (7048), `f2_loopCall_frame` (7075), `f2_loopCall_reframe` (7102).

**F2A-18: Round dispatch/debit/accept (11 declarations).** Host borrow phases implement fixed-width debit and reset counter position. Rejection clears the flag and either re-enters the body at the canonical next state or halts on underflow. Acceptance in decision mode emits true; in find mode it rewinds and replays captured payload. The round contract covers acceptance and rejection with a fixed per-round duration allowance.

Inventory: `f2_loopHost_borrow_step` (7134), `f2_loopHost_borrow_run` (7172), `f2_loopHost_borrow_rewind` (7205), `f2_loopHost_borrow` (7255), `f2_loopFrame_flag` (7277), `f2_loopFlag_clear` (7286), `f2_loopHost_reject` (7297), `f2_loopHost_payload_rewind` (7369), `f2_loopHost_frame_replay` (7422), `f2_loopHost_accept` (7457), `f2_loopHost_round` (7523).

**F2A-19: Loop contracts and space engines (8 declarations).** Canonical call heads, a numerical controller constant, and full host contracts produce a finite chain of seams with bounded heads and bounded individual durations. The find-chain theorem chooses the least accepted payload. Generic segment and startup lemmas turn the common seam radius plus one segment allowance into all-time visited space, independent of the number of rounds. The existential find wrapper combines these space and time results.

Inventory: `f2_loopCall_heads` (7586), `f2_loopHost_bound` (7611), `f2_loopHost_contracts` (7635), `f2_loop_find_run` (7821), `f2_segment_heads` (7856), `f2_space_radius` (7894), `f2_seamed_space` (7912), `f2_exists_loopFind_space` (7933).

**F2A-20: Split arithmetic and positions (14 declarations).** The candidate state grows by one true bit while its length is at most input length, and then stabilizes. Acceptance compares the remaining suffix length with C*(candidate length+1)^e. Orbit/find identities convert the first successful candidate into splitSolve, and arithmetic supplies polynomial round bounds. A clamped native-input position and a scratch-word definition support counting and cleanup.

Inventory: `f2_splitStep` (8034), `f2_splitAccept` (8038), `f2_splitStep_inv` (8042), `f2_splitStep_orbit` (8050), `f2_catalogFind_congr` (8063), `f2_splitFind_eq` (8073), `f2_splitFind_none` (8084), `f2_splitLoop_result` (8092), `f2_splitLoop_bound` (8112), `f2_splitPos` (8126), `f2_splitPos_read` (8130), `f2_splitPos_succ` (8141), `f2_splitScratch` (8156), `f2_splitScratch_erase` (8160).

**F2A-21: Split cleanup (7 declarations).** A restore machine scans a possibly arbitrary-bit candidate, appends the next candidate bit only when native input permits, erases temporary scratch, and rewinds. Scan/clean configurations and exact stage contracts end with the canonical candidate bank and zero work heads. It does not assume every input candidate bit is true.

Inventory: `f2_splitRestoreTM` (8172), `f2_splitRestoreScan` (8194), `f2_splitRestore_scan` (8203), `f2_splitRestoreClean` (8235), `f2_splitRestore_append` (8242), `f2_splitRestore_rewind` (8279), `f2_splitRestore_run` (8312).

**F2A-22: Split counted simulation (10 declarations).** The counted embedding suppresses source output while advancing native input for each emitted bit; an overflow flag distinguishes overshooting the bounded input. Configuration/action/run lemmas account for the count and source halt. A specialized unary-loop endpoint, least-entry lemma, restoration cut, acceptance criterion, and first-halt selection supply safe phase endpoints.

Inventory: `f2_splitCountAction` (8345), `f2_splitCountCfg` (8353), `f2_splitCount_over` (8361), `f2_splitCount_apply` (8374), `f2_splitCount_run` (8405), `f2_splitPoly_loop_end` (8450), `f2_catalogFirstEntry` (8477), `f2_splitRestore_first` (8496), `f2_splitCount_accept` (8524), `f2_splitCount_firstHalt` (8539).

**F2A-23: Split preparation and safe cuts (11 declarations).** Preparation copies candidate length plus one into each scratch bank, handles the extra marker cell, and rewinds to a canonical source start. First-entry extraction supplies the live prefixes needed for phase simulation. The safe-prefix predicate records absence of the enclosing anchor through an inclusive endpoint; it does not itself assert liveness. Safe concatenation and an embedding cut preserve anchor avoidance when phases are embedded.

Inventory: `f2_splitPrepareTM` (8560), `f2_splitPrepareScan` (8577), `f2_splitPrepare_scan` (8584), `f2_splitPrepareReady` (8611), `f2_splitPrepare_extra` (8617), `f2_splitPrepare_rewind` (8636), `f2_splitPrepare_run` (8663), `f2_splitPrepare_first` (8684), `f2_splitSafe` (8704), `f2_splitSafe_add` (8709), `f2_splitEmbed_cut` (8726).

**F2A-24: Split controller (9 declarations).** The split controller has anchor, preparation, source-counting, native-rewind, restoration, and emission states. Its machine uses one candidate tape and k scratch/source tapes. The initial empty bank already is the anchor; embeddings move between finite phase labels while retaining the physical bank. Rewind and emission machines are explicit transition tables.

Inventory: `f2_splitRewindTM` (8773), `f2_splitEmitTM` (8788), `f2_SplitBodyState` (8805), `f2_splitBodyStateFintype` (8814), `f2_splitBodyStateDecidableEq` (8819), `f2_splitBodyTM` (8835), `f2_splitBank` (8858), `f2_splitBody_start` (8864), `f2_splitEmbed_run` (8873).

**F2A-25: Split phase contracts (4 declarations).** Individual prepare/count/rewind/restore contracts provide actual phase endpoints, durations, and strict-prefix safety. Counting runs the source on virtual empty input over the prepared work words; restore returns to the anchor with the canonical next candidate and cleared scratch.

Inventory: `f2_splitBody_prepare` (8892), `f2_splitBody_count` (8948), `f2_splitBody_rewind` (8979), `f2_splitBody_restore` (9006).

**F2A-26: Split emission and rounds (8 declarations).** The emitter doubles exactly the chosen native prefix, emits 01, and copies the remaining suffix. Single-step and concatenation safety facts exclude anchor returns inside the enclosing round; actual endpoint identities supply the phase behavior. The positive round contract either halts with the encoded split or returns the exact next canonical state within source time plus linear candidate/input overhead.

Inventory: `f2_splitEmitCfg` (9031), `f2_splitEmit_double` (9041), `f2_splitEmit_separator` (9084), `f2_splitEmit_suffix` (9108), `f2_splitEmit_run` (9149), `f2_splitSafe_one` (9166), `f2_splitSafe_join` (9178), `f2_splitBody_round` (9195).

**F2A-27: Split closure (6 declarations).** A generic suitable source is lifted into the split body and then the find-loop wrapper. Separate positive-degree nested-unary and degree-zero constant sources have bounded time and restore their work heads. The body-envelope and closure lemmas instantiate candidate count n and the polynomial per-round bound, yielding degree e+2 time and degree e+1 space.

Inventory: `f2_splitSolve_of_body` (9325), `f2_splitSource_poly` (9396), `f2_splitSource_constant` (9406), `f2_splitBody_envelope` (9427), `f2_splitSolve_source` (9454), `f2_splitSolve_closed` (9481).

**F2A-28: Timed conditional machine (11 declarations).** Pad the two branches onto disjoint banks, capture the decider output on one extra tape, read its Boolean choice, rewind native input, and run the selected branch on its genuine initial bank while the other stays idle. Configuration and capture/read/start/branch-run contracts transfer full behavior, including the decider halting emission and selected branch output. A time lemma adds only fixed decider/rewind overhead.

Inventory: `f2_timedPadTM` (9638), `f2_timedCondTM` (9647), `f2_timedBranchCfg` (9673), `f2_timedControlCfg` (9682), `f2_timed_capture` (9690), `f2_timed_control_init` (9707), `f2_timed_branch_run` (9728), `f2_timedReadyCfg` (9763), `f2_timed_read` (9775), `f2_timed_start` (9833), `f2_cond_time` (9866).

**F2A-29: Rewind and bank sums (4 declarations).** Native-input rewind prefixes preserve all work-head positions. A finite-index bijection and exact sum decomposition partition concatenated banks; they introduce no loss in coefficients or cardinality.

Inventory: `f2_rewind_scan_heads` (9896), `f2_rewind_heads` (9930), `f2_finSumEquiv` (9960), `f2_sum_add` (9983).

**F2A-30: Conditional ledger (7 declarations).** The padded branch space equals the selected source space plus the idle other-bank origins. A common head relation decomposes the host into decider heads, branch heads, and a capture coordinate; control/branch/read projection lemmas preserve it. At every host time, a bounded decider time and a branch time no greater than the host time witness this relation, yielding source visited-set containment and a two-cell capture allowance.

Inventory: `f2_branch_space` (9992), `f2_condHeads` (10033), `f2_control_heads` (10040), `f2_branch_heads` (10051), `f2_read_heads` (10059), `f2_cond_ledger` (10085), `f2_cond_space` (10148).

**F2A: individual load-bearing declarations**

The family inventory above also covers each supporting lemma. The following rows state the witness definitions and the substantive contracts used at the audit boundary individually; “matches” includes comparison with the helper description and its claimed route, with the sole exception explicitly noted.

| Declaration · line | Restatement and fidelity assessment |
|---|---|
| `f2_idTM` · 1311 | Zero work tapes, one live control state: emit each native input bit while moving right; halt without output on blank. Hence identity with no work-space charge. Matches. |
| `f2_idTM_run` · 1323 | Through time `t≤x.length`, control is live, native position is `t+1`, and output is exactly `x.take t`. The next blank step halts. Matches. |
| `f2_constTM` · 1358 | Zero work tapes and `w.length+1` finite states; the received emission action walks a fixed word encoded in control. No input-length-dependent work storage. Matches. |
| `f2_catalogPrefixTM` · 1365 | Zero work tapes; emit a fixed prefix without moving input, then scan/forward native input, and halt on blank. Matches. |
| `f2_catalogPrefixTM_computes` · 1434 | The prefix machine computes `w++x` within `w.length+x.length+1` steps. Includes either word empty. Matches. |
| `f2_pairDupTM` · 1507 | Zero work tapes and five states: emit each native bit twice, emit false at the right blank, rewind native input, emit true, then copy input. The output is doubled `x`, delimiter `01`, then `x`. Matches. |
| `f2_pairDup_computes` · 1567 | Compute `pairEncode x x` within `4*(x.length+1)` steps, including empty input. Matches. |
| `f2_incFixedTM` · 1696 | Zero work tapes and four states: silently seek the first false; if none exists, halt with empty output. Otherwise rewind, emit false for the initial true run, true for the first false, then copy the remainder. Overflow is the specified failure output, not an added high digit. Matches. |
| `f2_incFixed_computes` · 1723 | Compute `(incFixed x).getD []` within `3*(x.length+1)` steps. Covers empty width and all-true overflow. Matches. |
| `f2_pairValidTM` · 1805 | Zero work tapes; the live control is an optional pending bit. Equal pairs continue; `01` emits true and halts; `10` or input ending before a delimiter emits false and halts. Does not need to scan the arbitrary suffix. Matches. |
| `f2_pairValid_computes` · 1887 | Emit exactly `[(pairDecode x).isSome]` within `x.length+1` steps. Matches. |
| `f2_pairExtractTM` · 1902 | One work tape buffers decoded A until a delimiter is verified. On success, rewind and scan that buffer, optionally emitting A, then optionally copy B from native input. On malformed input, halt with no output. Selection flags give fst, snd, concat, or empty. Matches. |
| `f2_pairExtract_computes` · 2197 | Within `5*(x.length+1)` steps, output the selected concatenation of decoded A and B, or empty on decode failure. This sharp time applies to every flag choice and is the one passed to the space helper. Matches. |
| `f2_catalogPolyUnaryTM` · 2244 | On `d+1` work tapes, build parallel words of `x.length+1` true cells; nested fixed-bank scans and rewinds enumerate `(x.length+1)^(d+1)` combinations and emit `C` trues per combination using finite control. No emitted word is retained as a work buffer. Matches. |
| `f2_catalogPoly_unary_computes` · 2606 | Compute the unary word of length `C*(n+1)^(d+1)` within `(C+5*(d+1)+4)*(n+1)^(d+1)`. Valid even for `C=0`; exponent zero is handled by a different witness upstream. Matches. |
| `f2_polyHeads` · 2646 | A predicate on post-setup state and heads: halt allows `[-1,q]`; loop states allow `[0,q]` with inactive heads strictly below `q`; rewind allows `[-1,q)` with inactive heads nonnegative; advance/emit require `[0,q)`. Setup/copy states fail the predicate. It is not claimed as an invariant before setup. Matches. |
| `f2_polyHeads_bounds` · 2656 | Every state satisfying that predicate has every work head in `[-1,q]`. Matches. |
| `f2_poly_step` · 2671 | For positive word length q, fixed replicated-true work words and the post-setup predicate imply that one step preserves those tape contents and the predicate. Read/head bounds justify that each branch is the intended loop phase. Matches. |
| `f2_head_steps` · 2794 | For any starting configuration, each endpoint work head differs from its starting coordinate by at most the elapsed time; from zero this gives radius equal to elapsed time. Used for bounded setup/segments, not as a replacement for the unary invariant. Matches. |
| `f2_poly_space` · 2812 | At every horizon, the unary generator uses at most `5*(d+1)*(x.length+1)` work cells. Setup is bounded separately; thereafter the same post-setup interval applies forever, including halt. Matches. |
| `f2_counterInc` · 2858 | Little-endian unbounded-width increment: empty becomes `[true]`; a leading false becomes true; a leading true becomes false and carries into the tail. Matches. |
| `f2_counterCarry` · 2864 | Count the initial run of true digits, stopping at a false or empty tail. Matches. |
| `f2_counterInc_potential` · 2870 | New popcount plus carry length equals old popcount plus one. This exact identity supports amortization; it does not bound each individual increment by a constant. Matches. |
| `f2_counterInc_bits` · 2882 | Incrementing `Nat.bits n` gives `Nat.bits (n+1)`, including `n=0`. Matches. |
| `f2_counterTM` · 2914 | One work tape and four states: count input symbols by variable-width binary increment, finish each carry by returning to head zero, then emit the counter low bit first and halt on blank. The input bit values are ignored. Matches. |
| `f2_counter_increment` · 3095 | One input-symbol increment, including carry and rewind, transforms the explicit origin-based counter configuration into the next one in `2*carry+2` steps. Matches. |
| `f2_counter_count` · 3117 | For every `i≤x.length`, reach the canonical count-`i` configuration with zero counter head and empty output, at a time satisfying `time+2*popcount(bits i)≤4*i`. Matches. |
| `f2_counter_computes` · 3195 | Compute `Nat.bits x.length` within `5*(x.length+1)` steps. Matches. |
| `f2_counter_count_space` · 3228 | Strengthen each count-prefix endpoint with bounds on **all** preceding work-head positions, using radius `2*(Nat.size x.length+1)`. The potential/time statement is retained but is not used as the logarithmic space bound. Matches. |
| `f2_counter_heads` · 3279 | Extend the same radius to every time, including the final counter emission and halted suffix. Matches. |
| `f2_counter_space` · 3323 | The one-tape visited set at any horizon has at most `5*(Nat.size x.length+1)` cells. Matches. |
| `f2_pairCountTM` · 3348 | Add one capture tape to source M, run M with its output captured, position the capture head at its last output cell, rewind native input, validate the pair prefix, and consume one capture cell per suffix symbol. Emit true iff valid suffix length does not exceed captured output length; malformed grammar emits false. Matches. |
| `f2_pairCount_computes` · 3669 | If M computes `g` within `T`, this checker outputs `[length(B)≤length(g x)]` on a decoded pair and `[false]` on malformed input, within `T(n)+2*n+5`. It measures `g` on the **whole original input**; upstream composition supplies the desired unary budget. Matches. |
| `f2_space_of_time` · 3716 | From a genuinely initialized computation halted with output `y` by `T`, every horizon has work space at most `M.k*(T+1)`. The proof includes the entire finite trajectory and identifies all later configurations with its halted endpoint. Matches. |
| `f2_unary_sharp` · 4100 | For all `C,e`, there is a unary polynomial-output witness with time `a*((n+1)^e+n+1)`. The linear term survives in constant cases, allowing composition with input parsing without false absorption. Matches. |
| `f2_first_length` · 4119 | The length of the decoded first component, defaulting to empty on failure, never exceeds input length. Matches. |
| `f2_rawStripTM` · 4217 | One tape copies the input, erases backwards through trailing false cells and then the last true cell, rewinds, and emits the remaining prefix. If no true exists it halts empty. It has no awareness of pair grammar. Matches. |
| `f2_rawStrip_computes` · 4392 | Compute `(splitAtLastTrue x).getD []` within `4*(x.length+1)` steps. Matches. |
| `f2_anyTrueTM` · 4412 | Zero-tape scan skips false bits, emits true and halts at the first true, or emits false at end. Matches. |
| `f2_anyTrue_computes` · 4458 | Compute `[x.any id]` within `x.length+1` steps. Matches. |
| `f2_strip_linear` · 4495 | There is a machine computing the specified pair-aware strip operation in `c*(n+1)`: preserve decoded A and strip B at its last true; return empty when decoding or marker search fails. The proof’s guard tests B, so A’s delimiter cannot supply a false success. Matches R8. |
| `f2_loop_first_halt` · 5596 | A run with a live initial configuration and a halt by the supplied time has a positive first actual halting time no later than that time, with live strict prefixes and the same halted endpoint. Prevents a post-halt budget time from being treated as a live capture trajectory. Matches. |
| `f2_loop_fuel_width` · 5629 | A fuel output consisting of `bits(R(n))` produced within `T(n)` has length at most `T(n)`, by the one-emission-per-step rule. Matches. |
| `f2_loopDebit` · 5715 | Fixed-width little-endian subtraction by one, with a success Boolean: borrow turns initial false bits true; the first true becomes false; reaching empty reports underflow. Width is retained even on underflow. Matches. |
| `f2_loopDebit_length` · 5732 | One debit preserves the word’s exact length. Matches. |
| `f2_loopValue` · 5738 | Evaluate a Boolean list as a little-endian natural, permitting noncanonical leading high zeroes. Matches. |
| `f2_loopDebit_value` · 5754 | Successful debit decreases that value by one; unsuccessful debit implies the original value was zero. It does not claim that an underflow result represents zero. Matches. |
| `f2_loopDebit_success` · 5768 | Debit succeeds exactly when the original numerical value is positive. Matches. |
| `f2_loopDebit_iterate_length` · 5779 | Every iterate of the debit-word operation retains the original width. Thus decrement never extends the counter bank. Matches. |
| `f2_loopDebit_iterate_value` · 5789 | Starting from `Nat.bits R`, for indices i no larger than R, iterated debit represents `R−i`. This does not assert nonwrapping subtraction after underflow. Matches. |
| `f2_loopDebitTM` · 5832 | A one-tape borrow/rewind controller implements fixed-width debit, preserving the native input and returning to origin in a success/failure control state. Matches. |
| `f2_loopBorrow_correct` · 5940 | Starting with the counter at zero, exactly `2*borrowPosition+2≤2*word.length+2` steps produce the debit result, its success tag, and head zero. Matches. |
| `f2_loopBodyTM` · 5958 | Add a stationary flag tape. At an unreleased anchor, suppress source execution and halt with flag false; otherwise perform the source action verbatim, reset release, and write flag true if that action halts. Thus a halting emission is preserved. Matches. |
| `f2_loopBody_run` · 6058 | Under live strict-prefix and no-anchor guards, with an initially released anchor allowed, the wrapper tracks the source exactly to the endpoint, consumes release after a positive time, and records source halt in the flag. Matches. |
| `f2_loopBody_capture` · 6086 | Any host whose embedded actions are the captured wrapper actions follows the corresponding capture configurations for the same guarded prefix. This is conditional transition agreement, not an assumption about arbitrary hosts. Matches. |
| `f2_loopFuelSource` · 6113 | Pad the fuel machine into its own bank, leaving the body, flag and counter banks idle; retain the source finite control. Matches. |
| `f2_loopBodySource` · 6121 | Pad the flagged body into the body/flag bank, leaving counter and fuel banks idle. Matches. |
| `f2_loopControlAction` · 6128 | Administrative action may write flag, move/write counter and capture, move native input, emit, and set control; every body/fuel cell and head is untouched. Matches. |
| `f2_loopHost` · 6152 | On `body.k+1+(1+F.k)+1` work tapes, capture fuel output, install its fixed-width word as a counter, clear/reuse capture, rewind native input, and execute startup plus body rounds. A returned anchor is released; rejection debits and either repeats or exhausts. Acceptance emits true in decision mode, or replays captured body output in find mode. Source banks are retained rather than replicated per round. Matches. |
| `f2_loopHost_body_capture` · 6229 | The host’s body-call transition branch is exactly the padded body source under the capture embedding, with the startup-dependent return label. Matches. |
| `f2_loopHost_fuel_capture` · 6243 | The host’s fuel branch is exactly the padded fuel source under capture, returning to fuel installation. Matches. |
| `f2_loopHost_prepare` · 6835 | A correct time-bounded fuel computation yields an actual halted fuel configuration and the exact ready host within `5*T(n)+7`; its retained source heads are within radius `T(n)`. This original helper asserts an endpoint radius, whereas A2 adds the preparation trajectory ledger. Matches. |
| `f2_loopCall` · 6892 | Canonical capture embedding of the padded body, augmented with startup/release flags, result flag, counter word and retained fuel configuration. It exposes the exact bank positions; it is not an abstract cost oracle. Matches. |
| `f2_loopHost_start` · 7028 | A startup reaching its first canonical anchor at source time `t` reaches the released nonstartup host call at `t+2`, with the fuel-output counter retained. Allows `t=0`. The statement matches; its sketch needs F2-1’s qualification. |
| `f2_loopHost_halt_return` · 7048 | A positive first actual body halt with no intervening positive anchor return maps to the captured host call at exactly that time, with release false and true result flag. Matches. |
| `f2_loopHost_reject` · 7297 | From a silent false-flag return, within `2*word.length+4` steps either debit succeeds and resumes the released anchor with the updated counter, or the host halts with mode-appropriate failure output. Matches. |
| `f2_loopHost_accept` · 7457 | From a true-flag source halt, within `2*source.output.length+3` administrative steps halt with the source payload in find mode or `[true]` in decision mode. Empty accepting payload is allowed. Matches. |
| `f2_loopHost_round` · 7523 | A positive guarded source round of duration `t` is implemented within `3*t+2*word.length+5`: acceptance returns mode-appropriate output; rejection either continues with the exact next canonical body/counter or exhausts. It does not multiply this cost by the number of future rounds. Matches. |
| `f2_loopHost_bound` · 7611 | The controller coefficient is `max 1 (max 9 (3+2+5)) = 10`. It depends on neither input nor round count. Matches. |
| `f2_loopHost_contracts` · 7635 | Given invariant-preserving state evolution, bounded fuel/startup, and positive guarded rounds, construct startup plus `R(n)+1` candidate seams and a halted failure terminal. Startup and each segment cost at most `c*(T(n)+1)`; live seam heads lie in `[-T(n),T(n)]` and the terminal within radius `T(n)+c*(T(n)+1)`. Each accepting segment halts with the appropriate payload/Boolean, otherwise reaches the next seam. No source-space premise is asserted here. Matches. |
| `f2_loop_find_run` · 7821 | A finite chain with per-segment time bound B and empty-output failure terminal halts within `N*B`, returning the payload of the least accepted index in `range N`, or empty if none. An accepted empty payload remains a successful branch. Matches. |
| `f2_segment_heads` · 7856 | With seam heads within radius H, individual segments at most B steps, and an explicitly halted terminal within radius `H+B`, the full run from seam zero stays within radius `H+B`, for any N including zero and for early acceptance. N does not enlarge the radius. Matches. |
| `f2_space_radius` · 7894 | If every initialized head at every time lies in `[-B,B]`, work space at any horizon is at most `M.k*(2*B+1)`, by per-tape interval containment. Matches. |
| `f2_seamed_space` · 7912 | Add a genuine startup of at most B steps to the preceding finite seam chain. Then all-time work space is at most `M.k*(2*(H+B)+1)`. Startup starts at zero; terminal and early halted tails are included. Matches. |
| `f2_exists_loopFind_space` · 7933 | Under the full guarded body/fuel/invariant contracts, construct a machine returning the first accepted payload among indices `0,…,R(n)`, or empty, within `c*(T(n)+1)*(R(n)+2)` and all-time space `c*(T(n)+1)`. The witness is the reopened host in find mode. Matches. |
| `f2_splitStep` · 8034 | Append one true to candidate state s when its length is at most input length; otherwise retain s. Existing candidate bits are not inspected. Matches. |
| `f2_splitAccept` · 8038 | Decide exactly `s.length+C*(s.length+1)^e=w.length`; it has no independent well-formedness requirement on s. Matches. |
| `f2_splitRestoreTM` · 8172 | Explicit candidate/scratch cleanup: scan the candidate and native input, append a candidate bit when permitted, erase scratch, and rewind to the restoration stop state. Preserves arbitrary existing candidate bit values. Matches. |
| `f2_splitCountAction` · 8345 | Lift a source action onto the payload bank, suppress its physical output, and instead count an emitted bit by native-input movement and an overflow tag. The candidate head/content are retained, and source halt changes to the designated return state. Matches. |
| `f2_splitCount_run` · 8405 | For a source configuration on empty input, a host with the specified counted transition agreement, and a run with live strict prefixes, the counted host configuration at the endpoint is the embedding of the source configuration, with native input/overflow representing candidate length plus output count. This preserves source work tapes and heads and handles the final emitting halt. Matches. |
| `f2_splitPrepareTM` · 8560 | Scan the candidate to install a true scratch word of length `s.length+1` on each source tape, then rewind scratch heads; the finite tag records candidate/input overshoot. The candidate itself remains the canonical first tape. Matches. |
| `f2_splitSafe` · 8704 | Every configuration at times `j≤t` avoids the specified anchor. This includes the endpoint, but does **not** assert liveness, first arrival, or a space bound. Matches its uses. |
| `f2_splitEmbed_cut` · 8726 | Given a stationary source stop state reached by time T, agreement outside stop states, and an embedding whose labels avoid the host anchor, choose a time at most T reaching the exact embedded endpoint with anchor avoidance throughout. First-entry selection avoids assuming transition agreement at the stop state. Matches. |
| `f2_splitBodyTM` · 8835 | One candidate tape plus the source tapes; anchor dispatches to prepare, count, acceptance check, native rewind, then either emit or restore and return. Counting passes `none` as source input, so the supplied source is run on virtual empty input over preinstalled scratch. Matches. |
| `f2_splitBody_start` · 8864 | Genuine initialization is already the canonical anchor with empty candidate state. This supplies a zero-step startup, not a positive one. Matches. |
| `f2_splitBody_prepare` · 8892 | Preparation reaches the exact initialized counted-source embedding in at most `2*(s.length+1)+1` steps from the prepare state, avoiding anchor through the endpoint. Matches. |
| `f2_splitBody_count` · 8948 | If a source on the prepared bank reaches the prescribed restored-bank halt by T, the host reaches its exact counted-return configuration by T, avoiding anchor. The actual first halt may precede T. Matches. |
| `f2_splitBody_rewind` · 8979 | From the native rewind phase, reach input position one and phase state two within `inputPos+2`, preserving other fields and avoiding anchor. Matches. |
| `f2_splitBody_restore` · 9006 | Restore reaches the canonical next candidate bank, still at the restoration stop label, within `2*s.length+w.length+5`, with anchor avoidance. The controller subsequently takes the separate step to anchor. Matches. |
| `f2_splitEmit_run` · 9149 | When `s.length≤w.length`, the prepared emission configuration halts after exactly `s.length+w.length+3` steps with `pairEncode (w.take s.length) (w.drop s.length)`, using the doubled-prefix/separator/suffix phases. The native data, not the unary candidate bits, supplies the first output component. Matches. |
| `f2_splitBody_round` · 9195 | Given a source-bank computation of duration T whose endpoint restores the prescribed bank, one positive body round takes at most `T+5*s.length+3*w.length+20`, avoids anchor at strict positive interior times, and either halts with the encoded split when `s.length+out.length=w.length`, or returns the exact canonical `f2_splitStep` state. Matches. |
| `f2_splitSolve_of_body` · 9325 | Any body satisfying the explicit startup/round contracts with envelope `A*(n+1)^(e+1)` yields the desired solveSplit machine with degree `e+2` time and degree `e+1` all-time space. The invariant bounds candidate length by `n+1`; the actual search has `n+1` candidates. Matches. |
| `f2_splitSource_poly` · 9396 | Starting the nested unary machine directly at its top loop on preinstalled banks produces `C*(s.length+1)^(d+1)` trues after recursive loop cost plus one, halting with the same bank and zero heads. Matches. |
| `f2_splitSource_constant` · 9406 | The zero-tape prefix machine on virtual empty input emits C trues in `C+1` steps, with the prescribed empty source bank at halt. Handles degree zero without a nonexistent top loop. Matches. |
| `f2_splitSolve_source` · 9454 | A source producing the unary length polynomial on every prepared candidate bank, restoring that bank, and satisfying the stated cost envelope instantiates the split-body theorem, with the same exported time/space degrees. Matches. |
| `f2_splitSolve_closed` · 9481 | For every `C,e`, provide an actual machine computing the split selected by `solveSplit`, or empty on failure, with degree `e+2` time and `e+1` space. Its degree split selects one of the two preceding source constructions. Matches. |
| `f2_timedPadTM` · 9638 | Pad D’s work bank on the right with idle tapes, leaving its control and source actions unchanged. Matches. |
| `f2_timedCondTM` · 9647 | Disjoint D, M₁, M₂ banks plus one capture tape. Capture D, move capture head back one cell and read the decision, rewind native input, then execute the chosen branch with source output forwarded. The branch control label selects the branch; the syntactic `branchTM … false` transition call does not change that label-dependent transition table. Matches. |
| `f2_timed_capture` · 9690 | The decider phase runs the exact capture embedding of padded D through a guarded source prefix, including its halting action. Matches. |
| `f2_timed_branch_run` · 9728 | A branch configuration runs in lockstep inside the conditional host, preserving the supplied decider bank and choice bit while forwarding source branch output, also after halt. Matches. |
| `f2_timed_read` · 9775 | From captured one-bit decision output, the controller takes the two capture-position/read steps to the correct decision-specific rewind configuration. Other source banks remain as supplied. Matches. |
| `f2_timed_start` · 9833 | A decider computing `[b]` within T yields the exact genuine initialized selected branch embedded in the host at some time at most `2*T+5`, retaining some decider tapes/heads. The statement alone does not characterize those heads as a source trajectory; the ledger below does. Matches. |
| `f2_cond_time` · 9866 | Given the decider and both branch time contracts, the same timed host computes the conditional within `5*(T₀(n)+max(T₁(n),T₂(n))+1)`. Matches. |
| `f2_rewind_heads` · 9930 | For the specified native-input rewind transition table, reach input position one and the chosen destination within `inputPos+2`; every work head at **every prefix** through that time equals its starting head. Matches. |
| `f2_finSumEquiv` · 9960 | Concatenation equivalence `Fin a ⊕ Fin b ≃ Fin(a+b)`, including zero-sized banks. Matches. |
| `f2_sum_add` · 9983 | Exact natural-valued finite-sum decomposition over the two concatenated banks. Matches. |
| `f2_branch_space` · 9992 | At every horizon, padded branch space equals selected source space plus the unselected machine’s tape count: each idle tape contributes its visited origin. This is equality, not a constant-factor bound. Matches. |
| `f2_condHeads` · 10033 | Concatenate a decider head vector, a combined branch head vector, and one capture coordinate, in that physical bank order. Matches. |
| `f2_cond_ledger` · 10085 | For a decider halted with `[b]` by T and every host time u, some decider time `v≤T`, branch time `w≤u`, and integer capture coordinate `0≤z≤1` give the host’s entire head vector exactly. No branch-time bound or monotonicity premise is needed. Matches. |
| `f2_cond_space` · 10148 | Host space through t is at most D’s source space through T plus the selected padded branch’s source space through t plus two capture cells. This follows by per-bank visited containment from the preceding time-indexed ledger, preserving coefficient one. Matches W3. |

**Redirect projections requested by the brief**

These seven `catalog_redirect*` declarations are already in the reconstructed F1 baseline and are unchanged by F2. They are additional requested coverage, not seven of the 306 F2A additions. Their bodies match the attached Wrappers originals after removal of the private prefix and normalization of comments/whitespace.

| Declaration · line | Individual blind restatement; comparison |
|---|---|
| `catalog_redirectState` · 9530 | A live source state becomes a live simulated state carrying its last-output register. A halted source becomes a host halt exactly when the register equals `some haltOn`; otherwise it becomes a distinguished live stationary state. Matches. |
| `catalog_redirectAction` · 9537 | Preserve the source action’s native-input and work-tape actions, suppress physical output, update the remembered last bit with the action’s output when present, and then apply the redirect-state decision. A halting step’s emission is consulted before deciding whether to halt. Matches. |
| `catalog_redirectCfg` · 9543 | Preserve source input position, work tapes and heads; replace control using source state and the last source-output bit; set host output to empty. Matches. |
| `catalog_redirect_loop` · 9550 | From the distinguished live stationary state, every number of steps returns the entire same configuration. This is deliberate divergence without new visited work cells. Matches. |
| `catalog_redirect_apply` · 9562 | Applying a redirected action to a projected configuration equals projecting the result of the source action. The last-output update and suppressed physical output commute with this projection. Matches. |
| `catalog_redirect_step` · 9575 | Source and redirect steps commute with the configuration projection for **all** source configurations, including halted sources whose projections halt and those whose projections stay live. Matches. |
| `catalog_redirect_run` · 9604 | From genuine initialization, the redirect run at every time equals the projected source run at that time. No halting or acceptance premise. Consequently the frozen W2 theorem has exact per-tape visited-set/space equality, including nonterminating rejected redirections. Matches. |

**Declared anomalies and scope of copy verification**

| Anomaly | Assessment from the supplied artifacts |
|---|---|
| Dual-mode map controller | Faithful. Both modes use the identical setup transition table; only the live payload branch differs. False mode establishes a bounded endpoint and first-entry identity; true mode alone is the exported witness. `a2_map_launch` transfers the valid setup prefix, `a2_map_reject` transfers malformed runs at all times, and `a2_mapVirtual_run` supplies every valid post-entry step. No false-mode freeze is asserted of the exported running payload. |
| `a2_mapSumEquiv`, `a2_map_sum` | Exact copies of the later `f2_finSumEquiv`/`f2_sum_add` bodies after the identifier substitution. Their location before the map proof explains the duplicate during an append-only frozen fill. Their finite-bank role is accurate. |
| `a2_loop_halted_run` | Its literal formal contract is the finite Boolean-result chain restated above. It supports the exported time/output clause and imposes the correct failure terminal. The corresponding historical Loop source is not attached, so the report’s historical copy provenance is not independently established byte for byte. No semantic mismatch was found. |
| Reopened Wrappers implementation | All ten `f2_timed*` copies match the attached Wrappers definitions/proofs after removing the `f2_` prefix; for `f2_timed_start`, the locally available bounded-rewind helper name is also substituted for the received `timed_rewind`. The seven redirect copies match as described above. This is a name-adjusted local reopening, with the new trajectory/space lemmas layered over the actual transition table. |
| Other reopened source families | The received Loop, Primitives, Composition and direct-counter source modules are not attached. Their precise historical textual equality cannot be certified from this packet. Their local transition tables, finite-state realizability, actual helper hypotheses, emitted functions, phase contracts, and needed space mechanisms have been audited here; none is treated as correct merely because a report calls it a copy. The imported `virtualMove_correct` implementation is similarly outside the supplied source, while its fully general use, tag preservation and lack of an empty-input exclusion are visible. |
| Deduplication destination | The per-theme split is the appropriate later home for the large primitive and loop reopenings. Bank-sum facts should have one common owner. Native-rewind and conditional head/visited projections belong with Wrappers; loop seam contracts belong with the loop controller. The packet records current layout decision 12.2(a), with option (c) queued for later refactoring; it does not show that the split has already occurred. The F1 resolutions explicitly queue the redirect projection beside `redirect_run`. No prerequisite shared-file edit is missing for this gate. |
| Excluded `environment/self_exe.c` | The shim is mentioned as agent-side execution support and explicitly excluded from the integrated delivery. Neither patch touches such a file, adds an import of it, or contains a hook to it; final Catalog has no new axiom, admission, `unsafe`, `native_decide`, `extern`, or `implemented_by` code. It was not compiled or run for this audit. The independent maintainer logs, rather than the agent’s shim-assisted execution claim, are the supplied kernel evidence. There is no visible integrated dependency on the shim. |
| Conservative loop interval | Benign and explicitly checked. `a2_heads_steps` enlarges the radius only for the current administrative fragment; each new canonical call again has body heads zero, administrative seam heads zero, the same retained fuel configuration, and unchanged counter width. `a2_segments` joins whole segments using one fixed `B=S+4ℓ+8`. The allowance is never added to the next round’s starting bound. |

**Adversarial instantiations**

These are symbolic substitutions into the supplied definitions/contracts, not claims of fresh Lean executions. They check degeneracies that the numerical bounds or prose could otherwise conceal.

| Instance | Expected behavior and audit result |
|---|---|
| Zero-time startup | A split body begins at its empty canonical anchor. Choose startup `t=0`: the strict no-anchor premise is vacuous, and the host executes the two stop/release steps. The statement and proof route work; the unconditional time-zero claim in the sketch produces F2-1. |
| Both mapped components empty | Input is `01`, length two. The parse takes two steps, suffix/rewind/prefix emission takes five, and the payload starts after seven steps with output `01`, within the bound 15. No positive component length is required. A payload that emits on its first halting step has that bit forwarded after `01`. |
| Empty virtual B at both boundaries | Source input positions 0 and 1 correspond to buffer coordinates −1 and 0. Outward motion stays at the same boundary; inward motion crosses to the other. Tag-sensitive `virtualMove_correct` gives the exact bounded move even though both cells contain blank. An untagged “blank means left end” implementation would fail this case; this controller retains the tag. |
| Malformed map input | `[]`, singleton `[true]`, initial `10`, or any sequence of doubled blocks without `01` has no valid decode. Setup produces no output before validation, halts within `5*(n+1)`, and never enters the frozen false-mode payload state. True mode therefore has the same silent halt. |
| Payload output much larger than input | Let g emit a fixed word of arbitrary large length with zero work tapes. After setup, the host forwards these emissions; the two administrative heads remain in their fixed intervals, and there is no payload-output work buffer. The map-space expression remains `Sg(n)+22*(n+1)`, without an output-length term. |
| Zero polynomial coefficient or exponent | `C=0` gives `Nat.bits 0=[]` for every input; `e=0` gives fixed `Nat.bits C`. `polyBits` chooses constant witnesses before positive-case absorption. A factor C is never used to absorb input growth when C is zero. The length checker keeps its separate linear input term. |
| Unary output of degree two | With `C=1,e=2`, the output has `(n+1)^2` bits, while two fixed unary banks have all-time space at most `10*(n+1)`. Their state-dependent bounded heads, not output length or elapsed output time, establish the space result. |
| Counter at zero and at a long carry | Empty native input has blank counter, emits the empty numeral, halts after two steps, and visits only its origin. At `i=2^m−1`, an increment has a long carry, but it remains within the final numeral-width interval and returns to head zero. The popcount potential pays the time cost without pretending each increment is constant time. |
| Fixed-width increment overflow | Empty width and an all-true word halt with empty output, as `(incFixed x).getD []` requires. No work tape or unrequested extra output digit is introduced. |
| Zero loop fuel | `R=0` gives an empty counter word but still one candidate, index zero. Acceptance succeeds before debit; rejection underflows and yields `[false]` in decision mode or `[]` in find mode. The chain has `N=R+1=1`, satisfying `a2_segments` positivity. |
| Arbitrarily many rounds; opposite-side excursions | Different canonical body rounds may explore opposite sides of the origin, and R may be large. Every body excursion is nevertheless in `[-S,S]`, retained fuel stays there, and the same fixed administrative enlargement contains every round. Taking their union does not sum radii or introduce a factor R. |
| Strip with delimiter but no payload marker | For `pairEncode a (replicate m false)`, the delimiter contains true although B does not. The suffix-only guard rejects, returning empty. Raw stripping of the whole encoding is selected only when B itself has a true marker, so it cannot strip at A’s delimiter by mistake. |
| Split on empty input and arbitrary candidate bits | With `C=0`, empty input accepts candidate length zero and returns `pairEncode [] [] = 01`, distinguishable from the no-split output `[]`. Helper rounds and cleanup allow candidate words containing false bits; only length drives the candidate arithmetic. Overshoot is recorded rather than mistaken for exact exhaustion of native input. |
| Conditional with idle work tapes and fast decider | Give the unselected branch any number of tapes and let the decider emit its bit in one halting action. The action is captured before the choice is read; unselected tapes each contribute one visited origin, charged by the additive constant. Native input rewind does not add work-head visits, even when no relation `n≤T₀(n)` is available. |
| Empty accepting find payload and halted tails | An accepting loop body may output `[]`; the find chain takes that acceptance and does not continue merely because output is empty. Every trajectory engine explicitly handles halt absorption, so horizons after termination cannot introduce unbounded new cells. |

No missing sanity theorem is needed to close the gate: the supplied setup, lockstep, halt-extension, and zero-case contracts already imply these cases. Useful optional regression corollaries at the later refactor would name the zero-startup case, the two empty-virtual-input clamps, and setup followed by a payload’s emitting halting step. They would make the sensitive boundary facts easier to reuse; they are not new acceptance requirements.

**Notation used in this report**

| Notation | Meaning |
|---|---|
| `n`, `x`, `w` | Input length and Boolean input words; `n=x.length` in the main ledgers. |
| `a.length` | Number of bits in word a. |
| `01`, `10` | Lists `[false,true]` and `[true,false]`, not binary numerical values. |
| `++`, `[]` | List concatenation and empty list. |
| `S,T,R`, `Sg,Tg` | The received source-space, time, round-count, and payload budgets, with their original theorem hypotheses. |
| `ℓ` | The length of `Nat.bits (R n)`, the installed loop counter word. |
| `B,H,D` | Local nonnegative integer radii or duration bounds as specified in each lemma; they are not additional exported budgets. |
| `k`, `M.k`, `E.k` | Number of physical work tapes of the relevant machine. |
| `c,c₀,K,A` | Fixed natural coefficients from the indicated construction, independent of input and elapsed time. |
| `space` | Sum of per-work-tape visited-cell cardinalities, including each tape’s time-zero origin; native input and output channels are not counted. |
| `radius B` | All physical work-head coordinates lie in the integer interval `[-B,B]`. A trajectory bound quantifies this over all relevant times. |
| `q,d,e,C,N` | Local word-length/state parameter, loop-depth predecessor, polynomial exponent/coefficient, and finite chain length, respectively, as specified at their use. |
