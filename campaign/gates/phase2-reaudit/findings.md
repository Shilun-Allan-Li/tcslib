# Phase 2, round 2: external re-audit findings

Audited the supplied `phase2-reaudit-bundle.md`, which identifies its amended sources as commit `85b66f2a`, against the attached Arora-Barak textbook: PDF pp. 42-45 (Claims 1.5/1.6/1.8 and Remark 1.7), pp. 51-52 (§1.6.1), and p. 60 (Exercise 1.5 and the palindrome lower-bound attribution). References below to bundle lines identify the supplied Markdown, not repository line numbers.

**Disposition: no blocker or major found in the supplied mathematical surface; four minor findings remain.** The corrected `oblivious_of_mem_DTIME` sketch is an adequate construction outline. The folding coordinate and initialization argument are repaired, but the literal alphabet description in `nonnegative_heads` remains incomplete. These are assessments of statements and outlines, not completed proofs or a blanket approval. The six phase-2 modules still contain 11 `sorry`s; the 12 supplied Lean modules contain 28. Lean and Lake are unavailable here. No attachments or source declarations were modified.

Historical byte identity is **not verified**: the packet includes the amended source and the earlier findings, but not the earlier source bytes or a commit diff. Current formulas agree with the earlier findings' mathematical restatements. That is weaker than the byte comparison requested in the brief.

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | minor | `Robustness/Bidirectional.lean` · module description and `nonnegative_heads` sketch (bundle 982, 1010-1025) | Folding uses `Γ × Γ`, with an origin tag added and preserved. | Here `Γ` excludes blank. A folded cell must hold two independent `Option Γ` payloads, including a symbol paired with blank; an outer physical blank does not supply these mixed cases. For `Γ = Bool`, `Option (Γ × Γ)` has five values, whereas two independently blank payloads require nine, even before distinguishing the origin. The corrected coordinate and safe-halt argument do work; the missing representation is a local repair, not a counterexample to the theorem. | Specify, for example, `Γ' = Bool × Option Γ × Option Γ`, with the Boolean component an origin flag. Decode an untouched physical `none` as two blanks with no origin flag; use `e γ = (false, some γ, none)`. Initialize `(true, none, none)` at each origin and preserve the flag on every update. Replace the literal `Γ × Γ` description. |
| 2 | minor | `Composition.lean` · design; `ClassP/DTIME.lean` · deviations; plan §7 (bundle 702-712, 1475-1481, 517) | The convention bridges are consistently recorded as waived. | The amended composition disclaimer and decision log explicitly waive the bridges, but `DTIME.lean` still calls the output simulation a “phase-2 obligation” with an “until then” restriction. Composition's closing “costs no generality” phrase is also broader than its demonstrated buffering of already append-only computations. These are residual prose inconsistencies; no exact AB step-count transfer was found. | Synchronize the `DTIME.lean` status with the waiver. Replace the last composition sentence with a precise statement that buffering and delayed emission are available within this model; the cross-model bridge remains unestablished. Narrow “all bounds carry existential constants” to the adapted source bounds, since internal exact bounds and lockstep lemmas are legitimate exceptions. |
| 3 | minor | `Robustness/AlphabetReduction.lean` · `alphabet_reduction` sketch (bundle 835-848) | Per-step overhead is `O(k · L)`, including zero work tapes. | The all-blank block repair is correct, and the bit embedding forces positive block length. But at `k = 0` the displayed overhead vanishes even though the simulator must still read, change state, move its input head, and possibly emit. The theorem's unrestricted existential constant has no such defect. | State `O((k + 1) · L)` or give the zero-work-tape case separately. Keep the all-`none` blank code and the theorem statement. |
| 4 | minor | `AroraBarakChapter1Plan.md` · §5, phase 3 (bundle 473-475) | Phase 2 supplies a “one-work-tape, four-symbol normal form.” | `one_work_tape_binary` supplies `FinTM Bool`, whose physical tape alphabet is `Option Bool`, with three symbols. The phase-2 declaration does not provide the stated four-symbol interface. | Call it the one-work-tape binary normal form. If phase 3 actually needs a fourth symbol, name the additional embedding step. |
| 5 | note | `Robustness/Oblivious.lean` · `Oblivious`, design, theorem scope; plan §7 | Round-1 findings 1, 6, and 7 are resolved. | The prose now agrees with the predicate: only input/work-head trajectories are constrained; equal first halting times and emission schedules do not follow. The theorem explicitly covers the first assertion of Exercise 1.5 in this model and promises neither one work tape nor the exercise's combined work/output tape. | No declaration change. Any downstream use of simultaneous obliviousness, a tape restriction, or length-determined halting must receive its own stated guarantee. |
| 6 | note | `Robustness/Oblivious.lean` · `oblivious_of_mem_DTIME`, steps 1-2 | Masking the witness's input preserves its budget output, and one copy scan suffices to obtain the length. | Induction identifies the masked run on a length-`n` input with the witness's run on `List.replicate n false`. `TimeConstructible` explicitly specifies that input and therefore supplies `(T n).bits`. During copying, write one unary marker per input symbol on a fresh tape; movements are independent of the copied bit. See the construction checks below. | No mathematical repair required. State these invariants explicitly when implementing the outline, including resetting the input head before the copy phase. |
| 7 | note | `Robustness/Oblivious.lean` · `oblivious_of_mem_DTIME`, steps 3-5 | The revised construction supports the quadratic bound and obliviousness. | `B n = (a + 1) · (T n + 1)` dominates both the decider budget and `n + 1`. A fixed number of full sweeps per original step costs `O(B n)`, hence `O((B n)^2)` over `B n` steps. Setup fits the same allowance. Padding continues all physical motions after simulated halting; fixed-duration coding and final emission prevent data-dependent timing. | Adequate as an outline. Formalize the fixed layout, sweep invariants, phase transitions, and trajectories of auxiliary heads; no additional hypothesis or theorem-strength change is needed. |
| 8 | note | `Robustness/SingleTape.lean` · both simulation statements | Round-1 findings 5 and 9 are resolved. | The in-model scope is explicit and agrees with AB's distinct merged model (PDF p. 43). Tagged `Option Γ` payloads represent marked blanks; boundary tags and the unused-tape treatment of `k = 0` address the earlier omissions. AB's palindrome separation is correctly attributed (PDF p. 60). | No change required for these resolutions. |
| 9 | note | `ClassP/ModelInvariance.lean` · module and `mem_P_iff_one_work_tape`; composition and binary corollaries | Round-1 findings 4 and 12 are resolved; the forward implication has no residual mathematical defect. | With `C' = c(C + 1)^2`, `c(C(n + 1)^d + 1)^2 ≤ C'(n + 1)^(2d)` at every length, including zero. The reverse implication forgets the tape-count conjunct. Alphabet reduction preserves time up to constants; reducing work tapes supplies only the polynomial-time conclusion. The `T + 1` alphabet padding is absorbable under the computation premise, which implies `T n ≥ 1`. | No theorem change. Use the explicit pointwise inequalities below rather than an eventual-asymptotic argument. |
| 10 | note | `Composition.lean`, robustness and context docstrings; plan §5/§7; `Oracle.lean` | The waiver's restriction holds in the supplied development, and round-1 findings 11 and 13 are addressed. | The source constants `3n`, `4 log(card Γ) · T`, `5kT²`, and `4T` are quoted as source bounds, not imported as exact formal bounds. Exact internal oracle simulations and output-length lemmas are independently in-model. Alphabet reduction documents its string-output generalization and omitted constructibility hypothesis. The query-tape bridge is deferred to Chapter 3 with an explicit outstanding obligation. | No new bridge required for this packet. Apply the prose synchronization in finding 2. This scan covers the supplied modules and plan, not unseen repository files. |
| 11 | note | Audit packet · historical statement comparison | The theorem formulas at `85b66f2a` are byte-identical to those at `2917a1b9`. | The amended 11 theorem formulas match the earlier report's descriptions of hypotheses, quantifiers, bounds, embeddings, and tape-count conclusions. However, the old source is absent; a mathematical restatement cannot establish byte identity. | Supply a diff or both revisions' declaration bytes for reproducible comparison. Do not report historical byte identity as independently certified by this audit. |

The changelog is dispositioned as follows.

| Round-1 finding | Round-2 disposition |
|---|---|
| 1: frozen heads and halting | Resolved; see finding 5. |
| 2: oblivious construction | Resolved at proof-outline level; see findings 6-7 and the checks below. |
| 3: convention discharge | The major discharge overclaim is removed and the waiver is explicit; residual minor documentation mismatch is finding 2. |
| 4: model invariance | Resolved; see finding 9. |
| 5: one-work-tape scope | Resolved; see finding 8. |
| 6: output schedule | Resolved; see finding 5. |
| 7: Exercise 1.5 coverage | Resolved; see finding 5. |
| 8: blank block code | The reserved-code defect is resolved. Finding 3 concerns a separate zero-work-tape overhead expression. |
| 9: marked blank and zero tapes | Resolved; see finding 8. |
| 10: folding coordinate and detectable origin | Coordinate, fold crossing, initialization, and invalid-input handling are repaired. Explicit payload/tag typing still needs the minor correction in finding 1. |
| 11: embedded inputs and generalization | Resolved; the added deviations match the declaration and the output-prefix argument. |
| 12: constant absorption | Retained and valid; see finding 9 and the calculations below. |
| 13: stale phase-2 bridge scope | The specified phase-2 paragraph and query-tape deferral are aligned with the decision log. Findings 2 and 4 identify other stale prose. |

The following checks answer the brief's specific questions and substantiate the two outline assessments. They remain mathematical construction arguments, not machine-checked Lean proofs.

**1. Constant-input substitution preserves the output.** Let `W` be the constructibility witness and `W₀` its input-masked version. For each transition, replace its input read `r` by `r.map (fun _ => false)`. This preserves blank reads. Fix an input `x` of length `n`, and put `x₀ = List.replicate n false`.

Relate the run of `W₀` on `x` to the run of `W` on `x₀` by equality of states, numerical input positions, work heads, work-tape contents, and accumulated output. The inputs themselves differ, so literal equality of the dependent configurations is not the claim.

1. At time zero, every listed component agrees by initialization.
2. If these components agree at time `t`, the input heads are at the same numerical position in equal-length strings. At either boundary both effective reads are `none`; at every interior position both effective reads are `some false`. Work reads also agree.
3. The transition tables therefore choose identical actions. Equal-length input boundaries give equal numerical next input positions, and the same actions preserve all other components. Halted states remain paired by absorption.
4. Induction proves this relation for every time, including equality of accumulated outputs and of first halting times.

The actual witness specification, instantiated at `x₀`, is

\[
W.\mathrm{ComputesInTime}\bigl(x_0,(T(n)).\mathrm{bits},b(T(n)+1)\bigr).
\]

Consequently the masked machine produces that same output by that budget. The specification is universal over **every binary input**, so this instantiation needs no additional promise. Redirecting the emissions into a fresh work tape preserves the simulated witness by projection and costs a fixed overhead. The extra tape's trajectory is also length-dependent, since the witness's emissions now are. Merely ignoring the witness's output, or assuming that its budget alone determines its answer, would not suffice; the run relation above is the required justification.

**2. The copy scan also supplies length information.** First restore the real input head to the start of the input; the witness's ending position is length-dependent, and returning over the bounded input costs `O(n + 1)`. During the copy scan, move the input and copy heads once per logical input cell. On a separate fresh tape, append one unary marker on each of these iterations. Use the same motions for `false` and `true`, and stop on the right boundary blank. Thus the third tape contains a delimited unary segment of length `n`; the empty-input case gives a segment of length zero. Rewinding these tapes depends only on their segment lengths.

The copied bits affect writes but not motion. Unary length is already sufficient for layout construction; any later conversion to binary may use a length-dependent routine within the quadratic preparation allowance. A variable-time arithmetic routine is harmless for obliviousness here when its entire input depends only on `n`; the time bound must still be charged. This avoids silently assuming that the constructibility witness returned `n` as well as `T(n)`.

**3. Fixed layout, setup cost, and the quadratic bound.** The chosen budget satisfies

\[
\begin{aligned}
B(n)&=(a+1)(T(n)+1)=aT(n)+a+T(n)+1>aT(n),\\
B(n)&\ge T(n)+1\ge n+1.
\end{aligned}
\]

Allocate the original work-tape coordinates from `-B(n)` to `B(n)`, a virtual input segment with both boundaries, the virtual head markers, and counters. The original machine has a fixed finite number of tapes, so the layout occupies `O(B(n))` cells over a fixed finite tagged alphabet. A source head moves at most one cell per original step, so all relevant coordinates lie in this layout. Boundary tags must be structural fields preserved by simulation writes.

Preparing the layout is possible within `O(B(n)^2)`: compute the binary integer `B(n)` from the captured budget using constant multiplication, and generate its unary-sized allocation using a decrementing counter. Even allowing `O(B(n))` work per generated cell fits the stated allowance. Control scans in this phase depend on the budget and unary length, not on the copied input bits; copying payloads into fixed locations must follow that same rule.

One fixed collection of full sweeps reads marked symbols, determines the source transition in finite control, and updates payloads and head markers. Use additional full sweeps or fixed local coding phases where needed, rather than an early stop at a data-dependent marker. Keep every represented physical head, including counters and other auxiliary tapes, on a length-dependent schedule. After source halting, run the same sweeps with an inactive simulated state. Counter maintenance costs at most `O(B(n))` per macrostep. Simulate `B(n)` original steps, not `B(n)` steps of an already quadratic simulator.

Fixed-duration coding of this fixed finite alphabet retains the schedule over `Bool`. Before the final step, simulated emissions are buffered in finite control: the decider premise and append-only output imply there is exactly one final answer bit and no competing extra emissions. Emit it once, then halt at the common finishing time. Heads stay fixed thereafter, so the definition's quantification over all later times is satisfied too.

For a fixed construction-overhead constant `C`, its time is bounded by

\[
\begin{aligned}
\mathrm{time}(n)
&\le C\bigl(b(T(n)+1)+(n+1)+B(n)^2+1\bigr)\\
&\le C\bigl(b+2+(a+1)^2\bigr)(T(n)+1)^2.
\end{aligned}
\]

The second inequality uses `n ≤ T(n)` and `1 ≤ T(n)+1`, so it holds at every input length. Both the schedule and phase-ending times depend only on length. No quartic composition or assumption that an arbitrary constructibility witness is already oblivious remains.

**4. Fold initialization and the representation repair.** Use the concrete enlarged alphabet from finding 1,

\[
\Gamma'=\mathrm{Bool}\times\mathrm{Option}(\Gamma)\times\mathrm{Option}(\Gamma),
\qquad e(\gamma)=(\mathrm{false},\mathrm{some}\,\gamma,\mathrm{none}).
\]

The embedding is injective by its first payload component. An untouched physical blank decodes to `(false, none, none)`. An explicit tagged record contains an origin Boolean and two independent source-cell contents. This also makes sense for an empty `Γ`.

All work heads start at coordinate zero. Introduce one fresh initialization state whose single action writes `(true, none, none)` on **each** work tape, moves every head by zero, emits nothing, and enters the source's initial state with all component flags positive. A multi-tape action has a write/move component for every tape, so these writes are simultaneous; their cost is one transition, independent of input length. For zero tapes the write tuple is empty. No coordinate inspection or preliminary simulated activity is needed.

After initialization, physical position `p ≥ 0` stores source cells `p` and `-p-1`; its origin field is true exactly when `p = 0`. A write updates only the active payload and preserves the other payload and the origin flag. Thus a source symbol cannot manufacture or erase an origin tag.

The physical movement rules are:

| Active component | Source move | Physical movement / component change |
|---|---|---|
| Positive | right | Move right; retain positive component. |
| Positive | left, away from origin | Move left; retain positive component. |
| Positive | left, at origin | Stay; switch to negative component. |
| Negative | left | Move right; retain negative component. |
| Negative | right, away from origin | Move left; retain negative component. |
| Negative | right, at origin | Stay; switch to positive component. |
| Either | stay | Stay; retain component. |

Each row realizes the proposed coordinate

\[
\phi(z)=\begin{cases}z&z\ge0,\\-z-1&z<0,\end{cases}
\quad\text{with}\quad \phi(0)=\phi(-1)=0.
\]

An actual left move is made only from a strictly positive physical coordinate. Induction therefore gives nonnegative positions at every time, including initialization. On encountering a nonblank input symbol outside `e`'s range, use a stationary halting action before any simulated transition. Earlier activity preserves the same invariant, and subsequent halted configurations are fixed. Thus the universal `NonnegativeHeads` quantifier, including malformed enlarged-alphabet inputs, is covered. This safety argument does not require a source computation premise on malformed inputs.

The initialized tag and the two payloads are the missing typing details, not a new asymptotic construction. With them, the folding outline supports constant slowdown and the same number of work tapes.

**5. Waiver scan and polynomial corollary.** The supplied source quotes AB's exact numerical constants only while identifying its source statements or explicitly replacing their constants. In particular, the palindrome sketch derives its own padded in-model count; the oracle lockstep theorems compare machines within the shared `Cfg`/`Action` semantics. Neither transfers an AB step count across the waived convention bridges. The restriction therefore holds for the supplied files, subject to the documentation cleanup in finding 2. The restriction is not itself a proof of a semantic bridge.

For `mem_P_iff_one_work_tape`, `n + 1 ≥ 1` gives

\[
\begin{aligned}
C(n+1)^d+1 &\le (C+1)(n+1)^d,\\
c\bigl(C(n+1)^d+1\bigr)^2
&\le c(C+1)^2(n+1)^{2d}.
\end{aligned}
\]

Choose `C' = c(C + 1)^2` and degree `2d`, and apply time-bound monotonicity to the simulator. This handles `n = 0` and `d = 0` as written. No simultaneous obliviousness claim is used in this implication.

For the alphabet claim, instantiate any `DecidesInTimeVia` premise at `List.replicate n false`. If `T n = 0`, it contradicts `not_computesInTime_zero`; hence `T n ≥ 1` and

\[
c(T(n)+1)\le 2cT(n).
\]

Thus the module's alphabet-invariance assertion is consistent with the delivered padded theorem and existing monotonicity interface. It does not imply fixed-`DTIME T` invariance under the quadratic tape reduction.

Finally, the other retained estimates need no new repair: composition uses output length at most `T₁(n)` and monotonicity of `T₂`; the binary one-work-tape corollary absorbs the additive one because `(T(n)+1)^2 ≥ 1`; and the polynomial alphabet corollary uses `(n+1)^d ≤ 2^d(n^d+1)` pointwise. The string-output generalization of alphabet reduction remains supported by append-only output prefixes, including early emissions.

Notation glossary: `n` is input length; `t` is a step number; `x` is an input and `x₀` its all-false counterpart; `W` is the constructibility witness and `W₀` its input-masked variant; `T`, `T₁`, and `T₂` are time bounds; `a` and `b` are the decider and constructibility constants; `B(n)=(a+1)(T(n)+1)` is the simulation budget; `k` is the work-tape count and `L` in finding 3 is the binary block length. `Γ` is the source nonblank alphabet, `Γ'` the enlarged nonblank alphabet, and `e` the symbol embedding; `γ` is a source symbol, `z` a virtual coordinate, `p` a physical coordinate, and `φ` the folding map. `r` is an optional input read. `C` denotes a locally chosen fixed constant (construction overhead or the polynomial-decider coefficient), `c` a simulation constant, `d` a polynomial degree, and `C'=c(C+1)^2` the resulting polynomial coefficient. `Option` includes the blank value `none`; `some` marks an actual payload; `bits` denotes the specified binary representation. Big-O constants may depend on the fixed machines and alphabets, never on the input.
