# P4.3 round-2 statement-gate audit

**Verdict: FAIL — gate remains open. 1 blocker, 0 majors, 4 minors, 3 notes.**

The original unbounded-output pigeonhole obstruction has been removed. However, `exists_adjacency_codec_cnf` is still false: at `n = s = 0`, the new serialized-length bound prevents its adjacency CNF from inspecting the second configuration code. Section 3 gives a contradiction for every machine and every proposed constant `C`. The four round-1 major findings are resolved at statement-gate level; their named implementation obligations remain for the fill phase.

Independently verified input SHA-256:

`beb69f18e8fc8cd53cf277195dfb3d04d7d47cab6c8faa7c9df080a75919dbb7`

The packet contains **32 attachments**. Its asserted baseline is `aa02db412a3a3b8edd8c76bbdae3eb8f97cb07f6`, branch `complexity/arora-barak-ch3-4`. Scope is the supplied three-file repair diff, including the codec, `Cfg.InWindow`, and six other revised sketches. The round-1 report and supplied dependencies were used as context. No source files were changed; no sub-agents were used. This is a mathematical statement/sketch audit, **not a Lean kernel certificate or fresh elaboration**.

## 1. Findings

Paths below are relative to `TCSlib/Complexity/`, except for the pack and logs. Line numbers refer to the extracted round-2 files. “Resolved” below does not mean that a sorried proof has been filled.

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| R2-1 | **blocker** | `ClassPSPACE/TQBF.lean:161–195` · `exists_adjacency_codec_cnf`, especially 166 and 193 | Codes of length `C(s+n+1)` admit the stated adjacency CNF with serialized length at most `C(s+n+1)^C`. | Set `n=s=0`. Then each code has length `C`, while `φa.numVars ≤ length(serialize φa) ≤ C`. Consequently `φa` cannot distinguish any two assignments with the same first code. For a halted blank-work configuration with empty output, adjacency to itself must be true, but adjacency to the otherwise identical halted configuration with output `[true]` must be false. Section 3 proves the contradiction. It uses neither injectivity nor validity. | Give the serialization bounds independent room at the smallest input, e.g. replace their RHS by `C * (s+n+2)^C`, or use independent width and size constants. Merely increasing the existing shared `C` cannot work. Recheck all three size ledgers. |
| R2-2 | minor | `ClassPSPACE/TQBF.lean:27–31,167–172`; pack disposition 1 | The contract makes the code factor through `(input, coreSum)` and requires all equal-core dead-output examples to receive equal codes. | The formal clauses give only `code x c = code x d → coreSum c = coreSum d`. The reverse implication is absent. After repairing R2-1, the semantic clauses allow two codes for one dead-summary vertex, for example by retaining output-length parity in a spare code bit. Adjacency can ignore that bit and validity can admit both aliases. This does **not** obstruct the guarded hardness route. | If factorization is intended, add the reverse implication for same-input windowed configurations, or make the existing clause an iff. Otherwise describe the interface as uniquely decoding each valid code to an input and quotient vertex, while permitting aliases; correct the pack’s “equal codes required” assertion. |
| R2-3 | minor | `ClassPSPACE/TQBF.lean:45–47,237–239` · module description / hardness sketch | Live vertices are not self-adjacent. | A live state whose transition preserves state, input position and work data and emits nothing has `step c = c`. The model permits zero head moves; a zero-work-tape stationary loop already suffices. Even some output-emitting live loops preserve `coreSum` once the summary is `dead`. | Say that live vertices **need not** be self-adjacent. Keep the repaired equality-or-adjacency base case. |
| R2-4 | minor | `ClassPSPACE/TQBF.lean:134–160` · codec construction sketch | The listed tracks alone justify the stated accounting by `O(s+n)` constant-size local checks. | One-hot validity on a block of growing length requires a growing-width positive clause unless additional derived tracks are introduced; the straightforward uniqueness constraints are quadratic. A multitape action also depends jointly on symbols under independently located head markers. The listed tracks do not supply explicit scanned-symbol registers or an enumeration accounting for this coupling. These issues do not prevent polynomial-size CNFs. | Give an honest polynomial enumeration: one-hot constraints, and guarded transition checks over input/work-head tuples and scanned symbols. Alternatively add explicit, uniquely determined snapshot/auxiliary tracks and their consistency checks. Do not infer the linear check count from the listed tracks alone. |
| R2-5 | minor | `SpaceComplexity/Hierarchy.lean:209–215` · `SPACE_linear_ne_NP` sketch | The displayed set defining the padded language supports `L ≤ₚ L'`. | `L' := {pairEncode x (replicate (length x)^2 true)}` omits `x ∈ L`. Read literally as the range over all strings, it accepts every padding image, even when `L=∅`. The surrounding instruction to run the `L`-decider shows the intended restriction. | Write `L' = {y : ∃ x ∈ L, y = pairEncode x (replicate (length x)^2 true)}`. The theorem statement and the remaining padding argument are unchanged. |
| R2-6 | note | `ClassPSPACE/TQBF.lean:240–252` · guarded recursion size | The enlarged recursion remains polynomial. | It does, but `Valid z` occurs at every level: there are `ℓ` such copies, plus the two base endpoint guards. The three CNF families are not each used just once. Shifting variable indices also changes unary serialization lengths. | In the fill ledger count all validity copies and renumbered literals. The polynomial conclusion survives; no statement repair is needed for this observation. |
| R2-7 | note | `SpaceComplexity/Hierarchy.lean:93–106,158–160` · output suppression / W1 references | Silent probe/replay and a finite attempt summary suffice for the space bounds. | Correct if probe emissions are discarded and the hierarchy observer retains only finite-state information. The referenced W1 contract is not attached here. “Captured” must not mean storing the entire emitted word on a work tape: bounded-workspace computations can emit much more than their workspace. | Specify discard/finite-summary behavior in the fill obligation and verify the chosen wrapper’s space contract. This audit does not certify the unattached W1/§12 implementation. |
| R2-8 | note | Repair diff, pack attestations, sweep and lint logs | The packet certifies the repair scope and a fresh repository build. | Exact reverse reconstruction of every diff hunk succeeds, and both old and new Git blob hashes match the diff for all three files. Comment-stripped declaration comparison finds exactly one added definition and one changed theorem. The logs contain the expected warnings and no errors. Actual commit membership, process exits and fresh `.olean` artifacts are not supplied. | Retain the build/commit claims as maintainer attestations. The packet now gives substantially stronger source-change evidence than round 1; no gate decision depends on treating a log as kernel certification. |

## 2. Body-only restatements and quantifier audit

### `Turing.Cfg.InWindow`

For a configuration `c` with `k` work tapes,

\[
c.\mathrm{InWindow}(s)
\iff
\bigl(\forall i<k,\ |c.\mathrm{workTapePos}(i)|\le s\bigr)
\land
\bigl(\forall i<k,\forall z\in\mathbb Z,\ |z|>s
\Rightarrow c.\mathrm{workTapes}(i,z)=\mathrm{none}\bigr).
\]

This is a condition on the current work heads and work contents. It says nothing about state, output, input contents, reachability, or the number of previously visited cells. The input-head type already restricts its position to the input plus its two boundary blanks.

The definition matches its docstring and the former inline window hypotheses. At `s=0`, work heads must be at zero, but cells at zero may contain symbols and outputs may be arbitrary. With zero work tapes both conjuncts are vacuous. Increasing the radius preserves the predicate, and equality of `coreSum` preserves it. A run using at most `s` visited cells from blank origin tapes stays in this window; the converse is false. For example, the trajectory `0→1` fits radius one while visiting two cells. No defect found in this definition.

### `Complexity.exists_adjacency_codec_cnf`

The actual quantifier order is

\[
\forall M\;\exists C>0\;\forall n,s\;\exists\mathrm{code},\varphi_v,\varphi_a,\varphi_{\rm acc}.
\]

Fix these witnesses and write `ℓ = C(s+n+1)`. Here `φ(w)` abbreviates the displayed evaluation using `w.getD v false`.

| Clause | Literal content |
|---|---|
| Total code length | `length(code x c)=ℓ` for **every** input `x` and configuration `c`, including wrong-length inputs and configurations outside the window. |
| Input separation | For length-`n` inputs and windowed configurations, equal codes imply equal inputs. |
| Quotient separation | For the same length-`n` input and two windowed configurations, equal codes imply equal `coreSum`. The converse is not asserted. |
| Validity | For every length-`ℓ` word `w`, `φv(w)=true` iff `w` is `code x c` for some length-`n` input and windowed configuration. Both directions are present. |
| Same-input adjacency | For windowed `c,d` on the same length-`n` input, `φa(code x c ++ code x d)=true` iff `coreSum(step c)=coreSum d`. There is no hypothesis that `step c` remains windowed. If it leaves the window, no windowed target can match its core. |
| Cross-input adjacency | For distinct length-`n` inputs and windowed configurations, adjacency evaluation is false. |
| Acceptance | On a windowed configuration over a length-`n` input, `φacc(code x c)=true` iff its state is halted and its output summary is `accept`, equivalently its output is exactly `[true]`. |
| Variable bounds | `φv.numVars, φacc.numVars ≤ ℓ`, and `φa.numVars ≤ 2ℓ`. |
| Description bounds | Each of the three serialized CNFs has length at most `C(s+n+1)^C`. This is the contradictory clause identified in R2-1. |

The formulas are chosen before `x`, so they are input-independent at fixed `(M,n,s)`. The new input-content track makes this feasible. There is no uniform computability assertion for the selected witnesses. Adjacency and acceptance remain unconstrained on invalid words; the guarded consumer does not need them constrained there. Wrong-length inputs can be assigned a fixed dummy code of length `ℓ`, so totality outside the guarded domain is harmless.

## 3. Formal contradiction to the restated codec

Fix any `M : FinTM Bool`. Suppose the displayed witnesses exist. Choose their `C>0`, then specialize to

\[
n=s=0,\qquad x=[],\qquad \ell=C.
\]

Define `c` and `d` as follows, using their well-typed input-head position `0 ∈ Fin 2`:

\[
\begin{aligned}
c.\mathrm{state}=d.\mathrm{state}&=\mathrm{none},\\
c.\mathrm{inputPos}=d.\mathrm{inputPos}&=0,\\
c.\mathrm{workTapePos}(i)=d.\mathrm{workTapePos}(i)&=0,\\
c.\mathrm{workTapes}(i,z)=d.\mathrm{workTapes}(i,z)&=\mathrm{none},\\
c.\mathrm{output}&=[],\\
d.\mathrm{output}&=[\mathrm{true}].
\end{aligned}
\]

Thus

\[
c.\mathrm{InWindow}(0),\quad d.\mathrm{InWindow}(0),\quad
M.\mathrm{tm.step}(c)=c,
\]

\[
\mathrm{outSummary}(c.\mathrm{output})=\mathrm{empty}
\ne\mathrm{accept}=\mathrm{outSummary}(d.\mathrm{output}),
\qquad \mathrm{coreSum}(c)\ne\mathrm{coreSum}(d).
\]

**Step 1: the formula can read only the first block.** The supplied, already-proved `CNF.decode_serialize` and `CNF.numVars_decode_le` give

\[
\begin{aligned}
\varphi_a.\mathrm{numVars}
&=(\mathrm{CNF.decode}(\mathrm{CNF.serialize}(\varphi_a))).\mathrm{numVars}\\
&\le |\mathrm{CNF.serialize}(\varphi_a)|\\
&\le C(0+0+1)^C=C.
\end{aligned}
\]

The code-length clause gives `|code [] c| = |code [] d| = C`. Therefore, for every `v < φa.numVars`,

\[
\begin{aligned}
&(\mathrm{code}\ []\ c\mathbin{++}\mathrm{code}\ []\ c).\mathrm{getD}(v,\mathrm{false})\\
&\qquad=(\mathrm{code}\ []\ c).\mathrm{getD}(v,\mathrm{false})\\
&\qquad=(\mathrm{code}\ []\ c\mathbin{++}\mathrm{code}\ []\ d).\mathrm{getD}(v,\mathrm{false}).
\end{aligned}
\]

By the supplied `Complexity.eval_congr_of_lt_numVars`,

\[
\varphi_a(\mathrm{code}\ []\ c\mathbin{++}\mathrm{code}\ []\ c)
=\varphi_a(\mathrm{code}\ []\ c\mathbin{++}\mathrm{code}\ []\ d).
\tag{1}
\]

**Step 2: adjacency requires different answers.** The same-input adjacency clause, first at `(c,c)` and then at `(c,d)`, gives

\[
\begin{aligned}
\varphi_a(\mathrm{code}\ []\ c\mathbin{++}\mathrm{code}\ []\ c)&=\mathrm{true},\\
\varphi_a(\mathrm{code}\ []\ c\mathbin{++}\mathrm{code}\ []\ d)&=\mathrm{false}.
\end{aligned}
\tag{2}
\]

Indeed, the corresponding right-hand sides are respectively `coreSum c = coreSum c` and `coreSum c = coreSum d`. Equations (1) and (2) imply `true = false`, a contradiction.

This proof does not use injectivity, `φv`, `φacc`, any transition of a live state, or any machine resource bound. It also works with zero work tapes. Unlike the round-1 pigeonhole argument, the two outputs used here have **different** summaries, which the repair correctly requires adjacency to distinguish.

The underlying length problem can also be seen directly from the serialization grammar:

\[
|\mathrm{serialize}(\varphi)|
=1+2\varphi.\mathrm{length}
 +\sum_{\text{clause}\in\varphi}\sum_{(v,b)\in\text{clause}}(v+3).
\]

Even the singleton CNF `[[ (C,true) ]]`, reading just the first bit of the second block, has serialized length `C+6>C`. Increasing the same `C` lengthens the first block along with the allowed formula; it never repairs the contradiction.

Changing the size bound to `C(s+n+2)^C`, or separating the code-width and description-size constants, removes this particular obstruction. A polynomial construction must still be proved; the repaired inequality is not itself that proof.

## 4. Does the semantic interface suffice for hardness?

**Yes, after fixing the false size bound and supplying the explicitly deferred uniform construction.** A converse quotient-to-code equality is optional for this consumer.

Every valid code represents at least one length-`n` input and windowed configuration by the validity clause. The two separation clauses make its input and `coreSum` uniquely determined, even if two different codes represent the same quotient vertex. Cross-input rejection keeps every edge path in the input component of its starting code. Acceptance is well-defined because it depends only on the halted state and summary.

For a valid-code edge, choose windowed representatives of its endpoints. Its semantics is exactly the quotient step. Starting with the genuine initial configuration, repeatedly apply `coreSum_stepWith` through the deterministic embedding: if the current genuine configuration has the representative’s `coreSum`, its actual successor has the next representative’s `coreSum`. It is therefore windowed, and its state/acceptance summary agree. Induction lifts any code path to a genuine run up to quotient equality. In the other direction, coding a genuine windowed run supplies a code path. No equality between the chosen representative’s raw output and the actual run’s raw output is needed.

The guarded recursion is sound on **all** length-`ℓ` endpoint words:

\[
\psi_0(a,b)=\mathrm{Valid}(a)\land\mathrm{Valid}(b)
\land(a=b\lor\mathrm{Next}(a,b)),
\]

\[
\psi_{i+1}(a,b)=\exists z\left(\mathrm{Valid}(z)\land
\forall u,v\left(
((u=a\land v=z)\lor(u=z\land v=b))\Rightarrow\psi_i(u,v)
\right)\right).
\]

For fixed `z`, specializing the universal pair to `(a,z)` and `(z,b)` yields both required subpaths. Conversely, those two subpaths satisfy the implication for every pair. The base handles zero or one edge. Splitting a path of length at most `2^(i+1)` at step `min(length,2^i)`, and concatenating in the reverse direction, proves inductively

\[
\psi_i(a,b)\iff
\text{a path of length at most }2^i\text{ joins valid vertices }a,b.
\]

There are at most `2^ℓ` code words. Cycle removal gives a shortest path with at most `2^ℓ-1` edges, so depth `ℓ` suffices. In `∃ b (Accept b ∧ ψℓ(initial,b))`, the recursion itself forces the target to be valid; unconstrained acceptance on junk words is harmless.

Prenexing with fresh blocks and then putting existential gate variables after the original prefix is sound: for each complete original assignment, consistent gate values exist exactly when the unconverted propositional matrix is true. The algorithm must account for the repeated validity formulas and shifted unary indices (R2-6). All remain polynomial for a fixed machine.

A concrete route to the corrected codec is also available. Encode input contents, finite state, input head, each bounded work tape/head, and the three-valued summary, with canonical padding. Use explicit one-hot clauses and symbol-range clauses for validity. For adjacency, enumerate input-head positions, work-head tuples and the finitely many scanned-symbol/state cases; guard each update by its case and reject transitions leaving the window. Copy unmarked cells, preserve input contents, and update the output summary by its three-state append table. Because the tape count and transition table are fixed, this enumeration and its unary serialization are polynomial in `s+n+1`. It requires no free, unchecked Tseitin variables in the adjacency package. This is a construction argument for the corrected target, not a completed Lean proof or a claim that the current existential package supplies an emitter.

## 5. Disposition of every round-1 finding

| Round-1 # | Assessment of repair |
|---|---|
| 1 — blocker | **Original obstruction removed; replacement still false.** Full-configuration equality has been replaced by quotient equality, so the infinite dead-output family no longer demands infinitely many distinct codes. R2-1 is a new contradiction from the serialization bound. The claimed compulsory identification of all dead-output aliases is also absent (R2-2). |
| 2 — major | **Resolved at statement-gate level, using the requested option (b).** The module and hardness sketch explicitly disclaim uniform construction and name construction/serialization of the three formulas, the initial code, level indexing and final assembly as private polynomial-time fill obligations. The mathematical reduction must use the concrete witnesses built by those obligations, not arbitrary witnesses selected from the existence theorem. |
| 3 — major | **Resolved semantically.** Validity characterizes the image in both directions on every length-matching word. Base endpoint guards, guarded midpoints, cross-input rejection and the accepting target supply the required interface. Section 4 verifies the path correspondence, including aliases and invalid words. R2-1 independently prevents admitting the current package. |
| 4 — major | **Resolved mathematically; statement unchanged and need not change.** Min/max cardinality includes the initial and final head positions; the core clock handles nonhalting; discard-then-replay realizes tagged success and exact failure; canonization has a fixed-code constant. The unattached wrapper’s implementation is not certified (R2-7). |
| 5 — major | **Resolved mathematically; statement unchanged and need not change.** Increasing budgets, a cap on the fixed universal’s own workspace, bank reuse, a space-preserving normal form and padding only the payload remove the nonuniform-constant error. The domination inequality is correct; details below. |
| 6 — minor | **Base-case repair accepted.** Valid equality or adjacency gives reachability in at most one step. Replace the new universal claim that live vertices lack self-loops (R2-3). |
| 7 — minor | **Input omission repaired.** Input content is explicitly carried and cross-input adjacency is rejected. A machine branching on a scanned input bit is now representable. The proposed local-check accounting still needs R2-4’s correction. |
| 8 — minor | **Correct measure, incorrect normalization.** Direct serialized-length bounds include empty clauses and all syntax. Retaining the same coefficient as the exact code width creates R2-1 at `n=s=0`; this repair cannot yet be accepted as a true contract. |
| 9 — minor | **Resolved.** The fixed player-one value has existential recursion at even histories and universal recursion at odd histories. Both winning strategies are assembled with the correct polarity. |
| 10 — note | The attached P4.2 resolution records closure and the quotient/full-configuration bridge obligations. No new P4.2 defect found; that closed layer was used as context, not re-audited. |
| 11 — note | No arbitrary string was assigned a particular decoded machine. The repaired universal sketch is valid for whatever total decoded machine the fixed effective scheme supplies. |
| 12 — note | Source-change evidence is improved: exact hunk reversal and both blob hashes checked. Actual commit/build-artifact claims remain attestations (R2-8). |

### The six revised non-codec sketches

**Membership.** Full syntax validation prevents an apparent false prefix from overriding the total decoder’s true fallback on trailing garbage. On valid input, a depth-first evaluator needs a constant-size phase/value record per quantified variable and reusable cursors; variables beyond the prefix retain the default false value. Every relevant unary index and the prefix length are bounded by the input length. Reusing fixed banks gives `O(n+1)` visited cells. The unchanged membership statement remains true.

**Hardness.** The semantic construction is justified in Section 4, with its uniform-emitter obligation explicit. The theorem remains a valid mathematical target, but its current proposed codec dependency is false until R2-1 is repaired. R2-3, R2-4 and R2-6 concern the construction’s description and accounting.

**Games.** At terminal histories use `W`. At an even nonterminal history take OR of the child values; at an odd history take AND. If the root value is true, player one chooses a true child at every even winning node, while every odd successor remains true. If false, player two chooses a false child at every odd losing node, while every even successor remains false. Induction along play proves the respective strategy wins, including horizon zero. Playing two alleged winning strategies against one another proves mutual exclusion, although the declaration asks only for the disjunction. The unchanged statement needs no repair.

**Universal simulation.** For a coded one-work-tape machine, the visited set of any prefix is the interval from its minimum head position to its maximum. Its cardinality is therefore `max−min+1`; it is already one initially and must be checked after the halting transition as well. Under budget `s`, the number of possible cores is at most

\[
(\#M.\mathrm{State}+1)(n+2)3^{2s+1}(2s+1).
\]

A binary clock for this bound occupies `Oα(s+logSpace n+1)` bits. Before a first halt, repetition of a core repeats deterministic control forever: output contents cannot affect the transition. Thus a silent, bounded probe terminates with the right success/failure answer. On success, reset the same banks, emit the success tag and replay while forwarding emissions; on failure emit only `[false]`. The code canonizer halts on the fixed code, so its finite space is absorbed in the code-dependent constant. These arguments support the unchanged two-clause statement, with R2-7’s discard requirement.

**Hierarchy.** On well-formed code/payload inputs, each attempted universal call receives a well-formed virtual triple. It therefore halts unless first aborted by the workspace cap. There are finitely many budgets. The default answer must apply when the loop is exhausted by **failures or caps**. A fixed number of simulated tapes confined to `[-g(n),g(n)]`, plus resets and the budget/address registers, use `O(g(n))` visited cells uniformly in the code read from the input. Virtual-input addresses require `O(log(n+1)+log(g(n)+1))` bits, absorbed because `g` has the logarithmic floor. The fixed constructibility witness also fits `O(g(n))`.

For the contradiction, absorb the space-preserving normal-form overhead into `c₀` and fix its code `α`. At sufficiently large padded-payload lengths, the stated domination hypothesis gives

\[
\begin{aligned}
C_\alpha(c_0 f(n)+\mathrm{logSpace}(n)+1)
&\le C_\alpha(c_0+2)f(n)\\
&\le g(n).
\end{aligned}
\]

Since `Cα≥1`, the budget `c₀ f(n)` is among those tried. At that budget, and at every smaller one, the universal’s total visited-cell bound is at most `g(n)`, so no work head exits its cap. A successful attempt occurs by that budget, and every success reports the same deterministic output on the self-applied input. The diagonal answer is its opposite. Fixed-code payload padding supplies arbitrarily large such inputs without changing `Cα`. The ordinary inclusion follows from eventual `f≤g` by absorbing the finitely many exceptions using `g≥1`. Thus the unchanged hierarchy statement needs no repair.

**Padding inequality.** With the `x∈L` restriction restored, the padded length is

\[
m=2n+2+n^2=n^2+2n+2,
\]

including `n=0`. Validate the pair and pad, then simulate the original quadratic-space decider on the first component, using `O(n²+1)⊆O(m+1)` space. The polynomial padding function reduces the unpadded language to the padded one. Under the contrary class equality, downward closure of `NP` puts every quadratic-space language in linear space. Finally, for `n≥max(1,2A)`,

\[
A(n+1)\le 2An\le n^2\le n^2+1,
\]

which yields the hierarchy contradiction at the constructible linear/quadratic pair. Only the displayed padded-language definition needs R2-5’s textual correction; the theorem statement is unchanged and true.

## 6. Adversarial cases and independent finite checks

| Test | Instance and result |
|---|---|
| A1 | `n=s=0`, halted blank-work configurations with outputs `[]` and `[true]`: forces contradictory adjacency evaluations by Section 3. |
| A2 | A literal at index `C`, the first position of the target code: even a singleton CNF serializes to `C+6`, exceeding the asserted budget `C`. |
| A3 | `k=0`: `InWindow s` is true for every configuration; the new blocker still applies. |
| A4 | `s=0`, origin heads with a nonblank origin cell: `InWindow 0` holds. This is not a zero-visited-space assertion. |
| A5 | Head at `s+1`, or a nonblank work cell at `s+1`: `InWindow s` fails. A transition leaving the window has no allowed matching target. |
| A6 | Two unequal outputs of lengths two and three, both dead: equal `coreSum` does not require equal codes under the semantic clauses. A two-alias finite model satisfies their edge/acceptance behavior. |
| A7 | A live stationary, silent loop: `step c=c`, disproving the new nonreflexivity sentence. |
| A8 | Same work/state data on distinct one-bit inputs: content separation and cross-input rejection prevent changing input components during midpoint search. |
| A9 | Invalid words supplied arbitrary incident edges: endpoint validity and the guarded recursion exclude all resulting junk paths. |
| A10 | Live state with output `[true]`, or halted state with output `[]` or `[false]`: acceptance is false. Halted output `[true]` is accepted. |
| A11 | One work tape visiting `0→1` and halting at budget one: the revised cardinality test rejects, despite radius-one membership. Immediate halting at budget zero also fails. |
| A12 | Emit once, then loop forever: silent probing returns only `[false]`; forwarding probe output would violate the contract. |
| A13 | A syntactically complete false empty-clause matrix, then one trailing bit: the latter must take the true fallback. Validation precedes any verdict. |
| A14 | Game horizon zero with either winner bit: exactly the corresponding player wins. Higher-horizon strategy quantifiers agree with the revised fixed-perspective recursion. |
| A15 | Padding `L=∅`: the displayed unrestricted range is nonempty, exposing R2-5. The corrected restricted language is empty. |

An independent Python transcription checked:

- **505** exactly parsed CNF strings of length at most 14, their exact serialization-length equation and variable-index bound; also **128** right-block unit-literal length instances.
- **32,768** comparisons of the literal universal-pair recurrence against independently computed bounded shortest-path reachability: all 512 directed graphs on three valid vertices, an additional invalid word with arbitrary incident edges set true, all endpoint pairs, and depths 0–3.
- **9,841** unit-head walks of length 0–8 against the min/max interval cardinality rule.
- **189** output-summary/append cases; **278** complete Boolean winner predicates for game horizons 0–3 against explicit strategy quantifiers; **127** padding-length cases.

All checks passed. They support the stated finite examples and repaired recurrences; they are not proofs of the general Lean contracts. The blocker is the general mathematical contradiction above, not an inference from finite testing.

## 7. Source comparison, change verification, and closure requirement

I consulted the **2009 book itself**, via [this PDF copy of Arora–Barak](https://theswissbay.ch/pdf/Gentoomen%20Library/Theory%20Of%20Computation/Sanjeev_Arora,_Boaz_Barak-Computational_complexity__a_modern_approach-Cambridge_University_Press(2009).pdf), for Claim 4.4(2), §4.2’s QBF reduction, Theorem 4.8, and Exercises 3.2, 4.1 and 4.10. The input-carrying quotient codec and explicit validity guard are implementation adaptations; polynomial width/description size suffice for the stated polynomial-space reduction. The universal contract strengthens the exercise by specifying failure totality and tagged output. Those distinctions are declared and mathematically defensible. The zero-size contradiction comes from the packet’s own encoding and bounds.

All **11** diff hunks reverse exactly against the supplied current files. Reconstructed old and supplied new Git blob hashes match the diff’s six advertised prefixes:

| File | Old blob prefix | New blob prefix |
|---|---|---|
| `ClassPSPACE/Games.lean` | `094b1bdf` | `310129d3` |
| `ClassPSPACE/TQBF.lean` | `001c2e0a` | `61c2d946` |
| `SpaceComplexity/Hierarchy.lean` | `eca62a0a` | `0d778a03` |

Comment-stripped comparison finds exactly the advertised declaration changes: `Cfg.InWindow` added and `exists_adjacency_codec_cnf` restated. All other declarations in these three files are unchanged. The seven-module inventory is **15 definitions and 12 sorried statements**. The sweep lists all seven modules, exactly 12 admission warnings at the expected declaration lines, zero `error:` lines, and its completion marker. Lint summaries report 0 FAIL / 0 WARN over the 5-, 2-, and 42-file trees. These are textual/source checks, with the build limitations in R2-8. The incomplete repository/dependency packet was not used to claim a fresh build.

**To close the gate:** repair the codec’s description-size normalization and re-audit that statement. Correct the factorization description or add its missing converse, the live-self-loop wording, the codec check-count explanation, and the padded-language restriction. Keep the uniform emitter, quotient-path lift, nonbuffering probe, capped simulator and space-preserving normal form as explicit fill obligations. No counterexample was found to `Cfg.InWindow`, the unchanged universal/hierarchy statements, or the guarded reachability interface considered separately from the false size bound.

## Notation glossary

- `c,d`: the two halted blank-work configurations used in Section 3, with outputs `[]` and `[true]` respectively.
- `C`: the codec witness constant; `n,s`: its input length and work-window radius; `ℓ=C(s+n+1)`: code width.
- `φ(w)`: abbreviation for `φ.eval (fun v => w.getD v false)`; `v` is a zero-based variable index. `++` is list concatenation.
- `Valid, Next, Accept`: evaluations of `φv, φa, φacc`; `ψ_i(a,b)` is the guarded reachability formula at depth `i`; `a,b,z,u,v` in that recurrence are `ℓ`-bit blocks.
- `Cα`: the universal simulator’s constant for fixed code `α`; `c₀`: the space multiplier after normal-form conversion; `A`: an eventual-domination multiplier; `Oα`: constants may depend on `α`.
- `m`: padded input length; `L'`: the padded language with its membership restriction restored. Other machine and complexity-class notation is inherited from the packet.
