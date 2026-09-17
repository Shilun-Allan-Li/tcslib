External audit: phase-3 skeleton + fill round 1, supplied snapshot attributed to commit `f8621285` on `complexity/arora-barak-ch1`.

This report audits the declarations in `phase3-bundle.md` against Arora–Barak §1.4–§1.4.1, printed pp. 19–21 / PDF pp. 45–47. The discussion of the planned reduction also checks §1.5–§1.5.1, PDF pp. 48–49. Restatements below were derived from comment-stripped Lean source before comparing the phase-3 docstrings and the book. The counterexamples are mathematical arguments about the supplied machine semantics, not Lean-checked proofs. No Lean elaboration or historical Git comparison was performed.

The phase-3 surface has two independent blockers: arbitrary `MachineCode` values need not admit effective simulation, and the input layout makes all three asserted time bounds false. The findings below distinguish those defects from weaker-than-textbook interfaces and repairable proof-sketch omissions.

The new phase-3 declarations have the following meanings. Throughout, `ComputesInTime x output t` means that the initialized run is halted by time `t` with exactly `output`; it does not mean first halting at exactly `t`.

| Declaration | Blind restatement |
|---|---|
| `CodeTM` | A natural number `numStates` and a machine with one work tape, Boolean nonblank symbols, and live states `Fin (numStates + 1)`. Its transition table and its initial state are both part of the data. Halting is the separate `none` state. |
| `CodeTM.toFinTM`; `CodeTM.toFinTM_k` | Package the same machine as a finite machine; its work-tape count is exactly one. |
| `pairEncode x α` | Double each bit of `x`, append `[false, true]`, then append `α` unchanged. |
| `MachineCode` | Functions `encode : CodeTM → List Bool` and `decode : List Bool → CodeTM`, such that decoding `encode M` followed by any number of `true` bits returns exactly `M`. Neither function carries an effectiveness condition. |
| `MachineCode.decode_encode` | For every scheme and machine, `decode (encode M) = M`. |
| `exists_machineCode` | At least one structure satisfying precisely those fields and the padding equation exists. No machine implementation or running-time bound is asserted. |
| `exists_codeTM` | Every finite Boolean machine with one work tape has a coded machine with the same halting-by-time predicate and output, for every input, output, and time. No equality of intermediate configurations is asserted. |
| `universal` | For each scheme there is one finite Boolean `U`; for each coded `M` there is a natural `C`, independent of input, output, and time. Whenever `M` halts by `t` with `output`, `U` on `pairEncode x (c.encode M)` halts with that output by `C * (t + 1)`. Nothing is required when `M` diverges, or on a noncanonical representation. |
| `universal_quadratic` | For each scheme there is one `U` such that every finite Boolean machine computing a total function `f` within `T` has some string `α` and constant `C` enabling `U` to produce `f x` by `C * (T x.length + 1)^2`. The witnesses may depend on the machine, function, and bound. The conclusion does not use `c` or relate `α` to its encoding/decoding. |
| `timed_universal` | For each scheme there is one `U`, and for each coded `M` a constant `C` uniform over `x,t`. On the specified nested encoding, if `M` halts by `t`, `U` outputs `true :: output`; if no output witnesses halting by `t`, `U` outputs `[false]`. Both guarantees use `C * (t + 1)^2`. Only canonical machine codes are covered. |

The new public supporting lemmas have the following meanings. These statements concern arbitrary raw state/symbol types where the source does not impose finiteness; that is appropriate for the stated configuration identities.

| Declaration | Blind restatement |
|---|---|
| `Complexity.succ_pow_le` | For natural `n,d`, `(n + 1)^d ≤ 2^d * (n^d + 1)`. The brief calls this `Turing.succ_pow_le`, but the declaration is inside `namespace Complexity`. |
| `OracleTM.workTapePos_step_le` | One oracle-machine step moves each work/query head by distance at most one, for every oracle and configuration. |
| `OracleTM.workTapes_step_eq_of_ne` | A cell different from a tape's current head position is unchanged by one oracle-machine step. |
| `Cfg.embedOracle_inputSymbol` | Adding the query tape and embedding the state preserves the current input symbol. |
| `Cfg.embedOracle_workTapeSymbols` | On every original tape, identified by `i.castSucc`, the symbol under its head is preserved. |
| `Cfg.embedOracle_state_eq_none` | The embedded configuration is halted exactly when the original is halted. |
| `Cfg.embedOracle_output` | Embedding preserves the complete output list. |
| `Cfg.embedOracle_apply` | Mapping an action's states through `Sum.inl` and extending it by an idle tape, then applying it to the embedded configuration, equals applying the original action and then embedding. |
| `Cfg.embedOracle_init` | Embedding an initialized configuration equals initialization with the embedded initial state. |
| `OracleTM.step_ofMultiTapeTM` | For every oracle and original configuration, embedding commutes with one step of the plain machine and its oracle wrapper. |
| `OracleTM.step_plainEmptyOracle` | On every configuration, the compiled plain machine takes exactly the same step as the original oracle machine with the empty oracle. |

The private helper `apply_workTapes_eq_of_ne` is the corresponding off-head-cell identity for an action. `runFrom_workTapes_invariant` bounds every initialized work/query head's absolute position by `t` and says all cells with absolute position at least `t` are still blank. The latter includes the boundary cells: a write during the first `t` steps can occur only at a position reached before the last move. Neither helper assumes a simulation result.

The private `idTM` has no work tapes and one live state. On a Boolean input symbol it emits that symbol and moves right; on blank it halts without emitting. Its invariant says, for `t ≤ x.length`, that it remains live, has input position `t + 1`, and has emitted `x.take t`. Consequently it is live on the right blank at time `x.length`, and the next step halts with output `x`. This proves the public existential statement with the concrete witness constant `1`. For `x = []`, initialization is already on the right blank and the machine halts at step `1` with output `[]`.

The requested findings table follows. Evidence arguments A–E below make the counterexamples and boundary checks explicit.

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | blocker | `Encoding.lean · MachineCode`; `Universal.lean · universal`, `timed_universal` | Padding and totality do not justify universal simulation for every scheme. This already invalidates current phase-3 statements, independently of their time bounds. | Argument A constructs an allowed noncomputable permutation of an ordinary scheme. Even an unbounded forward-correct interpreter on canonical codes would decide an undecidable set. | Use a fixed effective scheme, or strengthen the abstract interface with an effective decoder to an explicit finite-table representation, or an equivalent effective evaluation contract. An abstract effective interface is sufficient; fixing one scheme is not logically mandatory. |
| 2 | blocker | `Universal.lean · universal`, `universal_quadratic`, `timed_universal` | The displayed time bounds are false for the actual `pairEncode x ...` layout. | Argument B uses one-step machines producing opposite bits and arbitrarily long identical inputs. Their differing codes lie beyond the allowed runtime. For the timed theorem, the same machine with budgets `0` and `1` already gives a contradiction. The startup sketch incorrectly absorbs scanning `x` into a machine-dependent constant. | Put the program and clock before `x`, or include startup costs, e.g. `C * (x.length + t + 1)` and `C * (x.length + (t + 1)^2)`. For the quadratic corollary use `C * (x.length + (T x.length + 1)^2)`. An explicit `x.length ≤ t`/`n ≤ T n` hypothesis is another restricted option, but cannot be silently assumed. |
| 3 | major | `Universal.lean · universal`, `timed_universal`; phase-4 interface | The current results do not supply the book's evaluator on arbitrary `α`, including padded and fallback representations. `universal` also omits divergence preservation. | Theorem 1.9, PDF p. 46, asserts `U(x, α) = Mα(x)` for all strings. Current statements only accept `c.encode M`. There is no equation `c.encode (c.decode α) = α`, nor an effective canonicalization operation. A forward-only interpreter could return a spurious result for a known looping program without violating the statement. The book's HALT-to-UC reduction, PDF p. 49, evaluates arbitrary `Mα(α)`. | Add an all-string evaluator with both directions of the halting/output relation, plus the desired forward time bound. State the timed theorem for `c.decode α` too. For general effective decoders, account for the decoding cost, potentially through an `α`-dependent constant. |
| 4 | major | `Universal.lean · universal_quadratic` | This is a total-function simulation corollary, not the full per-machine Theorem 1.9. Its encoding-scheme parameter is unused in the proposition after the binder. | The hypothesis requires halting on every input. The existential `α` has no specified decoding and can depend on `f,T`; partially defined computations and a fixed representation of the original machine are absent. | Label it explicitly as a total-function corollary, remove the unused scheme parameter if appropriate, and add a separate machine-level theorem for partial computations. If chaining normal forms for that theorem, strengthen the normal-form API beyond its current total-function statement. |
| 5 | major | `Encoding.lean · exists_machineCode` proof sketch | The proposed serialization omits `tm.q₀`, so its stated parser cannot recover every `CodeTM`. | Argument C gives two two-state machines with identical transition tables and different initial states, computing different constant bits. The sketched serialization assigns them the same string, contradicting the required exact round trip. | Serialize the initial-state index as well. Alternatively impose a canonical initial state in `CodeTM` and adapt state relabeling and the round-trip contract consistently. |
| 6 | minor | `Universal.lean · timed_universal` proof sketch | The operational outline must resolve the exact-deadline case in favor of success. | The formula includes a machine whose first halting step is exactly `t`. The phrases “before the clock expires” and “clock reaches zero first” do not specify simultaneous expiry/halting. | Check for halting after each simulated transition, including transition `t`, before declaring timeout. At `t = 0`, inspect the initial state and report failure in this model. |
| 7 | minor | Audit brief · `Turing.succ_pow_le` | The listed namespace is incorrect. | The supplied `P.lean` opens `namespace Complexity` and never enters `namespace Turing` before this lemma. | Replace the reference with `Complexity.succ_pow_le`. |
| 8 | note | `Encoding.lean · pairEncode` | The doubled first component is unambiguously delimited. | Argument D gives the aligned-pair parser; empty components cause no ambiguity. A raw search for an unaligned `01` would be wrong. The whole pair is not a prefix-free code because its second component is verbatim. | No definition change required. Add a parser/left-inverse lemma and describe precisely which component is self-delimiting. |
| 9 | note | `Encoding.lean · MachineCode`, `CodeTM` | The algebraic encoding requirements correctly give total interpretation and infinitely many representations, and rule out a constant encoder. | Argument D proves distinctness by padded-string lengths and injectivity by the round trip. `numStates = 0` means one live state, not zero. The recovery property concerns code-normal-form machines; its connection to general machines is through simulation. | Keep these laws, while adding the effectiveness contract in finding 1. Do not describe totality-by-type as a computability guarantee. |
| 10 | note | `Encoding.lean · exists_codeTM`; `Universal.lean` chaining | The per-input iff preserves all halting-by-time/output information needed for the stated chain. The order `∃ U, ∀ M, ∃ C, ∀ x output t` has the intended input-independent constant. | An iff at every time preserves halting existence, output, and first halting time. Argument E verifies constant absorption. Linear per-step table scanning for a fixed normal-form machine is reasonable once effective parsing and input-access startup are handled. | Keep this interface for the stated use. The linear/quadratic distinction is a valid declared variation after findings 1–2 are repaired. |
| 11 | note | `Universal.lean · timed_universal` cases and representation | The two semantic cases are exhaustive, the tags do not collide, and `Nat.bits` matches `TimeConstructible`. The clock's quadratic allowance is ample after startup is included. | Classically either some output satisfies halting by `t`, or every output fails it. `[false] ≠ true :: output`, including empty `output`. Output length is at most `t`; binary clock work is bounded by a constant times `(t + 1)^2`. Both declarations literally use `Nat.bits`. | No change to the case predicates, tags, or number representation. Apply findings 1–3 and the deadline clarification in finding 6. |
| 12 | note | `Composition.lean · idTM_run`, `computesFunInTime_id`; new public supporting lemmas | The inspected supporting statements do not assume the simulations they support. The identity invariant includes the empty input correctly. | Restatements above and the explicit final halting step. Oracle embedding lemmas are unconditional identities over configurations and every oracle; no hidden correctness hypothesis appears. | No statement repair identified in this inspected surface. This does not certify transitive freedom from `sorry` for simulation corollaries. |
| 13 | note | Fill round and header attestations | The current packet supports the reported count and current forms, but does not independently establish the historical diff or build claims. | There are 16 attached Lean modules and 13 literal `sorry`s: the eight listed previous constructions and five phase-3 statements. The remaining signatures are consistent with the included resolution summaries. Prior source snapshots, the audit records themselves, and an elaboration log are absent; Lean/Lake are unavailable here. | Retain the historical-signature and 18-module-elaboration claims as repository attestations. For independent verification, attach the exact baseline diff and build/axiom evidence. |

Argument A: why the abstract scheme already permits a counterexample.

Fix an undecidable set `A ⊆ ℕ`. For every `n` and bit `b`, choose the explicit machine `Hₙ,ᵦ` with `n + 2` live states, initial state `0`, and every transition immediately outputting `[b]` and halting. These form an effectively recognizable family of distinct `CodeTM`s. Let `p` swap `Hₙ,₀` and `Hₙ,₁` exactly when `n ∈ A`, and fix every other machine. Thus `p (p M) = M`.

Take an ordinary computable padded table scheme `c₀`, including the initial-state field. Define

\[
c.\mathrm{encode}(M)=c_0.\mathrm{encode}(pM),\qquad
c.\mathrm{decode}(\alpha)=p(c_0.\mathrm{decode}(\alpha)).
\]

The padding law follows step by step:

\[
\begin{aligned}
c.\mathrm{decode}(c.\mathrm{encode}(M)\mathbin{++}\mathrm{true}^m)
&=p\!\left(c_0.\mathrm{decode}(c_0.\mathrm{encode}(pM)\mathbin{++}\mathrm{true}^m)\right)\\
&=p(pM)=M.
\end{aligned}
\]

For `αₙ = c₀.encode Hₙ,₀`, which is computable from `n`, we have

\[
\alpha_n=c.\mathrm{encode}(pH_{n,0}),\qquad
(pH_{n,0})([])=[\mathbf1_A(n)].
\]

The machine on the right always halts in one step. An interpreter satisfying just the forward-correctness implication of `universal` would therefore halt on `pairEncode [] αₙ` and output `A`'s membership bit. The unknown machine-dependent runtime constant is irrelevant: run until it halts. This decides `A`, a contradiction. `timed_universal` with budget `1` yields the same decision after stripping the success tag. This counterexample does not use the input-access defect in finding 2.

Effectiveness of `encode` alone would not suffice either. One may reserve canonical codes beginning with `false`, preserve their computable interpretation and all their padding, and assign noncomputable meanings to strings beginning with `true`. The algebraic laws remain true while arbitrary-code evaluation fails.

For specific question 2, three distinct requirements must be separated:

1. The set-theoretic diagonal definition of `UC` and its contradiction at `c.encode M` need the round trip and coverage of the machines under consideration. They do not require computing `decode` or `encode`.
2. The book's particular reduction from computing `HALT` to computing `UC` runs `Mα(α)` after a positive halting answer. That construction needs effective evaluation on arbitrary `α`, which the present interface does not provide. A different direct diagonal proof of halting undecidability can avoid this particular evaluation step; that does not repair the claimed universal theorems.
3. A machine computing an explicit serialization of `c.decode α` is a sufficient way to obtain effective evaluation. It is not the only possible interface: a proved semantic evaluator is enough, and need not recover syntactically irrelevant machine data. Thus it is effective interpretation that is essential, not a uniquely prescribed syntactic `computable_decode` field. It may be supplied by a concrete fixed scheme or required of every scheme in an abstract class.

Argument B: the independent input-access contradiction.

Let `H₀,H₁` be one-work-tape machines with `numStates = 0`, initial live state `0`, and transition actions that ignore all read symbols, emit their respective bit, and halt. Directly from `Action.apply` and `Cfg.init`,

\[
\forall x,\quad H_b.\mathrm{toFinTM.ComputesInTime}\;x\;[b]\;1.
\]

For `universal`, let `C₀,C₁` be the promised constants and put `B = max (2C₀) (2C₁)`. Choose a common input `x` with `x.length = B + 1`. The two universal inputs have the same first `2 * x.length` symbols; their machine-code suffixes occur later. Starting at input position `1`, the real input head cannot exceed position `B + 1` during the first `B` steps. The left boundary is also identical.

Induct on the step number up to `B`: the live state, work-tape contents and positions, output, and numerical input-head position agree, since every inspected input symbol agrees and the transition function is identical. Halting configurations remain fixed. Both runs must have halted by `B`, but the theorem requires their outputs to be `[false]` and `[true]`. Contradiction.

For `universal_quadratic`, use these same machines with constant functions `f x = [b]` and `T n = 1`. After the existential strings and constants have been chosen, take `B = max (4C₀) (4C₁)` and the same long common `x`. The identical-prefix argument is unchanged, whatever strings were chosen. This refutes the formula even though its parameter `c` has no semantic role.

For `timed_universal`, one fixed machine `H₀` suffices. Its machine-dependent constant `C` is shared by budgets `0` and `1`. No initialized machine is halted at step `0`, so budget `0` requires `[false]` by time `C`. Budget `1` requires `[true, false]` by time `4C`. Choose `x.length = 4C + 1`. The clock and code both lie after the doubled input, so the two runs agree through time `4C`. The first run has already halted with `[false]`, forcing the second to have the same output. Contradiction. If `C = 0`, the required output at step zero is already impossible.

These examples also answer the adversarial zero-time cases: `universal` has a false premise at `t = 0`; `universal_quadratic` cannot have its computation hypothesis when `T n = 0` for any input length `n`; `timed_universal` affirmatively requires failure at budget zero. That last requirement is locally sensible but inconsistent with the current layout and other budgets.

Argument C: the omitted initial state.

Take `numStates = 1`, so the live state set is `{0,1}`. Use the same transition function in both machines: from state `0`, emit `false` and halt; from state `1`, emit `true` and halt, ignoring the input and work symbol. Set the first machine's initial state to `0` and the second's to `1`. Their state counts and entire transition tables agree; their initial states and outputs disagree. Therefore a serialization containing only the fields listed in the sketch cannot satisfy `decode (encode M) = M`. The existence theorem itself is repairable by adding the missing field.

Argument D: pairing, padding, and degenerate cases.

Read the doubled region in aligned two-bit blocks. A block `00` recovers `false`; `11` recovers `true`; the first aligned `01` ends the first component. No doubled bit is `01`, so the delimiter cannot occur prematurely at an aligned position. Consume the delimiter and take the remaining suffix verbatim. This parser returns exactly `(x, α)` on every `pairEncode x α`, proving injectivity of the pairing. The pattern `01` can occur across a `00|11` boundary, which is why alignment matters.

For `x = []`, the input starts with the delimiter. For `α = []`, the suffix after the delimiter is empty. Both-empty input is exactly `[false,true]`.

For fixed `c,M`, every string `c.encode M ++ List.replicate m true` decodes to `M`, and its length is `(c.encode M).length + m`. Equality for two padding lengths therefore implies equality of those lengths. There are infinitely many representations.

Finally,

\[
c.\mathrm{encode}(M)=c.\mathrm{encode}(N)
\Longrightarrow
M=c.\mathrm{decode}(c.\mathrm{encode}(M))
=c.\mathrm{decode}(c.\mathrm{encode}(N))=N.
\]

The distinct machines `H₀,H₁` above rule out a constant encoder. Totality-by-type correctly assigns every string a machine, but does not specify an algorithm or require all noncanonical strings to share one fallback machine.

Argument E: chaining and clock arithmetic.

The iff in `exists_codeTM` is quantified over every `x,output,t`, so it preserves the entire set of halting deadlines and their outputs. Consequently it preserves both the existence of a halting time and the least such time. Intermediate configurations are unnecessary for the stated chain.

For any natural `T n`, `(T n + 1)^2 ≥ 1`, and hence

\[
\begin{aligned}
C_U\bigl(c_1(Tn+1)^2+1\bigr)
&\le C_U\bigl(c_1(Tn+1)^2+(Tn+1)^2\bigr)\\
&=C_U(c_1+1)(Tn+1)^2.
\end{aligned}
\]

Thus `C = C_U * (c₁ + 1)` is sufficient for the displayed absorption. This correct arithmetic does not fix the missing startup term or effective-decoding assumption.

A straightforward binary countdown takes at most a constant times `t * (1 + (Nat.bits t).length)` work, with the binary length at most `t + 1`. Buffering and flushing the simulated output adds at most a constant times `t + 1` because `output_length_le` applies. These quantities fit within a constant multiple of `(t + 1)^2`; reading the outer `x` prefix remains additional work in the present layout. No special amortization claim is needed.

The eight earlier `sorry` statements were spot-checked as follows. “Retained” here means present in the attached declaration and consistent with the attached decision log; it does not assert an independently verified textual comparison with `fb91cf88`.

| Remaining declaration | Checked current form |
|---|---|
| `computesFunInTime_const` | Every fixed output string has a finite Boolean machine and constant bounding its runtime by `c * (n + 1)`. |
| `computesFunInTime_comp` | Both computation hypotheses and `Monotone T₂` are retained; bound `c * (T₁ n + T₂ (T₁ n) + 1)`. |
| `alphabet_reduction` | Finite decidable alphabet, Boolean embedding, input/output computation through that embedding, same work-tape count, and constant-factor `T + 1` bound. |
| `one_work_tape` | Finite decidable source and enlarged target alphabets, embedding, exactly one work tape, and quadratic `T + 1` bound. No claim of merging input/output into that tape. |
| `nonnegative_heads` | All initialized target-input runs have nonnegative work heads; target tape count is unchanged and computation on embedded inputs has constant-factor `T + 1` overhead. The piecewise fold, independent blank payloads, origin marker, and safe halt on nonembedded symbols remain in the sketch. |
| `oblivious_of_mem_DTIME` | Both `TimeConstructible T` and `L ∈ DTIME T` remain; conclusion is an oblivious Boolean decider within `c * (T n + 1)^2`. The corrected mask/copy/park/fixed-sweep sketch remains; the definition does not assert length-determined halting. |
| `timeConstructible_id` | Identity is time constructible under the retained definition `n ≤ T n` plus a positive constant and a machine emitting `Nat.bits (T n)` within `c * (T n + 1)`. |
| `PAL_mem_DTIME_linear` | Binary palindromes belong to `DTIME (fun n => n + 1)`, with the constant absorbed by `DTIME`. |

The filled monotonicity, output-bound/prefix, oracle lockstep, and arithmetic/class lemmas preserve their intended meanings in the inspected source. `one_work_tape_binary`, the model-invariance corollaries, and `PAL_mem_P` still depend on the relevant remaining construction sorries. Calling their proof bodies filled is accurate; calling their dependency closures complete would not be. No extra literal `axiom`, `admit`, `sorryAx`, or `unsafe` declaration appeared in the comment-stripped attached source. This source scan does not replace an elaborated `#print axioms` report.

Notation glossary: `++` is list concatenation; `true^m` is a list of `m` true bits; `A` is an undecidable subset of the natural numbers; `𝟙_A(n)` is its Boolean membership bit; `Hₙ,ᵦ` is the explicit one-step constant-bit machine with `n + 2` live states; `H₀,H₁` in argument B are the one-live-state constant-bit machines; `p` is the involutive permutation in argument A; `c₀` is an ordinary effective padded scheme; `c` is the scheme being discussed; `αₙ` is `c₀.encode Hₙ,₀`; `B` is the shared finite runtime bound in argument B; `C₀,C₁,C,C_U,c₁` are natural-number runtime constants. Other identifiers and variables are those of the supplied declarations; `n` is an input length or family index, `t` a step budget, and `m` a padding length.
