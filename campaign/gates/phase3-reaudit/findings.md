External audit: phase 3, round 2 — repaired encodings and evaluator

Audited input: the supplied `phase3-reaudit-bundle.md`, whose repaired snapshot is attributed to commit `afe5c3ea`. Source comparison: Arora–Barak §1.4–§1.4.1, PDF pp. 45–47, and §1.5–§1.5.1, PDF pp. 48–49. I derived the restatements from comment-stripped declarations, then compared their docstrings, the attached round-1 findings, the project policy, and the book. This is a mathematical statement/interface audit. Lean and Lake were unavailable; no elaboration, repository diff, or completed Lean proof of the construction sorries is claimed.

Arguments A and B no longer refute the repaired statements. I found no new blocker or major in the changed declarations. Two minor corrections remain: explicitly handle the simulated input's left boundary in the universal-machine sketch, and correct the brief's description of the order of `Nat.bits`. The evaluator provides the semantic interface needed for the two specified phase-4 arguments. The machine constructions and the guarded-composition proof described below remain obligations; this report does not certify their completion.

For the restatements, `ComputesInTime x w t` means *halted by time t with completed output w*, not first halting at exactly t. Write `M(x) ↓ w` for `∃ t, M.ComputesInTime x w t`, and put `Mα := (c.decode α).toFinTM`. In descriptions of bit formats, `0` and `1` mean `false` and `true`.

Blind restatements of the changed/new declarations follow.

| Declaration | Restatement |
|---|---|
| `signBits` | Head moves negative, zero, positive are encoded respectively by `11`, `00`, `10`. These are distinct fixed-length fields. |
| `optBoolBits` | No bit, bit `false`, bit `true` are respectively `00`, `10`, `11`. |
| `optOptBoolBits` | No write, write blank, write `false`, write `true` are respectively `00`, `01`, `10`, `11`. In particular, leaving a cell unchanged differs from writing blank. |
| `unaryFin` | State index `j` is encoded as `j` ones followed by zero, namely `1^j 0`. The type-level bound is not itself serialized here. |
| `optStateBits` | Halting successor is `0`; live successor index `j` is `1^(j+1) 0`. |
| `actionBits` | Concatenates, in order: input movement, work-tape write, work-tape movement, optional output bit, optional successor state. The first four fields occupy eight bits; the last is self-delimiting. There is exactly one work tape. |
| `CodeTM.serialize` | First encodes `Nat.bits M.numStates` in the doubled, delimited first component of `pairEncode`. Its remaining component is the unary initial state followed by the complete transition table. There are `M.numStates + 1` live states, and `9 * (M.numStates + 1)` records, ordered by increasing state, then input symbol, then work symbol; each symbol order is blank, `false`, `true`. Halting is a separate optional successor, not an additional live state. The serialization includes unreachable states and every action field. |
| `EffectiveMachineCode` | Extends the padded round-trip scheme `MachineCode` with one finite Boolean machine, a natural-valued length bound, and a proof that on every string `α` this machine halts with exactly `(decode α).serialize` by `canonizerTime α.length`. No computability of the supplied `encode`, monotonicity of the bound, or polynomial bound is required. |
| `exists_effectiveMachineCode` | At least one structure satisfying all those algebraic and machine-computation requirements exists. The theorem does not additionally assert a particular parser, a polynomial bound, or the computability of its encoder. Those are features proposed in its sketch. |
| `pairEncode_injective` | Equality of two paired strings implies equality of both ordered components. This is an injectivity proposition, not itself a theorem that a particular finite machine parses pairs. |
| `universal` | For each effective scheme there is one finite Boolean `U`. For every string `α`, one constant `C` works for every `x,w,t`: if `Mα` halts by `t` with `w`, then `U` on `pairEncode α x` halts with `w` by `C * (t+1)`. Conversely, every completed output of that `U` run is a completed output of `Mα` on `x`. This covers all representations, not only `c.encode` values. |
| `universal_quadratic` | There is one `U` such that whenever any finite Boolean machine computes a total string function `f` within a length bound `T`, there exist `α,C` such that `U` on `pairEncode α x` computes `f x` by `C * (T x.length + 1)^2` for every `x`. Its proposition does not constrain `c.decode α` or identify its witness with a separately chosen witness of `universal`. |
| `timed_universal` | There is one finite Boolean `U`, with a constant for each string `α`, uniform over inputs and budgets. On `pairEncode (pairEncode (Nat.bits t) α) x`, it halts by `C * (t+1)^2`. It returns `true :: w` if `Mα` halts by `t` with `w`, and `[false]` if no output satisfies that deadline. These cases are exhaustive. No behavior is specified on strings outside this encoded-input form. |

The findings table uses the brief's severity definitions. “Note” rows record the disposition of the former blockers/majors and the precise remaining scope; they are not approvals of unfilled proofs.

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | note | `Encoding.lean · CodeTM.serialize`, `EffectiveMachineCode` | Round-1 Argument A is excluded. The fixed format determines the full coded machine, and its effective computation prevents the noncomputable permutation. | Argument A below proves unique parsing and gives a total decision procedure for the alleged undecidable set if the permuted scheme had a canonizer. An arbitrary `canonizerTime` does not evade the contradiction. | Retain the scheme-independent target. During proof filling, expose a parser/serialization round-trip and derive injectivity from it. |
| 2 | note | `Universal.lean · universal`, `universal_quadratic`, `timed_universal` | Round-1 Argument B is excluded by the code-first layouts. No scan of the input suffix is needed for startup. | Argument B bounds prefix lengths by `2*α.length+2` and `4*(Nat.bits t).length+2*α.length+6`. The old timed budgets `0` and `1` already differ at the first input bit. The absorption arithmetic does not require `x.length ≤ t`. | Retain the layouts and their documented deviation from the book. Prove startup locally in the prefix length. |
| 3 | minor | `Universal.lean · universal` proof sketch; inherited by `timed_universal` | The sketch should explicitly emulate the simulated input's left blank and clamping. Moving the physical head over the suffix verbatim is insufficient by itself. | From the first bit of nonempty `x`, one simulated left move reaches a blank for `Mα`, but reaches the last delimiter bit `true` on the physical paired input. A machine branching on that blank distinguishes the two executions. Further left moves must also stay at the virtual boundary. See Argument B. | Add a boundary marker on a spare work tape whose head tracks the simulated input position. At virtual position zero, supply blank and suppress outward moves. Explain the empty-input case. This costs constant work per simulated step and does not change the statements. |
| 4 | note | `Universal.lean · universal` converse | The converse is the correct completed-output/divergence condition and is consistent with the forward bound. | Argument C derives equality of the two halting/output relations. If `Mα` diverges, `U` cannot halt even with `[]`. Intermediate emissions on a nonhalting run are unconstrained. | No statement change. Read “output produces” in the docstring as “completed output on halting”; use the latter wording when exposing this interface downstream. |
| 5 | note | `Encoding.lean · EffectiveMachineCode`, `MachineCode` | Total canonization and arbitrary length bounds cause no new simulation pathology. Constant decoding and the identically zero canonizer bound are excluded. | Every input must halt; finite maxima give a length bound for any total transducer. The bound is not an oracle used by the simulator. The round trip makes `decode` surjective, so it cannot be constant. Initialization rules out halting at time zero. See Argument D. | No added monotonicity or computability requirement on `canonizerTime` is needed for these theorems. |
| 6 | note | `Universal.lean · universal` constant `C` | Dependence on the representation `α` is a genuine, documented weakening of the book's machine-parameter bound. It is necessary for this general interface. | Argument E gives an effective scheme with arbitrarily long, identical-prefix representations of two fixed one-step machines. Constants factoring only through `decode α` would reproduce the indistinguishability contradiction. | Keep the representation-dependent constant. Obtaining the book's more restrictive dependence requires further representation/decoding assumptions. |
| 7 | note | `Universal.lean · universal_quadratic` | The total-function labeling resolves the misleading scope of the old attribution; the corrected layout makes its bound plausible. The scheme/code association remains absent from the proposition. | Argument B gives `C = C_U*(c₁+1)` after normalization. `c` remains unused in the conclusion's syntax; choosing a witness through `universal` is a proof construction, not an exported association. Arbitrary partially computing multitape machines are not covered by this corollary. | No phase-4 blocker. If downstream proofs need a named evaluator or a semantically identified code, state a lemma for a specified evaluator satisfying `universal`, or add the corresponding conjunct. |
| 8 | note | `Encoding.lean · exists_effectiveMachineCode` sketch | The proposed serialization now records the initial state and supports the padded exact round trip. A total polynomial parser is possible. | The grammar in Argument A determines the end of the table. A parser can check symbol codes, state ranges, record count, and the trailing all-true suffix. A huge binary state count must be rejected without enumerating exponentially many missing records. | Make short-circuit failure or a length check explicit when implementing the polynomial sketch. Validate canonical binary count syntax if retaining “identity up to padding removal” for every accepted code. The existential statement itself requires only some bound. |
| 9 | note | `Universal.lean · timed_universal` | Budget zero and deadline-inclusive success are coherent, including an empty clock region and empty successful output. | `Nat.bits 0 = []` gives an immediate inner delimiter, not an absent field. `not_computesInTime_zero` forces timeout; first halting exactly at `t` satisfies the success premise. `[false]` and `true :: w` never coincide. | Retain the predicates, tags, and the explicit after-transition halting check. |
| 10 | note | Phase 4; `universal`, `timed_universal`, `Composition.lean · computesFunInTime_comp` | The repaired evaluator is semantically sufficient for UC and the book's assumed-HALT-decider-to-UC construction; computability of the supplied `encode` is unnecessary. A guarded machine-construction lemma is still needed. | Argument F fixes one code in diagonalization and uses only `α ↦ pairEncode α α` in the reduction. The existing composition theorem assumes both component functions total, so it cannot directly be applied to the partial evaluator on all inputs. | In phase 4, construct guarded simulation with buffered intermediate output, or prove a suitable partial/guarded composition lemma. Compare the entire completed output with `[true]`. No strengthening of `EffectiveMachineCode` is needed for these two arguments. |
| 11 | minor | Re-audit brief · specific question 1 | “No leading `false`s” is inaccurate if “leading” means the front of the list. `Nat.bits` is least-significant-bit first. | `Nat.bits 2 = [false,true]`; nonzero canonical lists end in `true`. This creates no collision because doubled fields are delimited in aligned pairs. See the [Mathlib documentation for `Nat.bits`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Nat/Bits.html#Nat.bits). | Say “least-significant-bit first, with no redundant most-significant zeros; `Nat.bits 0 = []`.” No Lean declaration change. |
| 12 | note | Supplied snapshot and build/history attestations | This audit does not establish proof completion, historical signature identity, or successful elaboration. | The 16 attached Lean modules contain 14 literal construction/proposition sorries: eight earlier ones and six current phase-3 ones. No additional literal `axiom`, `admit`, `sorryAx`, or `unsafe` appeared in the comment-stripped scan. Raw build/axiom logs and an independently checked baseline diff are absent. | Keep those claims as repository attestations. Supply exact diffs and elaborated axiom/build evidence for any future audit of proof completion. |

Argument A, rerun: serialization and the noncomputable permutation.

Unique parsing proceeds in a fixed order.

1. In the doubled count region, aligned blocks `00` and `11` are data and the first aligned `01` is the delimiter. Therefore equal serializations have equal count-bit lists. Binary reconstruction recovers the natural number, so their `numStates` values agree. The empty bit list encodes count zero and immediately encounters the delimiter. An unaligned `01` across doubled data is irrelevant.
2. The initial-state field ends at its first zero. Its preceding number of ones uniquely recovers the initial-state index. It cannot consume part of the table under a second valid parse.
3. Each action starts with four two-bit fields. All codes within each field's dictionary are distinct. The successor field ends at its first zero: zero preceding ones means halt, and `j+1` preceding ones means live state `j`. Thus each valid record has one parse and one ending position.
4. There are exactly `9*(numStates+1)` records. Induction over this fixed number recovers the whole table. The enumeration is exhaustive: every function `Fin 1 → Option Bool` is constant and is determined by its value at `0`. Equality of the parsed records therefore gives pointwise equality of transition functions, and then function extensionality gives equality of those functions.
5. Equal count, equal initial state, and equal transition function give equality of `CodeTM` values. Thus

\[
M.\mathrm{serialize}=N.\mathrm{serialize}\quad\Longrightarrow\quad M=N.
\]

The same parse shows that complete serializations are prefix-free: once the equal count, initial state, and fixed number of records have been consumed, both complete serializations end together. This is a property of `serialize`; arbitrary `pairEncode` outputs are not prefix-free because their second components are verbatim. Consequently a valid complete serialization has an unambiguous boundary before true-padding.

Now reuse the exact family and permutation from round 1. Let `A` be undecidable, let `Hₙ,ᵦ` have `n+2` live states and immediately output bit `b`, and let `p` swap `Hₙ,₀` with `Hₙ,₁` precisely for `n ∈ A`. For an ordinary effective scheme `c₀`, put

\[
c.\mathrm{encode}(M)=c_0.\mathrm{encode}(pM),\qquad
c.\mathrm{decode}(\alpha)=p(c_0.\mathrm{decode}(\alpha)),\qquad
\alpha_n=c_0.\mathrm{encode}(H_{n,0}).
\]

The old padding calculation still proves that `c` is a `MachineCode`. If it extended to `EffectiveMachineCode`, its canonizer would halt on every `αₙ`, and

\[
\begin{aligned}
\mathrm{canonizer}(\alpha_n)\downarrow H_{n,1}.\mathrm{serialize}
&\iff (pH_{n,0}).\mathrm{serialize}=H_{n,1}.\mathrm{serialize}\\
&\iff pH_{n,0}=H_{n,1}\\
&\iff n\in A.
\end{aligned}
\]

Here the first equivalence uses the canonizer contract and uniqueness of completed outputs of a deterministic machine. The input `αₙ`, the comparison string, and equality of finite bit lists are computable. Running the canonizer until it halts and doing this comparison would decide `A`. Its promised time bound need not be known or computed. Hence this extension cannot exist.

For contrast, canonization into the scheme's own encoding would cancel the permutation:

\[
c.\mathrm{encode}(c.\mathrm{decode}(\alpha))
=c_0.\mathrm{encode}(p(p(c_0.\mathrm{decode}(\alpha))))
=c_0.\mathrm{encode}(c_0.\mathrm{decode}(\alpha)).
\]

This confirms why the fixed, effectively parseable target is essential. Injectivity of a wholly arbitrary target map alone would not supply an effective inverse; here the concrete grammar does.

For the existence sketch, a parser can first reject a state count for which even the minimum record length exceeds the available input, or simply stop at the first incomplete record. It need not perform an exponential loop on a short malformed string declaring exponentially many states. On accepted canonical strings it can validate and copy the serialization prefix, discard the true-padding, and otherwise return the fixed fallback serialization. These are finite-string algorithms supporting the sketch; their realization as an in-model `FinTM` remains unproved in this packet.

Argument B, rerun: input access and the time bounds.

For the ordinary evaluator, the prefix preceding `x` has length

\[
2|\alpha|+2.
\]

Increasing `|x|` no longer moves a differing code beyond a fixed execution deadline. Parsing this prefix, running the canonizer on a buffered copy of `α`, and preparing its finite table cost some `Sα` independent of `x`. Let `Rα` bound one simulated step, including table lookup and input-boundary bookkeeping. Then

\[
S_\alpha+R_\alpha t
\le S_\alpha(t+1)+R_\alpha(t+1)
=(S_\alpha+R_\alpha)(t+1).
\]

This accounts for startup without assuming that the simulated computation reads its entire input. It applies to the original one-step constant-output counterexamples as well.

The boundary bookkeeping is real work missing from the short sketch. For nonempty `x`, a machine can move left once and then output `false` on blank and `true` otherwise, halting. It outputs `false` on its own input; a naive physical-head simulation at the paired delimiter outputs `true`. A separate marker tape, initialized with a mark for virtual input position zero and moved with the simulated input head, identifies the left blank. Supply blank at that mark and clamp left moves there. At the right blank use the actual input blank and clamp outward moves. For empty `x`, initialization is at the right blank adjacent to the marked virtual left blank. This repairs the simulation with constant work per step and no scan of `x`.

For the quadratic corollary, normalization provides a coded total-function machine with bound `c₁*(T n+1)^2`. Applying the forward evaluator with its code gives

\[
\begin{aligned}
C_U\bigl(c_1(Tn+1)^2+1\bigr)
&\le C_U\bigl(c_1(Tn+1)^2+(Tn+1)^2\bigr)\\
&=C_U(c_1+1)(Tn+1)^2.
\end{aligned}
\]

The inequality uses `(T n+1)^2 ≥ 1`. Thus `C := C_U*(c₁+1)` suffices; no input-length startup term is missing.

For the timed machine, expanding the two pairings gives prefix length

\[
2\bigl(2|\mathrm{Nat.bits}(t)|+2+|\alpha|\bigr)+2
=4|\mathrm{Nat.bits}(t)|+2|\alpha|+6.
\]

Again it is independent of `x`. For `t=0` the nested prefix begins `0011`; for `t=1` it begins `11110011`. The two runs used in the old timed contradiction can now distinguish their budgets immediately.

Clock processing costs a constant multiple of `(t+1)(|Nat.bits t|+1)`, output buffering/flushing a constant multiple of `t+1`, and code processing a fixed cost for each `α`. Since `|Nat.bits t| ≤ t+1`, all fit within `Cα*(t+1)^2` after enlarging `Cα`. At `t=0` there is still a delimiter and a positive timeout execution allowance. These are bound checks for the intended construction, not a completed formal simulator proof.

Argument C: the converse and divergence.

Fix the evaluator supplied by `universal`. Its forward implication and converse give, for every `α,x,w`,

\[
\begin{aligned}
M_\alpha(x)\downarrow w
&\Longrightarrow \exists t,\ U.\mathrm{ComputesInTime}
  (\mathrm{pairEncode}\ \alpha\ x)\ w\ (C(t+1))\\
&\Longrightarrow U(\mathrm{pairEncode}\ \alpha\ x)\downarrow w,\\
U(\mathrm{pairEncode}\ \alpha\ x)\downarrow w
&\Longrightarrow M_\alpha(x)\downarrow w.
\end{aligned}
\]

Consequently

\[
\neg\exists w,\ M_\alpha(x)\downarrow w
\iff
\neg\exists w,\ U(\mathrm{pairEncode}\ \alpha\ x)\downarrow w.
\]

Every halted configuration has some finite output list, so the right side means that `U` never halts. A diverging run may emit no bits, some finite prefix, or infinitely many bits; the statement does not constrain those emissions. In particular it permits *never emitting and never halting*, but excludes *halting with empty output* as a response to divergence. This matches equality of partial string functions in Theorem 1.9.

Argument D: totality, bounds, and degenerate schemes.

The canonizer contract is stronger than effective evaluation alone: it recovers exact syntax, including unreachable states. This deliberate sufficient hypothesis can exclude schemes whose behavior is effectively evaluable but whose irrelevant syntactic data is not. It is consistent with the concrete format and existence sketch.

A total finite-string transducer has only finitely many inputs of each fixed length. The maximum of their halting times exists, giving a length bound. Indeed a computable bound can be obtained by running the transducer to completion on each such input and taking the maximum; the chosen `canonizerTime` field need not be that bound. No time-constructibility assumption is needed. During universal simulation the canonizer is run until it halts; `canonizerTime` is used only in the mathematical bound.

The algebraic round trip gives both

\[
c.\mathrm{encode}(M)=c.\mathrm{encode}(N)\Longrightarrow M=N,
\qquad
\forall M,\ \exists\alpha,\ c.\mathrm{decode}(\alpha)=M.
\]

The second statement, applied to the distinct constant-output machines, directly rules out a constant decoder. Encoder injectivity alone would not be the correct standalone reason for that exclusion. For every length `n`, apply `canonizer_computes` to the all-false string of length `n`. If `canonizerTime n=0`, this contradicts `not_computesInTime_zero`. Therefore an identically zero bound, or even a bound vanishing at one length, cannot inhabit the structure.

Argument E: why a machine-dependent constant cannot replace the code-dependent one.

Construct an effective scheme as follows. Canonical codes are `false :: c₀.encode M`, decoded through an ordinary effective scheme after removing the initial `false`. For strings beginning with `true`, inspect the last bit of the remaining string and return the fixed one-step machine `H₀` or `H₁` according to that bit, using a fixed default for an empty remainder. Use a fixed fallback on the empty overall string. Canonization is total and effective, and the canonical codes retain the padded round trip.

In this scheme the strings

\[
\beta_{n,b}=[\mathrm{true}]\mathbin{++}[\mathrm{false}]^n\mathbin{++}[b]
\]

denote `Hᵦ`. Suppose the evaluator's constant factored through the denoted machine. Write `C₀,C₁` for its constants on those two machines and let `B := max(2*C₀,2*C₁)`. Choose `n>B`. The evaluator inputs `pairEncode βₙ,₀ []` and `pairEncode βₙ,₁ []` have the same length and the same first `2*(n+1)` bits. The initialized input head cannot reach their difference within `B` steps. Induction over steps therefore gives equal states, work tapes, heads, and emitted outputs through that time. Both would have to halt by `B`, with different outputs. Contradiction.

Thus the repaired quantifier order is appropriate for all `EffectiveMachineCode` values. It should not be described as recovering the literal constant dependence of Theorem 1.9 for arbitrary representations.

Argument F: what phase 4 can now prove, and what still needs construction.

Use the book's diagonal definition in the present output convention:

\[
\mathrm{UC}(\alpha)=\mathrm{false}
\iff M_\alpha(\alpha)\downarrow[\mathrm{true}].
\]

The complementary value is `true`, including divergence and every completed output other than the singleton `[true]`.

Assume a finite Boolean machine computes this total Boolean function, with singleton outputs. The existing total-function normal-form theorem and `exists_codeTM` provide a coded machine `N` computing the same function. If computability is initially defined with only a halting time for each input, take the finite maximum of those times at each input length to obtain the bound needed by that normal-form theorem. Fix

\[
\alpha:=c.\mathrm{encode}(N),\qquad c.\mathrm{decode}(\alpha)=N.
\]

Using deterministic uniqueness of completed outputs and total correctness of `N`,

\[
\mathrm{UC}(\alpha)=\mathrm{false}
\iff N.\mathrm{toFinTM}(\alpha)\downarrow[\mathrm{true}]
\iff \mathrm{UC}(\alpha)=\mathrm{true},
\]

which is impossible for a Boolean. This is selection of one fixed code inside a mathematical contradiction, not a runtime computation of `encode`.

For the book's HALT argument, suppose a total halting decider exists. On input `α`, a constructed machine can do the following:

1. Construct `pairEncode α α` and run the supposed HALT decider on it, buffering the answer.
2. If its answer is false, emit `[true]` and halt. By correctness of HALT, no completed output of `Mα(α)` exists, so this is the value of UC.
3. If its answer is true, run the all-string evaluator on that same pair, buffering its emissions. HALT correctness supplies a halting time for `Mα(α)`; the evaluator's forward clause ensures this run terminates with exactly its output.
4. After termination, emit `[false]` precisely when that entire output equals `[true]`; otherwise emit `[true]`.

The two branches establish termination and the UC value on every input. No step computes `encode(decode α)`, or the encoding of a machine depending on `α`. The timed evaluator also supports a variant that searches budgets until success after a positive HALT answer.

What is still needed is an in-model realization of this guarded sequencing and output buffering. `computesFunInTime_comp` alone cannot be invoked with the partial evaluator as its second total function. The paired-input boundary wrapper and prefix-local startup bound likewise need machine-level implementation, not merely the existing total-function composition bound in the whole input length. These are construction/API lemmas to supply; they reveal no false statement or additional encoding-effectivity requirement for the specified phase-4 arguments.

This scope matters: the total-function normalization results suffice for the hypothetical UC decider, which is total. They do not yet supply a representation-preserving compiler for every partially computing multitape machine, nor do the separately existential universal theorems identify a globally chosen evaluator. Later results needing those interfaces should state them explicitly.

Verification limits: the current scan finds the phase-3 sorries `pairEncode_injective`, `exists_effectiveMachineCode`, `exists_codeTM`, `universal`, `universal_quadratic`, and `timed_universal`, plus the eight earlier machine-construction sorries named in the attached round-1 report. The concrete semantics of initialization, absorbing halting, input clamping, output accumulation, and the total-function composition/normal-form statements were inspected where used above. No claim is made to have re-audited every supporting tactic proof. The supplemental `Nat.bits` documentation is not an independent check of the repository's pinned Mathlib build.

Notation glossary: `M(x) ↓ w` means that finite machine `M` halts on `x` with completed output `w`; `Mα` is `(c.decode α).toFinTM`; `|x|` is list length; `++` is list concatenation; `1^j 0` is `j` true bits followed by false, and `[b]^n` repeats bit `b` exactly `n` times. `A,p,c₀,Hₙ,ᵦ,αₙ` are the undecidable set, swapping permutation, ordinary effective scheme, constant-output family, and ordinary family codes from round-1 Argument A. `Sα,Rα` bound startup and one simulated step. `C_U,c₁,C,Cα,C₀,C₁` are natural-number runtime constants. `H₀,H₁` in Argument E are fixed one-step constant-output machines; `βₙ,ᵦ` are their reserved representations; `B` is their proposed common deadline. `N` is the coded hypothetical UC decider; `UC` is the diagonal Boolean function and `HALT` its assumed halting-decider subroutine. Other identifiers are those of the audited declarations.
