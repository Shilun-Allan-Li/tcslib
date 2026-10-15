**Input SHA-256:** `37d2fd94ac5539a756cbba23c826a21882449a3bc4d10c3da0131446f8421281` — independently recomputed, exact match.

**Gate position: PASS — 0 blockers / 0 majors / 2 minors / 4 notes.**

The bundle contains exactly **19 attachments**. I audited all **19 definitions/structures**, **10 sorried theorem statements**, and **nine declared skeleton-time proved statements** in the five named files. `ClassOracle.lean` introduces no declarations; its imports and description match the scoped surface. The raw chapter-1 oracle model remains frozen context. This is a statement audit with mathematical construction arguments, not a completion or independent kernel verification of the deferred Lean proofs.

Source comparison used the published [AB09, §3.4, Definitions 3.4–3.5 and Example 3.6(1)–(2), pp. 73–74](https://theswissbay.ch/pdf/Gentoomen%20Library/Theory%20Of%20Computation/Sanjeev_Arora%2C_Boaz_Barak-Computational_complexity__a_modern_approach-Cambridge_University_Press%282009%29.pdf#page=99), and, for the clock convention only, [BGS75, p. 432](https://cse.ucdenver.edu/~cscialtman/complexity/Relativizations%20of%20the%20P%3DNP%20Question%20%28Original%29.pdf#page=2). AB09 specifies a membership-answer step through three special states and defines the two classes by polynomial-time oracle machines. Its first two examples are complementing SAT and eliminating a polynomial-time oracle. BGS75 explicitly bounds computations under every oracle and explains the clock transformation. The class comparison below is my mathematical assessment of the attached code.

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | minor | `ClassOracle/Classes.lean` · module docstring, line 27 | The unrelativized identity is written `NP = ⋃ c, NTIME (n^c)`. | Under the attached exact-budget definitions, every positive exponent gives an empty class because its budget vanishes on the empty input. The displayed union therefore equals `NTIME (fun _ => 1)`, which does not contain the language of strings containing `true`, although that language is in P. The actual `NPOracle` definition correctly includes `+1`. | Write `NP = ⋃ c, NTIME (fun n => n^c + 1)`. No definition or theorem signature needs alteration. |
| 2 | minor | `ClassOracle/Classes.lean` · `POracle_eq_P_of_mem_P`, sketch, lines 167–179 | The sketch gives query cost `O(d·(q+1)^e)` and total exponent `k·e + O(1)` without an explicit query-count or tape-restoration ledger. | With total oracle time `t = c(n^k+1)`, there can be `t` queries, each of length at most `t`; the decider calls alone give the upper bound `O(d·t·(t+1)^e)`, hence degree `k(e+1)`. Head positioning, virtual-input preparation, and scratch cleanup also need accounting. If the displayed `O(1)` may depend on `k`, its exponent is not literally false, but it conceals the missing dependence. The theorem asserts only membership in P and remains true. | State the query-count factor and preservation/reset obligations, and ensure the virtual input contains only the extracted prefix, with blanks outside it. One sufficient ledger is `O(t + t(t+1+d((t+1)^e+1)))`, absorbed by degree `k(1+max(1,e))`; a looser explicit polynomial is also sufficient. See calculation below. |
| 3 | note | `Classes.lean` · `DTIMEOracle`, `NTIMEOracle`, `POracle`, `NPOracle` | Bounds relative to the specified oracle give the intended polynomial classes. | Adding an independent polynomial timeout preserves the original computation under that oracle and forces termination under every oracle, with polynomial overhead. This reconciles the class definitions with BGS75's stronger machine-level convention. It does not transfer exact timed bounds. | Retain the definitions. P3.2 must justify its own extrinsic-budget/clock coverage; that implementation is outside this bundle. |
| 4 | note | `SATOracle.lean` · all three statements | Set complement and the SAT fallback cause no wrong-language result here. | On parse failure the decoded empty CNF is satisfiable, so the input belongs to SAT and is excluded from its complement. On valid encodings the complement is precisely unsatisfiability. The other corollaries use exactly the quoted `SAT_NPHard` interface and complement closure. | None. Retain the declared fallback convention. |
| 5 | note | `OracleFinite.lean`, `OracleNondeterministic.lean` · nine proved statements | The declared mirrors have the claimed scope, including the plain-machine embedding under every oracle. | The run identities keep the oracle fixed; halting is absorbing; time monotonicity uses padding or prefix restriction. The plain embedding's fresh query states are unreachable from initialization, so its iff preserves the same input, output, and time bound for each oracle. | None. This is statement approval, not a fresh kernel replay. |
| 6 | note | Audit pack · sweep, lint, and revision attestations | Packet counts are verified; repository provenance and fresh-build claims have limited independent evidence here. | Source contains exactly 1/6/3 sorries in `OracleNondeterministic`/`Classes`/`SATOracle`. The sweep has the matching ten warnings, zero `error:` lines, five module markers, and a completion marker. Lint reports 0 FAIL/0 WARN for ClassOracle and 0 FAIL/8 size WARNs for TuringMachine, with no warning on either new oracle-machine file. The packet does not contain the Git objects, fresh oleans, build script, or axiom-print output; no Lean executable is available locally. | No statement repair. Treat build freshness, axiom closure, and byte identity between commits `edea2663` and `2cf44f1d` as maintainer attestations, not independently reproduced results of this audit. |

Reading the declarations directly gives the following blind restatements. All machine names in these tables are in namespace `Turing`; the four class names are in `Complexity`.

| File · definition | Blind restatement |
|---|---|
| `OracleFinite` · `FinOracleTM` | Data consisting of a natural number of ordinary work tapes, a state type with finite enumeration and decidable equality, a raw oracle machine on those tapes plus one query tape, and a proof that query/yes/no states are pairwise distinct. The initial state need not differ from those states. |
| `OracleFinite` · `FinOracleTM.ComputesInTime` | Starting from the raw initialized configuration, iteration with this oracle for exactly `t` steps ends halted with exactly the specified output. Absorption of halting makes this “within `t`.” |
| `OracleFinite` · `FinOracleTM.DecidesInTime` | For every binary input `x`, that computation predicate holds at `T x.length`, with singleton output equal to the indicator of membership in `L`. The promise concerns the single supplied oracle `O`. |
| `OracleFinite` · `FinTM.toFinOracleTM` | Adjoin three fresh states to the plain finite machine, add an unused query tape, and run the original transition table on the original states. The extra states supply the well-formedness field. |
| `OracleNondeterministic` · `OracleNDTM` | A raw machine with an initial state, three designated oracle states, and two total action-selection functions on the input symbol and the symbols under all `k+1` work heads. Neither finiteness nor special-state distinctness is imposed at this raw layer. |
| `OracleNondeterministic` · `OracleNDTM.WellFormed` | Exactly three inequalities: query differs from yes, query differs from no, and yes differs from no. There is no condition on the initial state. |
| `OracleNondeterministic` · `OracleNDTM.stepWith` | A halted configuration is unchanged. A live query state changes only to yes/no according to membership of `OracleTM.queryString cfg`; the supplied bit is ignored. Every other live state applies the action chosen by that bit. |
| `OracleNondeterministic` · `OracleNDTM.initCfg` | The shared initialization at `q₀`: blank ordinary and query tapes, heads at their initial positions, and empty output. |
| `OracleNondeterministic` · `OracleNDTM.runWith` | Fold `stepWith` over a finite Boolean word, from left to right, using one list element for each step, including query steps and padding after halting. The empty word is the identity. |
| `OracleNondeterministic` · `OracleNDTM.HaltsWithin` | Every Boolean word of length exactly `t`, run from initialization with the fixed oracle, leaves the state `none`. It is a condition on all branches, independent of their outputs. |
| `OracleNondeterministic` · `FinOracleNDTM` | Bundle a raw nondeterministic oracle machine with its ordinary-tape count, finite decidable state type, and the three distinctness proofs. Its alphabet remains a parameter. |
| `OracleNondeterministic` · `FinOracleNDTM.AcceptsWithin` | Some Boolean word of length exactly `t` leaves the initialized binary machine halted with output exactly `[true]`. This predicate alone does not require other branches to halt. |
| `OracleNondeterministic` · `FinOracleNDTM.DecidesInTime` | For every input, all branches halt at the prescribed budget, and membership in `L` is equivalent to existence of an accepting branch at that budget. Nonaccepting halted branches may have any output other than `[true]`. |
| `OracleNondeterministic` · `OracleTM.toOracleNDTM` | Keep all four named states and all tapes; use the deterministic transition function for both choice bits. |
| `OracleNondeterministic` · `FinOracleTM.toFinOracleNDTM` | Apply that raw embedding while retaining the state type, finite instances, ordinary-tape count, and distinctness proofs. |
| `Classes` · `DTIMEOracle` | Languages for which there exist a single natural constant `c` and a finite well-formed deterministic oracle machine deciding every input within `c*T n`, with the oracle fixed. Neither witness may vary with the input. |
| `Classes` · `NTIMEOracle` | The same existential constant and machine quantification, with nondeterministic decision: all-branch termination and existential acceptance under the fixed oracle. |
| `Classes` · `POracle` | Union over natural exponents of `DTIMEOracle O (fun n => n^c+1)`. The time class separately absorbs a multiplicative constant. |
| `Classes` · `NPOracle` | Union over natural exponents of the corresponding `NTIMEOracle` classes. It is a machine definition and asserts no relativized verifier characterization. |

There is no hidden infinite-machine advantage: the classes fix the alphabet to Bool and quantify over the finite bundles. Allowing zero ordinary tapes still leaves the designated query tape; allowing any finite number of ordinary tapes avoids a restriction of the polynomial classes. The inherited persistent-tape convention is used consistently. No new statement transfers an exact time bound to an auto-erasing oracle model. Output-based acceptance and arbitrary nonaccepting outputs inherit the chapter-2 convention and do not trivialize nondeterministic decision, because all-branch termination remains mandatory.

Each sorried statement has the following independent mathematical justification. The low-level host constructions described here remain Lean fill obligations.

| Sorried declaration | Assessment and true-as-stated argument |
|---|---|
| `OracleTM.toOracleNDTM_runWith` | **True.** One embedded nondeterministic step equals the deterministic oracle step for either bit, separately in the halted, query, and ordinary cases. Induction on the choice word therefore gives equality with `runFrom` at its length, for every starting configuration. Well-formedness is unnecessary for this identity because both sides use the same special states even when they collide. |
| `P_subset_POracle` | **True.** Take the plain P witness and apply `FinTM.toFinOracleTM`. Its proved computation iff transfers the indicator output at every input with the same multiplicative constant and polynomial exponent. |
| `POracle_subset_NPOracle` | **True.** Duplicate the deterministic transition function. Every word of the chosen budget has the deterministic final configuration, hence all branches halt; a word of that length always exists, and it accepts exactly when the deterministic output is `[true]`. |
| `mem_POracle_of_polyTimeReducible` | **True.** In the reduction machine, redirect each emitted bit to the next cell of a fresh query tape, suppress physical output, and replace the halting transition by entry into a fresh query state. The query is exactly `f x`, including when `f x=[]`; one answer step and one output-and-halt step suffice after the simulated reduction halts. The reduction's polynomial running time therefore gives a polynomial oracle decider, and `x∈L ↔ f x∈O` gives correctness without any computability assumption on `O`. |
| `oracle_mem_POracle` | **True.** The identity function is a polynomial-time reduction from any oracle language to itself. Apply the preceding statement; undecidability of the oracle is no obstruction. |
| `compl_mem_POracle` | **True.** An especially direct construction maps each emitted Boolean to its negation while leaving states, query tape, and all other actions unchanged. The simulated run has the same control and tapes, and its final output is the pointwise negation of the original singleton indicator; it therefore decides the complement at the same budget. The proposed capture wrapper is also viable, but unnecessary for the statement. |
| `POracle_eq_P_of_mem_P` | **True.** Inclusion of P follows from the first class theorem. For the reverse direction, suspend the oracle machine at each query, run the plain polynomial-time oracle decider on a faithful virtual or copied query input, suppress its output, restore the suspended configuration, and resume in the appropriate answer state. The query-length bound, at most one query per simulated step, and the explicit polynomial calculation below show that this remains in P; finding 2 concerns the sketch's ledger. |
| `compl_SAT_mem_POracle_SAT` | **True.** Apply `oracle_mem_POracle` to SAT and then deterministic oracle complement closure. Since failed parses decode to a satisfiable formula, those strings are correctly rejected by the complemented oracle decider. |
| `NP_subset_POracle_SAT` | **True, using the quoted imported theorem.** Unfolding `NPHard SAT` gives `L≤ₚSAT` for each `L∈NP`. The general one-query workhorse yields the desired membership. |
| `coNP_subset_POracle_SAT` | **True.** The attached definition gives `L∈coNP ↔ Lᶜ∈NP`. Apply the preceding inclusion to `Lᶜ`, then complement closure and `(Lᶜ)ᶜ=L`. |

The nine declared proved statements also pass individually:

| Proved declaration | Exact content and check |
|---|---|
| `FinTM.toFinOracleTM_computesInTime` | For any oracle, input, output, and budget, the initialized embedded computation holds iff the original plain computation holds. This concerns reachable embedded configurations; it does not assert oracle independence from arbitrary adjoined query states. |
| `OracleNDTM.runWith_nil` | The empty word leaves every starting configuration unchanged. |
| `OracleNDTM.runWith_cons` | Run one step under the head bit, then run the tail word with the same oracle. |
| `OracleNDTM.runWith_append` | Running concatenated words equals running the first, then the second from the reached configuration, with the oracle unchanged. |
| `OracleNDTM.stepWith_of_halt` | Any bit and any oracle leave a configuration whose state is `none` unchanged. |
| `OracleNDTM.runWith_of_halt` | The same invariance holds for an arbitrary choice word. |
| `OracleNDTM.HaltsWithin.mono` | All-branch halting at `t` implies it at `t'≥t`: take the length-`t` prefix of each longer word and use absorption. |
| `FinOracleNDTM.AcceptsWithin.mono` | An accepting word at `t` extends to one at `t'≥t` by appending `t'-t` false bits; haltedness and `[true]` output persist. |
| `OracleTM.toOracleNDTM_wellFormed` | The three distinctness inequalities transfer unchanged through the deterministic-to-nondeterministic embedding. |

For the six numbered questions in the brief:

1. **Definition fidelity.** The restatements above implement the specified oracle transition and polynomial deterministic/nondeterministic decision semantics. Bundling well-formedness prevents degenerate special-state collisions; the `k+1` layout reserves exactly one query tape. Neither changes the intended polynomial classes, and persistent queries are used only within the frozen convention. The fixed-oracle clock split is sound: attach a timeout for the witness's polynomial budget, increasing the host polynomial if necessary to account for clock setup and simulation; capture output so a timeout can emit a clean rejection. This wrapper agrees with the witness under the target oracle and terminates under every oracle; no universal-oracle quantifier must be added to these class definitions. The clock's correctness promise is still about the target language under the target oracle, not about computing that same language under all oracles.

2. **Consume-and-ignore.** No loss occurs for the named uses. Given a computation, insert an arbitrary bit at each query step and after an early halt to obtain a word of the time budget; conversely, the ignored bits cannot affect a query answer. An oracle-aware certificate verifier simulates this schedule using its oracle; it does not need an oracle-free test of query answers. For the proposed P3.2 language, guessing a string followed by a query uses one extra ignored bit at the query, with the answer/output step budgeted normally; the deterministic stage construction does not consume nondeterministic words. Time-budget monotonicity follows from prefix restriction and padding, including the reverse acceptance implication when a smaller all-branch halting bound is known. This is not monotonicity under inclusion of oracle sets, which is false in general.

3. **Eliminating a P oracle.** The theorem statement has exactly the class-equality strength of Example 3.6(2). The current sketch supports a polynomial simulation but should expose the calculation and restoration details in finding 2. The calculation below handles growing and repeatedly reused queries, and exponent zero.

4. **Workhorse, complement, and SAT.** The workhorse is correctly stated for every oracle language, including undecidable ones. Well-formedness is a condition on the constructed machine, and is provided by fresh special states; it is not a condition on a set of strings. Its reduction is an ordinary polynomial-time many-one reduction. Complement closure is valid for deterministic oracle decision, and the three SAT deductions in the statement table use exactly the needed hypotheses. The direct capture construction also shows that truth of the workhorse does not depend on the concurrent §12 gate.

5. **Proved mirrors.** All nine statements pass as listed above. The “every oracle” iff is pointwise universal in the oracle with the same original and embedded machine, output, and budget. None of the run algebra assumes a larger budget or a special initial state, except where initialization is explicitly part of the predicate. In particular, the raw deterministic-to-nondeterministic identity is valid without well-formedness, whereas the class witnesses carry it.

6. **Degenerate cases.** All six requested cases were checked, together with the additional cases below. They reveal no defective in-scope definition or theorem. In particular, the zero-time convention agrees exactly with the attached DTIME and NTIME definitions.

Here is the explicit calculation for question 3, using the sketch's exponents and constants. Let the simulated oracle-time budget be

\[
t=c(n^k+1).
\]

At every query reached within the run, the query length is at most `t`, and there are at most `t` query steps. A straightforward fixed-machine simulation can spend `O(t+1)` per query to position heads, copy the prefix ending at the first blank onto a clean virtual-input tape, and restore the suspended query head. Running the decider and clearing its used work region costs `O(d((t+1)^e+1))` per query; the number of decider tapes is fixed, and each head moves at most one cell per step. Separate tapes preserve the suspended machine's state and tapes, while captured decider output determines only the yes/no resumption state. Thus

\[
\begin{aligned}
\text{simulation time}
&=O\!\left(t+t\left[t+1+d\bigl((t+1)^e+1\bigr)\right]\right)\\
&=O\!\left((t+1)^{1+\max(1,e)}\right),\\
t+1
&=c(n^k+1)+1\\
&\le (2c+1)(n+1)^k,\\
\text{simulation time}
&=O\!\left((n+1)^{k(1+\max(1,e))}\right).
\end{aligned}
\]

For `e≥1`, the decider-call contribution alone has degree `k(e+1)`, not `ke` with a universal additive constant. The displayed safe degree also includes copying/reset work when `e=0`. The attached polynomial absorption inequality `(n+1)^c ≤ 2^c(n^c+1)` converts this to the class's normal form, including `n=0`. This is a mathematical construction and cost argument; the virtual-input, preservation, and cleanup invariants still need formal machine implementations in the fill phase.

The following adversarial instantiations were checked by unfolding the definitions and tracing their consequences; these are not claimed as executed Lean tests.

| Instantiation | Result |
|---|---|
| `O=∅` | Every query goes to `qNo`. Replacing query steps with that fixed state transition removes the oracle; conversely a plain machine ignores it. Thus the P classes agree, and the analogous machine-first nondeterministic classes agree as well. This also agrees with the frozen deterministic empty-oracle bridge. |
| `O=Set.univ` | Every query goes to `qYes`. The same elimination works with yes in place of no, so constant oracle answers add no polynomial-time power. |
| `q₀=qQuery` | Initially the query tape is blank, hence the first query is `[]`. Take distinct query/yes/no states and let the latter emit true/false and halt: the two-step machine decides `Set.univ` when `[]∈O` and `∅` otherwise. In the nondeterministic version every two-bit word gives the same result. |
| `T n=0` at even one length | Choose `x=List.replicate n false`. The budget `c*T n` is zero. Deterministic execution is still in `some q₀`; for nondeterminism the word `[]` has length zero and leaves the same live state. Therefore both oracle time classes are empty, for every oracle; `c=0` likewise supplies no witnesses. |
| `L=∅` in the workhorse | A reduction to `O` can exist exactly when `O` has a nonmember: any existing reduction gives one by evaluating it on `[]`, and a fixed nonmember gives a constant reduction. For `O=∅` the premise is realizable; for `O=Set.univ` it is impossible. The language nevertheless belongs to P and hence to every POracle independently of the workhorse premise. |
| `L=Set.univ` in the workhorse | Dually, a reduction can exist exactly when `O` has a member. The premise is realizable for `O=Set.univ`, impossible for `O=∅`, and there is no false conclusion from either case. |
| Reduction output `f x=[]` | The fresh query tape remains blank. Extraction returns exactly `[]`, so the one-query construction works without a nonempty-output hypothesis or a head rewind. |
| Query tape blank at cell 0 but containing `true` at cell 1 | This is reachable by moving past cell 0 before writing. The extracted query is `[]`; a virtual input must therefore be blank everywhere, even at cell 1. Directly exposing the whole query tape to a decider for “the second bit is true” would give the wrong answer. Copying only the extracted prefix, as in the construction above, handles this case and likewise excludes negative-cell garbage. |
| Early acceptance plus padding | A branch that halts after one step with `[true]` accepts at every larger exact budget after arbitrary padding. A branch emitting `[true]` but remaining live is not yet accepting; a halted branch outputting `[true,false]` is never accepting. |
| One accepting branch and one infinite branch | `AcceptsWithin` can hold at a positive budget, but `HaltsWithin` fails at every proposed global budget. The machine is therefore not a witness to `DecidesInTime`; rejecting or alternative branches cannot evade the totality condition. |
| An undecidable oracle, with `L=O` | Identity reduction yields the stated membership in POracle. This does not collapse unrelativized P: the simulation theorem explicitly requires `O∈P`. |
| Malformed SAT encoding | It decodes to the empty satisfiable CNF and is accepted by SAT, hence rejected by `SATᶜ`. A valid unsatisfiable CNF is accepted by the complemented oracle machine. No malformed-input correction is missing. |
| Polynomial exponent zero and empty input | `n^0+1=2`, including at zero, so constant-time machines are admitted. For every positive exponent, `0^c+1=1`, and the multiplicative constant supplies the finite startup budget. Omitting `+1` instead produces finding 1. |
| A machine fast only under its target oracle | Start with the empty query, halt on no, and loop on yes. It is a valid constant-time empty-oracle witness although it diverges under an oracle containing `[]`; this is intentional. Adding a timeout retains its empty-oracle language and gives the all-oracle clocked form. |

For completeness, finding 1 has a direct refutation of the displayed docstring equation. For every positive natural exponent, `0^c=0`, so the attached theorem `NTIME_eq_empty_of_exists_zero` gives

\[
c>0\ \Longrightarrow\ \operatorname{NTIME}(n\mapsto n^c)=\varnothing,
\qquad
\bigcup_{c\in\mathbb N}\operatorname{NTIME}(n\mapsto n^c)
=\operatorname{NTIME}(n\mapsto 1).
\]

The language of strings containing a true bit has a linear-time scanner. A machine bounded by a fixed constant `t` cannot distinguish an all-false length-`n` input from one differing only in its last bit when `n>t+1`: every branch sees the same symbols throughout its entire budget, so acceptance is identical. Thus that language belongs to P and NP but not to the displayed union. Adding `+1` is therefore mathematically necessary under these exact-budget definitions, rather than merely a typographical preference.

Coverage limits are explicit: I did not re-audit proofs of the frozen oracle model, chapter-2 SAT/Cook–Levin infrastructure, the P3.2 constructions, or the concurrent routine layer. `SAT_NPHard` was used at its quoted type; its unattached implementation was not inspected. I verified the supplied source and log counts, not the claimed Git revision equality, fresh build artifacts, or kernel axiom closure. These limits do not leave any of the five files' requested definitions or theorem statements unchecked.

Notation: `O,L` are binary languages; `M,N` are deterministic/nondeterministic machines; `D` is the plain oracle decider; `f` is the reduction function; `x,w` are input and choice words; `n` is input length; `t,t'` are step budgets; `c,d` are multiplicative constants and `k,e` the exponents in the simulation calculation (the definition tables separately use their source binders, where `k` counts ordinary tapes and `c` can be an exponent); `[]` is the empty word; `Lᶜ` is set complement; `≤ₚ` is ordinary polynomial-time many-one reducibility; `Pᴼ,NPᴼ` mean `POracle O,NPOracle O`; `O(·)` is asymptotic upper-bound notation with constants allowed to depend on the fixed machines.
