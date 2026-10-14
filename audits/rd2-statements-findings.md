Input SHA-256: `b873469afca84f2683f18f9ec2a2d1f73972527dfc3b0fa6aeb25d11e8a3c15f` — matches the expected digest. Exactly **63** `## ===== <path> =====` sections were counted.

**RD-2 statement-gate verdict: PASS — 0 blockers, 0 majors, 2 minors.** No counterexample to a proposed theorem was found. The two minors concern a proof-sketch length bound and duplication accounting; neither requires changing a theorem statement. This is a statement audit, not certification that the 41 admissions have been filled or that the eventual landed module tree has been rebuilt.

The audit used the supplied files, independently reconstructed their source/harness evidence, and consulted the published 2009 Arora–Barak text. No tactic proof was reviewed for kernel correctness. Lean and the campaign olean snapshot were unavailable here: the reported elaborations and axiom prints are supplied execution evidence, not runs performed by this auditor. Repository-wide absence claims and historical checkout equality cannot be independently established from this partial repository bundle; their scope is stated below.

In the tables, proposed-file references mean the files under `audits/evidence/rd2-gate/`; “tip” means the bundled `TCSlib/` sources. Declaration names are used where more precise than line numbers.

**Findings and explicit no-findings rows**

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | minor | `FormulaKitEmit.lean.txt:117–123` · `polyTimeComputable_flatMap_range` sketch | Initialized iterates have length at most `x.length + count x + O(1)`. | The aligned pairing doubles the first component: `length (pairEncode x (replicate i true)) = 2·x.length + i + 2`. With `count x = 0`, even the initial state has length `2·x.length + 2`, which is not bounded by `x.length + O(1)`. The theorem itself remains true. | Replace the initialized-orbit bound by `2·x.length + count x + 2`. Also distinguish this from `polyTimeComputable_emitIter`'s all-start-word orbit bound: account for an initially oversized second component and malformed pairs. Both remain polynomial by saturation and the total pair projections. |
| 2 | minor | `audits/rd2-statements-pack.md` · duplication ledger and “identical bodies” wording; `FormulaKitEmit.lean.txt` · `fragment_append` | The disclosed ledger exhausts the copies, and no copied proof exceeds a one-line unfolding proof. | `fragment_append` reproduces tip `CookLevin/Hardness.lean:127–130` · `clFragment_append`, including its one-line `simp` proof, but is absent from the ledger. The ledger itself lists the three-line `card_port` proof, contradicting the subsequent one-line-only sentence. `UnaryPT.add` is an overlapping theorem with a different proof, not a literal one-line proof twin. Moreover, MERGE means matching definitions/interfaces after the stated renaming, not identical proof bodies: public `cost_flatMap_le` is admitted whereas the private predecessor is proved. | Add `fragment_append` to the existing Cook–Levin re-basing family; distinguish definition/interface correspondence from proof transcription; replace the one-line-only sentence with an accurate description of the short copies. The corrected copied-proof count for these listed families is seven nonblank tactic lines: two in Gate, two in Emit, three in the codec. This is small accounting debt within the disclosed promotions/re-basing work, not a newly discovered wholesale-copy family. |
| 3 | note | `ConfigCodec` · layout and three CNFs; brief 1 | No findings. | Every field occupies the intended disjoint interval. Active gates reproduce the native step, including blank writes, boundary clamping, halted identity, summary recomputation, and rejection of window exit. Detailed arguments and concrete edge cases appear below. | None. |
| 4 | note | `rd2Evidence_oldShape`; brief 2 | No findings in retirement, with the expressly declared length change. | Every old clause is recovered at the exposed width, except the literal padded-length equation. The common constant and all three serialized bounds are recovered by the evidence theorem. No bundled Lean proof consumes the old existential. | Retire it as decided. Do not add a packaged corollary without a consumer. |
| 5 | note | Four codec uniformity theorems; brief 3 | No findings. | Parameterized `n`, `s`, and offset support calls on paired instance/level inputs. The adjacent universal blocks allow adjacency's single-offset interface. Prefix emission and `QBF.encode` use the available iteration, concatenation, and pairing closures. | Retain the disclosed guard-literal emission and bounded-reachability obligations. See the precise remaining obligations below. |
| 6 | note | `QBF.truth_exSuffix_of_pointwise`; brief 4 | No findings. | `hpt` quantifies over every full assignment, fixes exactly the original prefix variables, and permits the auxiliary assignment to depend on all of them. `hT` closes the matrix after the suffix. Empty prefixes and zero auxiliary variables are covered. | Keep this interface. A small public guarded-clause operation with its evaluation lemma is recommended before the hardness fill; the T2 pointwise theorem remains hardness-specific. |
| 7 | note | `FormulaKit` and Cook–Levin; brief 5 | No findings in the proposed functional interfaces. | All seven requested correspondences hold at the level described below. The new template deliberately need not equal the old chosen clause list. The emission theorem abstracts polynomial-time chunks rather than literally replacing the old native seam theorem. | Re-base Cook–Levin in its scheduled window, preserving these distinctions. |
| 8 | note | Migration log; brief 6 | No findings in the migration classification. | The supplied generator reproduces all 120 rows and their totals. An independent reference screen finds no KEEP/KEEP-R dependency on MOVE, REWRITE, or RETIRE, and no surviving operational A1–A6 choice site. The MERGE interfaces support the declared renamings. | Use the measured 703 surviving lines, not the draft estimate of approximately 820. Re-elaborate the actual renamed declarations during RD-2a. |
| 9 | note | `TQBF_PSPACEHard` sketch; brief 7 | No findings at this gate's sketch scope. | The equality-or-step base, valid midpoint, depth `W`, input preservation, quotient lifting, and run-window arguments suffice for the stated plan. The guard matrix and its pointwise correctness are still obligations, not established results. | Keep all named obligations explicit; include the nonblank-cell visitation lemma when proving the window invariant. |
| 10 | note | Files, namespaces, exports, and placement; brief 8 | No findings requiring relocation now. | Gate stays below the polynomial-time layer; Emit depends on that layer; QBF's semantic additions introduce no machine dependency. The in-place two-block codec follows the binding decision and makes public definitions available to surviving private lemmas. | Add the promised `TCSlib.lean` facade import when landing. Revisit a separate codec module at the second consumer, not because of file size alone. |
| 11 | note | Twenty statement-phase proofs; brief 9 | No findings requiring a proof to be postponed. | The disclosed proofs are local algebra, structural recursion, finite indexing, or short consequences of explicit admitted statements. The four corollaries with `sorryAx` are correctly identified; they are not independently closed results. | Accept the expressly disclosed statement-phase exception. Do not describe the four conditional corollaries as admission-free. |
| 12 | note | Documentation, attribution, and line widths; brief 10 | No findings beyond row 1. | Public declarations have statement prose; nontrivial admissions have literal sketches. The AB09 page references are correct. All six over-100-column lines are inherited; no new or changed overlong line was found. | None beyond row 1 and the separately stated landing export. |
| 13 | note | Duplication screen; brief 11 | No further findings beyond row 2. | The codec twins, cost family, port cardinality, fixed packing/fragment definitions, falsifying clause, and unary-add overlap are accounted for after that correction. No wholesale copied proof block or copied `DAGCircuitSat` private machinery was found in the additions. | Apply the existing MERGE/MOVE, Cook–Levin re-basing, and 12.2c dispositions. Ownership is not a blanket exemption from the duplication policy. |
| 14 | note | Finding A and attestations; brief 12 | No findings of a false replacement theorem or source-freeze violation. | A1–A6 identify real choices and a real missing uniformity interface. However, the annotation `noncomputable` alone does not prove mathematical uncomputability or a general impossibility of proving an emitter. Some attestations remain historical execution claims, as detailed below. | Read Finding A as “no uniformity contract or algorithm for these literal choices is supplied”; avoid presenting it as a proved noncomputability lower bound. |

**AB09 reference verification**

I consulted the published *Computational Complexity: A Modern Approach*, Cambridge University Press, 2009, in this [retrieved copy](https://theswissbay.ch/pdf/Gentoomen%20Library/Theory%20Of%20Computation/Sanjeev_Arora%2C_Boaz_Barak-Computational_complexity__a_modern_approach-Cambridge_University_Press%282009%29.pdf), using printed page numbers rather than PDF indices.

| Citation | Verification |
|---|---|
| Claim 4.4(2), pp. 80–81 | Claim begins on p. 80; clause (2) and its proof sketch are on p. 81. |
| Theorem 4.13, pp. 84–85 | The theorem and membership argument begin on p. 84; hardness and the succinct midpoint recursion are on p. 85. |
| Claim 2.13, p. 46 | The truth-table universality construction is there. |
| Lemma 2.11, pp. 45–49 | Statement on p. 45; proof begins on p. 46 and finishes on p. 49. |
| §4.2, p. 83 | Discusses prenex conversion and auxiliary-variable conversion of the matrix to CNF/3CNF. |

The code's polynomial serialized size, input-carrying width, output quotient, and explicit zero-step disjunct are disclosed adaptations. RD-2 does not newly claim the book's linear-size bound.

**Old statement: every clause compared**

| Old clause, tip `TQBF.lean` | Replacement | Audit conclusion |
|---|---|---|
| `:1748–1749`: exact length `C·(s+n+1)` for every input/configuration | `code_length`, `width_eq`, `width_le` | Deliberate change, not literally the same clause. The new code has exact exposed width with a uniform linear upper bound. |
| `:1750–1752`: input separation on windowed configurations | `code_input_eq` | Strengthened: the two input lengths are retained; the window hypotheses are unnecessary. |
| `:1753–1755`: equal codes iff equal `coreSum` | `code_eq_iff` | Same quotient and same length/window hypotheses. No full-output injectivity is asserted. |
| `:1756–1759`: validity iff membership in the codec image | `validity_eval_iff` | Same image characterization at the new exact width. Arbitrary unconstrained input bits are realized by choosing the corresponding input. |
| `:1760–1763`: adjacency iff quotient step | `adjacency_eval_iff` | Same step and same window hypotheses. It does not assume the successor is windowed; window exit is rejected. |
| `:1764–1767`: cross-input adjacency false | `adjacency_eval_of_ne` | Strengthened by dropping both window hypotheses. Equal input lengths and distinctness remain essential. |
| `:1768–1771`: acceptance iff halted and accepting summary | `acceptance_eval_iff` | Strengthened by dropping the length and window hypotheses. These fields remain readable even in an otherwise invalid code. |
| `:1772`: validity variable bound | `validity_numVars_le` | Same bound relative to the actual code width. |
| `:1773`: acceptance variable bound | `acceptance_numVars_le` | Same bound relative to the actual code width. |
| `:1774`: adjacency variable bound | `adjacency_numVars_le` | Same two-block bound relative to the actual code width. |
| `:1775`: validity serialization bound | `exists_serialize_length_le`, first conjunct | Preserved after enlarging the common constant. |
| `:1776`: adjacency serialization bound | Same theorem, second conjunct | Preserved after enlarging the common constant. |
| `:1777`: acceptance serialization bound | Same theorem, third conjunct | Preserved after enlarging the common constant. |

For the linear bound, direct expansion gives

\[
\begin{aligned}
\operatorname{width}(M,n,s)
 &=n+(n+2)+(\operatorname{card}(M.State)+1)+3k(2s+1)+2\\
 &=2n+\operatorname{card}(M.State)+5+6ks+3k,\\
(\operatorname{card}(M.State)+6k+5)(s+n+1)-\operatorname{width}(M,n,s)
 &=(\operatorname{card}(M.State)+5)s
   +(\operatorname{card}(M.State)+6k+3)n+3k\geq0.
\end{aligned}
\]

For repackaging, the evidence chooses

\[
C=\max\{\operatorname{card}(M.State)+6k+5,K\}>0.
\]

Since `s+n+2 ≥ 2` and `K ≤ C`, each serialized bound satisfies

\[
K(s+n+2)^K\leq C(s+n+2)^C.
\]

Thus `rd2Evidence_oldShape` has precisely the promised common-constant shape. It depends on the new admissions, as its printed axioms disclose; it is an interface-recovery check, not independent evidence that those admissions are true.

Nothing in the named consumer requires padded length. The reduction needs a known width, a vertex count bounded by `2^width`, and polynomial emission. If a future consumer truly needs the old exact length, append canonical zero padding, add validity clauses for it, and relocate the target block in adjacency. That is an additional construction, not an identity of the current definitions. There is no present reason to retain a packaged corollary under a new name.

**Definition restatements: all 48 new definitions, abbreviations, and inductive types**

These restatements were made from the declaration bodies with comments removed, then compared with the prose. The bounded field interpretations below concern the stated legal index ranges; the underlying natural-number functions are total outside those ranges too.

| Declaration | Meaning from the body | Comparison |
|---|---|---|
| `FormulaKit.blockVar` | Add the base, the block number times its width, and the within-block index. | Matches. It is not an injectivity claim without index bounds. |
| `bitsOf` | Return the low `ℓ` binary digits of the natural number, least significant first. | Matches. |
| `excludeClause` | List each variable once with the polarity opposite its specified assignment bit. | Matches, including the empty clause at zero arity. |
| `template` | Enumerate integers below `2^ℓ`; retain their excluding clauses exactly for false predicate values. | Matches; explicit order replaces the old choice. |
| `gate` | Relabel that fixed template by the global wire function. | Matches; colliding wires are allowed. |
| `readBit` | Read an in-range finite coordinate, returning false outside its domain. | Matches. |
| `exactlyOne` | Require a true listed variable and exclude simultaneous truth of every pair of unequal variable names. | Matches the theorem's variable-based semantics; duplicate occurrences do not impose a second truth requirement. |
| `cost` | Sum literal count plus one for each clause. | Matches; empty clauses contribute one. |
| `FormulaKit.fragment` | Serialize each clause with its opening marker and its clause terminator, omitting only the final formula terminator. | Matches. |
| `QBF.PrefixTruth` | Process the remaining quantifiers in order, updating the current numbered variable and then increasing its index; apply the supplied predicate at the leaf. | Matches. |
| `ConfigCodec.stateCount` | Number of machine states plus the separate halting marker. | Matches. |
| `stateIndex` | Assign halt index zero; enumerate ordinary states at the positive indices. | Matches; the enumeration depends only on the fixed machine. |
| `stateOffset` | Start the state block after the input bits and the input-head markers. | Matches. |
| `workOffset` | Start work flags after all state markers. | Matches. |
| `summaryOffset` | Start summary flags after three bits per work cell, tape by tape. | Matches. |
| `width` | End immediately after the two summary flags. | Matches; no padding. |
| `inputVar` | The input coordinate is its own variable number. | Matches. |
| `headVar` | Add input length to an input-head position. | Matches. |
| `stateVar` | Add the state block's start to the chosen state number. | Matches. |
| `workVar` | Flatten tape, cell, and flag in that order, using three flags per cell. | Matches. |
| `summaryVar` | Select the accepting flag, or its successor for the dead flag. | Matches. |
| `workFlags` | Test for a false symbol, a true symbol, and a head at the exact integer position `j-s`. | Matches; neither head position nor cell address is truncated or clamped. |
| `code` | Concatenate the first `n` input bits with false padding, input-head equality tests, state equality tests, all work flags, and the two output-summary tests. | Matches with a qualification already reflected in the hypotheses: the input-head track can have no marker when the actual input is longer than the chosen `n`. |
| `validity` | Impose one head/state choice, one work head per tape, and exclusion of both symbol flags or both summary flags; impose nothing on input bits. | Matches. |
| `acceptance` | Conjoin the halt marker and the accepting-summary marker. | Matches; validity is intentionally separate. |
| `inputEquality` | Conjoin two equality clauses for each corresponding pair of carried input bits. | Matches. |
| `Case` | A possibly halted state, one optional scanned input bit, and optional scanned work bits for all tapes. | Matches; machine-finite. |
| `caseAction` | Use the transition table at a live case and a silent, motionless, nonwriting halted action at a halted case. | Matches. |
| `caseList` | Choose an ordering of every machine case. | Matches; independent of `n,s`. |
| `Port` | Name the state/head tests, scanned symbols, old summary, and old/new coordinate bits used by a local gate. | Matches. |
| `portCount` | The number `3k+7`. | Matches the constructor count. |
| `portIndex` | Place the named port families in consecutive, disjoint numeric ranges. | Matches. |
| `portOf` | Decode those ranges; use `newBit` for the final legal index and all larger indices. | Matches its documented total fallback; only legal template indices are used. |
| `Expect` | Choose copying, a constant bit, or one recomputed summary flag. | Matches; five possibilities. |
| `GateKind` | Combine a machine case, an interior-input flag, and an expected-bit mode. | Matches; finite for fixed `M`. |
| `readSymbol` | Give the true flag priority, then the false flag, otherwise blank. | Matches; `11` is deliberately assigned a value but is excluded by validity. |
| `readSummary` | Give dead priority, then accept, otherwise empty. | Matches; validity excludes `11`. |
| `summaryWord` | Represent empty by `[]`, accept by `[true]`, and dead by `[false]`. | Matches. |
| `guard` | Require the selected source state and head positions, and require the scanned symbols to equal the case's symbols. | Matches; the dummy input-symbol wire is ignored at either end marker. |
| `expectBit` | Return the old bit, the supplied constant, or a summary flag after appending the action's optional emission to a representative old output. | Matches. |
| `kindPred` | Require the new bit to equal its expectation whenever the guard is true. | Matches. |
| `headOf` | Extract one base-`2s+1` digit of the head-tuple number. | Matches; denominator is always positive. |
| `moveInput` | Add signed movement in integers, truncate negative positions to zero, and clamp positions above the right boundary to `n+1`. | Matches native `moveInputPos` on legal positions. |
| `expectOf` | Decode a target coordinate's field and prescribe copying, the moved head/state bit, a kept or written symbol bit, or a recomputed summary bit. | Matches; `some none` is a blank write, distinct from no write. |
| `portWire` | Read all guard and summary ports from the source block, the old coordinate there, and the new coordinate from the target block. | Matches. |
| `transitionGate` | Select a finite-kind predicate, express it by a truth-table template, and wire numbered ports into the two code blocks. | Matches literally, including the evidence's `rfl` identity. |
| `transition` | Conjoin gates in input-position, mixed-radix head-tuple, case-list, and coordinate order. | Matches; all required indices are covered. |
| `adjacency` | Conjoin carried-input equality with all transition gates. | Matches; its semantics on arbitrary invalid strings is not strengthened beyond the stated contract. |

**Semantic audit of the transition equivalence**

1. A windowed source has exactly one input-head marker, one state marker, and one head marker on every work tape. Its scanned symbols therefore determine exactly one case. Its head tuple is represented by
   \[
   h=\sum_{i<k}(c.workTapePos(i)+s)(2s+1)^i,
   \qquad 0\leq h<(2s+1)^k,
   \]
   where each nonnegative integer `c.workTapePos(i)+s` is interpreted as a natural digit in `0,…,2s`. This also works at `s=0` and at `k=0`: the enumerated tuple number is zero and the enumeration has one member.
2. For this position/tuple/case, `guard` is true for every coordinate; for every other position/tuple/case it is false. At an interior position the input port reads `x[p-1]`; at either end marker its value is ignored. `portIndex_lt` and `portOf_portIndex` ensure that the truth-table predicate reads precisely these named ports.
3. Therefore each active gate requires exactly its corresponding expected target bit. `expectOf` copies input bits and unmodified cells, uses the native clamped input motion, writes at the old work head, and tests the moved work head by integer equality. No out-of-window work head is wrapped into the window.
4. The output step is sound because
   \[
   \operatorname{outSummary}(\operatorname{summaryWord}(\operatorname{outSummary}(c.output)))
   =\operatorname{outSummary}(c.output),
   \]
   and `outSummary_append_congr` preserves this equality after appending `act.output.toList`. Thus the two expected summary bits are the actual successor's summary bits.
5. If all gates agree with a windowed target, that target's unique head marker forces each successor head to remain in the window. The successor cannot create an outside nonblank cell: it writes only at a source head, which was inside. Thus the successor is windowed, and equality of all fields is equivalent to equality of `coreSum`.
6. Conversely, equality of successor and target `coreSum` makes every expected target bit agree, so all active gates hold; inactive gates impose no condition. Same-input equality clauses hold automatically. Across distinct equal-length inputs, at least one input equality clause fails independently of the gates.

This supplies the mathematical argument required at the statement gate. It is not a claim that the corresponding Lean proof has been completed.

**Adversarial instances and boundary checks**

| Instance | Direct check |
|---|---|
| `k=0`, `n=0`, `s=0`, one ordinary machine state | Width is `6`. A halted configuration at input position `0` with output `[true]` has code `[true,false,true,false,true,false]`: two input-head bits, two state bits, two summary bits. It is valid and accepting. The tuple enumeration is `range 1`; no work port or work-head requirement disappears incorrectly. |
| Halted source in that instance | `caseAction` has no writes, no moves, no output, and halted successor state. The adjacency gates accept the same code and reject a target with a different input-head marker. More generally they preserve the output summary, not the entire output history. |
| `k=1`, `n=s=0`, blank work cell, head at `0`, live state, empty output | The only work-cell flags are `[false,false,true]`. An action moving the work head right prescribes target head flag `false`, because `0+1≠0`. Every windowed target must set that sole flag true, so adjacency is false for every such target. The corresponding quotient-step equality is also false. |
| Left exit at `s=1` | The leftmost cell has `j=0` and position `-1`. A left move gives digit expectation `0+(-1)=-1`, unequal to every legal target cell index. There is no natural-subtraction truncation that could falsely keep the head at the boundary. |
| Blank write | For `(act.workTapes i).1 = some none`, both symbol expectations are false: `none ≠ some false` and `none ≠ some true`. For outer `none`, both old symbol flags are copied. These cases are correctly distinguished. |
| Empty input and end markers | At `n=0`, both legal input positions, `0` and `1`, are end markers and `interior=false`. Left from `0` remains `0`; right from `1` remains `1`. The summary flag used as a dummy input wire cannot change the scanned input symbol. |
| One-bit input | At `n=1,p=1`, the scanned bit is input coordinate `0`; positions `0,2` read blank. Distinct one-bit inputs fail the explicit cross-block input equality clauses. |
| Output summary transitions | Empty plus no emission stays empty; empty plus true accepts; empty plus false is dead. Accept plus no emission stays accept, while either emitted bit makes it dead. Dead stays dead under all three emission choices. These are exactly the native append semantics. |
| Live self-loop | A stationary, nonwriting, silent action that retains the live state is self-adjacent. An action changing a core field need not be. The theorem does not falsely assert either universal live self-adjacency or universal live non-self-adjacency. |
| Wrong nominal input length | Set `n=0` but use an actual nonempty input and an input head beyond position `1`. The resulting head track need not be valid; nevertheless the halt and summary fields still make `acceptance_eval_iff` correct. No weakened length hypothesis is being used to claim validity or quotient injectivity. |
| Zero-arity template | There is one empty assignment. A true predicate gives `[]`; a false predicate gives `[[]]`. Evaluation, variable bounds, width, and the cost ledger all retain the correct empty cases. |
| Empty or repeated exactly-one list | `exactlyOne [] = [[]]` is false. For `[v,v]`, there is no self-exclusion clause and the gadget is true exactly when `v` is true, matching `exactlyOne_eval`. |
| Repeated gate wires | Substituting the same global variable for multiple template variables restricts the predicate to the corresponding diagonal. `CNF.eval_relabel` needs no injectivity, so no hypothesis is missing. |
| Zero unary divisor | The division construction emits no bits when the divisor is zero. Remainder becomes the original dividend, agreeing with Lean's natural-number conventions. |

Useful eventual Lean sanity lemmas are: `moveInput` agrees with the value of `moveInputPos` on legal positions; mixed-radix enumeration covers every head tuple, including base one; a halted code is self-adjacent; a successor outside the window is adjacent to no windowed target; and an initial code is valid. They are not missing hypotheses of the present statements and need not be additional public abstractions.

**Every admitted theorem: literal plausibility argument**

There are exactly 41 new admitted theorems: 10 in Gate, 10 in Emit, and 21 in ConfigCodec. Each is covered below; these are mathematical proof arguments, not completed formal proofs.

| Admitted theorem | Argument |
|---|---|
| `template_eval` | Every assignment on `Fin ℓ` occurs as the low bits of a unique integer below `2^ℓ`. Its excluding clause is the unique row clause falsified by that assignment, and is present exactly when the predicate is false. |
| `template_numVars_le` | Every listed literal has variable `i.val` for `i : Fin ℓ`. Thus each successor index is at most `ℓ`, as is their maximum, including the empty maximum. |
| `template_length_le` | `range (2^ℓ)` has length `2^ℓ`. Filtering and optionally emitting one clause per entry cannot increase that length. |
| `template_widthAtMost` | Each retained clause is an `ofFn` list over `Fin ℓ` and has exactly `ℓ` literals. Consequently every clause has width at most `ℓ`, including zero arity. |
| `numVars_le_of_forall_lt` | Every literal contributes its index plus one to the maximum defining `numVars`. The hypothesis bounds every such contribution by `N`, and the empty maximum is zero. |
| `exactlyOne_eval` | The positive clause supplies one true listed variable. The negative pair clauses force every differently named listed variable false; conversely this assignment satisfies all clauses, even with duplicate occurrences. |
| `cost_flatMap_le` | Cost is additive under concatenation. Summing the bound `B` once for every element of the list yields `length·B`. |
| `serialize_length_le` | A literal at index `v<N` serializes to `v+3≤N+2` bits. Each clause adds two syntax bits and the whole formula adds one, all bounded by the claimed expression even when clauses are empty or `N=0`. |
| `gate_cost_le` | Relabeling preserves cost. The template has at most `2^ℓ` clauses, each with cost `ℓ+1`. |
| `exactlyOne_cost_le` | The positive clause costs `length+1`. At most `length²` ordered pairs produce negative clauses of cost three. |
| `polyTimeComputable_fragment_iff_serialize` | Append the constant final bit in the forward direction. In the reverse direction a finite-state one-bit-delay transducer omits the last bit, which is always the formula terminator. |
| `polyTimeComputable_flatMap_range` | Use a saturating counter in the second component of the state word and suppress chunks after `count`. Unary polynomial-time count bounds both the number of useful rounds and the initialized state length; an all-start-word polynomial envelope also accommodates oversized or malformed initial states. The finite outer polynomial clock may therefore exceed the count without changing the output. |
| `polyTimeComputable_fragment_relabel` | The formula has a fixed finite list of literal occurrences. Emit the polynomial-time unary index of each occurrence followed by its fixed syntax/polarity bits and concatenate; no wire outside `φ.numVars` is queried. |
| `polyTimeComputable_fragment_gate_select` | There are finitely many predicate kinds for the fixed type. Each fixed-kind fragment is polynomial-time, and finitely many polynomial-time equality tests choose the correct one. |
| `polyTimeComputable_unary_sub` | Drop `g x` bits from the unary word for `f x` using the existing prefix-dropping closure. Its length is exactly the truncated difference, including `g x>f x`. |
| `polyTimeComputable_unary_mul` | Run `f x` emission rounds, each outputting the unary word for `g x`. The total output length is their product, still polynomial in the original input length. |
| `polyTimeComputable_unary_le` | The unary truncated difference is empty exactly when `f x≤g x`. Compose subtraction with the existing empty-word test. |
| `polyTimeComputable_unary_div` | When `g x>0`, among indices `i<f x`, exactly `f x/g x` satisfy `(i+1)g x≤f x`. Emit one bit at those indices and none when the divisor is zero; all tests and loop lengths are polynomial-time. |
| `polyTimeComputable_unary_mod` | Natural remainder equals the dividend minus divisor times quotient. Compose the three preceding unary arithmetic operations; at divisor zero this reduces to the dividend. |
| `polyTimeComputable_serialize_relabel_add` | A grammar-aware scan identifies each literal's unary index and inserts `o x` additional ones at its start. The output length is bounded by `(o x+1)` times the original serialization length, so replaying the supplied unary offset is polynomial-time. A variable offset requires a tape/loop implementation, not a fixed finite-state output table. |
| `width_le` | Expand the width and subtract it from the claimed linear upper bound. The displayed calculation above leaves only nonnegative terms. |
| `code_length` | The five segment lengths are `n`, `n+2`, `stateCount M`, `3k(2s+1)`, and `2`. Their sum is the defined width, independently of the values encoded. |
| `code_getD_inputVar` | The requested coordinate lies in the first `n`-bit segment. Its `ofFn` entry is exactly `x.getD i false`, including short actual inputs. |
| `code_getD_headVar` | The head segment starts at index `n`. Subtracting that offset reads exactly the equality test for position `j`. |
| `code_getD_stateVar` | The state segment starts at `stateOffset`, and `stateIndex` lies within that segment. Its injectivity turns equality of indices into equality of optional states. |
| `code_getD_workVar` | There are `2s+1` cells per tape and three bits per cell. The stated flattened offset therefore reads the requested flag for every in-range tape, cell, and flag. |
| `code_getD_summaryVar` | The final two bits begin at `summaryOffset`. Selecting offset zero or one reads precisely the accepting or dead summary test. |
| `code_input_eq` | Equal codes give equal first `n` bits by `code_getD_inputVar`. Two inputs of length `n` agreeing at all those positions are equal; no window information is used. |
| `code_eq_iff` | Equal codes recover state, input position, all window symbols/heads, and output summary. Window hypotheses make every outside cell blank and place every head inside, so these data recover exactly `coreSum`; the converse follows field by field. |
| `validity_eval_iff` | Decode the unconstrained input bits, unique head/state choices, allowed cell-symbol flags, and allowed summary flags. Blank-extend the work tapes and choose a representative output to obtain a windowed configuration with that code; actual windowed codes satisfy all these same constraints. |
| `adjacency_eval_iff` | Unique source markers activate exactly the appropriate position/tuple/case, whose coordinate gates encode the native step. Agreement with a windowed target forces the successor into the window and equates its quotient, as detailed in the six-step argument above; quotient equality also satisfies every gate. |
| `adjacency_eval_of_ne` | Distinct inputs of equal length disagree at an in-range bit. One of that bit's two cross-block equality clauses is then false, whatever the other configuration fields are. |
| `acceptance_eval_iff` | The two unit clauses read the halt marker and the accepting-summary marker. The indexing lemmas identify these fields without requiring nominal input-length agreement or a work window. |
| `validity_numVars_le` | All listed variables belong to head, state, work, or summary fields strictly below the width. Apply the generic bound on literal indices. |
| `acceptance_numVars_le` | Both unit-clause indices are inside the state/summary segments. Their successor indices therefore do not exceed the width. |
| `adjacency_numVars_le` | Input equality uses one coordinate in each block. For each legal transition-gate index, every source port lies below the width and the new-bit port below twice the width, so relabeling introduces no larger variable. |
| `exists_serialize_length_le` | Validity has quadratic cost and linear index size; acceptance is smaller. Adjacency has `(n+2)(2s+1)^k·length(caseList M)·width` gates of machine-constant cost and linear index size, giving degree at most `k+3`; enlarge one constant to absorb every coefficient and degree at base `s+n+2`. |
| `polyTimeComputable_serialize_validity` | Enumerate the positive exactly-one clauses, their pair exclusions, cell exclusions, and summary exclusion in their defined order. Unary arithmetic supplies polynomial-time indices and polynomial round counts, after which the ordered-emission and offset lemmas apply. |
| `polyTimeComputable_serialize_adjacency` | Enumerate the four nested index families with mixed-radix unary arithmetic and the fixed case table. Each gate's kind is chosen from a fixed finite set and its wires are polynomial-time; any exponent depending on a tape index is handled by a finite split over the machine's tapes. |
| `polyTimeComputable_serialize_acceptance` | Emit two unit clauses at polynomial-time unary indices. Their fixed syntax and final terminator are finite concatenations. |
| `polyTimeComputable_code_initCfg` | Concatenate the input, head track `0 1 0^n`, constant start-state track, blank work tracks with their head marker at cell `s`, and summary `00`. All variable lengths are unary polynomial-time, including at empty input and radius zero. |

The four statement-phase corollaries depending on admissions are exactly `gate_eval`, `polyTimeComputable_serialize_flatMap`, `polyTimeComputable_fragment_gate`, and `polyTimeComputable_unary_pow`. Their dependencies are acyclic: gate evaluation uses the template theorem; serialization uses ordered fragment emission; gate emission uses fixed-formula relabeling; fixed powers use multiplication. The remaining 16 supplied proofs have the reported standard-axiom status, subject to the replay limitation already stated.

**Uniformity, auxiliary variables, and the hardness plan**

The uniformity theorem quantifiers are correctly ordered: the machine is fixed, then arbitrary polynomial-time unary parameters are supplied. The constants may depend on the machine, its state enumeration, its finite case ordering, and its number of tapes. No polynomial dependence on a varying machine description is claimed. This is sufficient for a Karp reduction for each language's fixed decider.

For an input `z = pairEncode x (replicate r true)`, use `n z = (pairFstD z).length`; compose the radius function with `pairFstD`; recover the level as `(pairSndD z).length`. The unary width and the required offsets follow from addition and multiplication. In particular the midpoint offset is `(3r+1)W`; adjacency on the adjacent universal pair starts at `(3r+2)W`, not at the midpoint. Both coordinates then shift together exactly as the adjacency theorem requires.

With `W` levels, the original prefix has

\[
W+W(3W)=W(3W+1)
\]

variables: the existential target, then an existential midpoint and two universal blocks per level. Prefix bits are polynomial-time repetitions and ordered concatenations; append the auxiliary existential bits. `PolyTimeComputable.pairEncode` then produces exactly `QBF.encode`, and `QBF.decode_encode` supplies the decoding identity. No binary-number encoding of the prefix is being silently substituted.

The size theorem is logically redundant once all uniformity theorems are proved: instantiate the parameters using paired unary `n,s`, use `output_length_le`, and absorb constants. It remains useful now as an independent semantic-fill target and as the explicit replacement for the old size clauses. Keep it.

The prefix theorem has the right strength. Its pointwise assumption is

\[
\forall\sigma,\quad
\bigl(\exists\tau,\; (\forall v<|qs|,\tau(v)=\sigma(v))\land T(\tau)\bigr)
\iff P(\sigma).
\]

This is substantially stronger than equisatisfiability after closing the original variables existentially. It also forces `P` to depend only on the prefix coordinates, because the left side has that property. The bound `T.numVars ≤ |qs|+G` prevents unbound matrix variables beyond the auxiliary suffix.

For a direct dependency test, let the original prefix be one universal bit and let the matrix assert equality of that bit and one auxiliary bit. An existential auxiliary suffix makes the formula true: the auxiliary bit can equal the universal bit. Placing that existential before the universal would make the formula false. The proposed theorem uses the correct order. At `G=0`, the variable bound ensures there is no unnoticed free coordinate that an arbitrary extension could change.

The remaining generic gap is the disclosed operation that adds a chosen literal to every clause, together with its polynomial-time serialization and elementary evaluation/variable-bound lemmas. I recommend putting this small primitive in Gate/Emit before the hardness fill. It should not be confused with constructing or verifying the whole T2 matrix.

The hardness-specific obligations remain: define the actual guard and selector-witness clauses; prove their pointwise extension equivalence; supply their variable bound and auxiliary count; emit them in the selected order; and complete the reachability induction and run-window bridge. Fixed-arity equality/disequality gates, initial-code bit access, and prefix assembly can be built from the existing template and closure machinery; no further independent generic host was identified. The bounded-reachability kit must still supply midpoint decomposition, shortening, and the appropriate quotient/run bridges.

The truth proof's route is sound: valid endpoints and midpoints prevent junk-code paths; input equality prevents changing the carried input; `coreSum_stepWith` permits step-by-step lifting from arbitrary quotient representatives. There are at most `2^W` code vertices, so depth `W` suffices for a shortened path. The explicit equality disjunct supplies zero-length paths even at a live non-self-adjacent vertex. An accepting target need not be unique.

For the run window, `abs_pos_lt_card_visited` handles heads, and `mem_visited_of_ne_none` handles nonblank cells. Each tape's visited-cardinality is at most total space; monotonicity transports the decider's space bound to every earlier configuration. After halting, the configuration remains fixed. At zero tapes the window predicate is vacuous. These are the ingredients needed to justify the named window obligation rather than only a head-position bound.

**Cook–Levin correspondence and module rulings**

| Cook–Levin private item | New interface | Ruling |
|---|---|---|
| `clPack` | `blockVar` | Same arithmetic layout. |
| `clTemplate` | `template` | Same Boolean purpose and size bounds; deliberately different literal clause-list construction. A later re-base must update the formula definitions, not assert equality of the chosen and explicit lists. |
| `clGroup` | `gate` and finite-kind selection | Same fixed-predicate-plus-variable-wiring pattern, including repeated wires. |
| `clFragment` | `fragment` | Same bytes and terminator convention. The append lemma also has a twin, as row 2 records. |
| `clChunks_serialize`, `clEmitter_of_body` | `polyTimeComputable_serialize_flatMap` | Same ordered serialization goal. The new theorem consumes polynomial-time chunks; the old emitter theorem consumes explicit native producer/body seams. This is an abstraction/re-basing correspondence, not a textual theorem replacement. |
| `clA5Template_native` | `polyTimeComputable_fragment_relabel` | Adequate strengthening: only actually relevant wire indices need polynomial-time witnesses. |
| `clA5Add/Sub/Times/Div/Mod/Le_native` | Unary arithmetic family | Covers the old uses, with variable multiplication and division additionally needed by the codec. Fixed exponentiation is enough because the number of tapes is fixed. |

`Complexity/FormulaKit/` is a coherent home for the combined topic: Gate has only the CNF layer below it, while Emit requires polynomial-time closure. Adding Emit to the low-level `Formulas` facade would invert that intended layering. Keeping the QBF suffix semantics in `Formulas/QBF.lean` is appropriate.

Unary arithmetic and the string-only `polyTimeComputable_flatMap_range` are more general than formulas. Their eventual canonical home can be the ClassNP closure layer, with FormulaKit consuming or re-exporting them. This is a modularity recommendation, not a correctness blocker: moving multiplication while leaving its generic ordered-emission dependency in FormulaKit would create the very reverse dependency to avoid. Handle the family together in the named deduplication window; do not make FormulaKit depend on `PolyHierarchy.Padding` merely to reuse its addition theorem.

The two codec blocks inside TQBF are appropriate under the binding in-place decision. Definitions precede the surviving private lemmas; public semantic theorems follow the old proved existential until its scheduled retirement. A separate codec module would reduce downstream imports, but no second live consumer is established here and file size alone is not a valid reason to override the decision. The promised root-facade import is still part of the landing checklist, not present in the bundled old root file.

**Migration, choices, and duplication**

| Fate | Declarations | Lines reproduced |
|---|---:|---:|
| KEEP | 39 | 510 |
| KEEP-R | 15 | 193 |
| MERGE | 10 | 48 |
| MOVE | 7 | 146 |
| REWRITE | 39 | 482 |
| RETIRE | 10 | 180 |
| Total | 120 | 1559 |

The totals are declaration spans including their attached docstrings, not the length of the entire B4a source interval. KEEP plus KEEP-R is `510+193=703` lines. The draft's approximately 820 counted merged twins and some declarations whose statements mention rewritten objects, so its discrepancy is explained. `codecTransitionCNF_step_iff` is correctly classified REWRITE even if most of its proof body remains useful.

I independently screened references in the surviving declaration spans after removing comments. No KEEP/KEEP-R row names a MOVE, REWRITE, or RETIRE row. The six structural/definition MERGEs match their public successors after the stated parameter and namespace renaming; the four cost-family MERGEs have the same generic interfaces. Existing proof terms are not claimed to be byte-identical to the public placeholders.

A1–A3's varying `equivFin` addresses are rewritten. A4's varying one-hot enumeration is replaced by explicit lists. A5's varying gate-index enumeration is rewritten. A6's post-wiring existential CNF selection is retired. Proof-side use of finite types or choice to realize a semantic witness is not an operational variable-numbering choice and need not be eliminated. The retained `stateIndex` and `caseList` choices are machine-constant and can be stored in a fixed emitter's finite control.

The current Mathlib documentation independently confirms the relevant general definitions: [`Fintype.equivFin`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Fintype/EquivFin.html) selects an equivalence from a truncation, and [`Multiset.toList`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Multiset/Basic.html) uses a quotient representative. Those current pages do not independently verify the packet's exact historical Mathlib line numbers; the pinned Mathlib sources are not bundled.

The corrected short copied-proof inventory is `cost_relabel` (one line), `cost_append` (one), `fragment_append` (one), `polyTimeComputable_unary_add` versus `clA5Add_native` (one), and `card_port` (three). Definition duplication is already identified in the pack: codec family, cost, packing, fragment, and excluding clause. The generalizations of Cook–Levin's substantial emission/arithmetic lemmas are presently statements with fresh sketches, not transcriptions of those long proved bodies. No additional wholesale debt requiring a new human-acknowledgment gate was found.

**Attestation disposition: each claim checked or bounded**

| Attestation | Independent check and limit |
|---|---|
| Bundle identity and population | Recomputed the SHA-256 and counted exactly 63 section headers before the audit. Both match. |
| Draft versus landing counts | Recounted 48 definition/type/abbreviation declarations and 47 theorems in the draft, with 11 proved and 36 admitted. Recounted 48 and 61 in the landing additions, with 20 supplied proofs and 41 direct admissions. |
| Old statement has no Lean proof consumer | The bundled Lean files contain its declaration and the disclosed documentation references only. The complete repository, blueprint, scripts, tests, and prior checkout are not all present, so the repository-wide negative remains a maintainer attestation. The in-place retirement decision is consistent with all supplied evidence. |
| Eight source files unchanged between the design checkout and tip; later commit changes unrelated | The bundle contains the asserted tip versions, not both historical trees or an independent commit diff. These are provenance attestations that this packet cannot independently prove. No contradictory source evidence was found. |
| 1: elaboration | All six proposed-source hashes and both evidence-tail hashes match the log. Reconstructed all three harnesses and both complete evidence files; all five reconstructed hashes match exactly. The displayed zero-error and sorry-warning counts are consistent with their source inventories, but Lean/oleans were unavailable for kernel replay. |
| 2: axioms | The evidence tails request the listed axiom checks, and their exact reconstructed files match the logged hashes. The QBF additions' output is at most `propext, Quot.sound`; the four conditional corollaries show `sorryAx`; the old existential shows the standard three. These are verified log-to-source correspondences, not a fresh axiom computation. |
| 3: freeze | Reproduced the declaration comparison: TQBF `172→236`, QBF `8→14`, no old declaration changed or removed, and old order preserved. Inspected the namespace/variable boundaries around the insertions as well; the added codec namespace does not enclose old declarations. The facade changes only documentation. |
| 4: names | The log's apparent missing names are explained by private visibility, namespace names, or module names. Checked the named private declarations in the bundled sources. A full-tree collision/absence screen cannot be reproduced without the rest of `TCSlib/`; no collision appears in the supplied population. |
| 5: lint | Independently checked the proposed line widths: no new overlong line, and the six long lines are inherited exactly. Checked public prose, reference sections, sketches, options in the new files, and facade contents. The lint tool itself is absent, so its exact run and the claim that it was unmodified remain execution attestations. The reported baseline findings are consistent with the sources. |
| 6: no lake, no oleans written, no git, isolated Python | The supplied run script uses `python3 -I` and invokes the external `leanelab.sh`; it has no direct lake/git/build-output invocation. That external helper and execution trace are not supplied, so historical absence of those operations cannot be independently certified. |
| 7: maintainer re-check | Reconstructed the harness/evidence bytes and reproduced the freeze and migration outputs. Both QBF and facade patches regenerate identically; applying the TQBF patch yields exactly the proposed file. Its regenerated hunk boundaries differ only in alignment around an unchanged blank line, so this is not source drift. The separate maintainer execution and unbundled `declfreeze.py v2` run remain supplied attestations. |
| Migration population and totals | Independently reproduced the full 120-row output, all counts, all span totals, and zero forbidden surviving dependencies. This verifies the current migration plan, not an already performed RD-2a migration. |
| Landing/export status | The proposed additions are identified as unlanded and the old proved existential remains intact in the proposal. The promised root import and record updates must accompany the eventual landing; no completed landing was inferred. |

The packet's evidence is sufficient for the stated external statement audit with these explicit limits. In particular, matching source and harness hashes is not a substitute for the maintainer's eventual fresh build of the actual module tree, and the 41 admissions remain the work of RD-2a/RD-2b.

**Glossary of mathematical notation used in this report**

`M` is the fixed machine; `k=M.k` is its number of work tapes; `n` is the nominal input length; `s` is the window radius; `x` is an input word; `c,d` are configurations; `W=width M n s` is the code width. `C,K` are machine-dependent bound constants. `ℓ` is template arity or the width variable in the old-shape evidence, according to context; `i,j,v` are indices; `p` is an input-head position; `h` is the mixed-radix head-tuple number; `r` is a recursion level. `qs` is a quantifier prefix; `G` is the number of auxiliary variables; `σ,τ` are Boolean assignments; `T(τ)` means that the CNF `T` evaluates to true at `τ`; `P` is its intended leaf predicate. `|x|` and `|qs|` denote list lengths; `card` denotes finite cardinality. All Lean declaration names retain the meanings in the packet.
