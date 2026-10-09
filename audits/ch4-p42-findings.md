# Chapter 4, P4.2 — statement-gate audit

**Verdict: PASS — 0 blockers, 0 majors, 5 minors, 3 notes.** All five definitions and all ten sorried statements were reviewed. The statements are true as written under the received conventions. Findings 1–5 concern documentation; none requires changing a declaration. The gate's zero-blockers/zero-majors criterion is met.

Input: `ch4-p42-bundle.md`, **24 attachments**, 5,260 lines. Independently computed SHA-256:

```text
5139d5aeeb9009888da2101c6a63ef70acf029a35265d567c8b7441db4de785c
```

The supplied snapshot is labeled commit `200f4693a40f30302efed75a4e23ac31216172b7`, branch `complexity/arora-barak-ch3-4`. This report audits that snapshot, not an independently fetched checkout. Line numbers below refer to the extracted attachments.

This is a **statement audit**, not a completed Lean proof. The mathematical arguments and resource bounds below justify the statements; implementation and kernel verification of the codec, search controller, frame stack, and composition routines remain fill work. P0 and P4.1 are treated as closed context. The concurrent §12, P4.3, and P4.4 gates are not reopened here.

**1. Findings**

Paths in this table are relative to `TCSlib/Complexity/SpaceComplexity/`, unless stated otherwise.

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | minor | `ConfigGraph.lean:196` · `acceptsWithin_of_spaceUsedWith_le`, sketch | When padding an accepting word, the padded siblings stay halted. | This theorem has no `HaltsWithin` hypothesis. Take a one-state, zero-work-tape machine: choice `false` emits `true` and halts; choice `true` stays in the initial state, stationary and silent. At empty input, `T = 1`, `s = 0`, both hypotheses hold and `configBound = 12`, but the all-`true` length-12 sibling is still live. The conclusion is nevertheless true: the accepting word alone can be padded. | Replace the sibling assertion by: “The accepting branch stays halted under padding, by `runWith_of_halt`.” Make the same correction in pack question 3. Do not add a halting hypothesis to the theorem. |
| 2 | minor | `ConfigGraph.lean:291` · `polyTimeReducible_of_mem_NL`, source attribution | The stated hardness conclusion is presented as Exercise 4.3 without explicitly identifying a correction. | The printed exercise, p. 93, says “complete for NL” for arbitrary nontrivial target languages. That is false without target membership in `NL`; an undecidable nontrivial target is a counterexample to completeness. The Lean theorem correctly asserts only hardness. Pack deviation 9 describes the formulation but does not explicitly identify this textbook error. | Preserve the theorem. Add: “Corrects Exercise 4.3's completeness wording to hardness; completeness additionally requires `L ∈ NL`.” |
| 3 | minor | `ConfigGraph.lean:170` · `configBound`, docstring | The received deterministic count is `Turing.MultiTapeTM.ConfigCount.configBound`. | In the supplied `ConfigCount.lean`, the count is declared in namespace `Turing.FinTM`, at line 311. The qualified name used in this docstring does not identify that declaration. | Replace it with `Turing.FinTM.configBound`. |
| 4 | minor | `ConfigGraph.lean:275` · `NL_subset_P`, sketch | The received proof of `LOGSPACE_subset_P` is the deterministic special case of the same search. | The supplied `ConfigCount.lean:449` proof keeps the original deterministic decider and bounds its halting time through `ComputesInSpace.computesFunInTime`. It constructs no breadth-first search or visited table. The common ingredient is configuration counting. | Say that the argument uses analogous count arithmetic; distinguish the nondeterministic search construction from the received same-machine time bound. |
| 5 | minor | `ConfigGraph.lean:257` · `NSPACE_subset_exp_dtime`, introductory prose; pack deviation 5 | The `+ 1` keeps the exponent positive. | The union permits `c = 0`, so `c * (S n + 1) = 0`. The time bound is still positive: `2^0 = 1`. Moreover `hS` already implies `S n ≥ 1`. This does not affect the theorem or its asymptotic rendering. | Describe the displayed time bound as everywhere positive, and the `+ 1` as a harmless normalization useful in the input-factor estimate. Do not claim every exponent is positive. |
| 6 | note | `ConfigGraph.lean`, `Savitch.lean` · finite-graph consumers | The raw edge relation and the finite summary graph are related, but are not the same typed object. | `CfgStep` relates full `Cfg`s, whereas `coreSum` forgets output history and `coreCode` additionally requires a window condition for injectivity. A finite search must use the induced summary transitions and lift paths back to actual runs. The arguments in §5 supply this bridge without changing the statements. | No declaration repair. Carry into fill: canonical decoding, outside-window rejection, quotient path lifting, enumeration of accepting vertices, and the reflexive base case of bounded reachability. |
| 7 | note | `ConfigGraph.lean:257`; `Savitch.lean:77,110` · resource accounting | Constructor execution and actual visited cells must be included in the simulations. | `SpaceConstructible` promises a halting space-bounded constructor, not a time bound syntactically. The received deterministic count theorem supplies its exponential time bound. Savitch must reuse fixed tape intervals, not merely bound simultaneously live data. Polynomial construction must output exactly `(n^c + 1).bits`, including at `n = 0`. All these obligations are satisfiable; see §5. | Carry the explicit ledgers below into fill. For the polynomial catalog route, verify its exact output contract and implement the final `+ 1`; asymptotic domination alone does not compute the requested function. |
| 8 | note | Pack · provenance, sweep, lint, concurrent interfaces | What the supplied evidence independently establishes. | The bundle hash, attachment count, source inventory, facade imports, ten matching warning locations, three sweep module markers, zero logged `error:` lines, and 42 distinct lint file rows were checked. The log reports completion but contains no independently checkable fresh-`.olean` evidence. No git history or §12 routine source files are attached. | Treat revision identity, the `50d72880..200f4693` prose-only comparison, and fresh artifacts as maintainer attestations. This report does not certify those claims, a new Lean build, or the pending §12 interfaces. No statement-gate obstruction follows. |

**2. Integrity, coverage, and source comparison**

The extracted source has 12 explicit declarations in `ConfigGraph.lean` (five definitions/type declarations and seven theorems), and three theorems in `Savitch.lean`. Every theorem body is `sorry`; there are no authored skeleton-time proofs in those two files. These are source-declaration counts, not a kernel inventory of automatically generated inductive declarations and instances. The facade imports both modules.

| Check | Independently observed |
|---|---|
| Bundle integrity | Exact match to the commissioned SHA-256 above |
| `ConfigGraph.lean` | 295 lines; 5 definitions/type declarations; 7 `sorry`s |
| `Savitch.lean` | 131 lines; 3 `sorry`s |
| Sweep log | Revision recorded at start; 3 modules; 10 warnings at the supplied theorem lines; no `error:` line; completion marker |
| Shared lint log | 42 distinct file paths; reported `0 FAIL, 0 WARN`; in-scope declaration counts match |
| Baseline history and fresh elaboration | Not independently reproduced; see finding 8 |

Comparison text: Arora–Barak, *Computational Complexity: A Modern Approach* (2009), [primary book text, PDF mirror](https://theswissbay.ch/pdf/Gentoomen%20Library/Theory%20Of%20Computation/Sanjeev_Arora,_Boaz_Barak-Computational_complexity__a_modern_approach-Cambridge_University_Press(2009).pdf). Printed pages 79–81 supply the constructibility convention, configuration graph, count, and exponential simulation; pp. 85–86 supply Savitch and the polynomial-space consequence; pp. 88 and 92 supply the logarithmic-class comparison; p. 93 contains Exercise 4.3. The hardness/completeness correction is recorded in finding 2. The campaign's visited-cell measure, append-only output, positive normalization, and all-branch halting convention remain the declared received deviations.

**3. Blind restatements from the five declaration bodies**

| Definition | Mathematical reading of the body | Comparison and delivered strength |
|---|---|---|
| `Turing.OutSummary` | A type with exactly three constructors, `empty`, `accept`, and `dead`, with decidable equality. The type by itself does not impose a meaning on any output word. | The meaning is supplied by `outSummary`; this is additional infrastructure for the campaign's output-based acceptance convention. |
| `Turing.outSummary` | Sends the empty Boolean list to `empty`, the singleton true list to `accept`, and every other list to `dead`. | Exactly the three classes needed to decide whether appending a suffix can produce `[true]`. It does not itself test halting. |
| `Turing.NDTM.coreSum` | Maps a configuration to its control state, input-head position, entire work-tape functions, work-head positions, and the summary of its output. Input `x` is fixed by the configuration's type. | Work-tape contents are not truncated here. This target need not be finite: bounded-window coding is a later restriction. Full outputs with the same summary are identified soundly. |
| `Turing.NDTM.CfgStep` | For a fixed machine, `c` is related to `c'` exactly when some Boolean choice makes one `stepWith` send `c` to `c'`. | A relation on full configurations, without a space/window predicate. There are at most two successors; a halted configuration has a self-loop. The declared relational rendering is sound. |
| `Turing.FinNDTM.configBound` | Returns `3 * ((card State + 1) * (n + 2) * 3^(k*(2*s+1)) * (2*s+1)^k)`. | Counts the finite coding universe: summary, optional state, input position, ternary contents of each window cell, and work-head positions. It upper-bounds reachable bounded-window summary vertices, not all full configurations or just the reachable vertices. |

No definition silently tests acceptance by `outSummary = accept` alone: the theorem interfaces additionally require the state to be halted. There is also no finiteness assumption missing from the two raw-machine theorems; only the counting theorem needs, and receives, `FinNDTM`.

**4. True-as-stated arguments for all ten statements**

Each row concerns the literal supplied signature. Detailed arithmetic and endpoint arguments follow in §5.

| Statement | Argument |
|---|---|
| `NDTM.reflTransGen_cfgStep_iff` (`ConfigGraph:140`) | A reflexive reachability derivation is realized by `[]`. Appending the witness bit for each additional edge extends the realizing word, by `runWith_append`. Conversely, induction on a choice word realizes each consumed bit as a `CfgStep` and composes the edges. Neither direction needs halting, finiteness, or a space bound. |
| `NDTM.coreSum_stepWith` (`ConfigGraph:156`) | Equal cores give equal states and scanned symbols, hence the same action under the same choice. That action updates equal cores equally and appends the same optional emission to both outputs. The append table in question 1 preserves summary equality; the halted case is identity on both sides. |
| `FinNDTM.acceptsWithin_of_spaceUsedWith_le` (`ConfigGraph:196`) | Apply the sibling-space hypothesis to an accepting witness word, obtaining a finite window for every prefix. Delete any segment between equal summary vertices; the remaining suffix has the same successive summary vertices and still accepts. A shortest such path has at most `configBound` vertices, hence fewer than that many steps, and the accepting word pads to the exact required length. Sibling halting is unnecessary. |
| `FinNDTM.DecidesInSpace.mem_iff_acceptsWithin_configBound` (`ConfigGraph:218`) | For membership, use the deciding budget and the preceding shortening lemma. Conversely, an accepting word at the configuration budget either pads to the deciding budget or has an already-halted deciding-length prefix with identical final output. In both cases the equivalence supplied by `DecidesInSpace` gives membership. |
| `Complexity.NSPACE_subset_exp_dtime` (`ConfigGraph:257`) | Hardwire the nondeterministic decider and the constructor for `S`, and search the finite coded graph within radius `c₀*S n`. The constructor and the search both take `2^{O(S n)}` time by the explicit calculation in question 5, including input access and table operations. Graph acceptance is equivalent to membership by the preceding interfaces and the quotient lifting argument. A fixed natural exponent coefficient and `DTIME`'s multiplicative constant package this into the stated union. |
| `Complexity.NL_subset_P` (`ConfigGraph:275`) | Apply the exponential-time inclusion with the received `spaceConstructible_logSpace`. For every fixed exponent coefficient, `2^(c*(logSpace n+1)) ≤ 2^(2*c)*(n+1)^c`, including `n = 0`. The latter is a polynomial budget and converts to the campaign's `n^c+1` form by constant absorption. |
| `Complexity.polyTimeReducible_of_mem_NL` (`ConfigGraph:291`) | Choose the two fixed finite target strings supplied by the hypotheses. Decide `L'` using `NL_subset_P`, and output the positive witness on acceptance and the negative witness otherwise. This is a polynomial-time function satisfying the required membership equivalence; it never decides membership in the arbitrary target language. |
| `Complexity.spaceConstructible_poly` (`Savitch:77`) | For `c ≥ 1`, `logSpace n ≤ n+1 ≤ n^c+1` for every natural `n`. Count the input length in binary, compute its fixed power, add one, and emit the result; a direct binary implementation uses at most `A_c*(logSpace n+1) ≤ 2*A_c*(n^c+1)` visited cells. The empty input emits `[true]`. The sketch's unary catalog route is also viable once its exact output and positive-bound packaging are supplied. |
| `Complexity.savitch` (`Savitch:110`) | The finite graph has `log₂ V = O(S n)` and an `O(S n)`-bit code and adjacency workspace. Depth-first evaluation of midpoint reachability stores `O(S n)` frames of `O(S n)` bits, reusing the child workspace between calls and the same physical tape interval across iterations. Constructor, target enumeration, and administrative space contribute only `O(S n)`. Since `S n ≥ 1`, the total is at most a fixed constant times `S n * S n`. |
| `Complexity.PSPACE_eq_NPSPACE` (`Savitch:128`) | The forward inclusion is the received deterministic-to-nondeterministic inclusion, degree by degree. For the reverse inclusion, absorb degree zero into the degree-one bound with twice the old multiplicative constant. Apply polynomial constructibility and Savitch, then absorb the square using `(n^c+1)^2 ≤ 4*(n^(2*c)+1)`. Both absorptions are valid also at the empty input. |

**5. Answers to the pack's eight questions**

**Question 1 — the output quotient.** The complete one-step table is:

| Previous summary | No emission | Emit `false` | Emit `true` |
|---|---|---|---|
| `empty` | `empty` | `dead` | `accept` |
| `accept` | `accept` | `dead` | `dead` |
| `dead` | `dead` | `dead` | `dead` |

For an arbitrary appended word `e`, an empty previous output gives `outSummary e`; an output `[true]` remains `accept` exactly when `e = []`; a dead output remains dead. Indeed, if `u ++ e = [true]`, then `u` must be a prefix of `[true]`, hence `u = []` or `u = [true]`. Thus no dead prefix can recover.

This proves the exact characterization

$$
\operatorname{outSummary}(u)=\operatorname{outSummary}(v)
\iff
\forall e,\quad\bigl((u\mathbin{++}e=[\mathrm{true}])
\iff(v\mathbin{++}e=[\mathrm{true}])\bigr).
$$

For the reverse implication, the suffix `[]` distinguishes `accept` from either other class; `[true]` distinguishes `empty` from `dead`. The three classes are therefore minimal for a summary supporting all possible append suffixes. A particular machine with restricted emissions may admit a smaller abstraction, which is not the claim here.

Equal `coreSum`s also give equal halting status. On live states, action selection never reads old output, and the same choice bit selects the same action. Combining this observation with the table proves the stated one-step congruence and, by induction, congruence under every common choice suffix.

**Question 2 — reachability endpoints.** Reflexivity corresponds exactly to an empty choice word. A one-edge witness `b` is realized by `[b]`, and extending a word `w` by `[b]` uses

$$
\operatorname{runWith}(w\mathbin{++}[b],c)
=\operatorname{stepWith}\bigl(b,\operatorname{runWith}(w,c)\bigr).
$$

For the reverse induction, the first edge goes from `c` to `stepWith b c`, followed by the path for the remaining word. If `c` is halted, every step and every run leaves it unchanged, so the only reachable configuration from it is itself. Self-loops create no endpoint mismatch.

**Question 3 — the bounded accepting branch.** Fix an accepting word `w` of length `T`. The hypothesis bounds this word in particular. On each tape, the visited set contains zero and every integer between zero and any visited position, because a head moves by at most one per step. Consequently

$$
|z|+1\le \#\operatorname{visitedWith}(w,i)\le s
$$

for every visited position `z` on tape `i`. Every nonblank cell was previously visited, since initialization is blank and a transition writes only at a head. All prefix cores therefore satisfy the hypotheses of `coreCode_inj` in the wider window `[-s,s]`.

For a repeated summary vertex, write the choice word as `u ++ v ++ e`, with `v` nonempty and equal `coreSum`s after `u` and `u ++ v`. Iterated `coreSum_stepWith` gives

$$
\operatorname{coreSum}(\operatorname{runWith}(u\mathbin{++}e,\operatorname{initCfg}(x)))
=\operatorname{coreSum}(\operatorname{runWith}(u\mathbin{++}v\mathbin{++}e,\operatorname{initCfg}(x))).
$$

The right side has halted state and summary `accept`, so the left side also has halted state and represents output exactly `[true]`. Every vertex of the new path is a vertex of the old path: before the cut it is unchanged; afterwards it matches the corresponding suffix vertex. Window validity is consequently preserved.

Choose a shortest accepting word whose prefix vertices lie in this finite window. The preceding deletion rules out repeated vertices. If its length is `t`, injection into the code universe gives

$$
t+1\le N.\operatorname{configBound}(n,s),
\qquad t<N.\operatorname{configBound}(n,s).
$$

`AcceptsWithin.mono` pads to the exact budget. If the original `T` is already no larger than that budget, padding the original accepting word suffices. Neither operation requires sibling halting. The all-siblings space premise is stronger than necessary for this single-branch argument but matches the packaged decision interface faithfully; it does not weaken the intended class consequence.

**Question 4 — the packaged iff.** Let `T` be the decision budget and `V = N.configBound n (s n)`. If `V ≤ T`, acceptance at `V` implies acceptance at `T` by padding. If `T ≤ V`, write a length-`V` accepting word as `w.take T ++ w.drop T`; its prefix has length exactly `T`, so `HaltsWithin x T` applies. The run equations give

$$
\operatorname{runWith}(w,\operatorname{initCfg}(x))
=\operatorname{runWith}(w.\operatorname{take}(T),\operatorname{initCfg}(x)).
$$

Thus the prefix already has output `[true]`, and the equivalence at `T` gives membership. Equality of the budgets is covered by either case. The forward direction uses the deciding witness's space premise directly.

**Question 5 — exponent normalization and uniformity.** Fix the machine and its class constant `c₀`, and put `n = length x`, `k = N.k`, `s = c₀*S n`, and `V = N.configBound n s`. The logarithmic floor gives

$$
S(n)\ge1,\qquad n+2\le2^{S(n)+1}.
$$

For positive `n`, use `n < 2^(logSpace n)` and then double the latter power; for `n = 0`, the inequality is `2 ≤ 2^(S 0+1)`. For all natural `s`,

$$
3^{k(2s+1)}\le2^{2k(2s+1)},\qquad
(2s+1)^k\le2^{k(s+1)},
$$

and hence

$$
\begin{aligned}
V
&\le3(\#N.\mathrm{State}+1)(n+2)\,2^{5ks+3k}\\
&\le3(\#N.\mathrm{State}+1)\,
2^{(5kc_0+1)S(n)+3k+1}.
\end{aligned}
$$

All constants depend on the fixed machine and its space multiplier, not on `x`. This yields a code width `O(S n)`. Binary encodings may have unused bit patterns; enumerating and rejecting them still costs only a fixed polynomial in the finite code count if fixed-width component encodings are used.

A tape implementation need not have constant-time table lookup or unit-cost random access to the input. Store the discovered codes and a queue sequentially; scan the table for membership and reposition the input head when needed. There are at most two successor computations per processed vertex. Encoding, comparison, queue maintenance, and table scans give a bound of the form

$$
A\,(V+n+S(n)+1)^d\le A'2^{C(S(n)+1)}
$$

for fixed natural constants. This follows from the displayed bound on `V`, the bound on `n+2`, and `S(n)+1 ≤ 2^(S(n)+1)`; fixed powers multiply the exponent by a fixed constant. Thus the whole table ledger fits the stated union.

There is also a constructor cost. If `M` is the `SpaceConstructible` witness, its actual halting run uses at most `a*S n` cells. The **received deterministic** `FinTM.ComputesInTime.of_spaceUsed_le` bounds that run by `M.configBound n (a*S n)`, which the same arithmetic bounds exponentially. This is not circular: that received theorem predates the nondeterministic simulation. Capturing `(S n).bits` on a work bank costs `O(S n)` cells because `S n ≥ 1`; input-head restoration and bank administration fit the same allowances.

Constructibility therefore supplies effective, uniform bound computation in this construction, and its dominance conjunct supplies essential size estimates. Merely asserting the existence of a suitable radius separately for each input would not supply the uniform simulator described in the sketch. The machine, constructor, and constants are chosen once per language, not once per input. Since `S ≥ 1`, replacing `S` by `S+1` changes only a constant factor in the exponent. The `c = 0` union component is harmless.

For `NL_subset_P`, the direct normalization, with `logSpace n = Nat.log 2 n + 1`, is

$$
\begin{aligned}
2^{c(\operatorname{logSpace}(n)+1)}
&=2^{2c}\bigl(2^{\operatorname{Nat.log}(2,n)}\bigr)^c\\
&\le2^{2c}(n+1)^c\\
&\le2^{3c}(n^c+1).
\end{aligned}
$$

The first inequality uses `2^(Nat.log 2 n) ≤ n+1`, valid also at zero. The last inequality is immediate for `n = 0`; for `n ≥ 1`, use `n+1 ≤ 2*n`. This avoids needing any BFS implementation detail a second time.

**Question 6 — Savitch, finite graph, and the polynomial consequence.** Interpret the finite graph on valid window codes paired with summaries. Decode work cells outside the window as blank; compute a chosen transition and reject the edge if its resulting core leaves the window. `coreCode_inj` and `coreSum_stepWith` imply that the resulting summary transition is independent of the chosen full-output representative. Inductively lifting each edge from the actual initial configuration gives an actual choice-word run with the recorded summaries. Conversely, every genuinely space-bounded run projects to this graph.

This graph can contain configurations violating the original *total* space budget while fitting the wider per-tape windows. That introduces no false acceptance: any path from the initial vertex still lifts to a genuine run, and `DecidesInSpace` already bounds all runs. The extra vertices only enlarge a sound search domain.

Use depth `i = ceil(log₂ V)` and the recurrence

$$
\begin{aligned}
\operatorname{reach?}(u,v,0)
&\iff u=v\ \lor\ \operatorname{edge}(u,v),\\
\operatorname{reach?}(u,v,i+1)
&\iff\exists m,\ 
\operatorname{reach?}(u,m,i)\land\operatorname{reach?}(m,v,i).
\end{aligned}
$$

The base-case equality is required because the predicate means length **at most** `2^i`. The recurrence is exact: concatenation proves one direction; in the other, split a path after the smaller of its length and `2^i`, allowing a zero-length remainder. A simple accepting path has fewer than `V` edges, so this depth suffices. Since acceptance need not have a unique target configuration, enumerate all halted vertices with summary `accept`, reusing the reachability workspace between targets.

Each frame stores a vertex pair, midpoint cursor, depth, and a constant amount of control information. The code width is `O(S n)` and the depth field fits within that allowance. Choose fixed constants so that the frame count is at most `A*S n`, frame size at most `B*S n`, and all other workspace at most `C*S n`; then

$$
\operatorname{spaceUsed}\le AB\,S(n)^2+C\,S(n)
\le(AB+C)\,S(n)^2.
$$

For the received visited-cell measure, this bound must hold for a fixed physical stack interval and fixed scratch intervals, including their initial origins and boundary markers. Resetting a scratch routine at ever-increasing tape offsets would invalidate the argument. Reusing the same stack slots and auxiliary banks meets the bound. The constructor uses `O(S n)` additional space; its potentially long running time is irrelevant to this space theorem. No monotonicity of `S` is needed, and the large graph is never stored in full.

For `spaceConstructible_poly`, a concrete alternative to the unary catalog route is a binary length counter and fixed-many multiplications followed by one increment. All counters can occupy fixed intervals of `O_c(logSpace n+1)` cells. The dominance and pointwise resource estimates are

$$
\operatorname{logSpace}(n)\le n+1\le n^c+1,
\qquad
A_c(\operatorname{logSpace}(n)+1)\le2A_c(n^c+1)
\quad(c\ge1).
$$

At zero, the target is `1`, so the output is `[true]`; a counter that merely emits `n^c` would be wrong. The sketch's ordinary asymptotic `O(n^c)` wording must ultimately be packaged as the positive bound `A*(n^c+1)` in `ComputesInSpace`.

Degree zero cannot satisfy the dominance conjunct: `logSpace 4 = 3 > 4^0+1 = 2`. Nevertheless an `NSPACE (n^0+1)` witness with multiplier `c₁` satisfies, at every length,

$$
c_1(n^0+1)=2c_1\le(2c_1)(n+1).
$$

The repaired degree-zero routing is therefore correct, including at zero. After Savitch, the square is absorbed by

$$
\begin{aligned}
(n^c+1)^2
&=n^{2c}+2n^c+1\\
&\le2(n^{2c}+1)\\
&\le4(n^{2c}+1).
\end{aligned}
$$

The middle inequality follows from `2a ≤ a²+1` for `a = n^c`. A machine multiplier `b` becomes `4b`; `SPACE.mono` alone does not erase the factor four. This explicitly supplies both constant absorptions promised in the sketch.

**Question 7 — Exercise 4.3 and choice.** The hypotheses are exactly target nonemptiness and nonuniversality. Choose the fixed finite words `y₀` and `z₀`, and use a polynomial-time decider for `L'`. Its two outcomes produce the corresponding fixed word, so

$$
f(x)=\begin{cases}y_0&x\in L',\\z_0&x\notin L',\end{cases}
\qquad x\in L'\iff f(x)\in L.
$$

The runtime is the decider's polynomial runtime plus a fixed output cost. Classical selection of two finite constants does not make this function noncomputable: the constructed machine hardwires those strings and tests only `L'`. The cited conditional interface must receive that computable decision test, not an assumed algorithm for the target language. The formal conclusion is correct for undecidable target languages as well; only the textbook completeness wording needs the correction in finding 2.

**Question 8 — adversarial instantiations.** The cases below include every case suggested by the pack and several additional attacks. Passing finite checks supports, but does not replace, the general arguments above.

| Case | Instantiation and calculation | Result |
|---|---|---|
| A1: zero space, positive tape count | Every tape's initial origin is visited, so `k ≤ spaceUsedWith`. With `s = 0`, the sibling-space hypothesis forces `k = 0`. | No positive-tape machine slips into the zero-space premise. The arithmetic formula at radius zero remains `3*(card State+1)*(n+2)*3^k`. |
| A2: zero tapes and empty input | One live state, no work tapes, immediate accepting halt. At `n = s = 0`, the count is `3*(1+1)*2 = 12`. | A one-step accepting word pads to 12. Empty input and exponent-zero factors cause no collapse. |
| A3: `T = 0` | The sole word is `[]`; `runWith []` is identity. A genuine initial configuration has state `some q₀` and empty output. | `N.AcceptsWithin x 0` is false for every `FinNDTM`, not a realizable initially accepting exception. Raw reachability from an already halted arbitrary configuration still has its reflexive witness. |
| A4: nonhalting sibling | The machine in finding 1 accepts on `false` and loops on every `true`. All branch spaces are zero. | Shortening/padding theorem applies, but sibling halting is false. `DecidesInSpace` cannot hold for this machine. |
| A5: deleting the only emission | Zero tapes, one live state. `false` emits `true` and stays; `true` halts silently. The word `[false,true]` accepts, while `[true]` rejects. | Initial and post-emission cores coincide, so a core-only splice is unsound. Their summaries differ, preventing this deletion. |
| A6: a long accepting branch | Zero tapes, one state; `false` loops silently and `true` emits `true` and halts. At empty input, 13 false choices followed by true accept in 14 steps, exceeding count 12. | Remove the silent cycle, accept in one step, then pad to 12. A machine with an accepting branch but **no** accepting word at or below the count cannot meet the lemma's premises. |
| A7: all-rejecting output | A machine immediately halts with `[false]`, `[]`, or `[true,true]` on both choices. | It decides the empty language. At every configuration budget there is no accepting branch, as required by the packaged iff. |
| A8: summary without halting | An emission produces `[true]` while the machine remains live. | Summary `accept` alone does not satisfy `AcceptsWithin`; the graph target test must also require the halted state. |
| A9: both budget orders | The immediate accepting decider permits deciding budget `T = 1` or `T = 20`, by halting absorption; its zero-input count is 12. | The same concrete machine exercises truncation for `1 < 12` and padding for `12 < 20`. |
| A10: trivial target languages | With target `∅`, the positive witness is impossible; with the full language, the negative witness is impossible. | The reduction theorem correctly excludes both obstructions. |
| A11: degree zero and one | At `n = 0`, `n^0+1 = 2 > n+1 = 1`; at `n = 4`, `logSpace n = 3 > 2`. | Bare pointwise monotonicity and degree-zero constructibility both fail. The doubled multiplier succeeds. Degree one is everywhere positive and dominates `logSpace`. |
| A12: dropping the logarithmic floor | A zero-work-tape parity decider uses constant space but needs unbounded input-reading time. For constant `S`, every function `2^(c*(S n+1))` is constant. | The inclusion would be false without the floor. `SpaceConstructible` excludes this attempted counterexample; effective bound computation alone would not suffice. |
| A13: remote nonblank cell | Two raw configurations differ only at a cell outside `[-s,s]`; their truncated codes can coincide. | `coreCode` is not globally injective. The actual-prefix window proof supplies precisely the missing side condition. |
| A14: dead histories | Compare outputs `[false]` and `[true,true]`, followed by every possible common emission. | Full outputs differ, but both remain dead; identifying them cannot create an accepting suffix. |
| A15: zero class multiplier | A zero-tape decider can satisfy `NSPACE S` with class multiplier zero, including when `S = logSpace`. | The count still retains the input-position factor `n+2`. No part of the proof assumes `c₀ > 0`; the logarithmic floor absorbs that factor. |

For A12's time lower bound, suppose a deterministic parity decider had a fixed time budget `t`. Choose `n > t+2`. On the two length-`n` inputs `0^n` and `0^(n-1)1`, every input cell it can inspect in its first `t` steps agrees. Induction on those steps gives identical configurations apart from the unread input, hence identical outputs, contradicting the opposite parities.

As additional mechanical checks, an independent finite model verified 12,645 append-summary comparisons (old words of length at most four and suffixes of length at most three), and all 36 one-state zero-tape transition tables with stationary input heads and optional Boolean emissions, through the zero-input count 12. It also reproduced the sibling and core-only-splice counterexamples. Arithmetic boundary checks covered `n,s = 0..256` and degrees `1..6`. These checks are not Lean proofs and are not the basis for the universal claims.

**6. Disposition of the nine declared design decisions**

| Pack item | Assessment |
|---|---|
| 1: core plus three summaries | Sound and minimal for arbitrary append suffixes; question 1. |
| 2: relation instead of finite graph object | Sound declared representation; finite quotient lifting remains explicit fill work, finding 6. |
| 3: explicit count | Correct cardinality of the coding universe; source-reference typo only, finding 3. |
| 4: all-siblings space premise | Sufficient and directly usable from `DecidesInSpace`; sibling **halting** is a separate condition, finding 1. |
| 5: exponential union and `+1` | Correct strength and normalization; positivity wording corrected by finding 5. |
| 6: iterative Savitch stack | Delivers `SPACE (S*S)` if fixed physical work intervals are reused; question 6 gives the visited-cell ledger. |
| 7: exclude degree zero | Necessary for the chosen constructibility predicate; the repaired constant absorption is valid at every length. |
| 8: absorb the square | Correct; multiplier explicitly changes to four times its old value. |
| 9: nontriviality witnesses and hardness | Correct theorem; identify the source's completeness error explicitly, finding 2. |

**7. Suggested additive sanity lemmas for fill**

No frozen statement needs alteration. The most useful small permanent checks are:

- `outSummary (u ++ e)` preserves equality of `outSummary u`, together with `outSummary u = .accept ↔ u = [true]`.
- Iterated `coreSum_stepWith` for an arbitrary common choice word.
- `¬ N.AcceptsWithin x 0`, and `N.k ≤ N.tm.spaceUsedWith w (N.tm.initCfg x)`.
- A bounded-code transition/lifting lemma with the window condition explicit, plus the zero-length case of bounded reachability.
- The constructor's exponential time bound derived from the received deterministic count theorem, and the two constant-absorption steps used by `PSPACE_eq_NPSPACE`.

**Notation glossary.** Existing declaration names retain their supplied meanings. Locally, `n` is input length; `k` is the machine's work-tape count; `s` is a concrete window radius; `S` is the space-bound function; `V` is the displayed configuration count; `T,t` are time budgets/word lengths; `u,v,w,e` are words in the append arguments and `u,v,m` are vertices in the reachability recurrence; `++` denotes list concatenation; `i` is a tape index or recursion depth as indicated; `c₀,c₁,a,b` are fixed machine space multipliers, except `a = n^c` in the square calculation and `b` is a choice bit in question 2; `c,d` are fixed natural exponents, while `c,c′` in the raw-reachability discussion are configurations; `A,A′,A_c,B,C` are input-independent resource constants; `y₀,z₀` are fixed positive/negative target witnesses; `f` is the reduction; `#` denotes cardinality. `edge` and `reach?` denote the finite-code adjacency and bounded-reachability predicates described in question 6, not additional supplied Lean declarations.
