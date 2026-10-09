# P3.3 statement-gate audit

**Verdict: FAIL — 0 blockers, 2 majors, 7 minors, 2 notes. The gate remains open.**

The two majors concern the quantitative construction in `ntime_hierarchy`'s proof sketch. I found no counterexample to a literal Lean theorem statement. In particular, the findings do **not** refute the nondeterministic time hierarchy theorem. They identify missing arguments needed to turn this phase's particular interfaces and sketch into the promised uniform machine construction.

Audited input: `ch3-p33-bundle.md`, purported revision `a664c3e407a24e862d3ce719e589a8ef6533798c`. Its SHA-256 independently matches:

`45339e257283d441ad0afd38a6ed9d6c563ef72688a3f6b6e58b833e3b031ee1`

Scope: all seven definition bodies, seven sorried contracts, their sketches/docstrings, and `NDMachineCode.decode_encode`; the attached closed interfaces were read where needed. This was a single-agent audit. Declaration references below use the original attachment line numbers. `NDCodes.lean` and `NTimeHierarchy.lean` abbreviate the two full paths specified in the pack.

Primary-source comparison: [Arora–Barak, *Computational Complexity*, 2009, reproduced PDF](https://theswissbay.ch/pdf/Gentoomen%20Library/Theory%20Of%20Computation/Sanjeev_Arora,_Boaz_Barak-Computational_complexity__a_modern_approach-Cambridge_University_Press(2009).pdf), printed pp. 16, 19–20, 41–42, 64, 69–71, and the Exercise 2.6 hint on pp. 531–532. I checked the total-code/padding requirements, binary-choice and all-branch-time conventions, linear simulation exercise, and the delayed-diagonalization construction. The source states the shifted little-o hypothesis and illustrates a separation between linear time and time with exponent 3/2. Neither the referenced definition of time constructibility nor Theorem 3.2 explicitly adds monotonicity. No external Cook or Book–Greibach–Wegbreit text was needed.

**Findings**

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | major | `NTimeHierarchy.lean` · `ntime_hierarchy`, sketch at lines 215, 220, 225, 227 | The per-code universal bound and arbitrarily large padded indices yield both a uniformly `O(g(n)+1)` diagonal machine and the required successful stage. | The universal provides `∀ α, ∃ Cα`, whereas class membership needs one constant for all input lengths and therefore all stages. Choosing a budget proportional to `g(n)` does not absorb unbounded `Cαᵢ`. Dividing the budget by `Cαᵢ` creates a second problem: padding changes `αᵢ`, hence potentially the constant and its eventual-domination threshold. Padding preserves `decode`; no stated law preserves cost. The inference from “arbitrarily large padded index” to “past the threshold for that index's constant” is invalid. Details below. | Supply a concrete uniformly clocked diagonal construction and resolve the padding dependence. Options include an explicit interpreter estimate with a padding-independent simulation rate plus controlled startup, or scheduling the **same fixed code** at arbitrarily late stages. Define the actual budget and account for computing it. At the stage bottom also require the bound for `f(a)`, not only `f(a+1)`. Preserve the linear-overhead signatures. |
| 2 | major | `NTimeHierarchy.lean` · `ntime_hierarchy`, sketch at lines 211, 212, 213, 217, 221 | The displayed recurrence defines an effective stage locator running in `O(g(n))`. | “BF's bound” uses existential code-dependent coefficients with no computability export. A sequence selected by classical choice is not automatically a TM-computable sequence. Even with explicit coefficients, the sketch does not supply a capped evaluation procedure or an amortized locator ledger. The top-branch inequality pays for BF **at the top**; it does not pay for finding the top from an interior input. `TimeConstructible g` does not imply `g(a) ≤ g(n)` for `a < n`. | Specify computable stage data, include the cost of code/budget preparation, and give a locator using bounded evaluation of the next stage value. Prove its cumulative cost, including the final incomplete computation, is bounded by one fixed multiple of `g(n)+1`. Explain how its clock itself has linear total cost. |
| 3 | minor | `NDCodes.lean` · `exists_effectiveNDMachineCode`, line 174 | There are `2 · 9` transition records per state. | The actual definition enumerates two choices and three reads independently on the input and each of two work tapes: `2 · 3 · 3 · 3 = 54 = 2 · 27`. Following the stated 18-record parser plan would not parse the actual serialization. | Replace `2 · 9` by `2 · 27`; update the parser's minimum-length guard and all enumeration lemmas accordingly. |
| 4 | minor | `NDCodes.lean` · `exists_effectiveNDMachineCode`, lines 178, 179 | The polynomial canonizer ledger is inherited from the deterministic construction. | Attached `MathlibBridge.lean`, lines 1078, 1085, 1089, explicitly supersedes the polynomial construction and delivers an arbitrary-time computability route. A polynomial ND parser/canonizer is plausible, but is a new obligation, not a received time ledger. | Either follow the arbitrary-time mirror, which suffices for the literal existence statement, or explicitly commission and justify a new polynomial construction. If hierarchy costs use the stronger property, expose and prove it. |
| 5 | minor | `NTimeHierarchy.lean` · `exists_timed_universal_NDTM`, lines 101, 105, 106 | Each binary decrement, and hence each simulated step, costs `O(table length)` independently of `t`. | At `t = 2^r`, an ordinary first decrement borrows across `r` low zero bits. Its worst-case cost is unbounded with `r` even for a fixed one-state table. The **total** countdown can nevertheless be linear; the amortized proof below repairs the argument. | Say “amortized,” name the counter representation/zero test, and include the total borrow-and-return ledger. Fusing the clock alone does not establish the claimed bound. |
| 6 | minor | `NTimeHierarchy.lean` · `FinNDTM.exists_codeNDTM_accepts_linear`, line 166 | The construction costs `O_N(k · t)` for every `k`. | For `k = 0`, it still guesses a display and performs the input-verification sweep. A bound proportional to `k · t` is zero. The theorem's `C · (t+1)` is sound. | Use `O_N((k+1)(t+1))`, then absorb the fixed tape count into `C`. |
| 7 | minor | `NTimeHierarchy.lean` module docstring, lines 34, 35, 36; pack deviation 4 | Under the contradiction hypothesis the coded machine beats the budget, so timeout polarity never matters. | The normal-form theorem deliberately gives no all-branch halting guarantee for the coded machine. Its proposed guess phase has infinite nonaccepting branches even when the original decider is total. Those branches still time out. Rejecting them is correct; accepting them could produce false positives. | Explain the actual reason: accepting witnesses finish within the forward bound, and every completed accepting display is sound. The original decider's halting bound is used for backward truncation. Do not assert that all coded branches finish. |
| 8 | minor | Pack · specific question 7 | `g 0 = 0` is impossible under `TimeConstructible`. | `TimeConstructible` permits `c · (T(n)+1)` time. Attached `timeConstructible_id` is an explicit counterexample to the assertion. The received deterministic hierarchy already documents this seam. | Record a pack erratum. Retain `g+1` and the explicit positivity hypothesis in the positive form. |
| 9 | minor | `NTimeHierarchy.lean` · `NTIME_linear_ssubset_square`, line 262 | `A · (2n+2)^2 ≤ (n+1)^2` fails for every `A`. | It holds for `A = 0`; it fails for every `A ≥ 1`. The pack's corresponding qualification is already correct. | Change the docstring to “every positive `A`.” |
| 10 | note | `ntime_hierarchy` and showcase · delivered strength | The extra `f(n)` term is harmless for monotone `f`, but genuinely restricts nonmonotone bounds; the square example is a weaker illustration than the book's example. | The exact comparison and an oscillating counterexample appear below. These restrictions are declared. The principal contracts retain linear, rather than quadratic, dependence on the simulated time. | Keep the qualifications visible: equivalence to the shifted gap is established for monotone `f`; the square is the chosen alternative showcase, not mere rounding of exponent `3/2`. |
| 11 | note | Pack · repository attestations | The attachments support the inventory/log readings, not independent replay of repository history or build freshness. | Source count is 7 definitions, 7 `sorry`s, and 1 proved theorem. The sweep contains 7 admission warnings and no `error:` lines. Root imports include both audited modules. No complete build checkout/toolchain was supplied here. | Preserve the distinction between independently checked packet facts and maintainer attestations; no new build claim is made by this audit. |

**Independent restatements of all seven definitions**

1. **`CodeNDTM` — line 86.** An element consists of a natural number `numStates` and a binary-choice nondeterministic TM with exactly two work tapes, binary nonblank symbols, and exactly `numStates+1` named live states. The initial live state is part of the underlying machine; halting is represented separately by `none`. Thus `numStates = 0` means one live state, not an empty state space.

2. **`CodeNDTM.toFinNDTM` — line 93.** Repackage that same machine as a bundled finite NDTM, retaining its two tapes, state type, initial state, and transition functions. There is no simulation or time change.

3. **`workPair` — line 100.** This is the two-coordinate function whose value at tape 0 is `w₀` and whose value at tape 1 is `w₁`. Since `Fin 2` has only these two elements, it enumerates every possible pair of work-head reads exactly once as its two arguments range independently over `Option Bool`.

4. **`actionBits₂` — line 106.** Concatenate the encodings of input move, tape-0 write, tape-0 move, tape-1 write, tape-1 move, optional emission, and optional successor state, in that order. Relative to `actionBits`, precisely one work-write/move pair is inserted before the emission. In particular, “no write” and “write blank” remain different encodings.

5. **`CodeNDTM.serialize` — line 119.** Encode the state-count parameter as the first component of `pairEncode`; its second component begins with the self-delimiting initial-state index and then lists all transition records. The order is choice, state, input read, tape-0 read, tape-1 read, with the last coordinate varying fastest. There are `54(numStates+1)` records. The calls to `workPair w₀ w₁` and the order of the two action records agree.

6. **`NDMachineCode` — line 134.** A scheme supplies an encoder, a total decoder, and the equation `decode(encode(M) ++ true^m) = M` for every machine and padding length. Consequently decoding is onto, encoding is one-to-one, and each machine has infinitely many codes, distinguished by length. These are three fields, not three independent proved computability laws: the structure alone does not require an effective decoder, encoder, or padding-time bound.

7. **`EffectiveNDMachineCode` — line 155.** Add one finite deterministic TM that computes the fixed serialization of the decoded machine on every string, with a time bound depending only on string length. Neither polynomial time nor computability of the supplied numerical bound is asserted. Crucially the output format is independent of the representation scheme: its complete finite table and initial state determine the coded machine, so a noncomputable semantic reassignment cannot be hidden by choosing a matching scheme-specific encoder.

These bodies have the intended meanings. The two-work-tape carrier is adequate for direct interpretation, exhaustive deterministic replay, and display-and-replay normalization. The weaker acceptance-only normal-form transfer is a declared design choice, not an accidental assertion of all-branch totality.

For the serialization arithmetic, each action uses six two-bit fields followed by a successor field of at least one bit. Therefore

\[
\#\text{records per state}=2\cdot3^3=54,
\qquad
\text{minimum action length}=6\cdot2+1=13.
\]

A useful minimum table-length guard is consequently `702(numStates+1)` bits. A one-state silent-halting machine with all stationary/no-write actions has serialization length

\[
2+1+54\cdot13=705.
\]

The first `2` is the paired empty state-count header, and the next `1` is `unaryFin 0`. Parsing the fixed number of records and then checking an all-true suffix distinguishes padding from the table; the final unary state terminator is consumed as part of its field.

**Skeleton-time proof: `NDMachineCode.decode_encode`**

The complete proof body is `simpa using c.decode_encode_pad M 0`. Its logical steps are exactly

\[
\begin{aligned}
&c.decode(c.encode(M)\mathbin{++}\operatorname{replicate}(0,\mathrm{true}))=M,\\
&\operatorname{replicate}(0,\mathrm{true})=[],\\
&c.encode(M)\mathbin{++}[]=c.encode(M),\\
&c.decode(c.encode(M))=M.
\end{aligned}
\]

The first line instantiates the structure field; the next two are list simplifications. The last is precisely the goal. No machine-construction theorem or admitted existence theorem is used by this proof.

**All seven sorried contracts: literal meaning and construction assessment**

1. **`exists_effectiveNDMachineCode`.** It asserts nonemptiness of the effective-scheme structure, without a polynomial bound. A parser with the corrected 54-record enumeration, range checks, immediate failure on insufficient data, a fixed fallback, and tolerance of an all-true suffix gives the required total decoder and round trip. Parsing and reserialization are effective finite-string operations; the arbitrary-time compiler route described in the attached deterministic mirror suffices, and a maximum of halting times over the finitely many strings of each length supplies the time-bound field. **True as stated; findings 3–4 correct its construction description.**

2. **`exists_timed_universal_NDTM`.** One machine is chosen after the scheme; after each code, one constant must work for every input and every budget, guaranteeing both unconditional all-branch termination and exactly bounded source acceptance. Copy/canonize only the code prefix, interpret the two tapes directly, consume a choice bit only at each simulated transition, and use an amortized countdown; simulated halting must be checked after the last permitted transition. On timeout, reject, even if the source has already emitted a singleton true without halting; a finite output-status flag suffices to emit a verdict only at completion. **True as stated with the clock accounting below; this interface alone does not supply finding 1's stage-uniform estimate.**

3. **`exists_ndAcceptsWithin_decider`.** One deterministic machine must output exactly `[true]` or `[false]` according to bounded acceptance, within one code-dependent exponential budget valid for all inputs. Enumerate all `2^t` length-`t` choice words, cut every replay after at most `t` source steps, and retain only whether the halted output is exactly `[true]`; reset the visited work intervals, virtual input position, choice head, and countdown between replays. With a fixed code-dependent constant `d`, this costs at most `d(t+1)2^t`, after enlarging `d` to cover startup. **True as stated; diverging branches cannot stall a replay, and the two implications exhaust all cases.**

4. **`FinNDTM.exists_codeNDTM_accepts_linear`.** For each finite NDTM, one two-work-tape coded machine and constant preserve acceptance forward within `C(t+1)`; conversely, any bounded acceptance of the coded machine implies eventual acceptance of the original, with no reverse time estimate. Guess fixed-width records with initial-state, transition, termination, and output checks in finite control; verify the input and each work tape in separate sweeps, using fixed-size binary blocks for any auxiliary marks. There are `k+1` sweeps, each linear in display length; rewinding the display and clearing the marked replay interval have the same cost. **True as stated, including `k=0`; infinitely guessing branches are permitted, and backward truncation below suffices for the consumer.**

5. **`ntime_hierarchy`.** Its conclusion is strict inclusion of sets of languages, under constructibility of both bounds and eventual domination of every constant multiple of the displayed sum. The inclusion follows rigorously by finite absorption as shown below; if the lower bound vanishes, strictness reduces to nonemptiness of the positive upper class. For positive lower bounds, the intended general separation is the standard hierarchy claim with a stronger domination premise, but the supplied stage construction does not yet establish it: findings 1–2 prevent a complete true-as-stated construction argument from these interfaces. **Statement not refuted; sketch not approved, including for the otherwise benign monotone instances.**

6. **`ntime_hierarchy_of_pos`.** It has the same premises plus positivity of `g`, and concludes strict inclusion into `NTIME g`. For every length and every constant, `c(g(n)+1) ≤ 2c g(n)`; all-branch halting and bounded acceptance transfer using extension and truncation. The opposite inclusion is monotonicity, so the two upper classes are equal. **Correct reduction conditional on the summit theorem; no additional gap.**

7. **`NTIME_linear_ssubset_square`.** This is the unconditional strict separation between the two specified positive integer-valued bounds. Substituting them into the summit gives exactly `A(3n+4) ≤ (n+1)^2` eventually, as verified below. An amortized input-scan counter computes `n+1`; binary grade-school multiplication then computes its square in a budget well inside `O((n+1)^2)`, including a constant budget at the empty input. **Sound intended instance; its proposed derivation still inherits the summit's unclosed construction obligations.**

**Resource and implication checks**

The nested input format has prefix length

\[
2\bigl(2\,|\operatorname{bits}(t)|+2+|\alpha|\bigr)+2
=4\,|\operatorname{bits}(t)|+2|\alpha|+6.
\]

It contains no contribution from `x`. The outer separator locates the end of the code, so startup need not scan the input suffix. The virtual left boundary must still be marked and its clamp emulated; the physical delimiter is not a virtual blank. During `t` source transitions only an initial distance of at most `t` can be visited. This also permits replay reset without searching for the far end of a huge input. Thus the absence of an input-length term in both universal contracts is sound.

For the countdown, let `ν₂(j)` be the number of trailing binary zeros of positive `j`. A decrement from `j` borrows across `ν₂(j)` cells; return-to-origin work is proportional to the same quantity. Summing over a full countdown gives

\[
\sum_{j=1}^{t}\nu_2(j)
=\sum_{r\ge1}\left\lfloor\frac{t}{2^r}\right\rfloor
\le t.
\]

All sums are finite after their zero terms are removed. A counter maintaining its significant end and testing zero without a full-width scan on every tick therefore has total cost `O(t+|bits(t)|+1)=O(t+1)`. For a fixed code, adding table scans and startup gives the stated `C(t+1)`. This is a total-cost argument; it does not justify the current pointwise claim about every tick.

For the deterministic evaluator, using `t+1 ≤ 2^(t+1)` and choosing `C ≥ max(d,2)` gives

\[
d(t+1)2^t
\le d\,2^{2t+1}
\le C\,2^{C(t+1)}.
\]

The empty choice word is the sole replay at `t=0`. Cleanup must delimit the visited interval even when virtual cells have been erased to blank; a fixed-size block encoding can carry the interval/origin marks. This is a concrete replay implementation obligation, not a need for a term depending on the full input length.

Choice-word alignment is valid in both directions. On an accepting source run, place its bits at successive interpreter transition boundaries, choose arbitrary bits at deterministic bookkeeping steps, then pad after the host halts. Conversely, extract the bits at completed source transitions from an accepting host branch and pad the extracted source word to length `t`. Output `[true]` without source halting must never count as acceptance. These observations also cover first halting exactly at the deadline.

Backward truncation uses the original machine's all-branch bound, never an assumed bound on the normalized machine. Precisely, if `N.tm.HaltsWithin x T`, then

\[
(\exists s,\ N.\mathrm{AcceptsWithin}(x,s))
\iff N.\mathrm{AcceptsWithin}(x,T).
\]

For the nontrivial direction, take an accepting word `w` of length `s`. If `s≤T`, pad it. If `T≤s`, split it as `w.take T ++ w.drop T`. The prefix has halted by the hypothesis, and `runWith_append` followed by `runWith_of_halt` makes the full run equal to that prefix run, preserving `[true]`. Hence the unbounded backward normal-form clause is exactly adequate.

Consequently, whenever `N` decides `L` within `c₀ f` and the budget at an input `x` is at least `C₁(c₀ f(|x|)+1)`,

\[
x\in L
\iff M'.\mathrm{AcceptsWithin}(x,\text{budget}).
\]

At a stage bottom `a=ℓᵢ+1`, the top flip needs this inequality with `f(a)`. The middle transition from `n` to `n+1` needs it with `f(n+1)`. The theorem's sum already contains both terms; the repaired ledger should use both.

For inclusion, choose a threshold from `hfg` with `A=1`, and define the finite constant

\[
F=1+\sum_{j<N} f(j).
\]

For `n<N`, `f(n)≤F≤F(g(n)+1)`; for `n≥N`, `f(n)≤g(n)≤F(g(n)+1)`. An `NTIME f` decider with coefficient `c` therefore works with coefficient `cF` for `g+1`, using the same extension/truncation argument. This part does not need monotonicity.

**Why the two major findings remain**

For finding 1, the two available facts have the forms

\[
\forall A\ \exists N\ \forall n\ge N:
A\bigl(f(n+1)+f(n)+n+1\bigr)\le g(n),
\]

and

\[
\forall R\ \exists i\ge R:\quad c.decode(\alpha_i)=M'.
\]

They do not imply that some such `i` lies past the domination threshold for a new coefficient depending on `αᵢ`. As a pure quantifier test, the eventually true inequalities `A≤n` have threshold `A`; along any increasing sequence of stage starts `aᵢ`, the varying coefficients `Aᵢ=aᵢ+1` fail at **every** corresponding start. The exports impose no condition that rules out this dependence. Merely enlarging existential overhead witnesses is already enough to show why selecting arbitrary witnesses cannot justify the inference.

There are two separate obligations here: bounding the running time of `D` uniformly over all codes used by its stages, and guaranteeing that a stage for the alleged decider eventually has enough simulation time. A clock on the diagonal machine's own work can solve the first without solving the second. Reusing one fixed code at arbitrarily late stages, or proving a padding-stable simulation coefficient with separately bounded startup, addresses the second. The current sketch supplies neither complete combination.

For finding 2, a numerical upper bound is not an executable stage locator. `canonizerTime` is not required to be computable, and neither universal theorem exports a computable function selecting its coefficient. The fill may choose concrete implementations with additional properties, but those properties must be established rather than inferred from the existing existential signatures.

There is also a distinct time issue for interior inputs. For example, take `f(n)=n+1` and let `g(n)=2^n` at odd lengths and `(n+1)^2` at even lengths. Both are time constructible in the attached convention and satisfy the displayed eventual domination condition. Nevertheless, at arbitrarily large odd `a`,

\[
a<a+1,
\qquad
g(a)=2^a\gg g(a+1)=(a+2)^2.
\]

An allowed constructibility witness can spend order `g(a)` time before returning; its upper bound provides no affordable uncapped call at an interior input of length `a+1`. A bounded evaluation procedure can potentially resolve this, so the example is **not** a counterexample to the theorem. It shows what must be proved about the proposed locator, particularly since the sketch mentions iterated `f`-witness runs while its budget is obtained from `g`.

At the top itself the advertised inequality is correct:

\[
\mathrm{BFbound}\le\ell_{i+1}=n\le g(n).
\]

The equality in the middle is essential. At an interior point it is instead `n<ℓᵢ₊₁`. A repaired sketch needs an explicit computable recurrence, a way to stop evaluating the next value when the current allowance is exhausted, and an amortized sum for completed stages plus that last attempt. I have not supplied or verified that full machine construction in this audit.

**Adversarial instantiations**

| Test | Instantiation and result |
|---|---|
| A1: zero budget | For every initialized NDTM, the only length-zero word is `[]`, and its run still has state `some q₀`. Thus bounded acceptance at zero is false. The universal must halt without acceptance, and BF must output `[false]`. Their witnesses cannot use `C=0`. |
| A2: immediate acceptance | A one-live-state machine whose two actions emit true and halt accepts every input at time 1, including the empty input, but never at time 0. The universal's deadline convention must distinguish these cases. |
| A3: output before halting | A two-state machine emits true, then loops forever without further output. It has no accepting bounded run despite eventually having output `[true]`. Timeout must reject. Simply halting a pass-through simulator would be unsound. |
| A4: malformed short codes | For the proposed parser scheme, `α=[]` and `α=[true]` fail the paired header and denote the silent-halting fallback. Universal and BF clauses still apply, with false bounded acceptance at all times. For an arbitrary effective scheme, these strings need not denote that fallback; the contracts correctly use whatever the total decoder returns. |
| A5: enormous input, tiny budget | Fix any code and `t∈{0,1}`; let the input length grow without bound. The prefix formula above is unchanged, and no suffix scan is necessary. No hidden input-length term was found. |
| A6: empty input and boundary moves | On `x=[]`, the virtual initial position is the right blank adjacent to the virtual left boundary. Repeated left moves must clamp at the virtual left blank, not expose the pairing delimiter. The established marker discipline handles this. |
| A7: zero work tapes | A zero-work-tape immediate acceptor is allowed. Its normalization needs a guessed record and input check, exposing the `k·t` prose error while satisfying the actual linear contract. |
| A8: long carry/borrow | Set `t=2^r` for a fixed code. The first binary decrement has an `r`-cell borrow, refuting a uniform per-tick bound but respecting the total amortized estimate. |
| A9: padded representations | Fix a machine and use every `encode M ++ true^m`. All decode to the same machine, but no law bounds or equates their canonization times or universal coefficients. This is the missing quantitative premise in finding 1. |
| A10: `f=g` | Already at `A=1`, `f(n+1)+f(n)+n+1>f(n)=g(n)`. No threshold exists, so the hypothesis correctly excludes self-separation. |
| A11: identity versus exponential | The attached witnesses support `f(n)=n`, `g(n)=2^n`; the domination sum is `3n+2` and is eventually dominated by the exponential. However `NTIME id=∅` because the bound vanishes at length zero, so this is a degenerate lower-class test, not a substantive hierarchy demonstration. The positive linear showcase avoids it. |
| A12: positive linear versus square | Here both classes have nonempty time bounds, and the domination calculation below succeeds. There is no zero-budget trivialization of the advertised showcase. |
| A13: nonmonotone bounds | The oscillating examples above and below separate the locator's missing monotonicity inference from the explicitly stronger hypothesis. They do not refute the repaired theorem statement. |

For the requested exponential domination in A11, choose `n≥max(4,3A+1)`. Induction gives `2^n≥n²` for `n≥4`, and

\[
n^2-A(3n+2)=n(n-3A)-2A\ge n-2A\ge0.
\]

**Strength, positive bounds, and showcase arithmetic**

When `f` is monotone, constructibility gives `n+1≤f(n+1)`, and hence

\[
f(n+1)
\le f(n+1)+f(n)+n+1
\le3f(n+1).
\]

Applying the book's eventual integer-multiple condition at `3A` proves the package's condition; the reverse implication is immediate. Thus the conditions are equivalent in the monotone case, without any monotonicity assumption on `g`.

Outside that case the strengthening is real. Set

\[
f(n)=\begin{cases}2^n&n\text{ even},\\n+1&n\text{ odd},\end{cases}
\qquad
g(n)=(n+1)f(n+1).
\]

These positive functions are constructible by length/parity counting, shifts, and elementary multiplication. Then

\[
\frac{f(n+1)}{g(n)}=\frac1{n+1}\longrightarrow0,
\qquad
\frac{f(n)}{g(n)}=\frac{2^n}{(n+1)(n+2)}\longrightarrow\infty
\quad(n\text{ even}).
\]

Thus the added `f(n)` condition is not “only” a change of notation for unrestricted functions. It is useful for the inclusion proof and also supplies the stage-bottom bound. This confirms the declared restriction, with the necessary source-fidelity qualification.

At zero, `TimeConstructible id` shows that constructibility does not imply positivity. If a time bound vanishes anywhere, the all-branch-halting clause makes its `NTIME` class empty; a positive bound admits at least a constant rejecting decider. Consequently the larger `g+1` class is always nonempty, and the `hpos` hypothesis is precisely what permits replacing it by `g`.

For the showcase, if `n≥3A+4`, then

\[
\begin{aligned}
(n+1)^2-A(3n+4)
&=n(n-3A)+2n+1-4A\\
&\ge6n+1-4A\\
&\ge14A+25>0.
\end{aligned}
\]

This verifies the stated threshold, including `A=0`. The two constructibility witnesses fit the actual `c(T+1)` convention: scanning/counting takes `O(n+1)` time, and grade-school multiplication on `O(log(n+2))` bits fits in `O((n+1)^2)`. At `n=0` each target value is 1 and may be emitted in constant time.

For the deterministic comparison, when `A≥1`,

\[
A(2n+2)^2=4A(n+1)^2>(n+1)^2.
\]

Thus the received quadratic-overhead hierarchy cannot be instantiated for this pair. This observation does not equate the square showcase with the book's three-halves example.

**Coverage and proposed permanent checks**

All eight numbered questions are addressed: Q1–Q3 by the definition/proof/parser checks; Q4–Q6 by the construction, clock, replay, and truncation arguments; Q7 by findings 1–2, the exact hypothesis comparison, and the stage-top check; Q8 by the positivity and arithmetic checks. All ten declared deviations were considered. Deviations 4 and 5 need corrected explanations, deviation 7 needs its monotone qualification retained, and deviation 9 is an explicitly weaker showcase.

I independently counted 185 and 278 lines in the audited modules, nine and six explicit public declarations respectively, and one plus six admissions. The supplied sweep and lint outputs have the advertised warning/error counts. I did **not** independently verify the git comparison `72718693..a664c3e4`, `.olean` freshness, the full transitive dependency graph, or rerun Lean/style lint. Existing tactic proofs were outside scope except the declared skeleton-time lemma. Numerical spot checks of the showcase threshold and borrow-count identity were supplementary; the symbolic arguments above are the evidence for those claims.

Useful permanent sanity lemmas are: `workPair` at both coordinates and injectivity; injectivity/round-trip parsing of the complete ND serialization; impossibility of initialized zero-step acceptance; acceptance-at-any-time iff acceptance-at-`T` under `HaltsWithin T`; immediate-accept and emit-then-loop deadline tests; and a padding-aware quantitative interpreter/locator invariant supporting the repaired hierarchy construction. The last item is the material closure requirement, not a suggestion to add more shallow tests.

**Glossary of notation introduced in this report.** `Cα` is an interpreter coefficient for the particular code `α`; `αᵢ` is the code used at stage `i`; `a` or `aᵢ` is a stage's first input length; `Aᵢ` is a varying coefficient used only in the quantifier counterexample; `ν₂(j)` is the number of trailing binary zeros of positive `j`; `d` is a fixed-code replay-cost constant; `s` is the length of an accepting choice word; `T` is an all-branch halting budget; `F` is the finite-absorption constant `1+Σ_{j<N}f(j)`; `R` is an arbitrary index threshold; `true^m` denotes a list of `m` true bits. All other machine, hierarchy, and stage symbols are those of the audited pack or are local quantified integers.
