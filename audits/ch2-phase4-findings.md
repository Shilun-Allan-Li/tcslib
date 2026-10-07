**Chapter 2, phase 4, round 1 — independent adversarial audit**

Intended repository destination: `audits/ch2-phase4-findings.md`.
Audited snapshot: the supplied bundle labelled `6484ce88`, branch `complexity/arora-barak-ch1`.
Bundle SHA-256: `d7ff75a76e1378c08d3d165c7046a2fb79cd4ddf01838c102b85ebf03b987bee`.

**Disposition: zero blockers, one major, two minors, five notes. The gate remains open.** No false new definition or theorem statement was found. The major concerns an omitted machine-construction contract in the Cook–Levin emitter sketch, not the locality theorems or the mathematical validity of Cook–Levin. All closed gates remain trusted context.

This is a source-level mathematical audit of definitions, statements, and sketches, not a Lean elaboration or proof-completion attestation. The derivations below justify the semantic claims; the admitted lemmas and native polynomial-time machines still require their Lean fills. File locations below are relative to `TCSlib/Complexity/` unless otherwise specified.

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | major | `CookLevin/Hardness.lean:154` · `SAT_NPHard`, emitting-machine obligations | Evaluating the bounds and clock-simulating the reference run, followed by clause emission, supplies a machine computing exactly `serialize φ_x`. | The list does not name interception of the preparatory machines' output or their halting transitions. `TimeConstructible` supplies machines whose answers are on the real output tape. `Simulation.leftAction`/`rightAction` explicitly forward `a.output` and map a source halt to a physical halt; the module's scope note warns about both native-input and real-output behavior. Every reference run of the decider emits one bit. Forwarding it contaminates the serialized formula; forwarding its halt prevents the subsequent emitter from running. The concrete rejection example below turns this into a false positive under the audited fallback. | Name an output-silent, returning controller: capture arithmetic results on work tapes; discard the reference simulation's emissions; represent source halting internally and continue the recorded frozen trajectory through time `T`; then return to the clause emitter. State the invariant that physical output is empty before serialization and is exactly the emitted serialization prefix thereafter. Preserve the already-named exact reference-input semantics. This is a sketch repair, with no theorem-signature change. |
| 2 | minor | `ClassNP/Tautology.lean:101` · `TAUTOLOGY_mem_coNP` | The dual evaluation loop should “accept when some clause-conjunct fails”. | This contradicts the immediately following correct instruction to negate `evalDNF`. A DNF is false iff **every** term fails. The DNF `[[ (0,true) ], [ (0,false) ]]` is a tautology, but on assignment `a(0)=false` one term fails. The quoted rule would accept a false certificate for its complement. Severity is minor because the same sentence explicitly specifies the correct evaluator and the theorem is true. | Replace the phrase by “accept iff every term contains an unsatisfied literal; equivalently, iff `evalDNF = false`”. An empty term forces rejection; an empty formula forces acceptance. |
| 3 | minor | `CookLevin/Hardness.lean:6` · imports supporting `SAT_NPHard` normalization | The named normalization results are available to this module's fill. | The attached import graph contains neither `ClassNP.TMSAT` nor `TuringMachine.Robustness.Oblivious` in `Hardness`'s transitive import closure. Those are the homes of `timeConstructible_poly` and `oblivious_of_mem_DTIME`. Importing `ObliviousSchedule` supplies the predicate, not the conversion theorem. The present skeleton can elaborate because these names occur only in comments. | Add precise imports of `TCSlib.Complexity.ClassNP.TMSAT` and `TCSlib.Complexity.TuringMachine.Robustness.Oblivious`, or record that explicit import change as part of the fill brief. Both already precede `Hardness` in the order list, and neither creates a cycle. |
| 4 | note | `CookLevin/Snapshot.lean` · all five statements | The schedule and last-visit reconstruction are valid with optional writes, first visits, and absorption. | Derivation A establishes the cell recurrence, maximum-visit facts, and both branches. An outer `none` preserves the cell; `some none` erases it. No common halting time, positive tape count, or positive input length is needed. | No statement repair. Preserve the strict `s < t` bound and the distinction between no write and writing blank in the fill. |
| 5 | note | `CookLevin/Hardness.lean:89` · normalization, clause families, correctness, and acceptance | The snapshot tableau characterizes accepting runs even though the clauses only forbid `false` emissions. | Derivations B–C verify the exact-length normalization, index packing, constant-arity predicates, strong-induction reconstruction, and singleton-output argument. Bitwise field constraints are essential; equality of decoded fields alone does not exclude junk codes. | No acceptance or locality strengthening. Implement the promised bitwise constraints using a product encoding, and carry the silent-controller repair in finding 1 into the emitter brief. |
| 6 | note | `Formulas/DNF.lean`; `ClassNP/Tautology.lean` · duality, membership, completeness, and new hardness notions | The DNF fragment and the decode–dual–serialize reduction have the claimed semantics on all strings. | Derivation D checks empty data, fallback, certificate restriction, and the reduction equivalence. `coNPHard` and `coNPComplete` have the correct Karp-reduction quantifiers. The named DNF evaluation-congruence obligation is elementary and sufficient at statement phase. | No additional public theorem is required to close this statement audit. A private evaluation-congruence lemma is appropriate during the fill; fix the prose in finding 2. |
| 7 | note | `AroraBarakChapter2Plan.md:214` · Astra prior-art survey row | The other development is not directly compatible with the campaign's model, encodings, and audit protocol. | The campaign-side differences are real: native finite multi-tape FP, exact certificate lengths, set-valued languages, the audited serializer, and width at most three. Direct theorem transfer would need semantic and cost bridges. Bare `import Mathlib` and absent sketches would violate the attached contribution policy as supplied. The external artifact is not attached, so its kernel status, provenance, size, and actual definitions were not independently checked. | Treat the effort comparison as an engineering estimate and “un-auditable” as “not audit-ready under this protocol as supplied”, not mathematical impossibility. No adoption decision or reserved human question is disposed of here. |
| 8 | note | Pack · attestations 1–5; order list; facades/root | Source inventory and repository execution claims are separate kinds of evidence. | The attached tree has 53 ordered modules, 59 source admission sites, and exactly the advertised 14 new definitions, one abbreviation, and 14 new admissions. New file lengths, facade/root exports, and internal dependency order agree. The bundle contains no baseline source tree, fresh-olean sweep log, axiom log, or lint log; no Lean toolchain is available on this audit's executable path. | Preserve the distinction. These checks corroborate current source facts, not historical byte identity, compiler warnings, printed axiom footprints, or maintainer-local executions. |

**Definition and statement inventory.** The new declarations were first read with comments stripped. The following restatements match their bodies; `Snapshot` is an abbreviation and is not counted among the 14 definitions.

| Declaration | Restatement from the Lean body |
|---|---|
| `evalDNF` | Some list element has all its literals satisfied; a literal `(v,b)` tests whether `a v = b`. |
| `dual` | Preserve every variable index, list position, and clause boundary; negate every polarity bit. |
| `DNFTautology` | Every total Boolean assignment makes the DNF evaluator return `true`. |
| `Snapshot` | Optional machine state, optional input bit, and one optional bit per work tape. |
| `snapshotAt` | Project those three pieces from the initialized run after exactly `t` steps. |
| `inputPosAt` | Natural-valued input position at time `t` on exactly `n` false input bits. |
| `workPosAt` | Integer-valued work-head position on that same reference run. |
| `prevVisit` | Maximum time strictly below `t` with the same reference work-head position, or `none` if there is none. |
| `stepState` | Preserve halting; otherwise use the transition's successor-state field. |
| `writtenOrKept` | In a halted snapshot retain the scanned bit; in a live snapshot use the optional write, defaulting to the scanned bit. |
| `emitted` | No emission after halting; otherwise the transition's optional output bit. |
| `inputBitAt` | Blank at zero; otherwise the optional list element at index `p-1`, hence blank beyond the input. |
| `coNPHard` | Every language belonging to `coNP` polynomial-time Karp-reduces to this language. |
| `coNPComplete` | Membership in `coNP` and `coNPHard`. |
| `TAUTOLOGY` | Binary strings whose total CNF-carrier decode is a tautology when read as DNF. |

| New theorem(s) | Assessment |
|---|---|
| `evalDNF_dual`, `dnfTautology_dual_iff` | Correct pointwise and quantified De Morgan laws; Derivation D. |
| `oblivious_schedule_eq`, `snapshotAt_zero`, `snapshotAt_state_succ`, `snapshotAt_inputSymbol`, `snapshotAt_workSymbol` | All five signatures are correct; Derivation A. |
| `NPHard.polyTimeReducible` | For each NP source language, compose its reduction to `L` with `L ≤ₚ L'`. The reduction direction is correct. |
| `SAT_NPHard` | No false signature found. Mathematical tableau correctness holds; the emitter's named obligations need finding 1's repair. |
| `SAT_NPComplete` | Conjoin trusted `SAT_mem_NP` with the new hardness theorem. |
| `SAT3_NPHard` | Transfer SAT hardness along trusted `SAT_reducible_SAT3`. |
| `SAT3_NPComplete` | Conjoin trusted `SAT3_mem_NP` with the preceding hardness result. |
| `TAUTOLOGY_mem_coNP`, `TAUTOLOGY_coNPComplete` | Correct for the expressly documented DNF fragment; Derivation D. |

**Derivation A — locality, including the last visit.** Fix `M`, input `x`, and tape `τ`. Write

\[
c_t=M.\mathrm{tm.runFrom}(M.\mathrm{tm.initCfg}(x),t),\qquad
p_t=c_t.\mathrm{workTapePos}(\tau),\qquad
w_t(p)=c_t.\mathrm{workTapes}(\tau)(p).
\]

`Action.apply` writes at the old head position before changing that position. Its definition and the halted branch of `step` give, for every integer cell `p`,

\[
w_{t+1}(p)=
\begin{cases}
\mathrm{writtenOrKept}\ M\ (\mathrm{snapshotAt}\ M\ x\ t)\ \tau,&p=p_t,\\
w_t(p),&p\ne p_t.
\end{cases}\tag{1}
\]

The value in the first branch is, exhaustively:

| Source state/action | Value left at the old head |
|---|---|
| Halted | `w_t(p_t)` |
| Live, outer write option `none` | `w_t(p_t)` |
| Live, write `some none` | Blank, even if the old cell was nonblank |
| Live, write `some (some b)` | `some b` |

Thus (1) also applies to the halting transition itself, including a simultaneous write and move. It must not be replaced by a rule that ignores the action whose successor state is `none`.

1. Instantiate `M.Oblivious` with `x` and `List.replicate x.length false`. Their lengths agree. Its two conjuncts are exactly `oblivious_schedule_eq`; function equality on work positions specializes at `τ`. Consequently the filter in `prevVisit` selects precisely

   \[
   J_t=\{s\in\mathbb N:s<t\ \land\ p_s=p_t\}.
   \]

   This uses lawful integer Boolean equality, not an unproved correspondence between unrelated runs.

2. If `prevVisit = none`, the filtered list is empty, so `J_t` is empty. Fix `p=p_t`. Initially `w_0(p)=none`. For every `r<t`, `p_r≠p`, so (1) gives `w_{r+1}(p)=w_r(p)`. Induction yields `w_t(p_t)=none`. This includes `t=0`, where the filtered range is empty.

3. If `prevVisit = some s`, membership and maximality of the maximum give

   \[
   s<t,\qquad p_s=p_t,\qquad
   \forall r\;(s<r<t\Rightarrow p_r\ne p_t).
   \]

   Apply (1) at step `s`, then at each `r=s+1,…,t-1`:

   \[
   \begin{aligned}
   w_{s+1}(p_t)
      &=\mathrm{writtenOrKept}\ M\ (\mathrm{snapshotAt}\ M\ x\ s)\ \tau,\\
   w_t(p_t)&=w_{s+1}(p_t).
   \end{aligned}
   \]

   The left side is exactly the work-symbol projection of `snapshotAt`. This proves the claimed reconstruction, including consecutive visits `s=t-1`.

4. Halting creates no exception: after halting, configurations and positions are fixed. Every subsequent positive time has the preceding time as its last visit, and `writtenOrKept` preserves that cell. If the halting action moves to a previously unvisited cell, the first halted snapshot reads blank there; the write occurred at the old cell. Reference and actual runs need not halt together. Equality of their positions at every time is all the proof uses.

5. The other snapshot claims follow directly. Initialization puts state `some q₀`, input head at `1`, and blank work tapes. At a reachable input position, `0≤p≤|x|+1`; the `Cfg.inputSymbol` cases at `0`, at `|x|+1`, and in the interior agree exactly with `inputBitAt`. Transport the position by the schedule equality. Finally, `runFrom_succ_eq_step'` and the two branches of `step` give the state-successor equation.

For empty input, initial position `1` is the right boundary and reads blank. For zero work tapes, all work-symbol assertions are vacuous. Thus design questions **(b)** and **(c)** have affirmative answers without strengthening the hypotheses.

**Derivation B — normalization and tableau correctness.** Start with the actual NP witness

\[
Q(n)=C_0(n+1)^{c_0},\qquad
x\in L\iff\exists u\;(\lvert u\rvert=Q(\lvert x\rvert)\land x\mathbin{++}u\in V),\qquad V\in P.
\]

Only the verifier's running-time bound is enlarged. From `mem_P_iff`, choose enlarged constants `A,d≥1`; pointwise time monotonicity keeps the same verifier. Since `(d-1)+1=d`, `timeConstructible_poly A (d-1)` supplies exactly the enlarged bound's time constructibility. A `DTIME` witness uses multiplier `1`. The trusted oblivious conversion therefore supplies `M,c` with

\[
M.\mathrm{Oblivious},\qquad
M.\mathrm{DecidesInTime}\ V\ T^*,\qquad
T^*(m)=c\bigl(A(m+1)^d+1\bigr)^2.
\]

The decider contract excludes `c=0`, by `not_computesInTime_zero`. For fixed `x`, take `n=|x|`, `m=n+Q(n)`, and `T=T^*(m)`. This covers every candidate word of exactly length `m`, including rejection candidates. No machine-code scheme or canonizer is involved.

Computing `Q` must respect the closed phase-3 case split: `C₀=0` gives exactly zero; positive `C₀` and `c₀=0` give the fixed constant `C₀`; otherwise `timeConstructible_poly C₀ (c₀-1)` computes the exact value. The sketch's reference to that discipline is adequate. In particular, neither `m` nor the number of free witness bits may be obtained by majorizing `Q`.

Choose a **product** encoding `enc` of snapshots: a fixed code for the optional state, then fixed codes for the input symbol and each work symbol. Let `B` be its total bit length, and totalize a decoder `dec` so that `dec(enc(s))=s`. Finiteness supplies such codes; a snapshot has at least two possible state values, so a positive width can be chosen. Using a product code makes the sketch's bitwise “fields” literal slices of the block.

The packing is disjoint and injective:

\[
j<m\Rightarrow j<m+tB+i,\qquad
m+tB+i=m+t'B+i',\quad i,i'<B
\Rightarrow(t,i)=(t',i').
\]

The latter follows by quotient and remainder by `B`. All packed indices are strictly below `N=m+(T+1)B`. If `m=0`, no input variable is referenced: every scheduled input read is a boundary blank.

| Family | Boolean predicate required | Number of arguments / members |
|---|---|---|
| (i) Pinning | `y_j=x_j` | One bit; `n` members. |
| (ii) Initial block | Exact encoded initial snapshot, with the first input bit wired when `m>0` | At most `B+1` bits; one member. |
| (iii) State succession | Target state-code bits equal the encoding of `stepState` of the decoded preceding block | At most `2B` bits; `T` members. |
| (iv) Input read | Target input-code bits equal the encoding of the selected input bit, or blank at a boundary | At most `B+1` bits; `T+1` members. |
| (v) Work read | Target work-code bits equal the encoding of `writtenOrKept` at the last visit, or blank | At most `2B` bits; `k(T+1)` members. |
| (vi) Acceptance | The decoded source block's emission is not `some false` | `B` bits; `T` members. |

Claim 2.13 applies to each predicate with arity at most `2B+1`, bounding its clause count by `2^(2B+1)` and clause width by `2B+1`. These are constants of the fixed machine. There are finitely many templates, including the boundary and first-visit variants; changing `t` changes the relabeling, not the truth table. `eval_relabel` supplies the evaluation identity. Relabeling need not be injective: different referenced source blocks can coincide, and the same global assignment then supplies the same values to both occurrences.

For any assignment satisfying (i), its `m` input bits form exactly `x++u`, where `u` consists of the last `Q(n)` bits. This resolves design question **(d)**, including `n=0` and `Q(n)=0`.

Now use **strong induction** on `t≤T`. Family (ii) fixes the entire initial block. At positive `t`, the state field depends on `t-1`, each work field depends on `some s` with `s<t` or a blank constant, and the input field depends only on the selected input bit. All source blocks therefore already decode to genuine earlier snapshots. Derivation A identifies each reconstructed component with the corresponding component of `snapshotAt M (x++u) t`. Since the families pin the actual bits of every component code,

\[
z_t=\mathrm{enc}(\mathrm{snapshotAt}\ M\ (x\mathbin{++}u)\ t).
\tag{2}
\]

The concatenated fields cover the whole block, so there is no residual degree of freedom. Total decoding alone would **not** establish this: a junk code that decodes to the fallback would satisfy mere decoded-field equalities. The sketch explicitly requires stronger bitwise pinning; with the stated product encoding, that requirement is realizable by the constant-arity predicates above.

Conversely, a real witness `u` and the genuine encoded snapshots satisfy families (i)–(v) by their defining equations. Acceptance in both directions is the next derivation. Finally, `decode_serialize` transfers satisfiability of the resulting formula to membership of its emitted word in the audited `SAT` language.

**Derivation C — why forbidding false is enough, and what the emitter must still do.** For the genuine run on `x++u`, write `e_t=emitted M (snapshotAt M (x++u) t)` and let `O_t` be its output after `t` steps. Initially `O_0=[]`, and `step_output` gives

\[
O_{t+1}=O_t\mathbin{++}e_t.\mathrm{toList},\qquad
O_T=\mathop{\mathrm{concat}}_{0\le t<T} e_t.\mathrm{toList}.
\tag{3}
\]

The decider contract and `computesInTime_iff` give, **at this same horizon**,

\[
c_T.\mathrm{state}=\mathrm{none},\qquad
O_T=[\mathrm{indicator}_V(x\mathbin{++}u)].
\tag{4}
\]

Here `c_T` denotes the configuration of this run. Combining (3)–(4),

\[
\begin{aligned}
(\forall t<T,\ e_t\ne\mathrm{some\ false})
&\iff \mathrm{false}\notin O_T\\
&\iff \mathrm{indicator}_V(x\mathbin{++}u)=\mathrm{true}\\
&\iff x\mathbin{++}u\in V.
\end{aligned}\tag{5}
\]

Thus (2) allows family (vi) to imply acceptance, and an accepting genuine run satisfies (vi). A separate at-least-one-emission clause and a final-halted-state clause are unnecessary here: (4) already supplies both facts for every reconstructed run.

| Adversarial case | Why it does not defeat (5) |
|---|---|
| Halts early with `[false]` | The rejecting emission occurred before its halt, hence before `T`, and is forbidden. |
| Halts early with `[true]` | Later snapshots are fixed and later emissions are `none`; all acceptance clauses hold. |
| Halts with no output | Contradicts the singleton-output equality in (4). |
| Has emitted nothing by `T`, but emits later | Contradicts both output equality at `T` and absorption after the halt at `T`. |
| Emits on its last transition | The emission at source time `T-1` is included in (3) and in family (vi). |
| Emits only `true`, but more than once | Excluded by the singleton-output contract, not by (vi) alone. |
| Horizon zero | Excluded for this decider by the live initial state. |

Without the decider contract, a nonemitting run would satisfy the no-false condition. The sketch invokes the contract at exactly the point required, so this is not a counterexample to the stated construction. Design question **(a)** is resolved affirmatively.

The outstanding issue is the *different*, formula-emitting machine. Its output is not the simulated verifier's output. To see finding 1 concretely, take the source language and verifier language both empty, with certificate length zero. The normalized oblivious verifier's reference run necessarily emits `[false]`. If a preparatory simulation forwards this bit and then the controller emits `serialize φ_x`, its physical output becomes

\[
[\mathrm{false}]\mathbin{++}\mathrm{serialize}(\varphi_x).
\]

The serializer is always nonempty. The initial `false` ends the formula immediately, and the remaining suffix violates exact consumption. The whole word therefore decodes to fallback `[]`, which belongs to `SAT`, although `x∉L`. If the source halt is forwarded as well, the machine stops at `[false]=serialize []`, giving the same wrong SAT answer. These are failures of unwrapped simulation, not counterexamples to `SAT_NPHard`.

The repaired sketch should name the following contracts before fill work:

| Stage | Required invariant |
|---|---|
| Exact arithmetic | Retain `x`; compute exact `Q(n)`, `m`, and the chosen `T`; capture binary subroutine answers on work tapes and return control, with empty physical output. |
| Reference simulation | Present virtual input `List.replicate m false`, with virtual head initially at `1` and clamped to `0,…,m+1`; use disjoint work tapes. The physical input is still `x`, so native-input embeddings alone do not suffice. |
| Simulation output and halt | Discard the source's output field; keep an internal halted state rather than halting the controller. After source halting, record the unchanged source positions until the clock reaches `T`. |
| Trajectory | Record times `0,…,T` inclusive. Work-head counters match the signed source positions; input counters match the clamped reference positions. Administrative steps do not count as simulated time. |
| Last visits | For each target time and tape, compare all earlier recorded positions and retain the greatest matching time, or `none`. |
| Serialization | Emit exactly the fixed clause order and packed indices, including every marker and final terminator. Physical output equals the serialized prefix; no preliminary result is on it. Halt after completion. |

These are sufficient named obligations at statement phase. Existing buffered-composition and capture constructions are usable precedents; the bare lockstep embeddings are not substitutes for these contracts.

The numerical budget has polynomial room. Put `r=max(1,c₀)`. For every `n≥0`,

\[
\begin{aligned}
m+1&=(n+1)+C_0(n+1)^{c_0}\le(C_0+1)(n+1)^r,\\
T&\le c\bigl(A(C_0+1)^d+1\bigr)^2(n+1)^{2dr}.
\end{aligned}
\]

For unary serialization the exact length identity is

\[
\lvert\mathrm{serialize}(\varphi_x)\rvert
=1+2\,\#\mathrm{clauses}+\sum_{(v,b)\text{ occurrence}}(v+3)
\le1+2\,\#\mathrm{clauses}+(N+2)\,\#\mathrm{literals}.
\]

The constant-template bounds imply length `O((n+T+1)(N+1))`, hence a polynomial. The `n` pinning clauses alone cost `n(n-1)/2+5n` bits, not merely `O(n)` bits; however, this does not refute the sketch's *total* displayed upper bound: `c,A,d≥1` imply `T≥(m+1)²` and `m≥n`, so its larger term absorbs that cost. The exact identity is the better fill ledger.

Recording the trajectory needs `O((T+1) log(T+2))` bits for fixed `k`. There are `O(kT²)` last-visit comparisons. On native tapes, record access is not constant-time: sequential retrieval and binary arithmetic add polynomial scan overhead. Unary index emission similarly costs its emitted length plus polynomial counter overhead. These observations establish polynomial feasibility, not an already-proved native-machine bound; no random-access cost assumption is needed.

**Derivation D — DNF, certificates, and the coNP reduction.** For each literal,

\[
[a(v)=\neg b]=\neg[a(v)=b].
\]

Apply Boolean De Morgan first inside each list element, then outside:

\[
\begin{aligned}
\mathrm{evalDNF}(\mathrm{dual}(\varphi),a)
&=\bigvee_C\ \bigwedge_{(v,b)\in C}[a(v)=\neg b]\\
&=\neg\bigwedge_C\ \bigvee_{(v,b)\in C}[a(v)=b]\\
&=\neg\mathrm{eval}(\varphi,a).
\end{aligned}
\]

Universal quantification gives `dnfTautology_dual_iff` directly. The list conventions are necessary and correct:

| Carrier data | CNF value | DNF value | DNF tautology? |
|---|---|---|---|
| `[]` | `true` | `false` | No |
| `[[]]` | `false` | `true` | Yes |
| Nonempty formula with an empty list element | `false` | `true` | Yes |

For membership in `coNP`, fix a formula string `x` of length `n`. The complement condition is an assignment making `evalDNF (decode x)` false. Since `(decode x).numVars≤n`, a certificate of exactly `n+1` bits suffices: restrict a falsifying total assignment to those bits; conversely extend a certificate by `false` beyond its length. Agreement on mentioned variables preserves each literal, each conjunction, and their disjunction. This proves the named DNF congruence bridge without a new conceptual assumption. Alternatively, involutivity of `dual` and preservation of `numVars` reduce it to the trusted CNF congruence theorem and the new De Morgan identity.

The total verifier rejects even total input lengths and splits an odd length `2n+1` at `n`. It parses the formula half and evaluates the negated DNF with the certificate half. **Every term must fail** for acceptance, as corrected in finding 2. On malformed formula strings, total decoding yields `[]`; its DNF value is false, so every correctly sized certificate witnesses complement membership. Output remains one buffered verdict. The shared parser and assignment-walk obligations supply the same polynomial budget as the trusted SAT-membership construction.

For hardness, let `L∈coNP`, and obtain an arbitrary polynomial-time reduction `f` from `Lᶜ` to `SAT`. Its values need not be valid serializations. Define, exactly as in the sketch,

\[
g(z)=\mathrm{serialize}\bigl(\mathrm{dual}(\mathrm{decode}(f(z)))\bigr).
\]

For **every** input string `z`,

\[
\begin{aligned}
z\in L
&\iff f(z)\notin\mathrm{SAT}\\
&\iff\neg\mathrm{Satisfiable}(\mathrm{decode}(f(z)))\\
&\iff\mathrm{DNFTautology}(\mathrm{dual}(\mathrm{decode}(f(z))))\\
&\iff g(z)\in\mathrm{TAUTOLOGY}.
\end{aligned}
\]

If `f(z)` is malformed, the source SAT answer is true, so `z∉L`; the target is `serialize []=[false]`, also outside `TAUTOLOGY`. Thus fallback flipping causes no lost case. The transducer can validate/parse before emitting, then flip each literal polarity during serialization; it must not irreversibly emit a valid-looking prefix before discovering a trailing parse error. This is covered by the named parse–dual–serialize composition. Length is preserved on valid serialized formulas and becomes one on malformed strings; the shared parsing/serialization obligations are polynomial. Compose with `f` using the trusted FP composition theorem.

This verifies design questions **(e)** and **(f)**. The language is expressly a DNF-fragment rendering; it is not silently identified with arbitrary Boolean-formula syntax. Its hardness is sufficient for the stated example.

**Attestations, prior art, and verification limits.** The five new files have respectively 105, 252, 202, 23, and 131 source lines after removing bundle separator whitespace. Counts are `3+8+0+0+3=14` definitions, one abbreviation, and `2+5+5+0+2=14` new admissions. The entire attached campaign tree has 59 source `sorry` sites. Each new admitted theorem has a proof sketch; there are no new completed proofs. The order list has 53 distinct entries, every corresponding attachment exists, and every attached internal import precedes its consumer. The new facade and root paths are exported. This corroborates the source portions of the pack's inventory and size claims.

The historical freeze and the reported Lean 4.25.0/mathlib sweep, axiom prints, and lint results remain maintainer execution attestations. Missing imports of names used only in sketches do not contradict a clean skeleton elaboration. No closed-phase theorem was reopened to obtain the findings above.

The prior-art row has a valid compatibility rationale but is not an independently reproduced benchmark. For direct reuse of a theorem stated over TM2 NP, one needs to transport native NP verifiers into that framework and transport a TM2 reduction emitter back with polynomial costs, as well as align certificates and serialization. Other adaptation strategies could reuse pieces without proving a wholesale bidirectional equivalence; nothing in the attached campaign proves that all such strategies cost as much as the native fill. The convention differences are bridge obligations, not mathematical obstructions. The row's documentation objections apply to the artifact as described, and its decision to retain factoring ideas is consistent with the present split. The unattached artifact's own claims remain out of scope.

For source comparison I consulted the authors' [January 2007 online draft](https://theory.cs.princeton.edu/complexity/book.pdf), whose corresponding argument uses reference-input schedules, snapshot reconstruction, and negation for coNP hardness. Its numbering differs from the cited 2009 edition. This report retains the pack's AB09 item numbers; it does not claim independently to have checked the published edition's pagination. The detailed mathematical derivations here are from the supplied Lean definitions.

Finite executable corroboration, independent of Lean, checked 47,293 reachable configurations across every one-tape action history through four steps, with optional no-write, explicit blank/false/true writes, all three moves, and absorbing halts. It checked all 3,280 optional-emission streams through length seven, including all 56 singleton-output streams; all 9,724 ordered two-variable formulas with at most three terms of width at most two, giving 38,896 pointwise De Morgan checks; and 512 small variable-packing cases. All assertions passed. These bounded checks support the derivations; they are not substitutes for the quantified arguments or the eventual kernel checks.

**Notation glossary.** `n=|x|`; `Q(n)=C₀(n+1)^c₀` is the unchanged certificate length; `m=n+Q(n)`; `A,d` are positive enlarged verifier-time constants; `c` is the positive oblivious-simulation multiplier; `T*` is its length-indexed budget and `T=T*(m)`; `r=max(1,c₀)`. In Derivation A, `c_t` is the run configuration, `p_t` its head position on fixed tape `τ`, `w_t(p)` that tape's cell content, and `J_t` the set of earlier visits to `p_t`; in Derivation C the run input is `x++u`. `enc,dec` are the chosen snapshot encoder and total decoder; `B` is the block width; `y_j,z_t` are input bits and snapshot blocks; `N=m+(T+1)B` is the exclusive index bound. `φ_x` is the assembled formula; `e_t,O_t` are the genuine run's optional emission and accumulated output; `indicator_V` is its Boolean membership indicator. `f` is the reduction from `Lᶜ` to SAT, and `g` its decode–dual–serialize composition. Brackets `[P]` in Derivation D mean the Boolean truth value of proposition `P`; `#clauses` and `#literals` count clauses and literal occurrences.
