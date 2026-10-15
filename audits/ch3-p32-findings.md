# P3.2 statement-gate audit: Baker–Gill–Solovay relativization

**Verdict: FAIL — the gate does not close.** Findings: **1 blocker, 0 majors, 2 minors, 2 notes.** The blocking issue is the use of an arbitrary effective machine-code scheme in an assertion requiring uniformly efficient decoding. The diagonal construction and all seven locality statements survive the audit.

Audited packet: `ch3-p32-bundle.md`, declared commit `7fbac9bdff79aee148b916e077ad93b6ce4693f9`, branch `complexity/arora-barak-ch3-4`. SHA-256 independently verified:

```text
dbfadcfbc77ef508a89e927ab2d04c122c6ab65ddac98462e85fe0c0547c3e2a
```

This is a mathematical audit of definitions, statements, and proof sketches, not a Lean proof-completion or kernel audit. All four new definitions, all seventeen sorried statements, and the facade were inspected. File-local line numbers below refer to the source attachments extracted from the bundle.

## Findings

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | **blocker** | `Diagonalization/EXPCOM.lean` · `EXPCOM` (82), `NPOracle_EXPCOM_subset_EXP` (162), and the three identities (170, 178, 187) | The fixed effective code scheme makes variable-code bounded acceptance decidable within the claimed exponential ledger. | `Encoding.lean:558–566` permits an arbitrary `canonizerTime`. `TimeHierarchy/Diagonal.lean:107` chooses an arbitrary inhabitant of `EffectiveMachineCode`; its universal-machine specification at 113 has **`∀ α, ∃ C`**, with no bound on the code-dependent constant. In contrast, EXPCOM queries contain variable codes. The ledger at `EXPCOM.lean:146–152` silently treats their decoding/simulation overhead as uniform. The construction below gives permitted effective schemes for which EXPCOM is outside EXP, and even schemes for which its relativized P and NP differ. | Select an explicitly efficient scheme for EXPCOM, or select a scheme together with a proved uniform complexity property. Prove a bounded-acceptance algorithm whose time includes code parsing, canonization, decoded-table size, and simulation, uniformly in the code. Re-audit the resulting definition and four dependent assertions. The existing hierarchy scheme need not be changed: arbitrary effective schemes are adequate for its fixed-code argument. |
| 2 | **minor** | `Diagonalization/Relativization.lean` · sketch of `exists_finOracleTM_enumeration`, 129–147, especially 135 | A “well-formed one-state default” totalizes the enumeration. | Both `OracleTM.WellFormed` and the bundled `FinOracleTM` require three pairwise distinct special states. No one-state machine satisfies this. The enumeration theorem itself is true. | Use a three-state default, or embed a plain one-state machine using the existing embedding, which adjoins three states. Specify a separate repetition coordinate to make recurrence explicit; a bijective triple pairing alone has singleton fibers. |
| 3 | **minor** | `Diagonalization/EXPCOM.lean` · uniqueness citations at 80–81, 107, 144–145 | `pairEncode_replicate_inj` is the fact recovering the unary component in this nesting. | `Encoding.lean:256–264` concerns `pairEncode (replicate n true) u`: the unary word is the **first** component. Here it is the second component of the inner pair. Uniqueness is nevertheless true. | Apply `pairEncode_injective` twice, then apply `List.length` to the equality of the two replicated lists. Remove or replace the mismatched citation; no definition change is needed for this finding. |
| 4 | **note** | **[P3.1]** `ClassOracle/Classes.lean` · `DTIMEOracle`, `NTIMEOracle`, `POracle`, `NPOracle` | The attached classes impose a bound under the selected oracle; BGS75 enumerates machines clocked under every oracle. | This is the declared quantifier difference. P3.2 does not infer any runtime bound under a temporary oracle from a bound under the final oracle. Its bounded simulation and exact-horizon behavioral equivalence avoid that error. | Retain the deviation record. A class-level equivalence with BGS75's convention uses a polynomial clock wrapper; P3.2's diagonal proof does not require that equivalence as an intermediate lemma. |
| 5 | **note** | Pack · repository-side attestations and dependency coverage | The attached logs certify a fresh build and the complete imported implementation. | The five new files contain exactly 4 definitions, 17 theorem stubs, 17 executable `sorry` tokens, and no `axiom` declarations. The supplied sweep contains exactly 17 sorry warnings and no `error:` lines. Fresh `.olean`s, unchanged-file claims, root export, and a full dependency build cannot be independently checked from these attachments. In particular, the body/signature of `timed_universal` is not attached. | Preserve these as maintainer attestations, distinct from this audit's checks. Supply the actual uniform simulator contract in the repair packet. This evidence limitation is not an additional blocker. |

Finding 1 belongs to **P3.2**, not the deferred P3.1 gate: it is a new, invalid use of the hierarchy's deliberately weak coding interface.

## Why finding 1 is substantive

### Effective decoding does not imply the required bound

Write `EXPCOM[c]` for the packet's definition with code scheme `c`. This notation is only for the audit; the submitted definition is not parameterized.

Choose a decidable language $H\notin\mathrm{EXP}$. For completeness, such a language can be constructed without assuming any unproved separation: effectively enumerate all triples of deterministic machines and natural-number clock parameters $(M_j,a_j,k_j)$, and define

\[
1^j\in H
\iff
\neg M_j.\mathrm{ComputesInTime}
       (1^j,[\mathrm{true}],a_j2^{j^{k_j}}),
\]

rejecting non-unary strings. This is a terminating finite simulation on every input. If a machine with parameters $a,k$ decided $H$ in time $a2^{n^k}$, its enumerated triple would give a contradictory verdict on the corresponding $1^j$. Thus $H$ is decidable and outside EXP. Repetitions in this enumeration are harmless.

Start with an ordinary effective scheme $c_0$. Let $M_+$ and $M_-$ be one-work-tape binary machines that halt in one step with outputs `[true]` and `[false]`, respectively. Define another scheme $c_H$ by

\[
\begin{aligned}
\mathrm{encode}_{c_H}(M)&=0\,\mathrm{encode}_{c_0}(M),\\
\mathrm{decode}_{c_H}(0\alpha)&=\mathrm{decode}_{c_0}(\alpha),\\
\mathrm{decode}_{c_H}(1s)&=
\begin{cases}M_+&s\in H,\\M_-&s\notin H,\end{cases}\\
\mathrm{decode}_{c_H}(\varepsilon)&=M_-.
\end{aligned}
\]

This satisfies the attached interface:

1. Decoding is total.
2. For every machine $M$ and padding length $r$,
   \[
   \mathrm{decode}_{c_H}(\mathrm{encode}_{c_H}(M)1^r)
   =\mathrm{decode}_{c_0}(\mathrm{encode}_{c_0}(M)1^r)=M.
   \]
3. A canonizer is computable: inspect the tag, then run the old canonizer or decide $H$ and emit the appropriate fixed serialization. Because this machine halts on every word, the maximum of its runtimes over the finitely many words of each length supplies `canonizerTime`. The interface requires no efficient bound on that maximum.

Now consider the linear-time map

\[
f(s)=\mathrm{pairEncode}(1s,
              \mathrm{pairEncode}(\varepsilon,\varepsilon)).
\]

Both empty components are legitimate, the padding exponent is zero, and $2^0=1$. Therefore

\[
\begin{aligned}
s\in H
&\iff \mathrm{decode}_{c_H}(1s)=M_+\\
&\iff \mathrm{decode}_{c_H}(1s)
       \text{ halts on }\varepsilon\text{ with }[\mathrm{true}]\text{ within one step}\\
&\iff f(s)\in\mathrm{EXPCOM}[c_H].
\end{aligned}
\]

Moreover, $\vert f(s)\vert =2\vert s\vert +6$. An EXP decider for `EXPCOM[c_H]` would consequently decide $H$ in EXP, a contradiction. Since any oracle belongs to its own relativized P, and relativized P is contained in relativized NP,

\[
\mathrm{EXPCOM}[c_H]\in
\mathrm P^{\mathrm{EXPCOM}[c_H]}
\subseteq\mathrm{NP}^{\mathrm{EXPCOM}[c_H]}.
\]

Thus the upper inclusion and both identities with EXP fail for permitted effective schemes. Taking a maximum of code-dependent constants over codes of bounded length does not repair this: the maximum exists but need not have an exponential bound.

The issue with `Classical.choice exists_effectiveMachineCode` is precise: it supplies an inhabitant of the weak type, not a proof that the chosen inhabitant is an efficiently decoding witness used inside an existence proof. No attached theorem identifies this choice with an efficient scheme. The counterexample establishes insufficient specification; it does not purport to evaluate an opaque choice operation.

### The P-versus-NP identity is also not uniform over effective schemes

The fourth dependent assertion, `POracle_EXPCOM_eq_NPOracle_EXPCOM`, cannot be justified merely by dropping the identities with EXP.

Take any effective scheme $c_0$ and put $E_0=\mathrm{EXPCOM}[c_0]$. There is a **decidable** language $H$ such that, for

\[
A=\{0z:z\in E_0\}\cup\{1z:z\in H\},
\qquad \mathrm P^A\ne\mathrm{NP}^A.
\]

Here is the required construction. Use an effective recurrent enumeration of deterministic oracle machines. At a fresh length $n_i$, simulate its $i$-th machine for $t_i=n_i^i+i<2^{n_i}$ steps on $1^{n_i}$. Answer tag-0 queries with the fixed decidable language $E_0$, and tag-1 queries with the finite set already placed into $H$. If the machine accepts, add nothing at length $n_i$; otherwise insert a length-$n_i$ word whose tag-1 query was not asked. Require $n_i\ge i+2$, and choose each later length larger than all earlier lengths and budgets. The query-count bound supplies the word, and locality preserves each flipped answer. The polynomial-budget domination proved below then excludes the unary witness language of $H$ from $\mathrm P^A$, while one guessed word and a tag-1 query put it in $\mathrm{NP}^A$.

All stages are effective: finite simulation calls only the decidable $E_0$ and a finite set; choose the least suitable length and least unqueried word. To decide membership in $H$ for a word of length $m$, run stages until their fresh length exceeds $m$. Increasing fresh lengths guarantee termination and permanent membership at length $m$.

Construct $c_H$ as above using this $H$. Then `EXPCOM[c_H]` and $A$ reduce to one another in polynomial time. To reduce `EXPCOM[c_H]` to $A$, parse the triple; a tag-0 code asks the corresponding $E_0$ triple, and a tag-1 code asks membership of its suffix in $H$. In the reverse direction, retag the code of a parsed $E_0$ triple, or use $f(s)$ for a tag-1 query. Malformed inputs map to a fixed nonmember. The maps use only parsing and copying. Substituting these reductions for oracle calls preserves polynomial time, also branchwise. Consequently

\[
\mathrm P^{\mathrm{EXPCOM}[c_H]}=\mathrm P^A
\ne\mathrm{NP}^A=\mathrm{NP}^{\mathrm{EXPCOM}[c_H]}.
\]

This is a mathematical counterconstruction, not a Lean-checked counterexample file.

## Blind restatements of the four definitions

These restatements follow the formal bodies, including their boundary cases.

| Definition | Restatement | Fidelity assessment |
|---|---|---|
| `OracleTM.queriesWithin M O x t` | Initialize $M$ on $x$, and run with $O$. For each integer $s=0,\ldots,t-1$, inspect the configuration after exactly $s$ steps. If its state is `some qQuery`, append that configuration's `queryString`; otherwise append nothing. Preserve order and repetitions. | Correct list of consultations performed by the first $t$ transitions. It records query-state occupancy before the answering transition, not merely entry into that state. No well-formedness hypothesis is required. |
| `OracleNDTM.queriesAlong N O x w` | For each $s<\vert w\vert $, run from initialization using the first $s$ bits of $w$. Record the query string exactly when that prefix run is in `qQuery`, in increasing $s$ order and with repetitions. | Correct fixed-branch analogue. Every transition consumes a bit; query-answer transitions ignore its value. `w.take t` gives a horizon of $\min(t,\vert w\vert )$. |
| `EXPCOM` | A word belongs iff it equals `pairEncode α (pairEncode x (replicate n true))` for some code word, input word, and natural number $n$, and the decoded machine has halted with output exactly `[true]` after $2^n$ transitions. Absorbing halting makes this equivalent to halting by that deadline. | The triple layout, inclusivity, and rejection of nontriples are sound. Empty code/input/padding are allowed. Every code word denotes a machine; a malformed *machine code* need not be rejected. The weak decoding specification invalidates the advertised EXP interpretation: finding 1. |
| `unaryWitnessLang B` | A word belongs iff it consists of $n$ true bits for some $n$, and $B$ contains a word of length exactly $n$. | Matches the intended unary witness language. The empty input belongs iff the empty word belongs to $B$. Every input containing a false bit is excluded. |

## All seventeen statement verdicts

“True” below means the statement survives a mathematical reconstruction over the attached semantics; it does not mean its `sorry` has been filled.

| # | Declaration | True-as-stated argument or obstruction |
|---|---|---|
| 1 | `OracleTM.runFrom_eq_of_agree_length_lt` | **True.** Induct on the elapsed steps up to $t$. At step $s<t$, an initialized query has length at most $s<t$; agreement therefore fixes the answer. Other steps are oracle-independent. |
| 2 | `OracleTM.runFrom_eq_of_agree_queriesWithin` | **True.** The same induction uses membership of the actual query at index $s$ in the first oracle's list. Equality of prefix configurations makes the asymmetry sufficient. |
| 3 | `OracleTM.length_le_of_mem_queriesWithin` | **True.** A listed word comes from an index $s<t$, with length at most $s$. In fact the stronger conclusion $\vert z\vert <t$ holds. |
| 4 | `OracleTM.queriesWithin_length_le` | **True.** `filterMap` retains at most one item per element of `List.range t`. |
| 5 | `OracleNDTM.runWith_eq_of_agree_length_lt` | **True.** Induct over prefixes of the fixed word. The same tape invariant holds because actions write at the old head and move by at most one, while query/halting transitions do not write. |
| 6 | `OracleNDTM.runWith_eq_of_agree_queriesAlong` | **True.** Prefix equality plus agreement on the first branch's submitted queries gives equality of the next transition under the common next bit. |
| 7 | `OracleNDTM.length_le_of_mem_queriesAlong` | **True.** A listed query occurs after $s<\vert w\vert $ transitions and has length at most $s$; again the strict bound is available. |
| 8 | `EXP_subset_POracle_EXPCOM` | **True even for the weak code interface.** For each language, fix one decider and one code once and for all; its code is a constant in the reduction. Quadratic normalization preserves exponential time. A sufficiently large polynomial unary exponent makes one query correct. No uniform decoding bound is used here. Finding 3 corrects a cited lemma only. |
| 9 | `NPOracle_EXPCOM_subset_EXP` | **Not cleared; finding 1.** Variable-code decoding can exceed every EXP bound. |
| 10 | `POracle_EXPCOM_eq_EXP` | **Not cleared; finding 1.** A permitted `EXPCOM` can itself be outside EXP while belonging to its own relativized P. |
| 11 | `NPOracle_EXPCOM_eq_EXP` | **Not cleared; finding 1.** The same counterexample applies to relativized NP. |
| 12 | `POracle_EXPCOM_eq_NPOracle_EXPCOM` | **Not cleared; finding 1.** The second counterconstruction above gives an effective coding scheme whose EXPCOM oracle separates the classes. |
| 13 | `unaryWitnessLang_mem_NPOracle` | **True.** The explicit scan/guess/query/answer construction below runs in at most $n+3$ steps, with rejection on every non-unary branch. |
| 14 | `exists_finOracleTM_enumeration` | **True.** Finite transition tables with fixed tape/state counts form a finite set; state relabeling preserves exact-horizon output predicates under every oracle. Enumerate the canonical tables and add a repetition coordinate. Correct the impossible default in finding 2. |
| 15 | `exists_oracle_ne` | **True.** The fresh-length construction, query preservation, and explicit polynomial domination below prove the stated conjunction. Neither EXPCOM nor uniform decoding is needed. |
| 16 | `baker_gill_solovay` | **The existential theorem is true. Its submitted assembly is blocked.** A conventional efficient bounded-acceptance oracle supplies the equality half, and statement 15 supplies the separation half. The particular choice `A := EXPCOM` is not justified until finding 1 is repaired. |
| 17 | `exists_not_timeConstructible` | **True.** Its HALT-bit witness dominates the identity, is nondecreasing, and would make HALT computable if a constructor existed. Details below. |

The facade imports all four relevant component modules, including `OracleAgreement`. Its headline EXPCOM descriptions inherit finding 1. It introduces no definition or theorem.

## Answers to the seven numbered questions

### 1. Behavioral equivalence and enumeration

The quantifier order is adequate:

\[
\exists N\;\forall M\;\forall i_0\;\exists i\ge i_0\;
\forall O,x,\mathrm{output},t\;[\text{equal bounded-output predicates}].
\]

The enumeration is fixed before constructing the final oracle. Selecting a late representative of an alleged decider afterward does not change the enumeration or the oracle. Because equivalence holds at every horizon and for both Boolean verdicts, monotonicity transfers a decider's output to the stage deadline; output uniqueness excludes the opposite output.

State relabeling is strong enough: a bijection on states preserves the initial state, all three distinguished states, transition outputs, and halting. Its configuration transport commutes with each step, including query resolution. Well-formedness ensures at least three states; all such machines occur among the canonical `Fin (m+1)` tables. Empty well-formed table sets at smaller state counts cause no completeness problem.

For explicit recurrence, first let $E(j)$ enumerate canonical tables with a valid default. Set

\[
N(\mathrm{pair}(j,r))=E(j).
\]

For each fixed $j$, injectivity of the pairing makes these indices infinite, hence unbounded. This proves the required recurrence without asserting literal equality of bundled state types.

### 2. Stage construction, consistency, and diagonal quantifiers

Write $t_i=n_i^i+i$. Choose each $n_i\ge i+2$ larger than every previous $n_j,t_j$, with

\[
2^{\lfloor n_i/10\rfloor}>t_i.
\]

Such choices exist because an exponential eventually exceeds each fixed polynomial. Let $O_i$ be the finite set of positive insertions before stage $i$. It contains no word of length $n_i$. Run $N_i^{O_i}$ on $1^{n_i}$ for $t_i$ transitions. If it has halted with output `[true]`, insert nothing; otherwise insert one length-$n_i$ word outside its query list. There are $2^{n_i}>t_i$ candidates and at most $t_i$ listed queries.

Treat every remaining word of length at most $\max(n_i,t_i)$ as permanently negative, while retaining earlier positives. This specifies the negative declarations that the sketch leaves implicit. Define $B=\bigcup_i O_i$.

For every query $z$ made at stage $i$:

\[
z\in O_i\Rightarrow z\in B;
\qquad
z\notin O_i\Rightarrow z\notin B.
\]

The second implication holds because the current inserted word is unqueried, and every later inserted word has length greater than $t_i\ge\vert z\vert $. Therefore the asymmetric locality theorem applies with **first oracle $O_i$** and **second oracle $B$**. It preserves the complete configuration at the deadline and hence the exact acceptance predicate. Consequently

\[
(N_i).\mathrm{ComputesInTime}(B,1^{n_i},[\mathrm{true}],t_i)
\iff 1^{n_i}\notin\mathrm{unaryWitnessLang}(B).
\]

Suppose a machine $M$ decided that language within $c(n^k+1)$. Select a behaviorally equal recurrence index

\[
i\ge\max(k+1,2c,2).
\]

Since $n_i\ge i+2$,

\[
c(n_i^k+1)
\le 2c\,n_i^k
\le n_i^{k+1}
\le n_i^i
\le t_i.
\]

Monotonicity and behavioral equivalence now give acceptance at the stage budget iff $1^{n_i}$ is in the language, contradicting the displayed flip. Nonhalting and wrong-output machines need not be deciders: both merely fall into the nonaccepting case. Earlier positives cannot conflict with the accepting-stage instruction because their lengths are strictly smaller than $n_i$.

### 3. EXPCOM's shape and uniqueness

The existential definition does not assume decidability or a complexity bound. Its parsing is unambiguous. From

\[
\mathrm{pairEncode}(\alpha,\mathrm{pairEncode}(x,1^n))
=\mathrm{pairEncode}(\beta,\mathrm{pairEncode}(y,1^m))
\]

two uses of pair injectivity give $\alpha=\beta$, $x=y$, and $1^n=1^m$; taking lengths gives $n=m$. The cited unary-first lemma is unnecessary and mismatched.

The total length is exactly

\[
|z|=2|\alpha|+2|x|+n+4.
\]

`ComputesInTime` requires both haltedness and the exact output, so it is faithful to inclusive “within.” A machine that has merely written `[true]` but has not halted is excluded. Bounded acceptance is computable for every effective scheme, but finding 1 shows it need not be in EXP.

### 4. EXPCOM simulation summit and the last-step boundary

The class-inclusion shape is appropriate for an efficiently coded oracle. Its boundary arithmetic is correct. If the answering transition is the last of $p(n)$ transitions, its query is read after $s=p(n)-1$ transitions, so

\[
n'\le|z|\le s<p(n).
\]

For a parsed triple the stronger $\vert z\vert =2\vert \alpha'\vert +2\vert x'\vert +n'+4$ also holds. If `qQuery` is only reached *after* transition $p(n)$, no query has yet been answered at that horizon. Moreover such a branch is still live and cannot satisfy all-branch halting at the promised deadline.

An actual halted branch cannot end with the answering transition either: that transition leaves a live answer state. The length bound above is valid even without using this additional restriction.

What fails is the next inference, from bounded query length to a uniform cost for decoding its code. A sufficient repair is a concrete timed simulator with a fixed polynomial bound in

\[
|\alpha'|+|x'|+t+1,
\qquad t=2^{n'},
\]

including canonization. With that property, $2^{p(n)}$ branch words, at most $p(n)$ calls per word, and polynomial parsing/copying overhead give total time $2^{\mathrm{poly}(n)}$. This includes emitting the deadline, restoring simulated tapes, and dispatching the next transition. A merely code-dependent constant does not suffice. The precise `timed_universal` success/timeout interface remains an unattached dependency; the mathematical inclusive-deadline algorithm itself is possible with an efficient scheme.

### 5. Locality indexing and nondeterministic horizons

There is no off-by-one defect. The transition from time $s$ to time $s+1$ consults the oracle exactly when the time-$s$ state is `qQuery`; these are precisely the indices $s<t$. At $t=0$, the query list is empty. At $t=1$, an initial query state submits the empty word and is correctly included.

For nondeterminism, `runWith` consumes the next bit before recursively processing the suffix, including when `stepWith` ignores it at a query state. Prefix length therefore equals elapsed transitions. In particular, the guess-writer's witness is the **first $n$ choice bits**, while the full word also has bits for its deterministic tail and any halting padding. Equality along prefixes and the initialized tape invariant prove all seven locality statements; well-formedness and finiteness of the state type are unnecessary for them.

### 6. Non-time-constructibility and monotonicity

The requested nontrivialization is adequate for Exercise 3.5. In fact the proposed witness already satisfies monotonicity. Write its HALT bit as $b(n)\in\{0,1\}$. Then

\[
T(n)=n+b(n),\qquad
n\le T(n)\le n+1\le T(n+1).
\]

Thus it is nondecreasing and differs from the identity by at most one. No statement change is necessary to meet the exercise.

Let `str` and `rank` be inverse effective enumerations between naturals and binary strings. A putative constructor, run on $1^{\mathrm{rank}(s)}$, would return the canonical binary representation of $T(\mathrm{rank}(s))$. Hence

\[
\begin{aligned}
\mathrm{HALT}(s)=\mathrm{true}
&\iff T(\mathrm{rank}(s))=\mathrm{rank}(s)+1\\
&\iff (T(\mathrm{rank}(s))).\mathrm{bits}
       \ne(\mathrm{rank}(s)).\mathrm{bits}.
\end{aligned}
\]

The last equivalence uses injectivity of canonical binary representation. Computing the rank, emitting the unary word, running the total constructor, and comparing finite words are all terminating computations; no runtime bound is needed. This contradicts the attached `HALT_not_computable`. Equality comparison handles odd ranks with a carry and rank zero; merely reading a low bit without accounting for the rank's parity would not.

### 7. Unary witness membership in NPOracle

A four-state machine suffices: scan, query, yes, no. While scanning a true input symbol, write the current choice bit in the current query-tape cell and advance both heads. On a false input symbol, emit `[false]` and halt. On the input-end blank, enter the query state without writing. The query-answer step moves to yes or no; the next step emits the corresponding Boolean and halts.

On unary input of length $n$, this uses $n$ write steps, one end-detection step, one answering step, and one output step:

\[
n+3\le3(n+1).
\]

The first $n$ choice bits fill exactly cells $0,\ldots,n-1$; cell $n$ stays blank, so `queryString` is exactly the guessed word. Every word of length $n$ can be the prefix of a choice word of length $3(n+1)$. The remaining bits are ignored by the tail or absorbing halted state. Every branch halts, and an accepting branch exists exactly when the input belongs to the stated language. If the input is non-unary, every branch rejects at its first false symbol. At $n=0$, the unique guessed word is empty and the same three-step tail works.

The actual class definitions have independent polynomial exponent and multiplicative constant. Choosing exponent $1$ and multiplier $3$ supplies the required membership witness.

## Adversarial instantiations

| Test | Instantiation | Result |
|---|---|---|
| A1 | Deterministic horizon $t=0$, or empty nondeterministic choice word; let the oracles disagree on the empty word. | No consultation occurs. Both runs remain initial and the lists are empty. Locality is not accidentally claiming a first-step answer. |
| A2 | Well-formed machine with `q₀ = qQuery`, horizon $1$, and oracles disagreeing on the empty word. | Exactly one empty query is recorded. The runs go to distinct answer states, showing why agreement on length-zero strings is necessary. |
| A3 | Write one true bit and enter `qQuery` in the first transition; use horizon $2$. | The one-bit query is answered by the last transition and recorded at index $1$, with length $t-1$. With horizon $1$, it is not yet submitted. |
| A4 | Raw machine with all special states equal to `qQuery` and initially in that state. | It can submit the unchanged empty query on every step. The list has repetitions and length exactly $t$; all locality assertions still hold without `WellFormed`. |
| A5 | Nondeterministic query step with next choice bit false versus true. | The bit is consumed in either case but the same oracle answer is returned. No choice-bit shift occurs in the prefix horizon. |
| A6 | $B=\varnothing$, $B=\{\varepsilon\}$, and $B$ equal to all binary words. | The unary languages are respectively empty, ${\varepsilon\}$, and all true-only words. In the last case `[false]` is still rejected. |
| A7 | EXPCOM padding exponent $0$, using a one-step accepting machine and a machine that accepts only at step $2$. | The first triple belongs and the second does not, because the deadline is exactly $1$. |
| A8 | Empty outer word, malformed inner pair, or inner suffix containing a false bit instead of a unary padding word. | The defining existential fails. Empty code/input and a genuinely empty padding suffix remain valid when the two separators are present. |
| A9 | Stage $i=0$, fresh length $n_0=10$, budget $10^0+0=1$, and a nonaccepting bounded run. | The margin is $2^{\lfloor10/10\rfloor}=2>1$. A length-10 insertion must be protected despite its length exceeding the budget. The corrected cutoff $\max(10,1)=10$ does so. |
| A10 | An earlier stage inserts a word; a later stage's simulation accepts. | The later fresh length exceeds the earlier insertion's length, so declaring the later length empty never removes the earlier positive. |
| A11 | Enumerated machine loops forever, halts with `[]`, or halts with `[true,false]`. | All are nonaccepting at the budget and cause an unqueried insertion. The flip is against the exact `[true]` predicate, not an assumed Boolean decider. |
| A12 | A one-state candidate default and a representative with an arbitrary finite state type of size at least three. | The former violates well-formedness (finding 2). The latter relabels exactly, including at query transitions; no slowdown or oracle-dependent representative is needed. |
| A13 | The tagged effective code scheme $c_H$, with the one-step deadline and empty simulated input. | It embeds an arbitrarily hard decidable membership question into decoding, refuting the uniform EXP claim without any long simulated run. |
| A14 | Consecutive HALT bits $b(n)=1,b(n+1)=0$, and an odd rank with HALT bit $1$. | $T(n)=T(n+1)=n+1$, so monotonicity survives the downward bit change. At odd rank, the full equality comparison still recovers the HALT bit despite the binary carry. |

## Source comparison and declared deviations

[AB09] §3.4 defines the query/answer model and the relativized classes; Example 3.6$3$ gives the EXPCOM identities, and Theorem 3.7 supplies the two existential oracle conclusions. The packet's unary language and headline statements match those targets, subject to finding 1's coding issue. Exercise 3.5 asks only for existence of a non-time-constructible function; domination is a legitimate strengthening. The book also mentions exclusion of every oracle time bound $o(2^n)$ in the separation proof; the packet does not state that stronger result.

[BGS75] p. 432 explicitly clocks enumerated machines under every oracle. Lemma 1 and Theorems 1–2 concern the complete-language and equality constructions; §3, Theorem 3 uses fresh lengths and preserves earlier query answers. The packet's external budgets correctly replace the internal clocks for its diagonalization. BGS75's recursive-oracle strengthening is not asserted by the submitted existential statements. Its self-referential equality construction is properly treated as a fallback, not as the submitted EXPCOM proof.

Declared-deviation disposition:

| Pack item | Disposition |
|---|---|
| 1. EXPCOM layout, fixed code, inclusivity, totalization | Layout/inclusivity/totalization pass. Fixed-code reuse is the blocker; unary-tail lemma attribution is minor. |
| 2. Deterministic-only, clock-free recurrent enumeration | Correct statement and sufficient strength. Repair the default and make the repetition coordinate explicit. |
| 3. Stage packaging, larger fresh lengths, explicit acceptance predicate | Pass, including the corrected maximum cutoff and nonaccepting-run convention. |
| 4. Query lists, asymmetry, fixed ND word | Pass. Multiplicity and all-step bit consumption are handled correctly. |
| 5. Identity-domination and HALT witness | Pass; the witness is also nondecreasing. |
| 6. Deferred helper locations | No semantic defect. The ND invariant and oracle state transport can be proved locally and promoted later as declared. |
| 7. Sketch-level imports | No correctness defect. Full dependency/export verification is outside the supplied evidence. |

Primary texts consulted: [AB09 published-text copy, pp. 73–75](https://kubokovac.eu/zlozitost/arora.pdf), [AB09 Exercise 3.5, p. 77, alternate published-text copy](https://nzdr.ru/data/media/biblio/kolxoz/Cs/CsNp/Arora%20S.%2C%20Barak%20B.%20Computational%20complexity..%20A%20modern%20approach%20%28CUP%2C%202009%29%28ISBN%200521424267%29%28605s%29_CsNp_.pdf), and [BGS75 original scan](https://cse.ucdenver.edu/~cscialtman/complexity/Relativizations%20of%20the%20P=NP%20Question%20(Original).pdf). The AB09 comparisons used retrieved indexed passages: direct PDF fetches were unavailable. BGS75's relevant pages were accessible. No claim is made that a complete published-book PDF was downloaded.

The new-file source inventory and warning counts were checked directly. The full imported machine library, private chapter-2 enumerator proofs, parser implementation, and `timed_universal` were not independently reverified. No source files were modified and no Lean elaboration was run. These limitations do not affect the counterexample, which uses the explicit attached coding interface and the chosen-code definition.

## Notation glossary

| Notation | Meaning |
|---|---|
| $\varepsilon$, $\vert w\vert $, $1^n$, $0w$, $1w$ | Empty binary word, word length, $n$ true bits, and prepending a false or true tag. Numerals in these word expressions denote bits. |
| $\mathrm P^O,\mathrm{NP}^O$ | The packet's `POracle O` and `NPOracle O`. `EXP` and all Lean declaration names retain their packet meanings. |
| `EXPCOM[c]` | The packet's EXPCOM formula with scheme $c$ in place of `TimeHierarchy.code`; audit notation only. |
| $H,c_0,c_H,M_+,M_-,f$ | Auxiliary decidable language, base coding scheme, tagged scheme, one-step accepting/rejecting machines, and the displayed triple-encoding reduction. The second counterconstruction makes a separate choice of $H$. |
| $M_j,a_j,k_j$ | The machine, multiplicative constant, and exponent in the decidable diagonal language's enumeration. |
| $E_0,A$ | EXPCOM for the base scheme and the tagged join of $E_0$ with $H$. |
| $E(j),N_i,\mathrm{pair}(j,r)$ | Canonical-table enumeration, its recurrent version, and an injective bijective pairing of natural numbers. $r$ is the repetition coordinate. |
| $n_i,t_i,O_i,B$ | Fresh stage length, stage deadline $n_i^i+i$, finite set of prior positive insertions, and their final union. |
| $c,k,p(n)$ | A hypothetical decider's polynomial multiplier and exponent, and its polynomial step budget; these are separate parameters. |
| $x,z,\alpha,n'$ | Input or query words, code word, and the unary exponent in a parsed EXPCOM query, as specified locally. Other natural-number indices and word variables are locally quantified dummy variables. |
| $T,b,\mathrm{str},\mathrm{rank}$ | The non-time-constructible witness, its HALT bit, an effective enumeration of words, and its inverse. `HALT` uses the packet's fixed effective scheme. |
| $\mathrm{poly}(n)$ | Some fixed polynomial in $n$; its coefficients and degree do not depend on the input. |
