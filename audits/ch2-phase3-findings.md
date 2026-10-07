**Chapter 2, phase 3, round 1 — independent adversarial statement audit**

Intended repository destination: `audits/ch2-phase3-findings.md`.
Audited snapshot: the supplied bundle labelled `1a7554d1`, branch `complexity/arora-barak-ch1`.
Bundle SHA-256: `f43ad422e4af52d86d749d5efe1330004e9d4a3daf3e35b5bc18334c11dcc65f`.

**Disposition: keep the gate open. Two blocker findings, one major, two minors, and three notes.** The two blockers share one mathematical obstruction: `EffectiveMachineCode` permits computable but computationally expensive meanings for short codes. Consequently, `TMSAT_mem_NP` and `TMSAT_NPComplete` are false at their stated generality. The language definition and `MachineCode`-general hardness statement survive. I found no false statement among the other ten new signatures.

I read the new declarations with comments removed before reading their sketches. Chapter 1 and phases 1–2 were used as trusted dependencies; their closed gates and the reserved HALT design question were not reopened. The arguments below are mathematical audit arguments, **not kernel-checked Lean counterexamples or completed machine constructions**. Executable checks are explicitly distinguished from proofs.

The 2009 textbook and pinned Lean-core sources are not attachments. I consulted the [authors’ January 2007 draft](https://theory.cs.princeton.edu/complexity/book.pdf#page=60): it contains the same TMSAT language and CNF/SAT conventions, but its CNF-universality, SAT-to-3SAT, and TAUTOLOGY numbering differs. Published item numbers and the specific published fallback footnote remain the pack’s citations, not independently verified bibliographic claims. The [official current CNF API](https://lean-lang.org/doc/api/Std/Sat/CNF/Basic.html) corroborates literal polarity and conjunction/disjunction evaluation, but currently uses an array-backed formula structure. It is not evidence for the precise carrier/API at the claimed 4.25.0 pin; that version could not be independently retrieved. I do not infer a pinned-version defect from current-version drift.

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | blocker | `ClassNP/TMSAT.lean:152` · `TMSAT_mem_NP` | Every effective code scheme yields an NP language. | Argument A constructs a lawful `EffectiveMachineCode` for which a linear-size family of TMSAT instances, with certificate length **zero** and deadline **one**, decides a decidable language outside EXP. Also, the actual universal-machine coefficient contains the unrestricted `c.canonizerTime`; inspection cannot manufacture its asserted polynomial bound. | Add an efficient-canonization hypothesis, e.g. `PolyBound c.canonizerTime`, or a new refined code interface; alternatively specialize to a concrete scheme with a newly proved polynomial canonizer. Supply a uniform polynomial simulation theorem for that stronger interface. Preserve the frozen Chapter-1 contracts. |
| 2 | blocker | `ClassNP/TMSAT.lean:196` · `TMSAT_NPComplete` | Every effective scheme gives NP-completeness. | `NPComplete` includes membership in NP. The same lawful scheme in Argument A falsifies that conjunct; its NP-hardness is compatible with being outside NP. | Propagate finding 1’s stronger hypothesis to this theorem and the module/facade descriptions. Keep `TMSAT_NPHard` at plain `MachineCode`. |
| 3 | major | `ClassNP/TMSAT.lean:176` · `TMSAT_NPHard`, unary-emission sketch | `timeConstructible_poly` supplies both exact unary lengths after “standard majorization.” | The exact certificate length `Q n = C₀(n+1)^c₀` may be zero or constant, hence is not time constructible under the inherited definition. Replacing its value by a larger admissible polynomial can change the language. Argument B gives an explicit false-positive example and a corrected reduction budget. The promised “explicit” `T'` is also left as a description, not a formula. | Keep `Q` exact. Handle `C₀=0` and `c₀=0` by constant emitters; apply the lemma with predecessor exponent only when `C₀>0,c₀>0`. Majorize the **time bound**, not the certificate value. Insert an explicit `T'`, such as Argument B’s formula. If majorization meant only a runtime budget, state that distinction and name the exact-value computation. |
| 4 | minor | `ClassNP/TMSAT.lean:126` · `TMSAT_mem_NP`, split recovery | Reject odd total verifier-input lengths. | A valid concatenation has length `m+(m+1)=2m+1`, which is odd. Read literally, this rejects every valid verifier input. The analogous SAT sketch has the correct parity. | Replace “odd-length rejection” by “even-length rejection”; on odd length `N`, split at `(N−1)/2`. |
| 5 | minor | `ClassNP/SAT.lean:31` · fallback-independence prose | Changing the fixed fallback changes malformed-input membership sides uniformly for SAT and 3SAT. | A satisfiable clause with four repeated positive literals is a satisfiable fallback of width four. With that fallback malformed inputs belong to SAT and do **not** belong to SAT3. This does not affect the actual empty fallback or invalidate the reduction. | Say the two membership branches follow their respective predicates on the fallback. The reduction maps malformed inputs to the serialization of the **transformed** fallback. |
| 6 | note | `Formulas/CNF.lean`, `Formulas/CNFEncoding.lean`, `ClassNP/SAT.lean` · carrier, encoding, fallback | The selected conventions support the stated CNF/SAT results. | Arguments C–E verify polarity, finite assignment bounds, grammar/fuel, exact consumption, the empty-clause distinction, unary sizes, and clause splitting. The present malformed-string branch is indeed true on both sides of the reduction. | No mathematical redesign required. Keep complete syntax validation before any evaluation-based rejection. Retain the toolchain pin; unary encoding is not a polynomial expansion of arbitrary sparse binary labels without renaming. |
| 7 | note | `AroraBarakChapter2Plan.md` · TAUTOLOGY deferral | CNF tautology is in P; negating CNF naturally requires the DNF dual. | Argument F proves the complementary-pair criterion, including empty cases, and the negation equivalence. The deferral is coherent. DNF-only tautology is a restricted language, however, not literally the general-formula carrier. | No phase-3 theorem change. At phase 4, document a DNF-fragment rendering or supply a general Boolean-formula carrier; do not silently identify their syntax. |
| 8 | note | Audit pack · attestations and exported surface | The present source inventory agrees with the pack. | All 60 attachments, 48 ordered campaign modules, 16 new definitions, 12 new admissions, 45 total admissions, and the five stated line counts are reproducible. Imports/exports and order-list dependencies are consistent. Historical freeze, fresh elaboration, axiom prints, and lint execution are not established by this snapshot. | Preserve the source/execution distinction. No additional mathematical repair. |

**Blind definition restatements — all 16.** Here `0`/`1` mean Boolean false/true; string juxtaposition in encoding equations means concatenation, not numerical multiplication.

| Declaration | Literal content |
|---|---|
| `CNF.Satisfiable φ` | There exists a total assignment `a` with `φ.eval a = true`. |
| `CNF.numVars φ` | Maximum of `v+1` over all literal occurrences `(v,b)`, with default zero. It bounds the index range, not the number of distinct variables. |
| `CNF.WidthAtMost φ k` | Every clause of `φ` has list length at most `k`; repetitions count. |
| `serializeLit (v,b)` | The string `1^(v+1) ++ [0,b]`. |
| `serializeClause C` | Concatenate the serialized literals, then append `[0]`. |
| `serialize φ` | For each clause emit `[1] ++ serializeClause C`; concatenate these records and append the formula terminator `[0]`. |
| `takeTrues x` | Return the length of the maximal initial run of ones and the remaining suffix. |
| `parseLit x` | Require a nonempty initial one-run of length `k+1`, followed by zero and a polarity bit; return `(k,b)` and the suffix. Otherwise fail. |
| `parseClause fuel x` | A leading zero returns the empty clause and suffix, even at fuel zero. Otherwise a leading one requires positive fuel, one literal parse, and recursive parsing at fuel minus one. |
| `parseClauses fuel x` | A leading zero returns the empty formula and suffix, even at fuel zero. A leading one requires positive fuel; parse the clause body and remaining formula, each with fuel minus one, threading the returned suffix. |
| `parse x` | Run `parseClauses` with fuel `x.length`; succeed only if no suffix remains. |
| `fallback` | The empty CNF formula. |
| `decode x` | Return the parsed formula on success, otherwise `fallback`. |
| `SAT` | Strings whose decoded formula is satisfiable. |
| `SAT3` | Strings whose decoded formula is both width-at-most-three and satisfiable. |
| `TMSAT c` | Strings equal to `pairEncode α (pairEncode x (pairEncode (1^n) (1^t)))` for which some `u` of length exactly `n` makes `(c.decode α).toFinTM` halt on `pairEncode x u` with completed output exactly `[true]` by time `t`. |

These definitions have the advertised semantics. In particular, the TMSAT definition is a meaningful language for every `MachineCode`; the defect is the membership theorem’s insufficient hypothesis.

**Blind statement restatements — all 12.**

| Declaration | Literal content and assessment |
|---|---|
| `eval_congr_of_lt_numVars` | Assignments agreeing below `φ.numVars` give equal evaluations. Sound. |
| `exists_cnf_boolFun` | Every function on `Fin ℓ → Bool` has a CNF using indices below `ℓ`, at most `2^ℓ` clauses, width at most `ℓ`, and the same value on every restricted total assignment. Sound, including `ℓ=0`. |
| `parse_serialize` | Every formula’s serialization parses to exactly that formula. Sound. |
| `decode_serialize` | Total decoding is a left inverse of serialization. Sound. |
| `numVars_decode_le` | For every string `x`, `(decode x).numVars ≤ x.length`. Sound. |
| `SAT_mem_NP` | The declared SAT language belongs to the audited NP class. Sound. |
| `SAT3_mem_NP` | The declared SAT3 language belongs to NP. Sound. |
| `SAT_reducible_SAT3` | A total polynomial-time string function preserves membership from SAT to SAT3 in both directions. Sound. |
| `timeConstructible_poly` | For natural `C>0,c`, `n ↦ C(n+1)^(c+1)` satisfies the inherited constant-slack binary-output time-constructibility definition. Sound. |
| `TMSAT_mem_NP` | For every effective machine-code scheme, its TMSAT belongs to NP. **False: Argument A.** |
| `TMSAT_NPHard` | For every lawful machine-code scheme, every NP language polynomial-time many-one reduces to its TMSAT. Sound; sketch repair in Argument B. |
| `TMSAT_NPComplete` | For every effective scheme, its TMSAT belongs to NP and is NP-hard. **False: Argument A.** |

**Argument A — a lawful effective-code counterexample, not merely a missing estimate.**

1. There is a decidable binary language outside EXP, with no unproved class separation needed. For completeness, effectively enumerate all triples `(M_i,a_i,d_i)` of finite one-work-tape binary machines and natural clock parameters. Let
   \[
   D_i(z)=1\iff M_i\text{ halts with output }[1]\text{ within }
   a_i2^{(|z|+1)^{d_i}}\text{ steps}.
   \]
   Every `D_i` is decidable by finite simulation. Every EXP language occurs among these languages: the trusted finite-state renaming and quadratic one-tape normalization preserve exponential-polynomial time, and the coefficient/exponent enumerate all such bounds. Put
   \[
   w_i=1^i\mathbin{++}[0],\qquad
   A(w_i)=1-D_i(w_i),\qquad A(z)=0\text{ otherwise}.
   \]
   The words `w_i` are distinct, and their index is recoverable, so this defines a total decision algorithm. If `A=D_j`, then
   \[
   A(w_j)=1-D_j(w_j)=1-A(w_j),
   \]
   impossible for a Boolean value. Hence `A` is decidable and `A ∉ EXP`.

2. Choose an effective base scheme `c₀`, whose existence is the trusted `Turing.exists_effectiveMachineCode`. Let `M_b` be the one-state coded machine whose every transition leaves heads stationary, emits the Boolean `b`, and halts. For every input `z`,
   \[
   M_b.\mathrm{toFinTM}.\mathrm{ComputesInTime}(z,[b],1).
   \]
   Define a new scheme by
   \[
   \begin{aligned}
   c_A.\mathrm{encode}(M)&=[0]\mathbin{++}c_0.\mathrm{encode}(M),\\
   c_A.\mathrm{decode}([])&=M_0,\\
   c_A.\mathrm{decode}([0]\mathbin{++}\alpha)&=c_0.\mathrm{decode}(\alpha),\\
   c_A.\mathrm{decode}([1]\mathbin{++}z)&=M_{A(z)}.
   \end{aligned}
   \]
   The last two equations concern strings with the displayed leading bit, so the cases are disjoint.

3. This preserves the **full padding law**, not merely unpadded decoding:
   \[
   \begin{aligned}
   c_A.\mathrm{decode}(c_A.\mathrm{encode}(M)\mathbin{++}1^k)
   &=c_0.\mathrm{decode}(c_0.\mathrm{encode}(M)\mathbin{++}1^k)\\
   &=M.
   \end{aligned}
   \]
   Thus this is a lawful `MachineCode`, unlike a constant-decoder counterexample.

4. It is also **effective**. A canonizer reads the first bit. On the zero branch it runs the base canonizer on the suffix; on the one branch it decides `A(z)` and emits one of the two fixed serializations `M_0.serialize`, `M_1.serialize`; the empty-input branch emits the former. All branches terminate. A finite maximum of their running times over inputs of each fixed length supplies `canonizerTime`. This is exactly the kind of arbitrary length-dependent bound the inherited structure permits. The required output is the fixed `serialize ∘ decode`, not the new scheme’s own encoding. No polynomial claim is made.

5. Define the polynomial-time map
   \[
   g(z)=\operatorname{pairEncode}([1]\mathbin{++}z,
        \operatorname{pairEncode}([],
        \operatorname{pairEncode}([],[1]))).
   \]
   Its length is `2|z|+9`. Three uses of `pairEncode_injective`, followed by equality of unary lengths, force every TMSAT witness for this string to use the same code, `x=[]`, `n=0`, `t=1`. The only certificate is `u=[]`. Therefore
   \[
   \begin{aligned}
   g(z)\in\mathrm{TMSAT}(c_A)
   &\iff M_{A(z)}\text{ outputs }[1]\text{ on }
                 \operatorname{pairEncode}([],[])\text{ within one step}\\
   &\iff A(z)=1.
   \end{aligned}
   \]
   Output uniqueness excludes acceptance by `M_0`. Alternative tuple decompositions cannot supply another accepting machine or deadline.

6. If the asserted membership theorem held, trusted `NP_subset_EXP` would give `TMSAT(c_A) ∈ EXP`. Computing `g` and running that decider would put `A` in EXP: an affine input-length substitution and the fixed simulation overhead preserve exponential-polynomial time. Explicitly, for sufficiently large `n`, `2n+9 ≤ n²`, so an exponent `(2n+9)^d` is at most `n^(2d)`; polynomial overhead and finitely many smaller inputs are absorbed by the exponent and coefficient. This contradicts step 1. Thus both new membership and completeness signatures are false.

The source-level failure is equally explicit. `Encoding.lean:438` permits arbitrary `canonizerTime`. The witness chosen by `Universal.lean:2821` is
\[
 C_\alpha=\mathrm{timedStartupBound}(c,\alpha)
          +\mathrm{universalBlockBound}(c,\alpha)+14.
\]
`Universal.lean:2666` includes `c.canonizerTime α.length` in the first summand; `UniversalBlock.lean:750` also depends on the decoded serialization length and state count. These are not known to be polynomial in the original code length. `MathlibBridge.lean` explicitly says its concrete existence construction proves **no polynomial canonizer bound**. Even an easy scheme may carry an unnecessarily inflated `canonizerTime`, so a polynomial bound on this chosen coefficient is not automatic for easy semantics either.

A sufficient repair can be quantified. Write `r=|α|`, `H=c.canonizerTime r`, `L=|(c.decode α).serialize|`, `N=(c.decode α).numStates+1`, `h=|(Nat.bits (c.decode α).numStates)|`, and `q=(c.decode α).tm.q₀.val`. The actual coefficient is
\[
 C_\alpha=3r+H+4L+2h+2q+5N+50.
\]
The serialization contains every state’s records and its header, so `h,q,N ≤ L`; the canonizer’s output-length bound gives `L ≤ H`. Consequently,
\[
 C_\alpha\le3r+14H+50.
\]
If a new hypothesis gives `H ≤ A(r+1)^d`, then, with `e=max(d,1)`,
\[
 C_\alpha\le(14A+53)(r+1)^e,
 \qquad
 C_\alpha(t+1)^2\le(14A+53)(m+1)^{e+2}
 \quad(r,t\le m).
\]
This supplies the missing uniform polynomial budget. The current public `timed_universal` existential does not expose that quantitative refinement, and some witness machinery is private: a new audited public bridge or a separately constructed bounded simulator is still needed. Merely adding a prose fill obligation cannot prove the original unrestricted theorem.

For any well-formed instance, the exact length is `m=2|α|+2|x|+2n+t+6`, so `|α|,n,t≤m`. Pairing injectivity and unary-string lengths uniquely determine `α,x,n,t`; the existential certificate `u` need not be unique, as intended. Malformed quadruples have no witness.

The remaining membership obligations are appropriate **after this repair and the parity correction**: three aligned pair parses; all-one checks; exact-length padding to `m+1`; unary-to-binary conversion, including `Nat.bits 0=[]`; assembly of the stated nested universal input; relocated simulation with captured emissions; and acceptance only for the complete captured answer `[true,true]`. The forward branches of `timed_universal`, their exhaustiveness, and output uniqueness justify the converse acceptance test. A timeout or a completed output other than `[true]` is rejected. At `t=0`, `not_computesInTime_zero` makes every instance negative.

**Argument B — hardness survives; preserve exact certificates and exhibit the budget.**

Fix the audited NP witness with
\[
 Q(n)=C_0(n+1)^{c_0},\qquad
 x\in L\iff\exists u,\ |u|=Q(|x|)\land x\mathbin{++}u\in V.
\]
The proposed wrapper correctly rejects non-pairs and otherwise runs the total decider of `V` on the recovered concatenation, with output capture. Therefore it computes a total function, so `one_work_tape_binary` is applicable. Take a wrapper bound `B(s+1)^e` with `B,e≥1`, enlarging a bound if necessary, and let `K` be the normalization multiplier. The normalized coded machine has bound
\[
 K\bigl(B(s+1)^e+1\bigr)^2.
\]
On relevant inputs `s=2n+2+Q(n)`. Put
\[
 r=\max(1,c_0),\quad
 D=(K+1)(B+1)^2(C_0+3)^{2e},\quad
 T'(n)=D(n+1)^{2er}.
\]
Then, for every `n`, including zero,
\[
 \begin{aligned}
 s+1&=2n+3+C_0(n+1)^{c_0}
          \le(C_0+3)(n+1)^r,\\
 K\bigl(B(s+1)^e+1\bigr)^2
     &\le(K+1)(B+1)^2(s+1)^{2e}
      \le T'(n).
 \end{aligned}
\]
Here `D>0` and `2er≥1`; `timeConstructible_poly D (2er−1)` computes the **exact** binary value of this chosen `T'`.

For `Q`, the correct cases are:

| Parameters | Exact-value computation |
|---|---|
| `C₀=0` | Emit the empty unary string; its binary value is `Nat.bits 0=[]`. |
| `C₀>0, c₀=0` | Emit the fixed constant’s bits/unary run from finite control. No time-constructibility claim for a constant function is needed. |
| `C₀>0, c₀>0` | Apply `timeConstructible_poly C₀ (c₀−1)`. |

Binary countdown then emits the exact unary runs in polynomial time. The reduction has the concrete length
\[
 |f(x)|=2|\alpha_0|+2|x|+2Q(|x|)+T'(|x|)+6,
\]
where `α₀` is a fixed encoding of the normalized wrapper. Plain `MachineCode` suffices because this code is hardwired, not decoded by the reduction.

With this budget, tuple injectivity, wrapper semantics, and output uniqueness give
\[
 f(x)\in\mathrm{TMSAT}(c)
 \iff\exists u,\ |u|=Q(|x|)\land x\mathbin{++}u\in V
 \iff x\in L.
\]

To see why majorizing `Q` is not a substitute, take `C₀=0`, `c₀=0`, and `L=V={ [true] }`, with the exact zero-length certificate. At `x=[]`, the original existential is false. Replacing `Q(n)=0` by `n+1`, while retaining the proposed wrapper, admits `u=[true]` and makes it true. Repairing that alternative would require an additional padding/truncation verifier and a new correctness argument. The exact-value construction above avoids that change.

**Argument C — carrier, serialization, fuel, and fallback.**

Literal `(v,b)` is true precisely when `a(v)=b`; clauses are disjunctions and formulas conjunctions. Total assignments add no semantic freedom beyond the mentioned indices. Every occurring `v` contributes `v+1` to the maximum, hence `v<numVars φ`, giving the evaluation-congruence theorem. Extending the carrier’s namespace for carrier operations is coherent; language/class results remain in `Complexity`.

For a formula, the exact encoding length is
\[
 |\operatorname{serialize}(\varphi)|
 =1+2\,\varphi.\mathrm{length}
   +\sum_{C\in\varphi}\sum_{(v,b)\in C}(v+3).
\]
At formula level, one starts a clause and zero ends the formula. Within a clause, one starts a literal and zero ends the clause; a literal consumes its entire one-run, zero, and one polarity bit. These grammar positions are distinct. In particular, a positive literal’s polarity bit cannot be reinterpreted as a new clause marker.

The suffix-carrying round-trip inductions stated in the sketch work. With fuel at least the serialized fragment length, removing one literal leaves enough fuel because it consumes at least three bits. Removing the formula-level clause marker leaves enough fuel for both its clause body and the remaining serialized formula, since the whole clause record consumes at least two bits. Both terminator cases succeed without fuel. Thus `parse`’s initial `|x|` fuel suffices; no unproved fuel adequacy is being silently assumed.

For successful parsing, each output literal’s `v+1` ones occurred in the consumed input prefix. Hence every such `v+1≤|x|`, and their maximum is at most `|x|`. On failure, `numVars []=0`. This proves the claimed plain bound at every input length.

| Whole input string | `parse` result | Decoded formula | SAT / SAT3 membership |
|---|---|---|---|
| `[]` | failure | `[]` | yes / yes |
| `[0]` | `some []` | `[]` | yes / yes |
| `[1,0]` | failure: no formula terminator | `[]` | yes / yes |
| `[1,0,0]` | `some [[]]` | one empty clause | no / no |
| `[1,0,0,1]` | failure: trailing garbage | `[]` | yes / yes |

Thus the prose’s `[true,false]` is the **prefixed empty-clause record**, not a whole formula encoding; `serializeClause []=[false]`, whereas `serialize [[]]=[true,false,false]`. This is a clarification of grammar level, not an ambiguity in the parser.

Unary labels are sufficient for the present results. They do not give polynomial expansion of arbitrary binary labels: a literal labelled `2^k` already disproves that unrestricted assertion. For input formulas here, however, `numVars≤|x|`; the splitter allocates only linearly many fresh variables; and the planned tableau uses polynomially bounded indices. Dense relabelling would also make comparison with arbitrary binary-index SAT encodings polynomial. The detailed encoding docstring’s restriction to campaign-produced formulas is essential.

**Argument D — SAT membership and clause splitting.**

For an input `x` of length `n`, `numVars(decode x)≤n`. A certificate of length `n+1` therefore contains every relevant assignment bit. Restricting a satisfying total assignment supplies such a certificate; conversely `u.getD · false` supplies a total assignment from one. The verifier’s total length is `2n+1`, so it rejects even lengths and recovers the unique split on odd lengths, including length one. A complete syntax pass must precede rejection on a failed clause or excessive width: `[1,0,0,1]` shows why rejecting an unsatisfiable parsed prefix before discovering trailing garbage would be wrong. The stated parsing-then-evaluation order supports this requirement. Unary walks, width checks, and final buffered verdicts have polynomial cost. Both `(1,1)` NP witnesses are valid.

For one splitting step write `p` for the truth value of the first two literals and `r` for that of the remaining disjunction. For a fresh variable `z`,
\[
 p\lor r\quad\iff\quad\exists z\in\{0,1\},\quad
 (p\lor z)\land(\neg z\lor r).
\]
Forward: set `z=r`; the first conjunct is the original disjunction and the second is `¬r∨r`. Backward: if `p=r=0`, the conjuncts force both `z=1` and `z=0`. Iterating establishes equisatisfiability in both directions. The sketch’s alternative `z=false` when the head is already true also works; it need not equal the tail’s value in that case.

A global increasing counter beginning at the original `numVars` makes every allocated variable absent from the original formula and distinct from earlier allocations. Clauses of width at most three, **including the empty clause**, pass unchanged. A clause of width `k>3` produces `k−2` clauses and `k−3` fresh variables; an unsplit clause produces one clause. This is the piecewise interpretation needed for the sketch’s chain-size bound.

For completeness, if `N=|x|`, the decoded formula has at most `N` clauses and `N` literal occurrences. Splitting introduces at most `N` variables, produces at most `2N` clauses and `3N` literal occurrences, and uses indices below `2N` whenever there are literals. Therefore
\[
 |\operatorname{serialize}(t(\operatorname{decode}x))|
 \le 6N^2+10N+1.
\]
This includes malformed input of length zero, whose image is `[false]`. It distinguishes linear combinatorial growth from polynomial unary-string growth. The named parser, buffer, fresh-variable counter, and serializer obligations suffice at sketch level.

The total reduction is valid on all strings:
\[
 \begin{aligned}
 f(x)\in SAT3
 &\iff\operatorname{WidthAtMost}(t(\operatorname{decode}x),3)
       \land\operatorname{Satisfiable}(t(\operatorname{decode}x))\\
 &\iff\operatorname{Satisfiable}(\operatorname{decode}x)
 \iff x\in SAT.
 \end{aligned}
\]
For the actual fallback, `decode x=[]` and `t([])=[]`, so malformed inputs indeed make both sides true. The same general equivalence works for any fixed fallback, but its two separate language membership branches need not agree before transformation (finding 5).

**Argument E — Claim 2.13 and polynomial time constructibility.**

For each `v : Fin ℓ → Bool` with `f v=false`, form the clause containing `(i.val, !(v i))` for all `i`. For every total assignment `a`,
\[
 C_v.\mathrm{eval}(a)=false
 \iff\forall i:\mathrm{Fin}\,\ell,\ a(i.\mathrm{val})=v(i).
\]
Consequently, the conjunction of these clauses is false exactly when `f` is false on the restricted assignment. There are at most `2^ℓ` clauses, each of width `ℓ`, and all indices are below `ℓ`. At `ℓ=0`, the two functions on the singleton empty-assignment space are represented by `[]` and `[[]]`. Both obey all three bounds. For positive `ℓ` and a nonempty clause list, the connective count is `number_of_clauses·ℓ−1≤ℓ·2^ℓ`; empty cases use the chosen Boolean constants. The theorem’s clause-count/width rendering is sound and records the zero-variable convention explicitly.

For `timeConstructible_poly`,
\[
 n\le n+1\le(n+1)^{c+1}\le C(n+1)^{c+1}\quad(C>0).
\]
An input scan with the inherited binary-counter template costs `O(n+1)` **amortized**, rather than literally `n` transitions including increments. Fixed-degree binary arithmetic and final bit emission cost a fixed power of `log(n+2)`, with constants depending on `C,c`. For every fixed power, this is bounded by a constant times `n+1` after absorbing finitely many small inputs. Thus all work fits `a(C(n+1)^(c+1)+1)` for a fixed positive `a`. At `n=0`, the result is the fixed positive integer `C`, covered by that constant. The theorem, its positive-coefficient condition, and its placement as a flagged new statement are sound. The private counter is correctly treated as a construction template rather than a public lemma.

**Argument F — the TAUTOLOGY deferral is mathematically justified.**

For a clause `C`,
\[
 (\forall a,\ C.\mathrm{eval}(a)=true)
 \iff\exists v,\ (v,false)\in C\land(v,true)\in C.
\]
The reverse implication is immediate from the pair of opposite literals. For the forward implication, contrapose: if there is no such pair, every mentioned variable has only one polarity. Set its assignment to the opposite value, and set unmentioned variables arbitrarily. This falsifies every literal and hence the clause. The argument also covers an empty clause.

Therefore
\[
 \forall a,\varphi.\mathrm{eval}(a)=true
 \iff\forall C\in\varphi,\exists v,\ (v,false),(v,true)\in C.
\]
Searching literal pairs is polynomial in the chosen input encoding. The empty formula passes vacuously; a formula containing an empty clause fails. Parsing with the actual tautological fallback remains polynomial.

Negating a CNF produces the DNF obtained by exchanging conjunction/disjunction and flipping every literal:
\[
 \forall a,\ (\neg\varphi)(a)=true
 \iff\neg\exists a,\varphi(a)=true.
\]
This is exactly the semantic operation needed by the [authors’ TAUTOLOGY reduction](https://theory.cs.princeton.edu/complexity/book.pdf#page=73). Waiting for the SAT-hardness prerequisite and the dual layer is coherent. A DNF-only version still needs to be identified as a fragment when attributing a general-formula language; arbitrary distributive expansion is not a polynomial-size bridge. No claim about the not-yet-written phase-4 theorem is audited here.

**Verification and attestation accounting.**

A faithful Python transcription of the actual recursive parsers checked all **262,143 bitstrings of lengths 0–17**. There were **3,137 successful parses**; each reserialized to the identical input and satisfied the variable bound. Another **2,500 generated formulas** round-tripped, including empty clauses and larger unary indices. For **350 small formulas**, exhaustive fresh-assignment search verified the splitting projection for **1,922 original assignments**. These finite checks support the boundary analysis; the general arguments above supply the mathematical reasoning. They are not executions of Lean definitions.

| Attestation | Independently established here | Remaining limitation |
|---|---|---|
| Attachment/new-surface inventory | 60 attachments; 48 campaign modules plus root; exactly 16 new definitions and 12 new theorem signatures; each new theorem body is `by sorry`; no new proved lemma. | No parent snapshot or authenticated Git diff, so historical freeze and the exact commit delta are not certified. |
| Admission and size accounting | 45 comment-stripped `sorry` tokens overall; new distribution `2/3/3/4`; new file lengths `147/209/23/153/200`. Each new admission has its sketch. | This is source counting, not compiler-warning or axiom-footprint reproduction. |
| Export/order changes | Formulas facade imports both children; ClassNP facade imports SAT and TMSAT; root imports both facades; all campaign-internal imports precede consumers in the 48-entry order list. | The full root’s unrelated imports are outside this audit. |
| Elaboration, axioms, lint | Sources agree with the stated definition/theorem inventory and use explicit imports/options; no new explicit axiom, unsafe definition, or partial parser appears. | No Lean executable/pinned dependency tree was available; fresh-olean sweep, exact axiom lists, and lint results remain maintainer execution claims. |

The critical next gate is the strengthened **statement** for TMSAT membership/completeness, together with the repaired exact-value hardness sketch. Naming an impossible uniform bound as future fill work does not meet that gate.

**Notation glossary.** `0,1` denote false/true; `[]` is the empty list; `++` is concatenation; `1^k` is a run of `k` true bits; `|·|` is list/string length. `φ,C,(v,b),a,ℓ,f` are respectively a formula, clause, literal, assignment, variable bound, and Boolean function when discussing CNFs; `t` is the clause-splitting transform there and a machine deadline in TMSAT formulas. In Argument A, `D_i` is a clocked candidate language, `M_i,a_i,d_i` its machine/clock parameters, `w_i` its diagonal word, `A` the diagonal language, `M_b` the one-step constant-output machine, `c₀,c_A` the base/constructed schemes, and `g` the reduction. In its repaired budget, `r,H,L,N,h,q` denote code length, canonizer time, serialized length, number of states, header-bit length, and initial-state index; `A,d,e` there are polynomial-bound constants/degrees, and `C_α` is the universal coefficient. In Argument B, `L,V` are the NP language/verifier, `C₀,c₀,Q` its exact-length parameters/function, `n,s` the original/paired input lengths, `B,e` wrapper-bound parameters, `K` the normalization multiplier, `r,D,T'` the displayed majorizing degree/coefficient/deadline, and `α₀,f` the fixed wrapper code/reduction. In Argument D, `p,r,z` are clause truth values/the fresh bit and `N` is source-string length. Other class names and identifiers retain their supplied Lean meanings.
