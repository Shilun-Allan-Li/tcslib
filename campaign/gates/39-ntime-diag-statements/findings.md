SHA-256 verified exactly:

`0eb7578e06718ee938a0496d463f3975f1fb6c44dd3b6ca8589f2e338b3d3c9a`

**The chain interface passes, but the advertised diagonalizer construction misquotes its interpreter dependency.** Both existential statements are mathematically achievable; the supplied route needs the repair below before this gate closes. This is a statement audit, not an independent Lean replay.

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | **major** | `Diagonalization/NTimeDiagonalizer.lean:288–296` · `exists_diagonalizer`; `TuringMachine/NDCodeSimulator.lean:128–145` · `exists_ndInterpreterCore` | The published interpreter prefix clause establishes the proposed middle completeness condition. | The sketch claims time `C_R·(t′+1)+2·\|bits(g n)\|`. The actual clause is `C_R·(t′+\|x\|+\|bits(g n)\|+1)`, with `\|x\|=n+1`. A code-dependent multiple of `n` cannot be absorbed into one uniform reserve when `g(n)=n`. Moreover, the specified eager window copy takes at least `n` steps in this example, contradicting the claimed shorter bound for fixed `t′=1` and large `n`. | Explicitly adopt the smaller-budget guessing alternative already identified in `C1-design.md` §3.6, including the query-budget rewrite and its ledger; see below. Alternatively, publish and gate a stronger interpreter contract separating uniform setup costs from per-code simulation costs. Update the sketch and design records together. |
| 2 | **minor** | `NTimeDiagonalizer.lean:285–287` · clock ledger | Cutting the simulator at `K·(g n+1)` proves that the complete machine halts within that same quantity. | `exists_stepClockTMVia` charges up to `5d+2\|bits d\|+2` physical steps for a body allowance `d`, before adding setup. The same `K` cannot simply denote both allowances. | Distinguish the body allowance from the final physical-time coefficient. Charge setup, clock administration and final dispatch explicitly when choosing `K`. No theorem change is needed. |
| 3 | **minor** | `NTimeDiagonalizer.lean` · `stage`, `query` | The published equations cover every input, as required by `policy.md` §1. | `stage_spec` and `stage_eq` cover the intended brackets, but not lengths `0,1,2`. `query_eq` covers only unary inputs of length at least three. Mechanical check 8 finds matching names but does not establish exhaustive coverage. | Add `stage f n = 0` for `n≤2`, and `query f g x = []` outside its unary/length guard; alternatively publish unconditional equations. |
| 4 | **note** | Pack · records and attestations | All requested evidence comparisons are independently reproducible from this bundle. | Both pinned Lean blobs match, but the PR body is absent. The seven-file copy-screen population includes `TimeHierarchy/Diagonal.lean`, also absent. The supplied replay logs are execution attestations, not an independently reproduced build. | Include those two missing records in a subsequent packet, or qualify the verification claims. No soundness change is required. |

**1–2. Definitions and stage query.** Reading the definitions directly gives:

| Definition | Mathematical restatement |
|---|---|
| `budget f ℓ` | The square \((f(\ell+1)+\ell+2)^2\). |
| `ladder f` | Starts at \(2\); each successor is \(2^{(\operatorname{budget} f\,\ell_i)^2}\). Exponentiation is right-associated, as required. |
| `stage f n` | The least \(i\) satisfying \(n\le\ell_{i+1}\). For \(n\ge3\), precisely the unique bracket \(\ell_i<n\le\ell_{i+1}\). For \(n\le2\), its value is zero. |
| `stageCode i` | Take the first coordinate \(j\) of `Nat.unpair i`; remove the final, most-significant `true` bit from the little-endian expansion of \(j+1\). |
| `query f g x` | Returns `[]` unless \(x=1^n\), \(n\ge3\). At a top it returns `true :: ⟨⟨bits T*, α⟩, 1^a⟩`; otherwise `false :: ⟨⟨bits(g n), α⟩, 1^(n+1)⟩`. |

These agree with the pinned round-2 recurrence, including the seed and both `+1` offsets. Dispatch must consume the flag and pass the remaining word to the appropriate simulator.

The construction preserves AB’s middle propagation and top negation argument; the explicit ladder and recurring-code schedule are the campaign’s refinements. ([Arora–Barak, web draft, nondeterministic time hierarchy proof and Figure 3.1](https://theory.cs.princeton.edu/complexity/book.pdf))

**3. `exists_queryTM`.** The statement is mathematically sound. At a candidate bottom \(a\le n\), failure of the constructibility witness to halt within \(c_f(n+1)\) implies \(f(a)>n\), hence the next ladder value exceeds \(n\); a completed output is compared with \(n\) before multiplication. For every passed stage,
\[
a_h+f(a_h)+1\le\ell_{h+1},
\qquad
\sum_{h<s}\ell_{h+1}<2\ell_s<2n,
\]
so completed calls and preparation cost \(O(n)\), the final capped call costs \(O(n)\), and arithmetic costs \(O(\log^3(n+2))\). Materialization adds \(O(n+|\operatorname{bits}(g(n))|+1)\) in the middle and \(O(a+|\operatorname{bits}(T^*)|+1)\) at a top, both within \(O(g(n)+1)\); no monotonicity assumption is used.

**4. `exists_diagonalizer`: construction, nonvacuity and sufficiency.**

The published interpreter interface does **not** imply the sketch’s bound. This is more than loose notation: a conforming interpreter can spend a code-dependent number of passes copying its bounded input window. For \(g(n)=n\), a coded machine accepting in one step satisfies the diagonalizer’s completeness premise once \(n\ge2C\), while such copying can exceed any fixed uniform simulator allowance. Increasing the per-code \(C\) merely postpones the problem; that same code recurs at unbounded stages.

The design’s existing alternative repairs this without changing the diagonalizer statement:

1. In the middle, guess a nominal budget \(b\le g(n)\), as well as the choice stream. Replace the query’s budget field by `bits b`.
2. Run the interpreter under a uniform body cap. Its **total-time** clause gives \(C_R(b+1)\), without an input-length term.
3. For completeness, choose \(b=t'\). With \(C\ge\max(1,C_R)\),
   \[
   C(t'+1)\le g(n)
   \Longrightarrow C_R(b+1)\le g(n).
   \]
4. For soundness, completed acceptance implies coded acceptance within \(b\le g(n)\).
5. Budget selection, rewriting and guessing cost \(O(g(n)+1)\). The step clock supplies uniform halting after its physical overhead is charged. At tops, use BF and enlarge \(C\) to cover its coefficient.

Thus the existential contract is achievable by a concrete correction already contemplated in the design. It is not established by the currently advertised prefix-clause argument.

The contract is **not vacuous**. For every fixed \(C\ge1\), whenever \(T^*\ge\max(2,2C)\),
\[
C\,2^{C(T^*+1)}
\le2^{C(T^*+2)}
\le2^{(T^*)^2}
=\ell_{i+1}.
\]
Every fixed code has arbitrarily late stages, so choosing a large finite \(C\) cannot disable all its top clauses. A code for an always-rejecting machine therefore forces \(D\) to accept late tops, excluding an always-rejecting \(D\); middle soundness excludes an always-accepting \(D\). Allowing \(C=0\) strengthens the obligations rather than making them vacuous.

The contract is also **sufficient for the chain**. Let \(L\) be its bounded acceptance language. Assuming \(L\in\mathrm{NTIME}(f)\), fix a decider with coefficient \(c_0\), its normal form with coefficient \(C_1\), its literal code \(\alpha\), and the diagonalizer’s coefficient \(C\), enlarged to at least one.

Set, as in the earlier gate,
\[
A^*=C(C_1c_0+C_1+1)+1.
\]
Eventually,
\[
\begin{aligned}
C\bigl(C_1(c_0f(n+1)+1)+1\bigr)
&\le A^*(f(n+1)+1)\\
&\le A^*(f(n+1)+f(n)+n+1)\\
&\le g(n).
\end{aligned}
\]
Forward normal-form transfer and middle completeness therefore give
\(1^{n+1}\in L\Rightarrow1^n\in L\).
Middle soundness, backward normal-form transfer, and truncation using the original decider’s all-branch bound give the converse.

At the bottom \(a=\ell_i+1\), once \(a\ge C_1(c_0+1)\),
\[
C_1(c_0f(a)+1)
\le C_1(c_0+1)(f(a)+1)
\le(f(a)+a+1)^2=T^*.
\]
Consequently bounded coded acceptance at \(T^*\) is equivalent to \(1^a\in L\). Choose a repeated-code stage after **all** these thresholds and the top threshold. Finite induction through its middle rungs gives
\[
1^a\in L\iff1^{\ell_{i+1}}\in L,
\]
whereas the top clause gives the negation of that equivalence. `acceptLang_mem_NTIME` supplies the larger-class membership; inclusion uses eventual domination of \(f(n)\) and finite-exception absorption.

**5. Disclosed deviations.** Both are acceptable. One query machine preserves the required semantic output and total time bound. `Nat.unpair` supplies exact inverse laws and an efficient arithmetic implementation; since the stage index is \(O(\log n)\), its computation fits the locator allowance. ([Mathlib, `Nat.Pairing`](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Nat/Pairing.html))

**6. Proved lemmas and adversarial cases.** The mathematical statements check out. For `stage_eq`, a smaller stage would yield
\[
n\le\ell_{\operatorname{stage}(n)+1}\le\ell_i<n,
\]
a contradiction. For `stageCode_frequently`, choose \(m\) with
\[
\operatorname{bits}(m)=\alpha\mathbin{+\!\!+}[\mathrm{true}],
\qquad
i=\operatorname{pair}(m-1,N)\ge N;
\]
unpairing and deleting the final bit recover \(\alpha\), including the empty word.

The five supplied axiom prints contain only standard axioms. The remaining elementary lemmas introduce no apparent additional dependency, but I did not independently kernel-check them.

| Adversarial instance | Outcome |
|---|---|
| \(f(n)=g(n)=n\), coded acceptance in one step | Exposes finding 1; the smaller-budget repair handles it. |
| An arbitrarily large spike in \(f(a)\) | Timeout or large-output comparison stops the locator without expanding the next ladder value. |
| Empty or short inputs; a non-unary word | `query` returns `[]`; the missing public equations are finding 3. |
| A branch emits `[true]` and then loops | It is not accepting: acceptance requires halting. Timeout must reject and suppress provisional output. |
| Always-rejecting code; arbitrarily large per-code \(C\) | Late top clauses remain active, excluding trivial rejection. |

**7. Records.** Both extracted Lean files match the replay’s full Git blob pins; the new module also matches the patch exactly. I verified 20 public declarations, zero private declarations and two admissions. Scoped lint passes. On the six available screen files, the screened count changes \(26\to34\), with the same six pairs and 1,814 reproduced characters; the advertised \(40\to48\) totals require the missing seventh file. No new duplication was identified in the supplied material. The design’s old prefix description conflicts with the current interpreter contract, as recorded in finding 1; PR-body agreement remains unverified because that body was not included.

Notation: \(b\) is the additionally guessed nominal simulation budget; \(L\) is \(D\)’s bounded acceptance language. The remaining symbols follow the packet: \(\ell_i,a,T^*,\alpha,C_R,C_1,c_0,C,K,P,A^*\).

**FAIL — 0 blockers, 1 major, 2 minors, 1 note.**
