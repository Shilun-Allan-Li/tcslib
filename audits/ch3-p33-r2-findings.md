**P3.3 round-2 statement-gate audit: PASS — 0 blockers, 0 majors, 2 minors, 2 notes.**

Both round-1 majors close. Fixed-code repetition removes the quantifier error, and the repaired ladder admits a concrete capped locator with total time O(n), even without monotonicity of either bound. The middle and top comparisons give the required contradiction after reserving a fixed allowance for setup and clock administration. The two remaining minors concern the exact ladder definition and the wording of that clock ledger; their corrections below require no theorem or hypothesis change.

This is a mathematical audit of the statement-phase construction, not a completed Lean proof or an independently replayed build. The seven admissions remain admissions. The machine constructions and invariants identified below must still be implemented during fill.

Input: `ch3-p33-r2-bundle.md`. Independently verified SHA-256:

`fedeadf847a95c6ba78f7a0e377a76a922df3ca7f5ad97f3d3b7eef1620be99a`

Packet revision: `9a92fa1aeb377d568972e42229979cf81562ba41`. Scope: the supplied two-file repair diff, with the attached round-1 report and unchanged interfaces as context. This was a single-agent audit. File line references below refer to the extracted attachment, not the concatenated bundle.

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | minor | Round-2 pack, brief 1(ii); `NTimeHierarchy.lean` · `ntime_hierarchy`, lines 230–232 | The pack and rebuilt sketch specify the same explicit ladder. | The pack has `(f(ℓ_i+1)+ℓ_i+1)²`; the source has `(f(a)+a+1)²`, which becomes `(f(ℓ_i+1)+ℓ_i+2)²`. Also, the replacement deletes the old initial value without supplying another. Both positive-offset variants support the argument, but they are different sequences. | Use the source formula consistently, state a seed such as `ℓ₀=2`, and reject the finitely many lengths at or below the seed. The proof below uses these choices. |
| 2 | minor | `NTimeHierarchy.lean` · `ntime_hierarchy`, lines 238–258 and 266 | The displayed accepting-simulation bound is the whole host cost, and comparison with the whole cap alone proves completion. | Computing `g(n)` precedes availability of its countdown. Budget preparation and a partial binary countdown also require accounting: the first decrement from `2^r` can cost Ω(r), even for a short accepting simulation. The universal's total-budget contract alone does not assert a bound for every accepting prefix under a larger budget. Finally, earlier setup consumes part of a shared cap. These are bounded costs, but the displayed chain does not explicitly charge them. | State the prefix bound for the concrete interpreter core, charge budget/clock overhead and setup to a fixed allowance, and choose `K` with a remaining simulation allowance. The ledger below supplies this without depending on the scheduled code. Describe the initial `g`-witness run as separately bounded, rather than already cut by a not-yet-constructed clock. |
| 3 | note | `NTimeHierarchy.lean` · `ntime_hierarchy`, lines 262–265 | The stage-bottom square comparison uses the domination hypothesis's `f(n)` addend. | The comparison follows directly from the square and fixed constants as the bottom length grows. It needs no comparison with `g(a)`. The `f(n)` addend remains sufficient for the inclusion argument. | Attribute the bottom comparison to the square; retain the extra-addend qualification for inclusion. No statement change. |
| 4 | note | Round-2 pack · repository-side attestations | Packet consistency establishes fresh elaboration and repository history. | The reconstructed before/after files match both recorded Git blob prefixes, and their noncomment text is identical. The supplied sweep has seven admission warnings and no errors. These checks do not independently establish the remote commit's contents, build freshness, or successful Lean elaboration. | Retain the distinction between packet verification and the maintainer's build attestation. |

The round-1 dispositions check as follows.

| Round-1 finding | Round-2 disposition |
|---|---|
| 1 — per-code constants versus padding | **Closed.** One literal code recurs at unbounded stage indices. All constants and all eventual thresholds for that code are fixed before a late stage is selected. |
| 2 — nonexecutable/unpaid locator | **Closed.** The recurrence depends only on a fixed constructibility witness; the concrete cap and amortized calculation below establish an executable O(n) locator. No universal-coefficient selection or earlier `g` value is computed. |
| 3 — record count | **Closed at sketch level.** `2·3³=54`; the minimum action length is 13, hence the table guard is `702(numStates+1)` bits. There is not yet an implemented ND parser to inspect. |
| 4 — polynomial canonizer claim | **Closed.** The revised sketch explicitly uses arbitrary-time computability, matching the received `MathlibBridge` route. A fixed code's finite canonization time is absorbed only into that code's coefficient. |
| 5 — pointwise decrement claim | **Closed.** The revised text says amortized and names significant-end maintenance and a zero test without full-width rescans. The full-countdown sum is verified below. |
| 6 — zero work tapes | **Closed.** `O_N((k+1)(t+1))` correctly includes display generation and the input sweep at `k=0`. |
| 7 — timeout polarity | **Closed.** Cut branches reject; accepting displays are sound; backward truncation uses the original total decider. Infinite guessing branches are no longer claimed to finish. |
| 8 — `g(0)=0` pack assertion | **Closed by the acknowledged erratum.** `timeConstructible_id` refutes the assertion. The `g+1` conclusion and explicit positivity hypothesis remain correct. |
| 9 — “every A” | **Closed.** The corrected claim is for positive A; A=0 is explicitly excluded. |
| 10 — strength qualifications | **Retained.** Equivalence with the shifted gap is asserted for monotone `f`; the nonmonotone restriction and the weaker square showcase remain disclosed. |
| 11 — attestation limits | **Retained.** See finding 4 above. |

1. The fixed-code schedule has the required quantifier order.

Fix the scheme and a standard computable pairing/unranking once. For every fixed code index `j`, injectivity of `r ↦ pair(j,r)` gives an infinite, hence unbounded, set of stages. With the seed in finding 1, the source recurrence satisfies

\[
a_i=\ell_i+1,\qquad
T_i^*=(f(a_i)+a_i+1)^2,\qquad
\ell_{i+1}=2^{(T_i^*)^2}>2\ell_i.
\]

Thus the bottom lengths of that subsequence are also unbounded. Under the contradiction assumption, choose the alleged decider, its normalization, one code for that normalization, and the corresponding interpreter and BF coefficients. Only then choose the thresholds in the domination hypothesis and a stage past all those thresholds. No coefficient changes when the repetition coordinate changes. Padding and padding-time bounds are unused.

2. Here is an explicit capped locator and its complete asymptotic ledger.

Choose the witness to `TimeConstructible f` once. After incorporating a fixed simulation overhead, let its positive coefficient be `c_f`; on a unary input of length `a`, it halts with the canonical binary value `f(a)` within `c_f(f(a)+1)` witness steps. At input length `n>2`, maintain the invariant `ℓ_i<n`, beginning at `ℓ₀=2`.

At each candidate stage, prepare the witness input of length `a=ℓ_i+1≤n`. Run the witness for at most

\[
c_f(n+1)
\]

steps, testing for halting at the deadline. An unfinished run proves

\[
\begin{aligned}
f(a)\le n
&\Longrightarrow c_f(f(a)+1)\le c_f(n+1)\\
&\Longrightarrow\text{the witness has halted},
\end{aligned}
\]

so timeout implies `f(a)>n`, and consequently

\[
\ell_{i+1}=2^{(f(a)+a+1)^4}>n.
\]

The current stage is therefore an interior stage. This deduction uses the witness's **upper** time bound by contraposition; it makes no assumption that a constructibility witness spends its entire allowance.

If the run finishes, compare its canonical binary output with `n` before performing large arithmetic. If `f(a)>n`, the same interior-stage conclusion holds. Otherwise all operands in `(f(a)+a+1)^4` have O(log(n+2)) bits. Compute this exponent and compare it with `⌊log₂n⌋`. An exponent greater than that floor means the next ladder value exceeds `n`; an exponent less than it means the next value is smaller. At equality, the next value equals `n` exactly when `n` is a power of two; otherwise it is smaller. Return the current stage in the greater/equal cases, preserving `T_i^*` in the equal case. In the smaller case, write the next ladder value in binary and advance.

No candidate ladder value greater than `n` is expanded in unary or binary. A completed witness can have emitted O(n) bits before its result is found too large; scan/cleanup of those bits is charged to that final witness attempt. Preparing a unary witness input of length at most `n` is permitted and is counted below; it does not materialize a future ladder value exceeding `n`.

Let the loop stop at stage `s`. For each fully passed stage `h<s`,

\[
\begin{aligned}
a_h+f(a_h)+1
&\le 2^{(f(a_h)+a_h+1)^4}
=\ell_{h+1},\\
\sum_{h<s}\ell_{h+1}
&<2\ell_s<2n.
\end{aligned}
\]

Therefore preparation of all earlier witness inputs, their actual completed runs, and cleanup total O(n). The last input costs O(n) to prepare and its witness run is capped at `c_f(n+1)`, also O(n). Every attempted call has only O(log(n+2)) clock-initialization overhead in addition to its executed steps. There are O(log(n+2)) candidate stages, because the ladder more than doubles.

The remaining fixed-degree binary arithmetic costs O(log²(n+2)) per stage, hence O(log³(n+2)) overall. Writing a passed ladder value in binary costs O(log(n+2)) per stage. Standard pairing inversion and binary-string unranking at the final stage also fit in this allowance: the stage index is O(log(n+2)), and a fixed polynomial-in-that-index implementation suffices. Consequently

\[
\begin{aligned}
\text{locator time}
&=O\bigl(n+1+\log^3(n+2)\bigr)\\
&=O(n+1)\\
&\le O(g(n)+1).
\end{aligned}
\]

The last inequality uses the constructibility floor `n≤g(n)`. The constants depend on the fixed witness and locator architecture, never on the scheduled code. Strict increase of the ladder proves loop termination, and every individual witness attempt is bounded. In particular, the previous circular selection of code-dependent BF coefficients is gone.

For the round-1 oscillating example,

\[
f(n)=n+1,\qquad
g(n)=\begin{cases}2^n&n\text{ odd},\\(n+1)^2&n\text{ even},\end{cases}
\]

the locator has the same O(n) bound at both parities. It never calls the `g` witness at a stage bottom. More generally, an arbitrarily large interior spike in `f(a)` is handled by the timeout-or-large-output case above. There is no inference that `f(a)≤f(n)` or `g(a)≤g(n)`.

3. The clock has a uniform total bound and sufficient remaining allowance.

For a full binary countdown from `t` to zero,

\[
\sum_{j=1}^{t}\nu_2(j)
=\sum_{r\ge1}\left\lfloor\frac{t}{2^r}\right\rfloor
\le t.
\]

With a marked significant end, an origin, and a local empty-counter test, decrement-and-return costs O(1+ν₂(j)); initialization costs O(log(t+2)). This verifies the corrected universal-clock explanation, including `t=0` and the long first borrow when `t` is a power of two.

For a prefix of `s` decrements from a larger counter `B≥1`, the appropriate bound is instead

\[
\begin{aligned}
\sum_{j=B-s+1}^{B}\nu_2(j)
&=\sum_{r=1}^{\lfloor\log_2B\rfloor}
\left(\left\lfloor\frac B{2^r}\right\rfloor-
\left\lfloor\frac{B-s}{2^r}\right\rfloor\right)\\
&\le s+\lfloor\log_2B\rfloor,
\qquad 0\le s\le B.
\end{aligned}
\]

This is the additive clock term suppressed by the wording in finding 2. The concrete interpreter core has fixed-code startup and table-scan costs bounded by `C_α(s+1)` after enlarging `C_α` if necessary; its budget administration adds only a fixed multiple of `s+log(B+2)`. Absorb the linear-in-`s` part into `C_α`. The remaining logarithmic term, preparation of the virtual unary input, the locator, length scanning, unranking, and fixed clock initialization fit in a fixed allowance `P(g(n)+1)`. Here `P` is independent of `α`; canonization of an arbitrary code stays inside the interrupted interpreter computation, not inside the asserted uniform setup allowance.

Choose `K≥P+2`. Interpret the fused outer clock as counting transitions of the controlled computation, with its own borrow/return operations accounted for by the preceding amortized bound. One cannot literally decrement a counter once for every physical transition including those of that same decrement. This standard implementation still has a uniform physical-time coefficient. Compute `g(n)` first using its constructibility witness; that initial run is independently O(g(n)+1). Thereafter every possibly expensive code-dependent operation is interrupted by the outer clock. Thus every branch, including branches for badly behaved codes, halts in one fixed multiple of `g(n)+1`.

On the fixed code's successful late stages, the middle comparison below leaves the controlled computation within

\[
P(g(n)+1)+g(n)<K(g(n)+1).
\]

The same inequality pays for the top computation once its BF cost is at most `n≤g(n)`. This proves sufficient remaining allowance, rather than merely comparing one subroutine to the original whole cap. The argument uses the specified concrete interpreter construction; the universal's existential total-time contract alone would not give this prefix invariant.

4. The middle comparison works with constants fixed before stage selection.

Enlarge the interpreter coefficient to at least one, and use the pack's fixed assembled constant

\[
A^*=C_\alpha(C_1c_0+C_1+1)+1.
\]

For every natural `u`,

\[
\begin{aligned}
C_\alpha\bigl(C_1(c_0u+1)+1\bigr)
&=C_\alpha C_1c_0u+C_\alpha(C_1+1)\\
&\le A^*(u+1).
\end{aligned}
\]

Instantiate domination at this fixed `A*`. At every sufficiently large middle length `n`,

\[
\begin{aligned}
C_1(c_0f(n+1)+1)
&\le C_\alpha\bigl(C_1(c_0f(n+1)+1)+1\bigr)\\
&\le A^*(f(n+1)+1)\\
&\le A^*(f(n+1)+f(n)+n+1)\\
&\le g(n).
\end{aligned}
\]

The first-to-last comparison makes the **source** nominal budget sufficient. The second-to-last comparison, combined with the reserve in paragraph 3, makes the **host** budget sufficient. They are distinct requirements.

If `1^(n+1)` belongs to `L(D)`, the alleged decider has an accepting branch within `c₀f(n+1)`; normalization supplies a witness within `C₁(c₀f(n+1)+1)`; the middle interpreter completes that accepting simulation. Conversely, any accepting middle computation must have completed a genuine accepting computation of the coded machine. The backward normal-form clause gives eventual acceptance by the original decider, and its all-branch bound truncates that acceptance to `c₀f(n+1)`. Therefore

\[
1^n\in L(D)\quad\Longleftrightarrow\quad1^{n+1}\in L(D)
\qquad(a_i\le n<\ell_{i+1}).
\]

No claim is made that every normalized branch completes. In particular, an infinite display-guessing branch is rejected by the clock. Any simulated output must be buffered until source halting is confirmed, so an emitted true followed by a loop is not converted into acceptance by timeout.

5. The top budget and exponential ledger also work on that same subsequence.

Write `a=a_i`. Once `a≥C₁(c₀+1)`,

\[
\begin{aligned}
C_1(c_0f(a)+1)
&\le C_1(c_0+1)(f(a)+1)\\
&\le(f(a)+a+1)(f(a)+1)\\
&\le(f(a)+a+1)^2=T_i^*.
\end{aligned}
\]

Thus bounded coded acceptance at `T_i*` is equivalent to `1^a∈L(D)`. This is the bottom-length transfer; using only `f(a+1)` here would be wrong. Its proof does not require the extra `f(n)` addend, as noted in finding 3.

Enlarge the fixed BF coefficient to `C_BF≥1`. For `T_i*≥max(2,2C_BF)`,

\[
\begin{aligned}
C_{BF}\,2^{C_{BF}(T_i^*+1)}
&\le2^{C_{BF}(T_i^*+2)}\\
&\le2^{(T_i^*)^2}\\
&=\ell_{i+1}\\
&\le g(\ell_{i+1}).
\end{aligned}
\]

Indeed `C_BF≤2^{C_BF}`, and

\[
C_{BF}(T_i^*+2)
\le\frac{T_i^*}{2}(T_i^*+2)
\le(T_i^*)^2.
\]

At the actual top length `n=ℓ_{i+1}`, the locator cannot time out on this bottom witness: `f(a)<n`, so the capped run completes. It retains the exact `T_i*`. The BF computation, including its fixed-code startup, completes within the remaining allowance established above, and the top gives

\[
1^{\ell_{i+1}}\in L(D)
\quad\Longleftrightarrow\quad
1^{a_i}\notin L(D).
\]

Choose a repeated-code stage whose bottom exceeds the fixed middle threshold and bottom-transfer threshold and whose `T_i*` exceeds the fixed BF threshold. Finite induction through the middle equivalences gives

\[
1^{a_i}\in L(D)
\quad\Longleftrightarrow\quad
1^{\ell_{i+1}}\in L(D),
\]

contradicting the top equivalence. All thresholds precede the stage choice. This is the required strictness argument.

For completeness, inclusion uses the hypothesis at `A=1`. If its threshold is `N`, set `F=1+Σ_{j<N}f(j)`. For `n<N`, `f(n)≤F≤F(g(n)+1)`; for `n≥N`, `f(n)≤g(n)≤F(g(n)+1)`. The original decider works with its coefficient multiplied by `F`, using padding/truncation of choice words. This proves inclusion with no monotonicity assumption and covers the finite exceptional lengths.

6. The remaining minor arithmetic and boundary checks agree with their repairs.

The serialization has two choices, three input reads, and three independent reads on each work tape:

\[
2\cdot3\cdot3\cdot3=54.
\]

An action contains six two-bit fields and a successor field of minimum length one:

\[
6\cdot2+1=13,\qquad54\cdot13=702.
\]

Thus the scaled minimum table guard is `702(numStates+1)`; an initial-state word is additional. The one-state silent-halting example has total serialization length `2+1+702=705`, matching round 1. The arbitrary-time canonizer route needs only total computability and a finite maximum runtime over all strings of each fixed length; no polynomial claim is imported.

For the corrected showcase wording, when `A≥1`,

\[
A(2n+2)^2=4A(n+1)^2>(n+1)^2;
\]

when `A=0`, the inequality in question holds. The nondeterministic showcase's own domination calculation remains

\[
\begin{aligned}
A((n+2)+(n+1)+n+1)&=A(3n+4),\\
(n+1)^2-A(3n+4)
&=n(n-3A)+2n+1-4A\\
&\ge6n+1-4A\\
&\ge14A+25>0\qquad(n\ge3A+4).
\end{aligned}
\]

Positivity allows `c(g(n)+1)≤2c·g(n)`. Without positivity, `TimeConstructible id` has value zero at zero, so the acknowledged erratum is necessary.

| Adversarial replay | Result |
|---|---|
| Same decoded machine with arbitrarily expensive padded codes | Irrelevant to late-stage selection: the chosen literal code is held fixed. Other codes are interrupted uniformly. |
| Oscillating `g`, exponentially larger at an earlier length | Locator time depends on the current input length and fixed `f` witness, not that earlier `g` value. |
| Extremely slow allowed `f` witness at an interior bottom | The `c_f(n+1)` cap either completes it or certifies the next stage boundary exceeds `n`. |
| Huge `f(a)` returned quickly in a long binary word | Compare the output to `n` before multiplication; charge its scan to the capped attempt. No oversized ladder value is expanded. |
| Huge `g(n)` with short accepting source run; first countdown tick has a long borrow | The prefix ledger includes an additive logarithmic term; the fixed reserve pays it. This is why finding 2's wording needs correction. |
| Infinite guessing branch, or true output followed by an infinite loop | Timeout rejects; acceptance requires verified source halting. |
| `n=ℓ_{i+1}-1`, `n=ℓ_{i+1}`, and `n=ℓ_{i+1}+1` | Respectively middle, top, and the next stage. At equality the locator must return before advancing. |
| `n=0`, short inputs, zero work tapes, and zero simulated budget | Short inputs use the fixed default; normalization retains its `k+1` term; initialized zero-step acceptance remains impossible. No changed contract assumes positivity implicitly. |

I checked the source comparison against Arora–Barak, *Computational Complexity* (2009), §3.2, printed pp. 69–71: the construction retains the middle-length agreement and the deterministic flip at the stage top used in equations (3.3)–(3.4) and Figure 3.1. The unrestricted-function qualification and square-showcase qualification from round 1 remain applicable. Source: [reproduced 2009 book](https://theswissbay.ch/pdf/Gentoomen%20Library/Theory%20Of%20Computation/Sanjeev_Arora,_Boaz_Barak-Computational_complexity__a_modern_approach-Cambridge_University_Press(2009).pdf).

The declaration-freeze check was stronger than merely scanning the changed lines: I reversed every supplied diff hunk against the attached new files, checked all context, verified the reconstructed Git blob prefixes (`e97fabea → 3484e461` and `30e5c303 → 1f936e0b`), and removed nested Lean comments from both versions. The remaining text was byte-identical in each file. The attachments contain 190 and 318 lines, one and six `sorry`s, and the unchanged seven definitions plus the skeleton-time round-trip proof. The sweep records seven admission warnings and no `error:` lines; the relevant lint summaries agree with the pack. I did not run Lean or independently inspect the repository.

Glossary of additional notation: `a_i=ℓ_i+1` is a stage bottom; `c_f` is a fixed coefficient for the implemented `f` witness; `P` is a uniform allowance coefficient for setup and the additive clock costs; `B` is a countdown's initial value; `s` denotes the final locator stage or, in the explicitly separate countdown calculation, the number of decrements; `h` is a passed-stage index; `u` is a natural number used in the middle inequality; `ν₂(j)` counts trailing binary zeros of positive `j`; `F=1+Σ_{j<N}f(j)` is the finite-length absorption coefficient. `O_N` permits dependence on the fixed normalized source machine. The code, machine, budget, and hierarchy symbols otherwise follow the bundle; `1^n` is the unary string of length `n`.
