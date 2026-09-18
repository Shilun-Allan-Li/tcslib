**Chapter 2, phase 2, round 1 — independent adversarial statement audit**

Audited material: the supplied bundle labelled commit `e1e68ebd` on `complexity/arora-barak-ch1`. Intended destination: `audits/ch2-phase2-findings.md`.

**Findings: 0 blockers, 0 majors, 2 minors, 2 notes.** No wrong definition or false theorem statement was found in the new surface. The narrow zero-blocker/zero-major criterion is met at statement/sketch level. The two prose corrections below should be recorded before handoff. This does not certify filled Lean proofs, repository history, or a fresh build.

This is a fresh audit of the three new modules, including their six proved lemmas. The closed Chapter-1 and phase-1 results were used as trusted interfaces, not reopened. The human-reserved design question, universal NDTM, and later phases remain outside this disposition. I extracted comment-stripped declarations before reading the new modules' docstrings. The mathematical derivations below check the constructions and their obligations; they are not kernel-checked implementations of the proposed compilers.

The attachment has 51 sections: 43 campaign modules, the root import file, four phase-1 audit records, two plans, and the policy. Bundle SHA-256: `4c6d6ee600788baa99615aa5feacf8928c8f7b37baa4df923715f4fc4395d62d`.

**Textbook comparison.** The authors' [January 2007 draft, §2.1.2, Definition 2.5 and Theorem 2.6](https://theory.cs.princeton.edu/complexity/book.pdf#page=58) confirms binary choice, existential acceptance, a time bound on every input and every branch, and the two certificate compilations. Its [§2.6.2](https://theory.cs.princeton.edu/complexity/book.pdf#page=73) gives the exponential union and padding implication. The 2009 pages are not attached; published item/page numbers and Exercise 2.27's attribution are the pack's references, not independently authenticated quotations. In the draft, the padding implication is Theorem 2.25.

Paths below abbreviate `TCSlib/Complexity/`; line numbers start at the first line of each extracted source file.

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | minor | `ClassNP/Nondeterminism.lean:212` · `EXP_eq_NEXP_of_P_eq_NP`, verifier sketch | The binary representation of the required padding length is logarithmic in the supplied padded input's length. | This uses validity before checking it. With coefficient 1, degree 2, and malformed input `x' = pairEncode x []`, where the length of `x` is 31, the supplied `x'` has length 64 but the required padding length has a 1025-bit binary representation. The analogous family has quadratic bit length and logarithmic input-length logarithm. The preceding explicit polynomial bit bound is sufficient, so the algorithm and theorem survive. | Before validation, use the uniform bound `bits(E(n)) ≤ (n+1)^c + bits(C) + 1`, hence polynomial in the actual input length. Handle `C = 0` directly. Only after the padding-length check infer a logarithmic bound. |
| 2 | minor | `ClassNP/NTIME.lean:43` and `TuringMachine/Nondeterministic.lean:49` · exact-length convention prose | Exact-length and bounded-length quantifiers are interchangeable without qualification. | Existential accepting words can be shortened/padded. Universal halting cannot be rewritten as “every word of length at most the budget is already halted”: a machine halting in one step satisfies `HaltsWithin x 1`, but its empty word still ends in the live initial state. The actual definitions, monotonicity statements, and truncation sketches are correct. | State the existential bounded-length equivalence for acceptance separately. Describe all-branch bounded time using a halted prefix of each length-budget word, or of each infinite choice stream; retain the exact-length definition. Precise formulas appear below. |
| 3 | note | `ClassNP/Nondeterminism.lean` · the four directional compilation sketches and padding | The substantive machine obligations are identified, but remain fill obligations. | The sketches account for split failure, effective arithmetic, input relocation/clamping, choice alignment, suppressed physical emissions, final verdicts, and all-branch timing. `Simulation` and `universalCaptureTM` are construction precedents, not already-proved instances of these compilers. The reconstruction below finds no additional load-bearing mechanism missing. | No statement repair. Carry the listed simulation, branch-correspondence, and time contracts into fill; do not replace them with untimed composition or a bare appeal to computability. |
| 4 | note | Audit pack · attestations 1–5, facades, order-list claim | Source facts and execution/history attestations have different evidence. | The supplied source reproduces 11 definitions, 14 admissions, six short proofs, the 33-admission total, and import reachability. It contains no parent snapshot, Git diff, order list, verification scripts/logs, or pinned Lean environment. Neither `lean` nor `lake` is on PATH here. | No mathematical repair. Retain the evidence distinctions in the attestation table below; do not treat this report as reproduction of the fresh-olean sweep, axiom prints, lint run, or freeze comparison. |

**Blind restatements: 11 definitions.** All class-level inputs and outputs are binary strings. Raw configuration notation is inherited from the trusted layer.

| Declaration | Literal content | Assessment |
|---|---|---|
| `Turing.NDTM` | A starting state and a total transition function taking a choice bit, a state, one input symbol or blank, and the symbols or blanks under the fixed number of work heads, and returning one `Action`. | Exactly two total action tables; no branching relation, oracle tape, or input-dependent machine selection. Finiteness is imposed later. |
| `NDTM.stepWith` | On a halted configuration return that configuration; otherwise apply the action selected by the current choice bit and scanned symbols. | Correct action semantics and absorption, including output preservation after halting. |
| `NDTM.initCfg` | `Cfg.init` at the machine's starting state: live state, input position 1, blank work tapes with heads at 0, empty output. | Same initialization as the deterministic model, including empty input. |
| `NDTM.runWith` | The empty word does nothing; a word `b :: w` first performs `stepWith b`, then runs `w`. | Choices are consumed from left to right, one per abstract step. |
| `NDTM.HaltsWithin` | Every choice word of length exactly the supplied budget leaves the initialized machine halted. | Correct all-branch time bound by absorption; not a claim that shorter prefixes are halted. |
| `FinNDTM` | A fixed natural number of work tapes, a state type with `Fintype` and `DecidableEq` data, and an `NDTM` on that state type. | Finite control; the class layer also fixes the alphabet to `Bool`. The raw symbol parameter alone is not asserted finite. |
| `MultiTapeTM.toNDTM` | Preserve the starting state and use the deterministic transition table for both choices. | Exact deterministic embedding. |
| `FinTM.toFinNDTM` | Preserve the tape count, finite state type/instances, and apply `toNDTM` to the underlying machine. | Correct bundled embedding. |
| `FinNDTM.AcceptsWithin` | Some choice word of exactly the supplied length leaves the machine both halted and with output exactly `[true]`. | Neither a live configuration with that output nor a halted longer output beginning with `true` accepts. |
| `FinNDTM.DecidesInTime` | For every input, all branches halt at its prescribed budget, and membership is equivalent to existence of an accepting branch at that budget. | Both conjuncts concern every input, including nonmembers. |
| `Complexity.NTIME` | There exist one natural multiplier and one finite binary NDTM deciding the language within that multiplier times the given length function, on every input. | Uniform machine and uniform multiplier. A zero multiplier cannot witness membership. |

**Blind restatements: 14 admitted statements.** These are mathematical assessments, not claims that the displayed `sorry` bodies prove them.

| Declaration | Literal statement | Audit result |
|---|---|---|
| `NDTM.HaltsWithin.mono` | All-branch halting by a budget implies all-branch halting by any larger budget. | Sound: split at the old budget, then absorb. |
| `MultiTapeTM.toNDTM_runWith` | On every configuration and choice word, the embedded run equals the deterministic run for the word's length. | Sound: induction, with identical one-step actions. |
| `FinNDTM.AcceptsWithin.mono` | Acceptance by a budget implies acceptance by every larger budget. | Sound: extend the witness and absorb. |
| `NTIME.mono` | Pointwise increase of the time function enlarges the class. | Sound: padding forward and all-branch truncation backward. |
| `DTIME_subset_NTIME` | For every time function, deterministic time is contained in nondeterministic time with that same function. | Sound: the embedding gives both halting and the acceptance equivalence. |
| `NTIME_eq_empty_of_exists_zero` | A time function vanishing at any length has an empty nondeterministic class. | Sound: an input exists at that length, and its time-zero configuration is live. |
| `ntime_poly_subset_NP` | For each natural degree, `NTIME (n ↦ n^c + 1) ⊆ NP`. | Sound compilation with admissible coefficient `2a` and degree `c`. |
| `NP_subset_iUnion_NTIME` | `NP ⊆ ⋃ c, NTIME (n ↦ n^c + 1)`. | Sound guess-and-verify compilation, with a uniform all-branch polynomial bound. |
| `NP_eq_iUnion_NTIME` | Equality of the preceding classes. | Follows from the two inclusions. |
| `ntime_expPow_subset_NEXP` | For each natural degree, `NTIME (n ↦ 2^(n^c)) ⊆ NEXP`. | Sound compilation with certificate coefficient `a` and degree `c`. |
| `NEXP_subset_iUnion_NTIME` | `NEXP ⊆ ⋃ c, NTIME (n ↦ 2^(n^c))`. | Sound exponential guess-and-verify compilation; small lengths are absorbed by a multiplier. |
| `NEXP_eq_iUnion_NTIME` | Equality of the preceding exponential classes. | Follows from the two inclusions; reconciles the certificate definition. |
| `EXP_eq_NEXP_of_P_eq_NP` | `P = NP` implies `EXP = NEXP`. | Sound certificate-padding argument, with finding 1's cost clarification. |
| `P_ne_NP_of_EXP_ne_NEXP` | `EXP ≠ NEXP` implies `P ≠ NP`. | Direct contraposition of the preceding statement. |

**The six proved lemmas.** I checked their proof terms at source level. None invokes a new admitted theorem.

| Lemma | Restatement and proof check |
|---|---|
| `runWith_nil` | Running the empty word is the identity; `rfl` unfolds the first recursion clause. |
| `runWith_cons` | Run a head choice first, then the tail; `rfl` unfolds the second clause. |
| `runWith_append` | Running concatenated words equals the successive runs. The induction generalizes the configuration, which is necessary because the cons case changes it. After the two `runWith_cons` rewrites, the induction hypothesis has exactly the required configuration. |
| `stepWith_of_halt` | One step on a halted configuration is the identity. Unfolding `stepWith` and rewriting the state to `none` selects that branch. |
| `runWith_of_halt` | Every word fixes a halted configuration. The cons case reduces its first step using `stepWith_of_halt`, leaving the induction hypothesis at the same configuration. |
| `MultiTapeTM.toNDTM_initCfg` | The embedded machine's initial configuration equals the original's. Both reduce to `Cfg.init tm.q₀ input`, so `rfl` is appropriate. |

The admitted embedding run lemma similarly has a complete short outline: the step functions coincide on both live and halted configurations, and the cons case matches `MultiTapeTM.runFrom_succ_eq_step`. There is no reversal of word order or use of the wrong successor convention.

**Design questions (a)–(f).**

| Question | Answer |
|---|---|
| (a) Output acceptance and unconstrained rejection | Faithful for all stated uses. Acceptance requires completed output exactly `[true]`; every other completed output rejects. A finite-control monitor can distinguish empty output, exactly `[true]`, and all other outputs, updating on every emission and consulting the result only when the source halts. This translates to a distinguished accepting halt with constant overhead. Conversely, an accepting-state machine can suppress intermediate output and emit one verdict at termination. No stated theorem needs all rejecting branches to emit `[false]`. |
| (b) Totality | Correct. The quantified condition includes nonmembers and rejecting branches of members. In particular, one accepting branch does not excuse a divergent sibling. The uniform all-branch conjunct is also what justifies backward truncation. |
| (c) Lists versus streams | Equivalent for these time-bounded notions. Take the first budget-many bits of any stream; conversely extend any finite word by `false` forever. Their runs through the finite horizon coincide by induction on that horizon. No compactness or infinite-choice principle is needed. |
| (d) Exact versus bounded length | The declarations and padding/truncation uses are correct. Finding 2 concerns only the overbroad prose. The correct quantified equivalences are given next. |
| (e) Union padding | Correct. Positive-degree unpadded polynomial bounds vanish at zero, so their literal components are empty in this model. Including degree zero alone would leave only the constant-time component. The `+ 1` restores the conventional all-input polynomial class; for positive lengths it changes bounds by at most a factor of two. Exponential bounds are always at least 1 and need no such repair. |
| (f) Certificate-form Theorem 2.22 | Valid. Pairing preserves the input/certificate distinction, exact internal checks enforce the NEXP witness length, malformed inputs reject, and assembling the exponential padding followed by a polynomial-time decider remains exponential. The argument uses the trusted bounded paired NP interface, not either unproved NDTM equivalence. |

For the next derivations, write only

$$
R_x(w)=N.\mathrm{tm}.\mathrm{runWith}\,w\,(N.\mathrm{tm}.\mathrm{initCfg}\,x).
$$

If `R_x(w).state = none`, the proved append and absorption lemmas give

$$
\begin{aligned}
R_x(w\mathbin{++}v)
&=N.\mathrm{tm}.\mathrm{runWith}\,v\,(R_x(w))\\
&=R_x(w).
\end{aligned}
$$

Consequently the correct existential bounded-length reading is

$$
N.\mathrm{AcceptsWithin}(x,t)
\iff
\exists w,\ |w|\le t\ \land\ R_x(w).\mathrm{state}=\mathrm{none}
\ \land\ R_x(w).\mathrm{output}=[\mathrm{true}].
$$

The reverse implication appends `t − |w|` false bits. The correct all-branch reading, in finite words, is

$$
N.\mathrm{tm}.\mathrm{HaltsWithin}(x,t)
\iff
\forall w,\ |w|=t\ \Longrightarrow
\exists r\le t,\ R_x(w.\mathrm{take}\,r).\mathrm{state}=\mathrm{none}.
$$

Forward choose `r=t`; backward absorb the remaining suffix. Replacing the right side by `∀ w, |w| ≤ t → R_x(w).state = none` is false, already at `w=[]`.

More strongly, under all-branch halting at `t`, for every `t' ≥ t` and word `w` of length `t'`,

$$
|w.\mathrm{take}\,t|=t,
\qquad R_x(w)=R_x(w.\mathrm{take}\,t).
$$

This equality preserves the entire configuration, not merely the halting flag. It proves the backward acceptance implication in `NTIME.mono` and both forward compilers. Absorption alone, without halting of the truncated prefix, would not prove that implication.

For `DTIME_subset_NTIME`, `computesInTime_iff` supplies the deterministic halted state and singleton indicator output at the budget. Every word at that budget reproduces this configuration by `toNDTM_runWith`; a word of that length exists, for example the all-false word. Thus membership supplies an accepting branch, while nonmembership gives `[false]` on every branch. This establishes both conjuncts, including at arbitrary time functions. If the budget is zero, the supposed deterministic or nondeterministic witness is already impossible.

**Adversarial reconstruction: choice words to certificates.**

Fix an NDTM deciding a language with the indicated multiplier `a` and degree `c`. The two versions differ only in their length formulas:

| Version | Original time `T(n)` | Exact certificate length `Q(n)` | Admissible certificate parameters |
|---|---|---|---|
| Polynomial | `a(n^c+1)` | `2a(n+1)^c` | Coefficient `2a`, degree `c` |
| Exponential | `a·2^(n^c)` | `a·2^((n+1)^c)` | Coefficient `a`, degree `c` |

1. The necessary inequalities hold at every natural length and degree:

   $$
   a(n^c+1)\le a((n+1)^c+(n+1)^c)=2a(n+1)^c,
   $$

   $$
   n^c\le(n+1)^c
   \ \Longrightarrow\ a2^{n^c}\le a2^{(n+1)^c}.
   $$

   Degree zero is included (`0^0=1`). Multiplier zero cannot actually occur in a deciding witness because the initial state is live.

2. Each `Q` is nondecreasing, including the constant cases. If `n<n'`,

   $$
   n+Q(n)<n'+Q(n)\le n'+Q(n').
   $$

   Therefore, on an arbitrary verifier input `y` of length `m`, searching all `0≤n≤m` for `n+Q(n)=m` finds at most one split. Failure must reject; the sketches explicitly say so. On success, the prefix `x` and suffix `u` satisfy `|x|=n`, `|u|=Q(n)`. On an intended input `x++u`, uniqueness forces this very split; it cannot silently substitute another instance.

3. Define the verifier to accept precisely when the simulated `R_x(u)` is halted with output exactly `[true]`. For an accepting original word `w` of length `T(n)`, let

   $$
   u=w\mathbin{++}\operatorname{replicate}(Q(n)-T(n),\mathrm{false}).
   $$

   Its length is exactly `Q(n)`, and absorption preserves its accepting configuration. Conversely, from an accepting `u` of length `Q(n)`, its prefix of length `T(n)` is halted by the original all-branch bound. The full run equals that prefix run, so the prefix is an original accepting witness. Hence

   $$
   x\in L\iff\exists u,\ |u|=Q(|x|)\ \land\ x\mathbin{++}u\in V.
   $$

4. The verifier is polynomial-time on **all** its inputs. Polynomial split candidates have polynomial-size values. Exponential split candidates may have enormous values, but their binary representations have at most

   $$
   (n+1)^c+\operatorname{bits}(a)+1
   \le(m+1)^c+\operatorname{bits}(a)+1
   $$

   bits. There are at most `m+1` candidates; fixed-degree binary arithmetic is polynomial in `m`, also on failed searches. After success, `Q(n)≤m`, so the simulation has at most `m` logical steps. With a fixed source machine, polynomial bookkeeping per step gives a polynomial total bound. This uses no computation of an arbitrary numerically bounded length function.

The following invariant details are necessary for step 4 and are covered by the named obligations:

| Component | Required behavior and adversarial check |
|---|---|
| Source input | With shifted source head position `p`, read blank at `p=0,n+1`, and otherwise read `x[p−1]`. Update `p` by the source `moveInputPos`, clamping to `0,…,n+1`. A move to the right boundary must not expose the first certificate bit. Repeated outward moves must remain clamped, so a later inward move returns correctly. Initial position is 1 even when `x=[]`. |
| Choice tape | Before source step number `j`, use exactly the certificate bit at position `j`. Administrative simulator transitions do not consume source choices. A halted source remains unchanged; either finishing the clock with absorbed steps or stopping early preserves the verdict. |
| Source state and tapes | Store the fixed machine's finite state in finite control and keep its work tapes separate from counters, choice storage, and buffers. Simulation bookkeeping must not alter the represented source configuration. |
| Output | Suppress physical output during simulation. Capture every source emission, including an emission on the halting transition, before testing the final buffer. Emit exactly one verifier decision bit. A halted output `[true,false]`, `[]`, or `[false]` rejects; a live output `[true]` also rejects. |

These are genuine machine-construction obligations, but none needs a universal NDTM or a new complexity assumption. The transition tables are fixed and finite; the verifier is a single uniform deterministic machine.

**Adversarial reconstruction: certificates to choice words.**

Let the certificate length be `Q(n)=C(n+1)^c`, and let the trusted `P` interface provide a verifier machine deciding its language within `A(m+1)^d` steps.

1. Compute the input length and the explicit `Q(n)`; initialize the guess countdown. At each guess-writing transition, the current choice bit is written as the next certificate bit. All intervening transitions ignore their choice bit. The countdown and phase control are separate from guessed data, so the times of the guess-writing transitions depend on the input length, not their values.

2. For every `u` of length exactly `Q(n)`, assign its successive bits to those guess-writing positions of a branch word and set unused choices arbitrarily. This realizes `u`. Conversely, every sufficiently long branch word yields exactly one such `u`, because precisely `Q(n)` writes occur. Thus the construction has both witness coverage and witness extraction; it does not incorrectly equate the first `Q(n)` physical choices with the certificate. If `C=0`, there are no guess-writing positions and the sole certificate is `[]`.

3. Assemble `x++u` and start the verifier from its proper initial configuration with blank simulated work tapes, empty captured output, and virtual input head 1. Its virtual read-only input is the assembly tape, with the corresponding length's boundary guard and clamping. The two NDTM tables coincide throughout this simulation. Capture output and emit a single final verdict. The deterministic verifier's totality holds for every assembled string, so every branch terminates, whether or not `x∈L`.

4. A branch accepts exactly when its extracted certificate satisfies `x++u∈V`; existential branch acceptance is therefore equivalent to membership in `L`. Extend a terminated branch to the declared common budget by absorption. Conversely, every branch at that budget has completed the construction and yields a legitimate certificate. The later verifier phase may have certificate-dependent running time; the needed assertion is a **common upper bound**, not equal actual halting times.

5. For fixed positive constants `K,r` absorbing arithmetic, assembly, and simulation costs, a bound of the form

   $$
   H(n)\le K(n+Q(n)+1)^r
   $$

   suffices. It can incorporate any fixed-degree bookkeeping cost. Put `e=r·max(1,c)`. Then, at every `n`,

   $$
   \begin{aligned}
   n+Q(n)+1&\le(C+1)(n+1)^{\max(1,c)},\\
   H(n)&\le K(C+1)^r(n+1)^e\\
       &\le K(C+1)^r2^e(n^e+1).
   \end{aligned}
   $$

   The last inequality is the trusted `succ_pow_le`. This is precisely a component of the stated padded union, with one constant valid even at `n=0`.

For the exponential reverse direction, use `E(n)=C·2^((n+1)^c)` in the same construction. Computing its binary representation has polynomial cost in `n`; the number of guesses and the verifier input length may be exponential. When `C=0`, skip the guess phase directly. A fixed envelope is again `H(n)≤K(n+E(n)+1)^r`, after increasing `K,r` if necessary. Since

$$
n+E(n)+1\le(C+1)(n+1)2^{(n+1)^c},
$$

we have

$$
\log_2 H(n)\le\log_2K+r\log_2(C+1)
 +r\log_2(n+1)+r(n+1)^c.
$$

For `n≥2`, the right side is at most `B n^{max(1,c)}` for a fixed constant `B`. For `n≥max(2,B)`,

$$
B n^{\max(1,c)}\le n^{\max(1,c)+1}\le n^{c+2}.
$$

Thus `H(n)≤2^(n^(c+2))` beyond a fixed threshold. The sketch's larger choice `e=c+d+2` also works, regardless of the fixed bookkeeping degree. Choose a natural threshold `n₀` and

$$
a'=\max\bigl(\{1\}\cup\{H(n):n<n_0\}\bigr).
$$

For every length, `H(n)≤a'·2^(n^e)`: above the threshold use the eventual estimate; below it use `2^(n^e)≥1`. The same absorption/truncation equality preserves acceptance at the enlarged budget. This covers `c=0`, `C=0`, the empty input, and length 1 without changing the exponential union.

**Theorem 2.22: complete padding interface check.**

Fix a certificate-form NEXP witness `(C,c,V)` for `L`, with `E(n)=C·2^((n+1)^c)`. Let

$$
f(x)=\operatorname{pairEncode}\bigl(x,\operatorname{replicate}(E(|x|),\mathrm{true})\bigr),
\qquad L_{\mathrm{pad}}=\{f(x):x\in L\}.
$$

The trusted pairing grammar doubles the first component, appends the two-bit separator, and then appends the second component unchanged. Consequently

$$
|f(x)|=2|x|+2+E(|x|),\qquad f(x)=f(z)\Longrightarrow x=z.
$$

Define the paired verifier language by

$$
V'=\{\operatorname{pairEncode}(f(x),u):
 |u|=E(|x|)\ \land\ x\mathbin{++}u\in V\}.
$$

On an arbitrary string, its decider must execute the following sequence:

1. Parse the **outer** pair into `x',u`; reject parser failure. Parse `x'` into `x,pad`; reject parser failure. The grammar consumes aligned doubled bits through its first aligned separator; it does not search for arbitrary unaligned occurrences of `01`.
2. Evaluate `E(|x|)` in binary. Before any validity assumption, its bit length is at most `(|x|+1)^c+bits(C)+1`, polynomial in the actual outer input length. No exponential unary string is constructed by this verifier. For `C=0`, the value is zero.
3. Check that `pad` contains only `true`, that `|pad|=E(|x|)`, and that `|u|=E(|x|)`. Reject any failure. Both exact length checks are needed; the bounded outer NP witness condition does not replace either one.
4. Assemble `x++u` and call the relocated, captured decider for `V`. After the checks, `|x++u|≤|x'|`; all parsing, arithmetic, checks, and the call are polynomial in the actual verifier input length. Emit one verdict.

This proves the required verifier language is polynomial-time once those named native machine contracts are implemented. Finding 1 repairs the unjustified logarithmic estimate in step 2; the uniform polynomial bound already present in the formula suffices.

For the trusted bounded paired NP interface, take coefficient and degree both 1. If `x'=f(x)`, then

$$
\begin{aligned}
x'\in L_{\mathrm{pad}}
&\iff x\in L\\
&\iff\exists u,\ |u|=E(|x|)\ \land\ x\mathbin{++}u\in V\\
&\iff\exists u,\ |u|\le|x'|+1\ \land\operatorname{pairEncode}(x',u)\in V'.
\end{aligned}
$$

The last forward implication uses `E(|x|)≤|x'|`; the backward implication uses the verifier's exact check and pairing injectivity. If `x'` is not any `f(x)`, both ends are false: outer pairing injectivity prevents any witness from changing that first component. This covers all malformed strings, not only well-padded inputs. If `C=0`, valid padding and certificates are both empty and these equivalences still hold.

Therefore `L_pad∈NP`. Under `P=NP`, obtain its deterministic polynomial-time decider. On input `x`, a total machine can compute `E(|x|)`, write the padding and the pair `f(x)`, then run that decider with relocated input and captured output. Its total cost is polynomial in `2|x|+2+E(|x|)`, including the cost of producing this whole string. The preceding exponential normalization and finite-length multiplier put the result in `EXP`. Together with the trusted `EXP_subset_NEXP`, this gives the equality and then its contrapositive. No untimed composition theorem is being used to supply this time bound.

**Attestations and verification limits.**

| Attestation | Independently reproduced from this bundle | Not independently reproduced |
|---|---|---|
| 1 — freeze and changed paths | Current new declarations; current facade imports and Contents entries; root imports reach both facades and all three new modules. | Authentication of `e1e68ebd`; exact changed-path list; byte identity against the closed gates; the three order-list insertions. The order-list file is not attached. |
| 2 — fresh elaboration | The source has exactly the claimed 33 `sorry` tokens, with the stated module distribution. | Lean 4.25.0/mathlib pin, fresh oleans, zero compiler errors, gate results, and the comment-only recheck. No Lean executable, dependencies, scripts, or logs were supplied here. |
| 3 — admissions and axiom footprints | All 14 new admissions have proof sketches; the six supplied short proofs use definitions/run algebra and no admitted theorem. No explicit new axiom or unsafe declaration occurs. | Kernel axiom prints, including the claimed Chapter-1 headline footprints. A lexical admission count is not an axiom-footprint computation. |
| 4 — policy/lint | New file lengths are 233/160/234 lines. New public declarations have statement prose; the headers, namespaces, and precise in-repository imports match the stated conventions. | Execution of `style_lint.py`, zero FAIL, unchanged historical WARNs, and claims about unattached legacy files. |
| 5 — new inventory | Exactly 11 definitions/structures, 14 sorried theorems, six proved lemmas, and the two bundled-instance attributes; no additional new declaration categories were found. | The maintained toolchain's elaboration of those instances and proof terms. |

The comment/string-stripped admission inventory is:

| Module | Definitions/structures | Admitted theorems | Proved lemmas |
|---|---:|---:|---:|
| `TuringMachine/Nondeterministic.lean` | 8 | 2 | 6 |
| `ClassNP/NTIME.lean` | 3 | 4 | 0 |
| `ClassNP/Nondeterminism.lean` | 0 | 8 | 0 |
| **New surface** | **11** | **14** | **6** |

The five trusted phase-1 files contain `3/2/4/3/7` admissions in `PolyTime/NP/CoNP/EXP/Reductions` order, totaling 19. The other supplied files have no `sorry` tokens. This verifies a current count, not historical preservation of the sources.

As limited executable corroboration, I checked 1,350 polynomial and 324 exponential parameter triples for the padding inequalities and strict split-length increase. An independent finite model enumerated 6,561 two-state, input-independent binary transition tables, including optional emissions and halting: 98,415 ordered budget pairs through length 4 checked acceptance monotonicity and conditional halting/truncation, and 104,976 word-pair checks verified append semantics. I also checked the paired parsing/re-encoding invariant on all 2,047 binary words of length at most 10. These finite checks exercise the identified failure modes; they do not execute Lean, implement the full compilers, or replace the quantified arguments above.

**Notation glossary.** `N` is a fixed finite binary NDTM; `R_x(w)` is its configuration after choice word `w` on input `x`. `x,x',y,z,u,v,w` are binary strings; `|·|` is length, `++` is concatenation, `[]` is the empty string, `take` is prefix extraction, and `replicate` repeats a bit. `L,V,V'` are a language and verifier languages; `f` and `L_pad` are the padding map and its image of `L`. `n,n',m` are lengths or candidate split positions; `t,t'` are time budgets; `p` is a shifted input-head position; `j` is a logical step index. `a,a',A,C,K,B` are fixed coefficients/constants; `c,d,e,r` are degrees or auxiliary natural indices (the halted-prefix formula uses `r` as its prefix length). `T,Q,E,H` are, respectively, the original time bound, the section's polynomial or exponential certificate length, the exponential certificate length, and a uniform total-time envelope. `n₀` is a fixed threshold; `bits` is binary representation length, with `bits(0)=1`; `log₂` is the base-two logarithm. Class names and other Lean identifiers refer to the attached definitions.
