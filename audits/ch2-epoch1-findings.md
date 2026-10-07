# Chapter 2 fill campaign, epoch 1 — audit findings

**Verdict: PASS for the commissioned proof/helper gate.**

**0 blockers · 0 majors · 1 minor · 1 note.** All 27 filled targets and all 19 private helpers were examined. No mathematical defect was found in their proofs. The minor concerns a helper docstring's description of its formal contract; it does not invalidate the construction or any target. The gate's zero-blocker/major condition is met on the supplied evidence and the maintainer's build/freeze attestations.

Audit date: 2026-10-02. Single-agent audit; no delegation. Input: the supplied `ch2-epoch1-bundle.md`, SHA-256 `1df87e1da0cf7b63915c6a5ac22839cbe04d4ee8eac1c0d4bba9893946585391`. The bundle identifies base `7494522e8826be6b54675307668435afc59c005d` and the integrated agent-commit endpoint `b5ff4c75`. This audit makes no claim to have independently authenticated those revisions.

Source references below use line numbers within each attachment, beginning at its first content line, not line numbers within the combined bundle. References to the pack itself use combined-bundle lines 1–94. In tables, source paths are relative to `TCSlib/Complexity/`; report paths are relative to `audits/ch2-epoch1-agent-reports/`.

## Findings, in severity order

### E1-1 — Minor: the width helper's docstring describes a stronger property than its theorem contract

**Location:** `TCSlib/Complexity/Formulas/CNF.lean:201–206`.

The docstring says, “Every truth-table clause has exactly one literal per prescribed variable.” The theorem `falsifyingCNF_width` states only

```lean
(falsifyingCNF f).WidthAtMost ℓ
```

By `WidthAtMost` at lines 99–103, this means that every clause has length at most `ℓ`. It does not export exact length, the occurrence of every prescribed variable, or uniqueness of those occurrences. The implementation proves the upper bound by taking `.le` of the exact `List.length_ofFn` equality.

The stronger descriptive sentence is **true of the actual construction**: `falsifyingClause` enumerates each `i : Fin ℓ` once. This finding is solely a mismatch between the advertised theorem contract and the proposition supplied to callers, under priority 5's explicit docstring/contract check. It is not a counterexample to the helper or the public theorem. Batch D's report correctly describes the weaker contract at line 67.

**Proposed repair:** change this new helper's docstring to: “Every truth-table clause has width at most the prescribed arity; its constructed length is exactly that arity.” No public statement or proof change is needed.

### E1-2 — Note: several procedural attestations cannot be independently reproduced from this packet

**Locations:** `ch2-epoch1-bundle.md:17–47,67–70`; `batchA.md:75–108`; `batchB.md:72–109`; `batchC.md:23–87`; `batchD.md:96–124`.

The 16 attachments are exactly four reports, ten integrated source files, the 27-entry axiom log, and the 53-entry module order. They do **not** include the base sources, batch briefs, original archives or checksum manifests, patch series, integration record, freeze/style checkers, imported project dependencies, or `audits/logs/ch2-e1-sweep-53mod.log`. The local audit environment also did not expose `lean` or `lake` on `PATH`.

Consequently, this audit independently checks the visible mathematics, source/helper inventory, report consistency, and the **contents** of the supplied axiom log. It does not independently rerun the Lean kernel, establish fresh-olean provenance, reproduce the baseline diff, verify archive hashes/replay/authorship, or certify compliance with the unprovided briefs' additional instructions. These remain attestations, not newly reproduced audit results. Their omission does not contradict them and is not treated as a mathematical blocker.

**Disposition:** retain this evidence boundary with the verdict. If independent procedural replay is desired, supply the already cited base/brief/patch/checker/build evidence and the pinned dependencies. No source repair is demanded by this note.

## Six-priority assessment

| Priority | Verdict | Evidence and conclusion |
|---|---|---|
| 1. Composition exponent arithmetic | Pass | `ClassNP/PolyTime.lean:99–160`; full derivation below, including zero coefficients and degrees. |
| 2. Parser round trip and consumed-prefix bounds | Pass | `Formulas/CNFEncoding.lean:167–249,279–445,460–473`; the strengthenings quantify over every adequate fuel, recursive calls meet their hypotheses, and the final suffix remains in the bounds. |
| 3. Backward truncation in `NTIME.mono` | Pass | `ClassNP/NTIME.lean:153–163`; equality of complete configurations transfers the output exactly `[true]`. |
| 4. Timed complementation | Pass | `ClassNP/CoNP.lean:72–108`; explicit use of `computesFunInTime_comp`, explicit monotonicity, explicit coefficient/degree absorption. |
| 5. All 19 private helpers | Pass with E1-1 | Inventory and individual assessment below. No circular proof relocation, hidden admission, or public declaration introduced by a helper was found in the supplied source. |
| 6. Agent and maintainer reports | Pass within E1-2's evidence boundary | Counts, visible proof routes, helper contracts/locations, and supplied axiom footprints reconcile. Procedural claims lacking their underlying evidence remain attested. |

## Detailed priority checks

### 1. Independent derivation of `comp_time_bound`

Fix arbitrary natural numbers `a, C, c, C', c', n`, and write

\[
d=\max(c,cc').
\]

Since `n + 1 ≥ 1`, including when `n = 0`,

\[
1\le(n+1)^c,\qquad
(n+1)^c\le(n+1)^d,\qquad
(n+1)^{cc'}\le(n+1)^d.
\]

Therefore

\[
\begin{aligned}
C(n+1)^c+1
&\le C(n+1)^c+(n+1)^c\\
&=(C+1)(n+1)^c,\\
\bigl(C(n+1)^c+1\bigr)^{c'}
&\le\bigl((C+1)(n+1)^c\bigr)^{c'}\\
&=(C+1)^{c'}(n+1)^{cc'}\\
&\le(C+1)^{c'}(n+1)^d.
\end{aligned}
\]

Multiplication and addition preserve these inequalities because all coefficients are nonnegative. Also `1 ≤ (n + 1)^d`. Thus

\[
\begin{aligned}
&a\left(C(n+1)^c+C'\bigl(C(n+1)^c+1\bigr)^{c'}+1\right)\\
&\quad\le a\left(C(n+1)^d+C'(C+1)^{c'}(n+1)^d+(n+1)^d\right)\\
&\quad=a\left(C+C'(C+1)^{c'}+1\right)(n+1)^d.
\end{aligned}
\]

This is precisely the private helper's contract. The proof at `PolyTime.lean:109–133` follows these steps and never cancels or divides by a coefficient.

Boundary cases are covered, not excluded:

| Case | Direct reduction |
|---|---|
| `a = 0` | Both sides are zero. |
| `C = 0` | Left side is `a(C' + 1)`; right side is `a(C' + 1)(n + 1)^d`, which is at least it. |
| `C' = 0` | The growing first-machine term is still bounded using `d ≥ c`; the independent constant is absorbed using `(n + 1)^d ≥ 1`. |
| `c = 0` | `d = 0`; both sides equal `a(C + C'(C + 1)^{c'} + 1)`. |
| `c' = 0` | `d = c`; the required inequality is `a(C(n + 1)^c + C' + 1) ≤ a(C + C' + 1)(n + 1)^c`. |
| `n = 0` | Every power with base `n + 1` is one, and the helper is an equality. |

In particular, replacing `max c (c * c')` by just `c * c'` would lose the first-machine term when `c' = 0`; the implementation does not do this.

The application at lines 154–160 separately proves monotonicity of the second **explicit** polynomial and passes it to the timed composition interface. The resulting coefficient is constant in the input length. `mem_P_of_polyTimeReducible` then uses this proved closure result, identifies the composed singleton indicator through the reduction equivalence, and applies

\[
A(n+1)^d\le A2^d(n^d+1)
\]

at `Reductions.lean:112–120`. It uses the audited imported `succ_pow_le` interface; this audit does not reverify that absent dependency's implementation. No untimed composition invocation occurs in either filled proof.

### 2. Parser fuel and consumed-prefix accounting

The definitions at `CNFEncoding.lean:85–100` give the exact identities

\[
\begin{aligned}
|\operatorname{serializeLit}(v,b)|&=v+3,\\
|\operatorname{serializeClause}([])|&=1,\\
|\operatorname{serializeClause}((v,b)::C)|&=v+3+|\operatorname{serializeClause}(C)|,\\
|\operatorname{serialize}([])|&=1,\\
|\operatorname{serialize}(C::\varphi)|&=1+|\operatorname{serializeClause}(C)|+|\operatorname{serialize}(\varphi)|.
\end{aligned}
\]

`takeTrues_replicate` preserves the delimiter `false` as part of its returned suffix. Consequently `parseLit_serializeLit` consumes the nonempty unary run, its delimiter, and the polarity bit, leaving **exactly** its supplied suffix. Variable zero and either polarity are included.

For the clause round trip, the nonempty-clause case cannot have fuel zero. With fuel `k + 1`, the hypothesis is

\[
v+3+|\operatorname{serializeClause}(C)|\le k+1.
\]

It implies `|serializeClause C| ≤ k`, exactly the induction hypothesis used at lines 204–214. The suffix for the literal call is `serializeClause C ++ r`, and the recursive clause call retains `r`. An empty clause reads its closing `false` without spending fuel, consistent with the parser's first pattern, including at fuel zero. The lemma's sufficient lower bound is deliberately not a claim of minimal fuel.

For the nonempty-formula case, fuel `k + 1` and the premise give

\[
1+|\operatorname{serializeClause}(C)|+|\operatorname{serialize}(\varphi)|\le k+1.
\]

Hence **both**

\[
|\operatorname{serializeClause}(C)|\le k,
\qquad
|\operatorname{serialize}(\varphi)|\le k.
\]

These are the separate hypotheses established at lines 236–243. The clause parser is applied with suffix `serialize φ ++ r`; the tail formula parser uses the same decremented fuel and suffix `r`. Reusing that fuel is exactly the definition at lines 136–145: fuel bounds recursion depth, rather than serving as a single mutable total-step counter.

The final application at lines 266–269 supplies `r = []` and `fuel = |serialize φ|`. Its sole adequacy obligation is reflexivity. Thus the strengthening actually yields complete consumption at the public target; it is not merely a round trip at some unspecified larger fuel.

For the independent variable bound, `parseLit_length` proves

\[
\operatorname{parseLit}(x)=\operatorname{some}((v,b),t)
\ \Longrightarrow\ |x|=v+3+|t|.
\]

In a successful clause step, let the recursive clause parse return `(D, r)` from `t`. Its induction hypothesis gives

\[
|r|\le|t|,\qquad
\forall(j,\beta)\in D,\ j+1+|r|\le|t|.
\]

For the new literal,

\[
v+1+|r|\le v+1+|t|\le v+3+|t|=|x|.
\]

For every old literal,

\[
j+1+|r|\le|t|\le|x|.
\]

The remainder bound follows from `|r| ≤ |t| ≤ |x|`. These are exactly the head/tail cases at lines 356–364.

For a successful formula step on `true :: s`, suppose the clause parser returns `(D, t)` and the tail formula parser returns `(ψ, r)`. The two induction results give

\[
\begin{gathered}
|r|\le|t|\le|s|,\\
\forall(j,\beta)\in D,\ j+1+|t|\le|s|,\\
\forall C\in\psi,\ \forall(j,\beta)\in C,\ j+1+|r|\le|t|.
\end{gathered}
\]

For the first clause, replace `|t|` on the left by the smaller `|r|`; for tail clauses, enlarge the right side from `|t|` to `1 + |s|`. This establishes the claimed bounds for the whole formula at lines 417–427. Crucially, the proof never discards the final remainder while composing the bounds.

Given `|r| ≤ |x|`, the additive inequality `j + 1 + |r| ≤ |x|` is equivalent to `j + 1 ≤ |x| - |r|` over natural numbers. Batch D's report is correct about the subtraction-free formulation.

`numVars_decode_le` handles every parser outcome: failure, success with empty remainder, and success with nonempty remainder. The first and third decode to the empty fallback and have variable measure zero; the second uses `r = []` in the bound above and bounds the maximum fold termwise. There is no reliance on a round-trip-only hypothesis for arbitrary malformed strings.

### 3. Backward acceptance transfer preserves exactly `[true]`

Fix the machine, multiplier, and input used in `NTIME.mono`. Put `t = c T₁(|x|)` and `t' = c T₂(|x|)`. Pointwise domination gives `t ≤ t'`. For a larger-budget accepting word `w`, `|w| = t'`, so

\[
|w.\operatorname{take}(t)|=t.
\]

All-branch halting at the **smaller** budget says the configuration after this prefix has state `none`. The run algebra therefore gives equality of whole configurations:

\[
\begin{aligned}
N.\operatorname{runWith}(w,N.\operatorname{initCfg}(x))
&=N.\operatorname{runWith}\bigl(w.\operatorname{drop}(t),
 N.\operatorname{runWith}(w.\operatorname{take}(t),N.\operatorname{initCfg}(x))\bigr)\\
&=N.\operatorname{runWith}(w.\operatorname{take}(t),N.\operatorname{initCfg}(x)).
\end{aligned}
\]

Projecting `.output` transfers the equality to `[true]`; projecting `.state` retains halting. The prefix is therefore a witness for acceptance at time `t`, and the original decider equivalence gives membership in the language.

This is what `NTIME.lean:155–163` proves. Discarding the larger word's halting conjunct at line 153 is legitimate: smaller-budget all-branch halting supplies the stronger fact needed for absorption. The code does **not** infer that a halted extension forces an arbitrary shorter prefix to be halted, and it does not weaken acceptance to containing a true bit or merely halting.

The forward direction pads by `false` bits and applies absorption; `HaltsWithin.mono` splits at the smaller budget in the same way. No positivity assumption on the multiplier or either budget is silently needed.

### 4. Complement closure uses timed composition and an explicit polynomial

At `CoNP.lean:74–81`, the original decider computes exactly `[indicator L x]` within `C(n + 1)^d`; the fixed postprocessor maps `[true]` to `[false]` and `[false]` to `[true]`. Its total behavior on other strings is harmless because the intermediate output is always a singleton Boolean indicator.

The proof explicitly calls `Turing.FinTM.computesFunInTime_comp`, supplying monotonicity of the postprocessor budget `a(n + 1)`. It obtains the concrete composed budget

\[
b\left(C(n+1)^d+a\left(C(n+1)^d+1\right)+1\right).
\]

The two membership cases identify the output with the complement indicator, not a concatenation of the original and complemented bits. Buffered timed composition is used as an imported audited interface; its internal machine is not supplied for a fresh audit here.

Since `(n + 1)^d ≥ 1`, the normalization is

\[
\begin{aligned}
&b\left(C(n+1)^d+a\left(C(n+1)^d+1\right)+1\right)\\
&\quad\le b\left(C+a(C+1)+1\right)(n+1)^d\\
&\quad\le b\left(C+a(C+1)+1\right)2^d(n^d+1).
\end{aligned}
\]

Lines 96–108 establish this with an explicit intermediate bound on `C(n + 1)^d + 1`. The coefficient passed to `mem_P_of_dtime_le` is precisely `b(C + a(C + 1) + 1)2^d`, and the degree remains `d`. The `DTIME` witness uses multiplier one. Zero coefficients and degree zero cause no division, cancellation, or positivity gap. No abstract length function, untimed composition theorem, or unproved class-closure result is substituted.

## Complete target coverage

“Pass” below refers to proof reasoning against the frozen supplied statement, under the imported-interface and kernel-attestation boundary in E1-2.

### Batch A — 8 targets

| Target and source | Verdict | Check |
|---|---|---|
| `polyTimeComputable_id`, `ClassNP/PolyTime.lean:78–82` | Pass | Uses the supplied identity-machine interface with degree one; the pointwise budget conversion is equality after `pow_one`. |
| `PolyTimeComputable.output_length_le`, `ClassNP/PolyTime.lean:91–97` | Pass | Uses the same coefficient and degree as the computing machine, its output at the budget, and the per-step output-length bound. |
| `PolyTimeComputable.comp`, `ClassNP/PolyTime.lean:149–160` | Pass | Correct order of function composition; explicit monotonicity and the checked exponent/constant bound above. |
| `PolyTimeReducible.refl`, `ClassNP/Reductions.lean:65–66` | Pass | Identity function and reflexive membership equivalence. |
| `PolyTimeReducible.trans`, `ClassNP/Reductions.lean:73–77` | Pass | `g ∘ f`, with the two membership equivalences composed at `x` and `f x`; no direction reversed. |
| `mem_P_of_polyTimeReducible`, `ClassNP/Reductions.lean:98–120` | Pass | Timed polynomial composition of the reduction and singleton-indicator decider; correct indicator identification and `succ_pow_le` normalization. |
| `P_eq_NP_of_NPHard_mem_P`, `ClassNP/Reductions.lean:136–140` | Pass | Uses the now-filled `P_subset_NP`; the other inclusion applies downward closure to each NP language. |
| `NPComplete.mem_P_iff`, `ClassNP/Reductions.lean:146–152` | Pass | Forward direction uses hardness and membership in P; reverse direction transports NP membership across class equality. |

### Batch B — 6 targets

| Target and source | Verdict | Check |
|---|---|---|
| `MultiTapeTM.toNDTM_runWith`, `TuringMachine/Nondeterministic.lean:234–241` | Pass | Induction generalizes the starting configuration; the cons case compares first-step decompositions, with choices ignored definitionally. No word reversal. |
| `NDTM.HaltsWithin.mono`, `TuringMachine/Nondeterministic.lean:183–191` | Pass | Prefix has exactly the old length; halting at that prefix absorbs every remaining choice. |
| `FinNDTM.AcceptsWithin.mono`, `ClassNP/NTIME.lean:103–109` | Pass | Padding length is exactly the budget difference; absorption preserves halting and the entire singleton output. |
| `NTIME.mono`, `ClassNP/NTIME.lean:143–163` | Pass | Both acceptance directions and all-branch halting checked; backward transfer is detailed above. |
| `DTIME_subset_NTIME`, `ClassNP/NTIME.lean:177–202` | Pass | Every choice word simulates the deterministic run. A padded false word witnesses acceptance for members; nonmembers have output `[false]`, contradicting `[true]`. |
| `NTIME_eq_empty_of_exists_zero`, `ClassNP/NTIME.lean:213–220` | Pass | Uses an actual input of the vanishing length and the empty choice word, forcing `some q₀ = none`; includes input length zero. |

### Batch C — 6 targets

| Target and source | Verdict | Check |
|---|---|---|
| `P_subset_NP`, `ClassNP/NP.lean:93–96` | Pass | Coefficient and degree zero; length zero forces the empty certificate, and the original language is the verifier. |
| `compl_mem_P`, `ClassNP/CoNP.lean:72–108` | Pass | Timed composition and explicit budget absorption checked above. |
| `mem_coNP_iff_forall`, `ClassNP/CoNP.lean:122–139` | Pass | Negates the exact-length certificate quantifier in both directions, complements the verifier using proved P closure, and preserves coefficient and degree. Classical quantifier negation is explicit. |
| `P_subset_NP_inter_coNP`, `ClassNP/CoNP.lean:145–147` | Pass | Applies `P_subset_NP` to the language and its polynomial-time complement. |
| `NP_eq_coNP_of_P_eq_NP`, `ClassNP/CoNP.lean:154–163` | Pass | Both inclusions use the assumed equality and complement closure; the reverse inclusion explicitly eliminates the double complement. |
| `P_subset_EXP`, `ClassNP/EXP.lean:81–90` | Pass | `n^c < 2^(n^c)` implies the stated majorization; multiplying the old time constant by two gives the required `DTIME` witness, including `n = 0` and `c = 0`. |

### Batch D — 7 targets

| Target and source | Verdict | Check |
|---|---|---|
| `eval_congr_of_lt_numVars`, `Formulas/CNF.lean:131–143` | Pass | Each occurring variable contributes its successor to the flattened maximum; both literal polarities are covered before applying evaluation congruence. |
| `exists_cnf_boolFun`, `Formulas/CNF.lean:252–256` | Pass | A concrete truth-table construction satisfies all four conjuncts via proved helpers. At arity zero, the construction is `[]` for true and `[[]]` for false. |
| `parse_serialize`, `Formulas/CNFEncoding.lean:266–269` | Pass | Instantiates the genuinely fuel-uniform suffix lemma at exact serialized length and empty suffix. |
| `decode_serialize`, `Formulas/CNFEncoding.lean:276–277` | Pass | Reduces total decoding after the parser round trip; no fallback ambiguity. |
| `numVars_decode_le`, `Formulas/CNFEncoding.lean:460–473` | Pass | Bounds every successful exact parse; both failure modes use the zero-variable fallback. |
| `evalDNF_dual`, `Formulas/DNF.lean:90–104` | Pass | Literal and clause inductions implement Boolean De Morgan laws. Both empty-list cases are definitional equalities. |
| `dnfTautology_dual_iff`, `Formulas/DNF.lean:113–116` | Pass | Pointwise duality turns universal DNF truth into the negation of existence of a satisfying CNF assignment. |

## All 19 private helpers

The source inventory gives **one private lemma, 16 private theorems, and two private definitions**. Batch A contributes one; batch D contributes 18; B and C contribute none. All 18 source line numbers in batch D's helper table match the attachments.

| # | Helper and source | Contract/proof assessment |
|---|---|---|
| 1 | `comp_time_bound`, `ClassNP/PolyTime.lean:106–133` | Pass. Arbitrary natural parameters; independent derivation above. |
| 2 | `le_foldr_max_of_mem`, `Formulas/CNF.lean:112–120` | Pass. Empty-list membership is impossible; head and tail use the corresponding maximum inequalities. |
| 3 | `foldr_max_le_of_forall`, `Formulas/CNF.lean:146–152` | Pass. Empty fold is zero; inductive maximum is bounded precisely when both arguments are bounded. |
| 4 | `falsifyingClause`, `Formulas/CNF.lean:155–156` | Pass. `List.ofFn` enumerates each finite variable with the opposite polarity. |
| 5 | `falsifyingClause_eval_false`, `Formulas/CNF.lean:160–174` | Pass. All literals fail iff each assignment bit equals the excluded bit. Function extensionality handles the finite assignment equality; arity zero is included. |
| 6 | `falsifyingCNF`, `Formulas/CNF.lean:177–178` | Pass. Maps the excluding-clause constructor over precisely the falsifying assignments in the finite universe. Noncomputability is compatible with this existential target; no efficient constructor is claimed. |
| 7 | `falsifyingCNF_numVars`, `Formulas/CNF.lean:181–190` | Pass. Every flattened successor is `i.val + 1 ≤ ℓ` from `i.isLt`; maximum-fold bound includes empty data. |
| 8 | `falsifyingCNF_length`, `Formulas/CNF.lean:193–199` | Pass. Filtering cannot increase cardinality; the finite function space has cardinality `2^ℓ`. |
| 9 | `falsifyingCNF_width`, `Formulas/CNF.lean:202–206` | Proof passes. Every mapped clause has length `ℓ`, hence width at most `ℓ`. New docstring should match the weaker exported contract: E1-1. |
| 10 | `falsifyingCNF_eval`, `Formulas/CNF.lean:213–230` | Pass. A false clause identifies the restricted assignment with a listed falsifier; conversely that falsifier supplies a false clause. Boolean cases convert equivalence of falsity to equality. |
| 11 | `takeTrues_replicate`, `Formulas/CNFEncoding.lean:169–176` | Pass. Induction preserves the leading false delimiter and every following bit. |
| 12 | `parseLit_serializeLit`, `Formulas/CNFEncoding.lean:179–182` | Pass. Applies the unary-run identity to the delimiter/polarity/suffix sequence. |
| 13 | `parseClause_serializeClause`, `Formulas/CNFEncoding.lean:191–214` | Pass. Every fuel at least clause serialization length; induction generalizes fuel, with exact suffix threading. |
| 14 | `parseClauses_serialize`, `Formulas/CNFEncoding.lean:223–249` | Pass. Every adequate fuel; separate adequacy obligations for the clause and tail are discharged. |
| 15 | `takeTrues_length`, `Formulas/CNFEncoding.lean:280–289` | Pass. Induction partitions total length into counted true bits and returned remainder, including strings with no false delimiter. |
| 16 | `parseLit_length`, `Formulas/CNFEncoding.lean:293–303` | Pass. Successful pattern match forces a positive run plus two additional bits; exact consumption is variable index plus three. |
| 17 | `parseClause_bounds`, `Formulas/CNFEncoding.lean:312–364` | Pass. Success-only invariant includes both remainder domination and each variable contribution plus final remainder; zero-fuel closing markers handled correctly. |
| 18 | `parseClauses_bounds`, `Formulas/CNFEncoding.lean:373–427` | Pass. Composes clause and tail bounds without losing the final suffix. |
| 19 | `numVars_le_of_literal_bounds`, `Formulas/CNFEncoding.lean:431–445` | Pass. Converts literalwise successor bounds to the flattened maximum, with its local fold induction proved directly. |

No helper merely renames an audited target and assumes it. The four `falsifyingCNF_*` lemmas establish distinct properties of an explicit witness; the parser helpers prove stronger recursive invariants from the definitions. Their use makes the final public proofs short without moving an unproved obligation out of view.

Every listed helper is used along a visible dependency path to one of the 27 printed targets. Therefore, **if the integrated axiom prints were generated from this source tree as attested**, their absence of `sorryAx` also covers these helper paths. This observation is not a substitute for independently generating the prints.

The maximum-fold upper bound is a reasonable shared-utility candidate already flagged by D3. Its companion `le_foldr_max_of_mem` is similarly general and may be considered in that same later promotion. Neither needs a public API to complete this epoch; the other helpers have clear local consumers. The local duplicate inside `numVars_le_of_literal_bounds` is an independently proved `have`, not a cross-file reference to an inaccessible private theorem.

## Attestation and report reconciliation

### Maintainer attestations

| Pack item | Independently checked from supplied material | Remaining attestation |
|---|---|---|
| 1. Archives/provenance | All four reports name the same full base hash. Their reported commit counts sum to `1 + 6 + 1 + 1 = 9`. | Archive checksum totals `26/26, 26/26, 22/22, 18/18`; actual replay, integrated revision identities, and authorship. Different delivered/integrated commit hashes are consistent with patch application and are not themselves a defect. |
| 2. Statement freeze | The current proofs fit their supplied statements. The disclosed reduction-proof appendix is present at `Reductions.lean:93–97`. | Exact deleted-line inventory, byte preservation, statement freeze relative to base, and the rule-2 authorization. No base or integration diff is attached. |
| 3. Declaration drift | Exactly 19 explicit private declarations, with the stated distribution and names. All helper-report line references match. | No public additions/removals relative to base; `succ_pow_le`'s historical presence in the absent imported source. |
| 4. Fresh elaboration | Module order contains 53 distinct modules and includes every supplied source. Every import edge visible in the ten sources points to an earlier listed project module. `59 − 27 = 32`. | Actual 53-module successful fresh sweep, zero compiler errors, and the 32 warning occurrences. The full sweep log is absent. |
| 5. Axioms | Exactly 27 distinct target entries: 16 standard triples, 10 `[propext, Quot.sound]` pairs, one axiom-free target; no `sorryAx`. All names match the 27 filled declarations. | Generation of the log from fresh oleans matching the attached source. |
| 6. Policy | No explicit unsafe declaration, axiom declaration, `native_decide`, implementation override, or custom elaborator appears in the supplied Lean code. All new helpers have docstrings. | Style-checker outputs, baseline warning preservation, and verbatim preservation of original prose/attributions. E1-1 concerns a new docstring, not the preservation claim. |

There are **five** explicit remaining `sorry` bodies in the ten attachments: `HALT_NPHard`, `HALT_not_mem_NP`, `mem_NP_iff_exists_length_le`, `NP_subset_EXP`, and `EXP_subset_NEXP`. These are the disclosed out-of-scope admissions. Five is the inventory of the supplied files, **not** an alternative claimed count for the 53-module tree. No filled target or new helper contains an explicit admission.

### Agent-specific claims

| Report | Cross-check result |
|---|---|
| A | All eight proof-route descriptions match the source. Factoring the reduction proof through timed `PolyTimeComputable.comp` is sound and documented. The report's standalone `sorryAx` occurrences for the two collapse targets are compatible with the integrated clean log: the visible `P_subset_NP` fill closes that dependency. `59 − 8 = 51` is arithmetically correct. The claimed transitive-dependency traversal itself is not attached. |
| B | All six routes match, including exact-output preservation in truncation. Its five proper-subset axiom footprints agree with the integrated log. Staged module counts match the order: positions 32–53 contain 22 modules; positions 41–53 contain 13. `59 − 6 = 53`. First-attempt success, per-edit scheduling, fresh outputs, and the exact insertion count remain report-only evidence. |
| C | Empty certificates, complement composition, quantifier negation, and exponential absorption are exactly the visible routes. Its three named residual admissions are present. All six integrated axiom entries are standard triples, matching the report. `59 − 6 = 53`. The claimed source freeze and procedural execution are not independently reproducible here. |
| D | All seven proof-route descriptions match, including both fuel strengthenings and the additive bounds. There are exactly 18 helpers: 16 theorems and two definitions, one noncomputable. Every reported helper location is correct. The six proper-subset footprints agree with the log. `59 − 7 = 52`; all three owned formula files contain no admissions. Its new-docstring claim has the small contract-description qualification in E1-1. |

The reports' standalone totals are not meant to add to the integrated residual total. Each subtracts only its own fills from the common 59-admission base. The disjoint fill counts sum to `8 + 6 + 6 + 7 = 27`.

### Maintainer dispositions

| Disposition | Verdict |
|---|---|
| D1: accept subsets of the standard axiom triple | Accept. An upper bound on allowed axioms is the appropriate condition; missing `Classical.choice` or having no axioms is not a defect. All 11 proper-subset cases are accounted for. |
| D2: branch-name differences | Accept on the supplied reports and integration attestation. B/C/D explicitly report a later user branch instruction; a different branch label does not affect these proofs. No independent branch history was inspected. |
| D3: defer shared maximum-fold lemma | Accept. The duplicate proofs are complete and local; deferral creates no unproved dependency. Consider the companion membership bound during the same later utility review. The claimed backlog entry is not attached. |

## Supplemental finite checks

Independent Python models were transcribed from the supplied parser/serializer and Boolean-formula definitions. They were used to challenge boundary-case readings, **not** as Lean kernel verification or as proofs of the universal claims. All checks passed:

| Check | Exhaustive finite domain / count |
|---|---|
| Arbitrary bit strings and decoder variable bound | All 8,191 strings of lengths 0 through 12. |
| Successful parser consumption/bounds | For each such string, every fuel from zero through its length plus two: 114,687 string/fuel pairs. Checked 4,072 successful literal parses, 96,562 successful clause parses, and 86,797 successful formula parses. |
| Suffix-carrying round trips | Variables 0–2, either polarity, clauses of width 0–2, formulas with 0–2 clauses, every suffix of length 0–3, fuel equal to fragment length or greater by one/four: 87,120 clause/formula round-trip cases. |
| Truth-table construction and De Morgan evaluation | All 278 Boolean truth tables of arities 0–3; 2,122 table/assignment pairs. Checked clause count, variable bound, exact constructed width, evaluation, and dual evaluation. |
| Composition inequality | 45,000 cases: `a,C,C'` from 0–4, `c,c'` from 0–5, `n` from 0–9. |
| Complement budget normalization | 7,500 cases: `a,b,C` from 0–4, `d` from 0–5, `n` from 0–9. |

The universal reasoning for the priority obligations is given above; the bounded computations only supplement it. No upstream AB09 statement gate was reopened, no source was repaired during this audit, and no GitHub interaction was used.

## Notation glossary

- `ℕ`: natural numbers including zero; powers use the natural-number convention, including exponent zero.
- `|s|`: list length; `[]`: empty list; `::`: prepend one element; `++`: list concatenation; `.take` and `.drop`: prefix and remaining suffix.
- `a,b,C,C',A`: nonnegative constant coefficients in the arithmetic sections; `c,c',d`: natural exponents. In the composition derivation only, `d = max(c,cc')`; in the complement derivation, `d` is the original degree. `n`: input length; `k`: decremented parser fuel.
- `x,r,s,t,u,w`: bit strings when used in parser/run calculations; in the truncation subsection only, `t = c T₁(|x|)` and `t' = c T₂(|x|)` are budgets. `T₁,T₂`: the two time-bound functions.
- `C,D`: clauses in formula/parser sections, rather than numerical coefficients; `φ,ψ`: formulas; `(v,b)` and `(j,β)`: literals, consisting of a natural variable index and a Boolean polarity; `ℓ`: Boolean-function arity; `i : Fin ℓ`: an index smaller than `ℓ`.
- `serializeLit`, `serializeClause`, `serialize`, `parseLit`, `runWith`, `initCfg`, `some`, `none`, `numVars`, and `WidthAtMost`: the functions, constructors, and predicates named in the supplied source. `N` denotes the nondeterministic machine's underlying run interface in the truncation equations.
- `P`, `NP`, `coNP`, `EXP`, `DTIME`, `NTIME`, and language complement: the frozen supplied complexity definitions; `f` and an assignment have their source-defined Boolean-function meanings.
