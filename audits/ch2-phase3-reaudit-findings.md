**Chapter 2, phase 3, round 2 — independent adversarial re-audit**

Intended repository destination: `audits/ch2-phase3-reaudit-findings.md`.
Audited snapshot: the supplied bundle labelled `8b09a184`, branch `complexity/arora-barak-ch1`.
Bundle SHA-256: `6baddbca2c107355d2a87183daf86d818105e0e7875a760e57b9bf0ddb516d6d`.

**Disposition: zero blockers, zero majors, two minors, two notes. The narrow statement-audit gate condition is met.** Both signature repairs are sufficient; the repaired numerical bounds and exact-value cases are correct. The minors concern the new audit-history prose, not the Lean statements. Round-1 certifications and earlier closed gates remain trusted context.

This is a source-level mathematical audit, not a Lean elaboration or proof-completion attestation. The calculations below establish the numerical implications; the quantitative public bridge and the named verifier/reduction machine constructions remain fill obligations. The supplied snapshot does not independently establish historical byte equality or the reported build/lint executions.

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | minor | `AroraBarakChapter2Plan.md:210`; round-2 pack introduction | These are “the chapter's first statement-level repairs.” | The attached `audits/ch2-phase1-resolutions.md`, round-1 repairs at `8660c416`, already records theorem-statement changes: the bounded-certificate equivalence switched to `pairEncode x u`, and `HALT_NPHard` generalized from `EffectiveMachineCode` to `MachineCode`. These were not merely changes to definitions or sketches. | Say “phase 3's two statement-level repairs.” Correct the current plan and record a pack erratum in the resolution record; preserve the issued pack. |
| 2 | minor | `AroraBarakChapter2Plan.md:209`; round-2 resolution table, row 1 | The old claims were “false at every `EffectiveMachineCode`.” | Argument A proves failure for a particular lawful effective scheme, hence falsity of the universally quantified theorem. It does not prove failure for every scheme. The repaired sufficient condition expressly identifies a class of schemes for which membership and completeness hold. | Replace with “false at their stated generality” or “false for some lawful effective schemes.” This is a quantifier correction to prose only. |
| 3 | note | `ClassNP/TMSAT.lean:182`, `TMSAT_mem_NP`; `:240`, `TMSAT_NPComplete` | The added hypothesis restores the polynomial simulation budget. | Derivation A below verifies the actual chosen simulator coefficient and its polynomial majorant. The change is a small sufficient strengthening of the existing interface, not a logically necessary condition on the language. The public `timed_universal` still exposes only an existential coefficient; the sketch explicitly records that limitation. | No further statement repair. In the fill, supply the named public quantitative bridge for one uniform simulator, preserving both success and timeout clauses; do not infer a bound on an arbitrary existential witness. |
| 4 | note | Round-2 pack, attestations 1–4, especially erratum 3 | The corrected comparison establishes the historical freeze claims. | The disclosed filename-versus-stdin error makes the original comparison vacuous. Feeding the actual source through stdin addresses that error. However, this bundle supplies only the current modules, not the old module versions, stripping script, exact rerun command, or comparison/build/lint outputs. Thus the rerun remains a maintainer execution attestation. Current-source inventories and the presence of the phase-2 prose repairs are independently corroborated below. | Retain the disclosure and the separation of source facts from execution claims. For reproducibility, append the exact corrected command and script version, baseline/current refs, nonempty stripped-output counts or hashes, and checked comparison exit statuses to the resolution record. No mathematical reopening of phase 2 follows from this disclosed tooling error. |

**Resolution table checked row by row.** File locations in this table are under `TCSlib/Complexity/` unless otherwise stated.

| Round-1 finding | Current evidence | Assessment |
|---|---|---|
| 1 — membership blocker | `ClassNP/TMSAT.lean:182` has `(hc : PolyBound c.canonizerTime)`. Its sketch gives the coefficient bound and explicitly names the required new public bridge. | Resolved at statement/sketch level. The tagged counterexample is excluded by the added efficiency requirement. |
| 2 — completeness blocker | `ClassNP/TMSAT.lean:240` has the same hypothesis; its sketch passes `hc` to membership and applies hardness to `c.toMachineCode`. | Resolved. No extra condition belongs on the hardness conjunct. |
| 3 — exact unary emissions and missing deadline | `ClassNP/TMSAT.lean:189` gives all three exact-value cases, the zero-certificate false positive, the explicit `D` and `T'`, and both predecessor-exponent instantiations. | Resolved. Derivation B verifies the inequalities at every natural input length. |
| 4 — split parity | `ClassNP/TMSAT.lean:144` rejects even lengths and splits odd length `N` at `(N−1)/2`. | Resolved, including the empty verifier input. |
| 5 — fallback prose | `ClassNP/SAT.lean:26` assigns each language its own fallback predicate and sends malformed inputs to the serialization of the transformed fallback. | Resolved. The width-four example is correctly transcribed. |
| 6 — carrier/encoding guidance | `Formulas/CNF.lean:37` retains the pin rationale; `Formulas/CNFEncoding.lean:41` restricts the polynomial unary-size statement to campaign-produced formulas. The round-2 pack explicitly retains complete syntax validation before evaluation. | Retained as required. The fill must respect that order; no redesign or new hypothesis is needed. |
| 7 — TAUTOLOGY guidance | The new plan row at `AroraBarakChapter2Plan.md:209` records that the phase-4 DNF rendering must be presented as a fragment. | Retained. The carrier choice and phase-4 construction are outside this round. |
| 8 — accounting/evidence | The attached order list, source declarations, imports and admissions agree with the source-verifiable inventory. | Corroborated for this snapshot; historical comparisons and execution claims have the limitations in finding 4. |

The two new plan rows accurately record the mathematical repairs and public-bridge obligation, subject to findings 1–2. Their erratum acknowledges the actual failure mode; the phrase “the corrected recipe is recorded here” currently describes the correction but does not supply a runnable command or its output.

**Changed statements and hypothesis scope.** The two declarations literally assert:

\[
\begin{aligned}
&\forall c:\mathrm{EffectiveMachineCode},\quad
  \mathrm{PolyBound}(c.\mathrm{canonizerTime})
  \Longrightarrow \mathrm{TMSAT}(c.\mathrm{toMachineCode})\in\mathrm{NP},\\
&\forall c:\mathrm{EffectiveMachineCode},\quad
  \mathrm{PolyBound}(c.\mathrm{canonizerTime})
  \Longrightarrow \mathrm{NPComplete}(\mathrm{TMSAT}(c.\mathrm{toMachineCode})).
\end{aligned}
\]

`ClassNP/PolyTime.lean:63` defines the added condition as

\[
\exists a,d\in\mathbb N\;\forall r\in\mathbb N,\qquad
c.\mathrm{canonizerTime}(r)\le a(r+1)^d.
\]

This is sufficient despite `PolyBound` being only numerical. `Encoding.lean:440` already supplies an actual finite machine computing `serialize ∘ decode` within that bound. The verifier need not compute `canonizerTime`; it executes that machine, and the explicit polynomial majorant supplies the analysis. Thus the phase-1 defect of extracting information from an arbitrary certificate-length function does not recur.

The remaining ten phase-3 statements divide exhaustively as follows:

| Statements | Reason no additional canonizer hypothesis is needed |
|---|---|
| `eval_congr_of_lt_numVars`, `exists_cnf_boolFun` | Formula-level facts; no machine-code scheme is involved. |
| `parse_serialize`, `decode_serialize`, `numVars_decode_le` | The fixed CNF serialization/parser, independent of `MachineCode`. |
| `SAT_mem_NP`, `SAT3_mem_NP`, `SAT_reducible_SAT3` | Explicit CNF parsing, evaluation and transformation machines; no input-supplied machine code is interpreted. |
| `timeConstructible_poly` | Arithmetic on the input length; no representation scheme occurs. |
| `TMSAT_NPHard` | For each source language, the reduction hardwires one finite string `c.encode M''`. It never computes a variable-code decoder, canonizer, or encoder. `MachineCode.decode_encode` is sufficient. |

The general `TMSAT` definition likewise needs no strengthening. The added condition is minimal in the practical sense of adding one condition on the existing interface rather than introducing a new representation interface. It is **not claimed to be the weakest possible semantic condition**: increasing an effective scheme's recorded clock from `canonizerTime(n)` to `canonizerTime(n)+2^(n+1)` preserves its canonizer correctness by time monotonicity and leaves its language unchanged, while destroying `PolyBound` for that recorded clock. A polynomial-time alternative canonizer could also suffice.

**Derivation A — Argument A and the repaired uniform budget.**

The counterexample transcription retains its essential data: the one-bit tagged branch decodes `[true] ++ z` to a one-step machine outputting the characteristic bit of a decidable language `A ∉ EXP`. Its query has `x=[]`, certificate length zero, and deadline one. Pairing injectivity and completed-output uniqueness give

\[
\begin{aligned}
g(z)&=\operatorname{pairEncode}([\mathrm{true}]\mathbin{++}z,
       \operatorname{pairEncode}([],\operatorname{pairEncode}([],[\mathrm{true}]))),\\
|g(z)|&=2|z|+9,\\
g(z)\in\mathrm{TMSAT}(c_A)&\iff z\in A.
\end{aligned}
\]

This is the same obstruction as round 1, with no changed time or certificate convention. The zero-tag branch preserves the base encoding and its arbitrary-true-padding law. Under the new hypothesis, the polynomial simulator below would decide these instances in NP and hence in EXP, contradicting `A ∉ EXP`. The counterexample therefore cannot satisfy the new premise.

For the budget, use exactly the round-1 local quantities:

\[
\begin{gathered}
r=|\alpha|,\quad H=c.\mathrm{canonizerTime}(r),\quad
L=|(c.\mathrm{decode}(\alpha)).\mathrm{serialize}|,\\
N=(c.\mathrm{decode}(\alpha)).\mathrm{numStates}+1,\quad
h=|\mathrm{Nat.bits}((c.\mathrm{decode}(\alpha)).\mathrm{numStates})|,\quad
q=(c.\mathrm{decode}(\alpha)).\mathrm{tm}.q_0.\mathrm{val}.
\end{gathered}
\]

The concrete witness in `Universal.lean:2821`, together with `timedStartupBound` at `:2666` and `UniversalBlock.lean:750`, gives

\[
\begin{aligned}
C_\alpha
&=(3r+H+L+2h+2q+16)+(3L+5N+20)+14\\
&=3r+H+4L+2h+2q+5N+50.
\end{aligned}
\]

Here the required size bounds follow from the actual serialization, not from a complexity assumption about decoding:

1. `Encoding.lean:393` serializes a doubled binary header and the unary initial state, hence
   \[
   2h+2+q+1\le L,\qquad h\le L,\quad q\le L.
   \]
2. There are nine transition records per state. Each record has four two-bit fields and a nonempty successor-state field (`Encoding.lean:381`), so
   \[
   81N\le L,\qquad N\le L.
   \]
3. The canonizer completes this length-`L` output within `H` steps. `MultiTapeTM.output_length_le` (`Finite.lean:88`) yields
   \[
   L\le H.
   \]

Consequently,

\[
\begin{aligned}
C_\alpha
&\le3r+(1+4+2+2+5)H+50\\
&=3r+14H+50\\
&\le3r+14a(r+1)^d+50\\
&\le(14a+53)(r+1)^{\max(d,1)}.
\end{aligned}
\]

For a valid TMSAT input `y`, writing `m=|y|`, the three nested pairings give

\[
m=2|\alpha|+2|x|+2n+t+6,
\qquad r,n,t\le m.
\]

Therefore the simulated run satisfies

\[
C_\alpha(t+1)^2
\le(14a+53)(m+1)^{\max(d,1)+2}.
\]

All constants are uniform over the code strings for the fixed scheme. Polynomial parsing, clock conversion, input assembly, relocation and output capture preserve polynomial time in the actual verifier-input length `2m+1`.

The new public bridge must expose this bound for **one simulator chosen before the code and input**, with both clauses of `timed_universal`. One suitable general bridge uses the bound

\[
\bigl(3|\alpha|+14c.\mathrm{canonizerTime}(|\alpha|)+50\bigr)(t+1)^2
\]

directly and therefore need not import `PolyBound` into Chapter 1. Its proof can reuse the concrete witness above and time monotonicity. The current public existential alone does not imply the numerical bound on its arbitrary witness. The repaired sketch makes this distinction explicitly; accepting the statement-phase repair does not certify that bridge as already available.

**Derivation B — exact certificate length and deadline.**

Let the NP witness use exact certificate length

\[
Q(n)=C_0(n+1)^{c_0}.
\]

The three emission cases exhaust all natural parameter choices:

| Parameters | Exact output length | Use of `timeConstructible_poly` |
|---|---|---|
| `C₀=0` | Zero, including when `c₀=0` | None; emit the empty run. |
| `C₀>0`, `c₀=0` | The fixed constant `C₀` | None; use finite control. |
| `C₀>0`, `c₀>0` | `C₀(n+1)^c₀` | Coefficient `C₀`, exponent parameter `c₀−1`, and the proof `0<C₀`. Since `(c₀−1)+1=c₀`, the resulting value is exact. |

In particular, the first two cases make no false time-constructibility claim about a zero or constant function. At `C₀=c₀=0`, `L=V={[true]}` and `x=[]`, the original only certificate is `[]` and is rejected. Replacing its length by `n+1` permits `[true]` and accepts. The repaired sketch correctly uses this to prohibit majorizing `Q` while keeping the same wrapper.

The wrapper is total: reject malformed pairs, and on `pairEncode x u` decide `V` on `x ++ u`, with completed verdict capture. Thus the audited total-function normalization applies. Choose a wrapper time bound `B(s+1)^e` with `B,e≥1`, and let `K` be its quadratic normalization multiplier. On the relevant inputs,

\[
s=2n+2+Q(n).
\]

Use the sketch's choices

\[
r=\max(1,c_0),\qquad
D=(K+1)(B+1)^2(C_0+3)^{2e},\qquad
T'(n)=D(n+1)^{2er}.
\]

For every `n≥0`, since `r≥1` and `r≥c₀`,

\[
\begin{aligned}
s+1
 &=2n+3+C_0(n+1)^{c_0}\\
 &\le3(n+1)+C_0(n+1)^{c_0}\\
 &\le(C_0+3)(n+1)^r.
\end{aligned}
\]

Also `(s+1)^e≥1`, so

\[
\begin{aligned}
K\bigl(B(s+1)^e+1\bigr)^2
&\le(K+1)\bigl((B+1)(s+1)^e\bigr)^2\\
&=(K+1)(B+1)^2(s+1)^{2e}\\
&\le(K+1)(B+1)^2(C_0+3)^{2e}(n+1)^{2er}\\
&=T'(n).
\end{aligned}
\]

There is no missing additive term at zero: when `n=0`, the first inequality is equality `s+1=C₀+3`. Every factor in `D` is positive, and `2er≥2`. Therefore

\[
(2er-1)+1=2er,
\]

and `timeConstructible_poly D (2er−1)` computes precisely the chosen deadline's binary value. The displayed Lean applications in the sketch suppress the required positivity proof arguments; those proofs are supplied by the cases above, not by an extra assumption.

Binary countdown emits the exact unary runs in polynomial time. With `α₀` the fixed code of the normalized wrapper, the reduction's length is exactly

\[
|f(x)|=2|\alpha_0|+2|x|+2Q(|x|)+T'(|x|)+6.
\]

Only the deadline is enlarged. The wrapper has a unique completed verdict, so increasing the deadline cannot turn its completed rejection into acceptance. The normalization bound supplies acceptance by the chosen deadline for every accepting source witness; output uniqueness excludes false positives. With tuple injectivity,

\[
\begin{aligned}
f(x)\in\mathrm{TMSAT}(c)
&\iff\exists u,\ |u|=Q(|x|)\ \land\ x\mathbin{++}u\in V\\
&\iff x\in L.
\end{aligned}
\]

Thus Argument B is faithfully transcribed, and neither predecessor exponent has an off-by-one defect.

**Parity and fallback.** For membership, a verifier input of length `N` has a legal split exactly when

\[
N=m+(m+1)=2m+1,
\qquad m=(N-1)/2.
\]

Rejecting even `N`, including zero, is correct. On odd `N`, the suffix has length `m+1`, enough to recover any declared `n≤m` certificate by taking its first `n` bits. At deadline zero the existing no-zero-step-computation lemma still makes every TMSAT instance negative.

For a malformed CNF string and fixed fallback `F`, SAT membership is `F.Satisfiable`; SAT3 membership additionally requires `F.WidthAtMost 3`. A single clause of four repeated positive literals is satisfiable but fails that width test. The reduction nevertheless works because its output serializes the transformed fallback: the transformation always has width at most three and is equisatisfiable with `F`. For the actual fallback `[]`, the transformation fixes it and both sides accept. The repaired prose describes exactly these facts.

**Attestation assessment and independent checks.**

| Attestation | Independently established here | Evidence limit |
|---|---|---|
| 1 — scope and drift | The two current theorem signatures have precisely the stated new premise; hardness remains at `MachineCode`; the `PolyTime` import is present. All twelve phase-3 signatures agree semantically with the round-1 restatements after these two repairs. | The exact commit file list, byte identity of unchanged files, comment-only SAT diff, and verbatim preservation of the prior report cannot be established from a single current snapshot. |
| 2 — elaboration/admissions | 62 uniquely named attachments; 48 ordered campaign modules plus the root; all campaign imports respect the supplied order. Independent nested-comment stripping finds 45 source `sorry` occurrences, distributed as 19 phase-1, 14 phase-2, and 12 phase-3, the last split 2/3/3/4. The phase-3 source has 16 definitions and 12 theorem statements. | Source admissions are not compiler warning counts. No Lean executable, dependency checkout, fresh oleans or sweep logs were supplied here; no elaboration run is claimed. |
| 3 — erratum | The described original invocation cannot verify equality when both outputs are empty. The current phase-2 texts contain the promised prefix-shaped all-branch reading and the polynomial pre-validation bound, so no contradiction to the repair narrative appears. | Correct stdin delivery repairs this specific flaw, but actual historical equality across `e1e68ebd..487f58cb`, or across this round's baseline and repair, remains an asserted rerun. The disclosed correction restores a coherent maintainer-side basis **if executed as stated**, not independently reproduced evidence in this bundle. |
| 4 — policy/lint | The repaired statements retain statement prose and detailed sketches; imports are precise; the new public-bridge obligation is explicit. | The reported zero lint FAILs and six unchanged Chapter-1 WARNs were not reproduced. |

To guard specifically against the disclosed failure mode, my current-source scanner rejects unterminated comments and asserts that every stripped module contains non-whitespace tokens. It does **not** compare a reconstructed or guessed historical baseline.

Independent integer checks additionally covered **43,680** deadline-parameter combinations, including `n=0`, `C₀=0`, `c₀=0`, `c₀=1`, and the harmless `K=0` boundary; **1,296** nested-tuple length/split cases; and **2,465** coefficient-bound cases. All passed. These finite checks corroborate the algebraic derivations above; they are not Lean proofs or substitutes for the missing execution evidence.

**Notation glossary.** `|s|` is string length; `++` is concatenation; `∈` is membership; `ℕ` denotes the natural numbers including zero; `Nat.bits` is little-endian binary encoding. `c` is a code scheme; `α` is an input code; `M''` is the normalized wrapper and `α₀` its hardwired code; `x` is a source input; `u` is a certificate; `y` is a TMSAT tuple; `m=|y|`; `n` is a certificate length in Derivation A and the source-input length in Derivation B; `t` is the simulation deadline. `a,d` are polynomial-majorant constants. In Derivation A, `r,H,L,N,h,q,C_α` are the code length, canonizer budget, serialization length, state count, header bit length, initial-state index and simulator coefficient defined there; `A,c_A,g,z` are the diagonal language, tagged scheme, query map and an arbitrary binary input. In Derivation B, `L,V` are the source and verifier languages, `C₀,c₀,Q` specify the exact certificate length, `s,B,e,K` specify wrapper length/time and normalization, and `r,D,T',f` are the auxiliary exponent, deadline coefficient, deadline and reduction. In the parity paragraph, `N` instead denotes total verifier-input length. `F` is a fixed CNF fallback.
