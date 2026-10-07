**Chapter 2, Phase 1, round 2 — independent adversarial re-audit**

Audited material: the supplied bundle labelled commit `8660c416`, branch `complexity/arora-barak-ch1`. Intended destination: `audits/ch2-phase1-reaudit-findings.md`.

**Disposition: the gate remains open. Blockers: none (0). Majors: 3. Minors: 2. Notes: 2.** The repaired definitions defeat Arguments A, B, and D in their original applications. I found no false Lean theorem statement. However, the reverse Exercise-2.1 sketch chooses an inadmissible certificate-length formula, the enumerator still omits an essential output-isolation obligation, and the claimed necessity of effectivity for HALT nonmembership is false.

These are mathematical and source-level findings, not kernel-checked proof submissions. I checked the declarations separately from their explanatory prose and inspected the relevant Chapter-1 interfaces and implementations. The native parser, enumerator, and control-transform correctness lemmas remain fill obligations. I did not re-audit Chapter-1 mathematics or resolve its human-reserved design questions.

The bundle contains 40 campaign Lean modules **plus** `TCSlib.lean`, both plans, policy, and the two earlier audit documents. It does not contain the parent source tree, Git metadata, verification scripts/results, pinned dependencies, or the published textbook pages. I consulted the [authors’ January 2007 draft, Definition 2.1](https://theory.cs.princeton.edu/complexity/book.pdf#page=56): it uses a polynomial certificate-length function and a polynomial-time verifier. This supports the intended interpretation, but does not certify the 2009 edition’s exact wording, footnote 4, exercise wording, or numbering. Published item numbers below are the pack’s citations. **No conclusion relies on remembered exact textbook wording.** The monomial formulas are a normalization, not literally every polynomial permitted by that definition.

The uploaded bundle’s SHA-256 is `1d698337867431a1f77583ce489dc7f2aba72d15ef6de7af0ff626c6dc1ae73a`.

In source references below, `ClassNP/` abbreviates `TCSlib/Complexity/ClassNP/`. Line numbers refer to the supplied file sections, with bundle separators removed.

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | major | `ClassNP/NP.lean:110` · `mem_NP_iff_exists_length_le`, reverse sketch | The proposed padded length supplies a witness for the repaired `NP`. | The sketch chooses `C(n+1)^c + 1`; `NP` permits only `C′(n+1)^c′`. For `C=c=1`, matching at `n=0` forces `C′=2`, while matching at `n=1` requires `2·2^c′=3`, impossible. This refutes the proposed witness, **not the theorem**. | Use exact length `(C+1)(n+1)^c`; recover the split using that formula and retain the check against the original `C(n+1)^c`. The derivation below discharges both directions and the boundary cases. |
| 2 | major | `ClassNP/EXP.lean:100` · `NP_subset_EXP`, enumeration sketch; resolution row 5 | The named native-machine obligations cover the verifier loop. | The list names work-region reset but omits interception of verifier emissions and its halting transition. Round 1 explicitly required buffering emissions. With width 1 and verifier “input ends in `true`,” successive candidates produce `[false]`, then `[true]`; forwarding them produces `[false,true]`, violating `DecidesInTime`’s singleton output contract. Resetting work tapes cannot erase output. | Name a verifier-call simulation that captures its bit, suppresses its physical emissions, and redirects its halt to the loop controller. Maintain empty real output until the final answer; reset simulated state, heads, work region, and captured bit between calls. Include these facts in the timed invariant. |
| 3 | major | `ClassNP/Reductions.lean:160` · `HALT_not_mem_NP` docstring; resolution row 11 and plan’s repair entry | Effectivity is mathematically necessary because a trivial-machine decoding scheme makes HALT decidable. | Constant decoding violates `decode_encode`. Even “fallback on every non-image string” violates `decode_encode_pad` on proper padded codes. More strongly, a direct halting diagonalization proves undecidability for **every lawful `MachineCode`**, using the same total-normalize-then-change-control construction as the hardness sketch. | Remove the purported counterexample and necessity claim. Keeping the current, weaker signature is legitimate to reuse the existing effective-scheme theorem; describe that as an API/proof-route restriction. Alternatively add the direct diagonal lemma and generalize nonmembership. No alteration of frozen Chapter-1 statements is required for the minimal fix. |
| 4 | minor | `AroraBarakChapter2Plan.md` · §2 and earlier §6 decision rows | The plan consistently describes the repaired foundations. | §2 still specifies an arbitrary “polynomially bounded certificate length,” says the language abstraction sidesteps splitting, and describes normalization by a majorant. An earlier §6 row still describes `NEXP` using `ExpBound`. The final decision row records the repair, but these earlier passages remain unmarked current instructions. | Update §2 and mark the obsolete decision rows superseded. State the explicit formulas, the computable unique split for exact concatenation, and paired bounded certificates. |
| 5 | minor | Re-audit pack · attestation 3 | Five listed changes leave “all other 14 statements” unchanged. | The list contains **2 definitions and 3 theorem signatures**. Among 19 theorems, 16 signatures remain; among 10 definitions, 8 remain. Among all 29 declarations, 24 remain. The number 14 mixes categories. | Separate definition changes from theorem-signature changes and correct the counts. Supply parent/current declarations for an actual ordered drift check. |
| 6 | note | `NP`, `NEXP`, `mem_coNP_iff_forall`, bounded characterization, `HALT_NPHard` | The old statement-level counterexamples still obstruct these repaired formulas. | They do not. Fixed finite parameters eliminate the arbitrary length selector; pairing breaks Argument B’s verifier-subset inference; Argument D loses its assertion that its diagonal language belongs to NP. The hardness construction is legal. | Retain these statement repairs. Findings 1–3 concern remaining sketches/exposition, not counterexamples to their Lean conclusions. |
| 7 | note | `TCSlib.lean:26`; `TCSlib/Complexity/ClassNP.lean`; attestations 1–4 | Root export and repository verification are fully established. | The root import and all five facade imports are present. Admission counts and local import relationships reproduce from source. Commit provenance, byte-identical Chapter-1 history, elaboration, axiom footprints, full-root compatibility, and lint results do not reproduce from this attachment alone. | Retain the export. Keep those unverified claims explicitly maintainer attestations and attach the relevant diff/build/lint evidence at the next gate. |

The resolution table checks out as follows; “verified” here describes the supplied source, not an independently authenticated Git delta.

| Round-1 finding | Resolution check against the repaired source |
|---|---|
| 1 — arbitrary length functions | **Verified.** `NP`, the coNP characterization, and `NEXP` quantify `C,c` before all inputs and use exactly the advertised formulas. Neither numerical helper occurs in a class definition. `PolyBound` explicitly disclaims computability/monotonicity of its argument; the EXP module labels `ExpBound` a numerical helper. |
| 2 — bounded concatenation/padding | **Statement repair verified; sketch incomplete.** The bounded side uses `pairEncode x u`. Split-first stripping, marker-free rejection, and the original-bound check are present. Finding 1 above is the remaining normalization error. |
| 3 — HALT hardness false for the old class | **Verified as a statement repair.** Argument D no longer establishes a counterexample, and the generalized fixed-code construction works. |
| 4 — untimed composition used for timing | **Verified.** Both `compl_mem_P` and `mem_P_of_polyTimeReducible` use `computesFunInTime_comp`, identify the total indicator function, and name explicit-budget monotonicity. |
| 5 — private/inapplicable enumeration API | **Partly verified.** Polynomial evaluation, fixed-width overflow, input/candidate retention, work-region reset, and a timed loop invariant are named; `counterInc` is correctly demoted to a template. The old report’s emission-buffer requirement was omitted: finding 2. |
| 6 — normalizing a divergent searcher | **Verified.** Normalization precedes divergence; the control lemma and fixed-prefix machine are explicitly new obligations. The relevant exact hypotheses are checked below. |
| 7 — composition degree | **Verified.** `max c (c*c′)` covers the first computation when `c′=0`. |
| 8 — monotonicity attribution | **Verified.** Only the majorant is asserted monotone for `PolyBound`; exponential padding is nondecreasing, and adding `n` makes the total length strictly increasing, including degree zero. |
| 9 — stale API names | **Verified.** The module advertises `output_length_le`; the identity sketch uses pointwise `ComputesInTime.mono`. |
| 10 — verifier language abstraction | **Verified.** `V ∈ P` supplies a single uniform total decider. It introduces no extra oracle. |
| 11 — `MachineCode` generality | **Partly verified.** Hardness is correctly generalized. The nonmembership signature remains a true conservative restriction, but its new necessity explanation is incorrect: finding 3. |
| 12 — root export | **Verified syntactically.** The root imports the facade, which imports all five children and lists them under `Contents`. Full-root elaboration is unverified. |

For clarity, the five changed declarations literally assert the following. Here and below, $xu$ means concatenation and $Q(n)=C(n+1)^c$, with fixed natural $C,c$.

| Declaration | Literal content |
|---|---|
| `NP` | $L\in NP\iff\exists C,c\in\mathbb N\;\exists V\in P\;\forall x,\ [x\in L\iff\exists u,\ \lvert u\rvert=Q(\lvert x\rvert)\land xu\in V]$. |
| `mem_NP_iff_exists_length_le` | $L\in NP\iff\exists C,c\in\mathbb N\;\exists V\in P\;\forall x,\ [x\in L\iff\exists u,\ \lvert u\rvert\le Q(\lvert x\rvert)\land\operatorname{pairEncode}(x,u)\in V]$. |
| `mem_coNP_iff_forall` | $L\in coNP\iff\exists C,c\in\mathbb N\;\exists V\in P\;\forall x,\ [x\in L\iff\forall u,\ \lvert u\rvert=Q(\lvert x\rvert)\Rightarrow xu\in V]$. |
| `NEXP` | The exact `NP` formula with certificate length $C\,2^{(\lvert x\rvert+1)^c}$, still with $V\in P$ measured on the complete concatenation. |
| `HALT_NPHard` | For every $\kappa:\mathrm{MachineCode}$, every supplied-NP language polynomial-time many-one reduces to $\{s:\operatorname{HALT}(\kappa,s)=\mathrm{true}\}$. |

**Arguments A, B, and D re-fired.** For Argument A, once $C,c,V$ are fixed, the algorithm on $x$ computes $Q(\lvert x\rvert)$, enumerates the finitely many strings of that length, and runs the total verifier. It always terminates. Thus the length value cannot select an undecidable set of lengths. The same termination argument applies to the explicit exponential width in `NEXP`; it does not assert that this exhaustive algorithm runs in EXP.

The original modulo-3 attack becomes particularly transparent:

$$
\exists u,\ \lvert u\rvert=Q(n)\land 3\mid\lvert xu\rvert
\iff 3\mid n+C(n+1)^c.

$$

The right side is computable; indeed its value is periodic with period 3, because

$$
(n+3)+C(n+4)^c\equiv n+C(n+1)^c\pmod 3.

$$

An unusual verifier cannot restore the missing selector: its membership is itself uniformly decided by a finite machine. A very large constant can encode finite information, but not an arbitrary infinite input-length-dependent sequence. Nonconstructive selection of the witnesses in a proposition does not change their finite, fixed nature.

Exact concatenation is unambiguous at the relevant lengths. For $n<n'$, nondecreasing $Q$ gives

$$
n+Q(n)<n'+Q(n)\le n'+Q(n').

$$

Consequently

$$
\lvert u\rvert=Q(\lvert x\rvert),\quad
\lvert v\rvert=Q(\lvert z\rvert),\quad xu=zv
\quad\Longrightarrow\quad
\lvert x\rvert=\lvert z\rvert,\quad x=z,\quad u=v.

$$

The split is also computable in polynomial time in the concatenated length, by testing all candidate prefix lengths. This includes $C=0$ and $c=0$. Thus retaining concatenation in the exact form is sound. More generally, an ordinary effective polynomial exact length can be normalized to a dominating monomial: recover the destination split, retain precisely the original number of certificate bits, and ignore the extra padding. This requires the original length computation, not merely a numerical bound.

Argument B’s first inference fails on the repaired bounded side. The empty witness gives

$$
\operatorname{pairEncode}(x,[])\in V\Longrightarrow x\in L,

$$

not $V\subseteq L$. The paired verifier constructed below therefore avoids the prefix-free obstruction.

The obstruction **does survive for a proposed plain-concatenation bounded variant**. For such a variant, $V\subseteq L$, and prefix-free $L$ satisfies

$$
x\in L\Longrightarrow
\exists u,\ xu\in V\subseteq L
\Longrightarrow u=[]
\Longrightarrow x\in V;
\qquad L=V\in P.

$$

With the repaired definitions, this is not an unconditional counterexample to an equivalence with all NP. Such an equivalence would imply $P=NP$: encode any NP language $L$ as the prefix-free language

$$
\{1^{\lvert x\rvert}0x:x\in L\}.

$$

This language has a paired polynomial verifier: parse the displayed encoding, check the old certificate length against the recovered $\lvert x\rvert$, and run the old verifier. Its witness bound is polynomial in the encoded length. The corrected padding construction below puts it in the supplied NP. The hypothesized concatenation characterization would put it in P, and the polynomial-time encoding would put $L$ in P. Conversely, if $P=NP$, every NP language admits the concatenation bounded form using coefficient zero; every language admitting that bounded form is in NP by parsing a pair and consulting its concatenation verifier. Thus that class equivalence is **equivalent to $P=NP$**, not a suitable routine Exercise-2.1 companion theorem. The old undecidable prefix-free counterexample is no longer an NP witness.

Argument D can still diagonalize against reductions to any fixed target, but its crucial step—putting the resulting arbitrary length language in NP—has disappeared. The repaired class has only countably many finite descriptions. Countability alone does not prove hardness exists; the legal HALT reduction below supplies that positive conclusion.

**Exercise 2.1, independently reconstructed in both directions.** For the forward direction, let the exact form have parameters $C,c,V$. Define

$$
W=\{\operatorname{pairEncode}(x,u):
\lvert u\rvert=Q(\lvert x\rvert)\land xu\in V\}.

$$

The grammar in `Encoding.lean` parses aligned `00`/`11` blocks and then the first aligned `01`; its suffix is the entire second component. Reject malformed strings. On a successful parse, check the displayed length equality, concatenate, and run the decider for $V$. Parsing, fixed-degree arithmetic, and copying take polynomial time in the input length; the queried concatenation is no longer than that input. Their native implementations and parser soundness on all accepted encodings must be proved, as the sketch acknowledges. Then, using pairing injectivity,

$$
\begin{aligned}
x\in L
&\iff\exists u,\ \lvert u\rvert=Q(\lvert x\rvert)\land xu\in V\\
&\iff\exists u,\ \lvert u\rvert\le Q(\lvert x\rvert)
\land\operatorname{pairEncode}(x,u)\in W.
\end{aligned}

$$

For the reverse direction, start with the paired bounded verifier $V$. **Correct the sketch’s target length to**

$$
R(n)=(C+1)(n+1)^c,
\qquad R(n)-Q(n)=(n+1)^c\ge1.

$$

The NP witness parameters are now exactly $C+1,c$. On input $y$, with $m=\lvert y\rvert$, define its verifier $W$ as follows:

1. Search $0\le n\le m$ for $n+R(n)=m$. Reject if none exists. Strict increase of $n+R(n)$ proves uniqueness.
2. Split $y=xv$ at that $n$. Then $\lvert v\rvert=R(n)\ge1$. Reject if $v$ has no `true` bit.
3. Split at the **last** `true` in $v$, obtaining the unique representation $v=u1 0^t$.
4. Require $\lvert u\rvert\le Q(n)$, and accept precisely when $\operatorname{pairEncode}(x,u)\in V$.

For every old witness $u$,

$$
\lvert u\rvert+1\le Q(n)+1\le R(n),
\qquad
v=u1 0^{R(n)-\lvert u\rvert-1},
\qquad \lvert v\rvert=R(n).

$$

The exponent is nonnegative, the inserted marker is the last `true`, and the verifier recovers exactly $x,u$. Conversely, an accepted certificate of length $R(\lvert x\rvert)$ forces the recovered prefix length to be $\lvert x\rvert$, by uniqueness of the total-length equation; steps 3–4 recover an old permitted witness. Hence

$$
\exists u,\ \lvert u\rvert\le Q(\lvert x\rvert)
\land\operatorname{pairEncode}(x,u)\in V
\iff
\exists v,\ \lvert v\rvert=R(\lvert x\rvert)\land xv\in W.

$$

This is a polynomial-time verifier on **all** inputs: the search has at most $m+1$ candidates, candidate arithmetic has fixed polynomial size, and an accepted parse queries a string of length

$$
2n+2+\lvert u\rvert
\le 2n+2+R(n)-1
=m+n+1\le2m+1.

$$

Native scans, arithmetic, copying, and buffered invocation still need their time/run lemmas; no uncomputable predicate or new asymptotic mechanism is hidden here.

| Edge case | Check |
|---|---|
| $C=0$ | $Q(n)=0$, so only $u=[]$ is allowed. The exact witness $1 0^{R(n)-1}$ works. A longer stripped string is rejected even if it fits the enlarged region. |
| $c=0$ | $Q(n)=C$, $R(n)=C+1$; total length $n+C+1$ remains strictly increasing. |
| $x=[]$ | Forward pairing begins with `01`; reverse recovery uses $n=0$, $R(0)=C+1$. No positive-input assumption occurs. |
| $u=[]$ | The certificate is $1 0^{R(n)-1}$; stripping returns the empty word. |
| Old $u$ entirely `false` | The added marker is still present and is the last `true`; every old zero bit is retained. |
| Entire new certificate region `false` | Reject; the search for a marker never enters the instance prefix. |
| Malformed $y$, including $y=[]$ | Reject if the length equation has no solution; $R(n)\ge1$ excludes empty $y$. |

The order `pairEncode x u` is correct. Delimiting the first component determines both components because the second ends at end-of-input; the certificate needs no extra internal delimiter. Swapping the components is unnecessary and would change the formal statement and constructions without fixing an existing defect.

**The HALT searcher, checked against the Chapter-1 API.** Fix a lawful scheme $\kappa$ and $L\in NP$.

1. `NP_subset_EXP`, once its enumerator is filled, yields a machine $D$ and a total time budget $T$ deciding $L$. By the definitions of `DecidesInTime` and `ComputesFunInTime`, the same hypothesis says that $D$ computes $x\mapsto[\operatorname{indicator}(L,x)]$ within $T$. No extra totality assumption is needed.
2. `FinTM.one_work_tape_binary D f T hD`, with $f(x)=[\operatorname{indicator}(L,x)]$, has precisely that total-function hypothesis. It returns a binary machine $N$, a constant $a$, and

   $$
   N.k=1,\qquad
   N.\mathrm{ComputesFunInTime}\ f\ (n\mapsto a(T(n)+1)^2).

   $$

   There is no time-constructibility or monotonicity hypothesis here. The quadratic slowdown is immaterial to the reduction’s running time.
3. Build $S$ with states $(N.\mathrm{State}\times\mathrm{Bool})\sqcup\{\mathrm{loop}\}$, retaining the same one work tape and binary alphabet. Initialize the register to `false`. For an action with output $o$, first replace the register by the emitted bit if $o$ is present; otherwise retain it. Preserve the simulated input/work actions. A live successor remains live; a halting successor becomes `none` iff the **updated** register is `true`, otherwise `loop`. The loop action moves no heads, performs no write, emits nothing, and returns `some loop`.
4. The run invariant follows the simulated state, heads, and tapes up to its first halt and records its most recent emission. Since a total decider’s completed output is exactly one bit and output is append-only, that recorded bit at halt is exactly its decision bit. The rule includes an emission on the halting transition. Therefore

   $$
   \exists w,t,\ S.\mathrm{ComputesInTime}\ x\ w\ t
   \iff x\in L.

   $$

   The machine can suppress its simulated emissions; its output contents are irrelevant to this halting equivalence. The stationary loop remains live at every later time. This is the run/halting lemma explicitly owed by the sketch, not a lemma already proved in the attachment.
5. `exists_codeTM S hk` requires **only** $S.k=1$. Its conclusion supplies $M:\mathrm{CodeTM}$ satisfying, for every $x,w,t$,

   $$
   M.\mathrm{toFinTM.ComputesInTime}\ x\ w\ t
   \iff S.\mathrm{ComputesInTime}\ x\ w\ t.

   $$

   Finite control extension preserves the `Fintype`/`DecidableEq` requirements. No totality is required at this step.
6. Let $\alpha=\kappa.\mathrm{encode}(M)$, one fixed string. Emit its doubled prefix and separator without moving the input head, copy the input, and halt on the boundary blank. The step count is

   $$
   (2\lvert\alpha\rvert+2)+\lvert x\rvert+1
   =2\lvert\alpha\rvert+\lvert x\rvert+3
   \le(2\lvert\alpha\rvert+3)(\lvert x\rvert+1).

   $$

   Thus this is a legal polynomial-time reduction function, including empty input. The existing diagonal-pairing theorem is a different function, so the sketch correctly names this new controller/lemma.
7. `HALT_pairEncode_eq_true_iff` and `decode_encode` give

   $$
   \begin{aligned}
   \operatorname{HALT}(\kappa,\operatorname{pairEncode}(\alpha,x))=\mathrm{true}
   &\iff\exists w,t,\ (\kappa.\mathrm{decode}(\alpha)).\mathrm{toFinTM.ComputesInTime}\ x\ w\ t\\
   &\iff\exists w,t,\ S.\mathrm{ComputesInTime}\ x\ w\ t\\
   &\iff x\in L.
   \end{aligned}

   $$

No machine computes a varying `encode` or `decode`. The fixed-code choice needs no effectivity. The recipe’s named control and prefixing obligations are adequate at this statement phase.

**Why the proposed pathological scheme is unlawful, and why effectivity is not necessary for nonmembership.** If `decode` were constantly a machine $M_0$, then

$$
\forall M:\mathrm{CodeTM},\qquad
M=\kappa.\mathrm{decode}(\kappa.\mathrm{encode}(M))=M_0.

$$

But the one-state machine whose every transition halts and the one-state machine whose every transition remains live are distinct `CodeTM`s. Thus constant decoding cannot satisfy even `decode_encode`.

Restricting that proposal to “all strings outside the image of `encode`” does not rescue it. For any $M$ and $j>0$, its padded code cannot itself be a canonical encoding: if

$$
\kappa.\mathrm{encode}(M)1^j=\kappa.\mathrm{encode}(M\prime),

$$

decoding both sides gives $M=M\prime$, hence the same equality would imply

$$
\lvert\kappa.\mathrm{encode}(M)\rvert+j
=\lvert\kappa.\mathrm{encode}(M)\rvert,

$$

contradicting $j>0$. Such padded strings lie outside the canonical image but must decode to $M$ by `decode_encode_pad`. Choosing $M\ne M_0$, the proposed non-image fallback would therefore contradict the required decoded value. A fallback outside **all padded valid encodings** can be lawful, but cannot make their HALT problem decidable.

To see the latter without a universal evaluator, suppose a machine computes $s\mapsto[\operatorname{HALT}(\kappa,s)]$. The public diagonal-pairing machine and total instances of `exists_comp_partial` produce a total machine computing

$$
z\longmapsto[\operatorname{HALT}(\kappa,\operatorname{pairEncode}(z,z))].

$$

`Computes.exists_computesFunInTime` supplies a length-based bound, and `one_work_tape_binary` now applies legally. Use the same finite-control transformation above, this time **halting on `false` and looping on `true`**, then `exists_codeTM`. For its coded machine $M$, set $\alpha=\kappa.\mathrm{encode}(M)$ and evaluate its diagonal pair. Then

$$
\operatorname{HALT}(\kappa,\operatorname{pairEncode}(\alpha,\alpha))=\mathrm{true}
\iff M\text{ halts on }\alpha
\iff \operatorname{HALT}(\kappa,\operatorname{pairEncode}(\alpha,\alpha))=\mathrm{false},

$$

which is impossible in either Boolean case. This proves the mathematical undecidability claim at full `MachineCode` generality; a Lean version still needs the named control-transform lemma. Since the repaired NP languages have total deciders, the stronger HALT nonmembership follows as well.

The attached `HALT_not_computable` is stated only for `EffectiveMachineCode` because its particular proof runs the universal evaluator. That explains the existing API’s hypothesis; it does not establish necessity for the conclusion. The current Chapter-2 nonmembership theorem is therefore true, and its proposed proof through that API is valid, but the new explanation for the restricted signature is materially wrong.

**Quantitative and remaining-sketch checks.** The composition repair uses an available theorem with hypotheses `ComputesFunInTime` for both components and `Monotone` for the second budget. Although its implementation chooses overhead 2, its public statement returns an existential constant; a fill agent should absorb the returned constant $a$. Writing the input budgets as $C(n+1)^c$ and $C'(n+1)^{c'}$,

$$
\begin{aligned}
&a\left(C(n+1)^c+C'\big(C(n+1)^c+1\big)^{c'}+1\right)\\
&\qquad\le
a\left(C+C'(C+1)^{c'}+1\right)(n+1)^{\max(c,cc')}.
\end{aligned}

$$

This follows from $C(n+1)^c+1\le(C+1)(n+1)^c$, and each remaining exponent is at most the maximum. It covers both zero degrees. For complementation, the postprocessor `ifEq [true] [false] [true]` has the right total singleton behavior; buffered composition keeps the first decider’s bit off the real output. For downward closure, the output-length bound supplies the intermediate length, and the same composition estimate applies. `mem_P_iff` and `mem_P_of_dtime_le` supply the advertised return to P.

For the enumerator, a sufficient bound is

$$
T(n)=a\,2^{Q(n)}(n+Q(n)+1)^d.

$$

The correct pointwise conclusion includes an external constant:

$$
\exists b,e\in\mathbb N\;\forall n,\quad T(n)\le b\,2^{n^e}.

$$

Here is an explicit absorption argument. Set $r=\max(c,1)$, $e=r+1$. Since $n+1\le2^{n+1}$,

$$
\begin{aligned}
n+Q(n)+1&\le(C+1)(n+1)^r,\\
T(n)&\le a(C+1)^d\,2^{C(n+1)^c}(n+1)^{rd}\\
&\le a(C+1)^d\,2^{(C+rd)(n+1)^r}.
\end{aligned}

$$

For $n\ge N_0$, where $N_0=\max(1,(C+rd)2^r)$,

$$
(C+rd)(n+1)^r\le(C+rd)2^r n^r\le n^{r+1}=n^e.

$$

Choose $b$ to be the maximum of $a(C+1)^d$ and the finitely many values $T(j)$ for $j<N_0$. The large-length inequality follows above; for small lengths, $T(j)\le b\le b2^{j^e}$. This proves the required all-length bound. The sketch’s displayed inequality without $b$ is an eventual comparison, consistent with its explicit small-length qualification, not literally an all-$n$ inequality.

If $C=0$, $Q(n)=0$ and $2^{Q(n)}=1$: execute exactly one verifier call on $x++[]=x$. If that call rejects, terminate with `[false]`; do not skip it because the counter has zero cells. Reset/call overhead and initialization can all be included in $T$ after increasing its fixed constants.

The timed enumeration invariant must assert: fixed width; each candidate occurs exactly once until overflow; unchanged instance/candidate storage across verifier calls; correct virtual input and head initialization; clean verifier work tapes and control at each restart; captured decision including halting-transition emissions; no real output before finalization; and a polynomial bound on each call/reset. Reset can clear a bounded visited region because each simulated head moves at most one cell per step. The existing list covers the numerical, retention, counter, and work-reset categories. Finding 2 adds the missing output/return contract; the reset wording should explicitly include heads and control. No existing total sequential-composition theorem by itself implements this evolving-configuration loop.

For `EXP_subset_NEXP`, take the displayed width $2^{(n+1)^c}$. Its sum with $n$ is strictly increasing. On length $m$, search $n\le m$; each binary representation of the exponential has $(n+1)^c+1\le(m+1)^c+1$ bits, so unsuccessful search candidates still cost polynomial time in $m$. On a valid split the original decider’s budget is

$$
a2^{n^c}\le a2^{(n+1)^c}\le am.

$$

At $c=0$, the padding is the constant 2; malformed short inputs are rejected. The named arithmetic and split/copy obligations suffice, with a buffered simulation of the final decider. No additional statement defect was found.

The following accounts for all 19 theorem sketches, including the unchanged ones.

| Theorem(s) | Assessment |
|---|---|
| `polyTimeComputable_id`; `PolyTimeComputable.output_length_le` | Identity and pointwise budget weakening are available; completed output length is bounded by steps. |
| `PolyTimeComputable.comp` | Correct with the returned overhead constant, explicit monotonicity, and repaired degree. |
| `P_subset_NP` | Coefficient zero, empty certificate, and verifier $V=L$ work on every input. |
| `mem_NP_iff_exists_length_le` | Statement correct; reverse witness must be corrected as in finding 1. |
| `compl_mem_P` | Correct timed total composition, with buffered intermediate output. |
| `mem_coNP_iff_forall` | Negate the NP existential and complement its P verifier; keep the same $C,c$. This proves both directions. |
| `P_subset_NP_inter_coNP`; `NP_eq_coNP_of_P_eq_NP` | Correct complement/set arguments using the preceding lemmas. |
| `P_subset_EXP` | For every $n,c$, $n^c+1\le2^{n^c}$; DTIME monotonicity and its multiplier suffice, including $n=0$. |
| `NP_subset_EXP` | Correct statement and numerical estimate; output/return obligations remain incomplete as in finding 2. |
| `EXP_subset_NEXP` | Correct padding, split uniqueness, and combined-input time estimate. |
| `PolyTimeReducible.refl`; `PolyTimeReducible.trans` | Identity/composition and the reduction membership equivalences suffice. |
| `mem_P_of_polyTimeReducible` | Correct timed composition and polynomial output-length reasoning. |
| `P_eq_NP_of_NPHard_mem_P`; `NPComplete.mem_P_iff` | Correct downward-closure and inclusion arguments. |
| `HALT_NPHard` | Correct at full `MachineCode` generality, with the named control/prefix machine obligations. |
| `HALT_not_mem_NP` | Correct at its stated effective-scheme generality; the final effectivity-necessity explanation is false. |

Thus the answer to whether the named obligations are complete **as written is no**. Findings 1 and 2 identify a missing normalization step and a missing native call contract. After adding them, the supplied strategies expose the relevant mathematical and machine-construction obligations; this is not a promise that filling them will require no auxiliary lemmas.

The pack’s six specific questions have these answers:

| Question | Answer |
|---|---|
| 1 — residual length-value channel | None of Argument A’s kind. Parameters are fixed before the input, and both width and verifier are effective. The modulo-3 replay and terminating exhaustive decider establish this directly. |
| 2 — pairing order | Keep `pairEncode x u`. The aligned delimiter locates the end of $x$, and the remainder is exactly $u$. Both proof directions use that order correctly. |
| 3 — a second bounded concatenation variant | Do not add an unconditional equivalence of that form: with the repaired class it would be equivalent to $P=NP$. The paired bounded theorem is the appropriate routine characterization. Direct normalization of effective exact lengths remains available. |
| 4 — exponential budget and width zero | Yes at the DTIME class level, with the explicit external multiplier proved above. Width zero performs one round. The displayed unit-coefficient inequality is not pointwise at all small lengths. |
| 5 — trivial-machine scheme | No. It violates `decode_encode`; the non-image fallback variant also violates the padded law. Furthermore, every lawful scheme has an undecidable HALT problem by direct diagonalization. |
| 6 — root export | The import and facade contents satisfy the visible export requirement. The harness should track root reachability of every campaign module, its ordered module inventory, and actual full-root CI elaboration at the pin. Relevant blueprint/dependency-graph checks remain subject to the plan’s phase-boundary workflow. The import line alone does not establish those results. |

Finally, the repository attestations divide into reproduced source facts and unverified historical/toolchain claims as follows.

| Attestation | Reproduced from the attachment | Not reproduced / challenged |
|---|---|---|
| 1 — repair scope and Chapter-1 freeze | Current repaired source and root export were inspected; there are 40 campaign modules plus the root. | No parent source or Git diff is attached. Exact commit scope, commit provenance, and byte-identical Chapter-1 history cannot be checked from one snapshot. The earlier audit report is not a byte-level baseline. |
| 2 — elaboration, 19 admissions, import isolation | A scan excluding nested comments and strings finds exactly 19 `sorry` tokens, distributed 3/2/4/3/7 across PolyTime/NP/CoNP/EXP/Reductions, and zero elsewhere in the supplied Lean files. Within this supplied tree, only the root imports ClassNP from outside ClassNP. | No Lean or Lake executable was available on PATH, and the bundle omits the verification scripts and dependencies. No fresh-olean sweep, compiler diagnostics, root build, or axiom traversal was reproduced. Import isolation across the rest of the repository is unverified. |
| 3 — statement deltas | The five named declarations exhibit the advertised conceptual changes compared with the round-1 report’s restatements. The numerical helper bodies have the same mathematical content reported in round 1. | No ordered or bytewise parent/current statement comparison is possible. The unchanged count is wrong: 16 theorem signatures and 8 definitions remain outside the listed changes, not 14 statements. |
| 4 — policy | All 29 definitions/theorems have declaration docstrings; all 19 admissions have adjacent sketches. The five child modules use the three standard options and precise imports. The facade imports/lists every child; the root exports it. No new explicit axiom, instance, or unsafe declaration appears in ClassNP. | `style_lint.py`, its zero-FAIL result, and its six unchanged WARNs were not reproduced. Docstring presence does not establish mathematical accuracy: findings 1–3 challenge that accuracy/completeness. The plan also needs the synchronization correction in finding 4. |

As finite corroboration, I executed 3,055 padding/pairing round-trip cases and 5,222 complete certificate-region cases for selected small widths, including zero coefficients/degrees, empty strings, and marker-free regions. These used the **corrected** length $R$, not the sketch’s inadmissible $Q+1$. They found no disagreement with the derivation. They are not Lean proofs or evidence of compiled native-machine implementations.

**Notation glossary.** $xu$ denotes concatenation; $\lvert x\rvert$ denotes string length; $0,1$ denote `false,true`; $0^t,1^t$ denote repeated-bit strings; $[]$ is the empty string. $L,V,W$ are languages (with $V,W$ used as verifiers); $x,u,v,y,z,w,s,\alpha$ are binary strings. $C,C',a,b$ are fixed natural coefficients; $c,c',d,e,r$ are natural degrees, and $n,n',m,j,t$ are natural lengths, indices, or times. $Q(n)=C(n+1)^c$ is the original bound; $R(n)=(C+1)(n+1)^c$ is the corrected exact padding length; $T$ is a running-time budget; $N_0$ is the finite threshold in its exponential absorption. $\kappa$ is a representation scheme; $D,N,S$ are finite Turing machines; $M,M\prime,M_0$ are coded machines; $f$ is a total string function; $o$ is an optional emitted bit. $\sqcup$ denotes disjoint union; $\operatorname{indicator}(L,x)$ is the supplied Boolean membership indicator. Class names, Lean declaration names, and $\le_p$ refer to the attached definitions; $P=NP$ compares those classes after the repair.
