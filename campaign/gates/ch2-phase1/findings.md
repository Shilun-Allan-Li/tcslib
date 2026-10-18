**Chapter 2, Phase 1 — independent adversarial statement audit**

Audited material: the supplied bundle labelled commit `ab82bb6a`, branch `complexity/arora-barak-ch1`. Intended destination: `audits/ch2-phase1-findings.md`.

**Disposition: the statement gate must remain open.** There are **3 blocker findings, 3 major findings, 3 minor findings, and 3 notes**. The declared `NP` contains undecidable languages; `NP_subset_EXP`, `mem_NP_iff_exists_length_le`, and `HALT_NPHard` are false as stated. These conclusions concern the supplied definitions, not the standard complexity classes.

I first read comment-stripped declarations, then their docstrings and sketches, and checked their dependencies against the attached Chapter-1 declarations. The counterexamples below are mathematical arguments, not kernel-checked Lean submissions. Small executable checks corroborated the finite padding examples; they are not substitutes for the general arguments.

The attachment contains the pack, both plans, policy, and 40 Lean modules. It does **not** contain the 2009 textbook pages, the cited historical audit reports, the parent commit, or the verification scripts/results. I consulted the [authors’ January 2007 draft, Definition 2.1](https://theory.cs.princeton.edu/complexity/book.pdf#page=56), which explicitly requires a polynomial certificate-length function. Its numbering differs from the published book. Below, published item numbers are the pack’s references; I do **not** certify their page/number accuracy, the published footnote 4, or the precise wording of the cited exercises from that draft. The statement-level counterexamples do not depend on these bibliographic limitations.

The uploaded bundle’s SHA-256 is `2be0df3dd1c3a95028ccbc08e36390925a291bc0a32cbe7e8d6fa06f0dcc5086`.

The following are the **10 blind definition restatements**. All quantified constants are natural numbers; all languages and strings are binary. In this document, `NP`, `coNP`, and `NEXP` mean the supplied definitions unless explicitly called standard.

| Declaration | Literal mathematical content | Comparison with intended source |
|---|---|---|
| `PolyBound p` | \(\exists C,c\;\forall n,\ p(n)\le C(n+1)^c\). | A numerical upper-bound property. It asserts neither that \(p\) is a polynomial nor that \(p\) is computable or monotone. |
| `PolyTimeComputable f` | Some `FinTM Bool` computes the total string function \(f\), on every input \(x\), within \(C(\lvert x\rvert+1)^c\) steps for fixed \(C,c\). | Appropriate FP notion underlying Definition 2.7. |
| `NP` | \(L\in NP\) iff \(\exists p,V,\ \operatorname{PolyBound}(p)\land V\in P\land\forall x,\ [x\in L\leftrightarrow\exists u,\ \lvert u\rvert=p(\lvert x\rvert)\land xu\in V]\). | **Material divergence from Definition 2.1:** polynomially bounded arbitrary functions replace polynomials. Concatenation also needs separate scrutiny; see findings 1–2. |
| `coNP` | \(L\in coNP\leftrightarrow L^c\in NP\). | Correct complement operation for Definition 2.19, but applied to the wrong underlying class. |
| `EXP` | \(\bigcup_{c\in\mathbb N}\operatorname{DTIME}(n\mapsto2^{n^c})\). | Appropriate deterministic exponential-time class for Claim 2.4/§2.6.2. Including degrees 0 and 1 changes no class. |
| `ExpBound p` | \(\exists C,c\;\forall n,\ p(n)\le C\,2^{(n+1)^c}\). | A numerical bound only; no effectiveness is asserted. |
| `NEXP` | The exact-certificate definition of `NP`, with `ExpBound` replacing `PolyBound`, still requiring \(V\in P\) on the entire concatenated input. | Polynomial verifier time in the combined length is appropriate for Exercise 2.27. Arbitrary exact lengths are not: this class also contains undecidable languages. |
| `PolyTimeReducible L L'` | \(\exists f,\ \operatorname{PolyTimeComputable}(f)\land\forall x,\ [x\in L\leftrightarrow f(x)\in L']\). | Correct total many-one/Karp reduction, Definition 2.7. |
| `NPHard L` | \(\forall L'\in NP,\ L'\le_p L\). | Correct relational shape, but the supplied `NP` makes it unsatisfiable for every target. |
| `NPComplete L` | \(L\in NP\land\operatorname{NPHard}(L)\). | Correct relational shape, but no language satisfies it under the supplied definitions. |

The following are the **19 blind theorem restatements and individual sketch assessments**. “Valid” means no statement-level mathematical defect was found; it does not certify a Lean proof or the intended interpretation of a defective class.

| Declaration | Restatement and cited item | Sketch assessment against the attached API |
|---|---|---|
| `polyTimeComputable_id` | The identity string function is polynomial-time computable. Technical FP infrastructure. | Valid; `computesFunInTime_id` directly supplies the witness. The cited `ComputesFunInTime.mono` is absent; pointwise `ComputesInTime.mono` suffices if weakening is needed. |
| `PolyTimeComputable.output_length_le` | If \(f\) is polynomial-time computable, \(\exists C,c\;\forall x,\ \lvert f(x)\rvert\le C(\lvert x\rvert+1)^c\). | Valid. Combine `computesInTime_iff` with `MultiTapeTM.output_length_le`. |
| `PolyTimeComputable.comp` | Polynomial-time computable \(f,g\) imply polynomial-time computability of \(g\circ f\). Theorem 2.8’s composition argument. | Valid using `computesFunInTime_comp` and monotonicity of the **chosen budget** for \(g\). The proposed degree \(cc'\) misses \(c'=0\); see finding 7. |
| `P_subset_NP` | \(P\subseteq NP\). Claim 2.4’s first inclusion. | Valid as written: \(p=0,V=L\). `PolyBound` and the empty-certificate equivalence are immediate. |
| `mem_NP_iff_exists_length_le` | \(L\in NP\) iff the same existential definition can use \(\lvert u\rvert\le p(\lvert x\rvert)\), with arbitrary `PolyBound p` and plain \(xu\). Exercise 2.1. | **False.** Both proposed proof directions contain invalid steps; Argument B refutes the theorem, and Argument C supplies a valid reverse direction only. |
| `compl_mem_P` | \(L\in P\Rightarrow L^c\in P\). | Valid. The specified Boolean postprocessor is correct, but `exists_comp_partial` gives no time bound. Use the timed total composition theorem. |
| `mem_coNP_iff_forall` | \(L\in coNP\) iff \(\exists p,V,\operatorname{PolyBound}(p)\land V\in P\land\forall x,\ [x\in L\leftrightarrow\forall u,\ \lvert u\rvert=p(\lvert x\rvert)\Rightarrow xu\in V]\). Definition 2.20/Exercise 2.24. | Valid for the supplied class by logical negation and complementing \(V\); inherits the wrong-class defect. No certificate-length computation is needed for this logical equivalence. |
| `P_subset_NP_inter_coNP` | \(P\subseteq NP\cap coNP\). Exercise 2.23. | Valid from `P_subset_NP` and repaired `compl_mem_P` proof. |
| `NP_eq_coNP_of_P_eq_NP` | \(P=NP\Rightarrow NP=coNP\). Exercise 2.25. | Valid complement argument. Under the current definitions its premise is false, so it does not express the intended open-problem consequence. |
| `P_subset_EXP` | \(P\subseteq EXP\). Claim 2.4. | Valid using `DTIME.mono` and absorption of constant factors. All small-length cases are harmless. |
| `NP_subset_EXP` | \(NP\subseteq EXP\). Claim 2.4. | **False**, by Argument A. A numerical majorant does not compute the original certificate length. Even after repairing the definition, substantial enumerator infrastructure remains to be built. |
| `EXP_subset_NEXP` | \(EXP\subseteq NEXP\). §2.6.2. | Valid padding construction, despite the target class being too large. Total length is strictly increasing; certificate length itself is constant at degree 0. Split recovery and verifier machines require new implementation. |
| `PolyTimeReducible.refl` | Every language reduces to itself. Exercise 2.9. | Valid using identity. |
| `PolyTimeReducible.trans` | \(L\le_p L'\land L'\le_p L''\Rightarrow L\le_p L''\). Theorem 2.8.1. | Valid using function composition and the two equivalences. |
| `mem_P_of_polyTimeReducible` | \(L\le_p L'\land L'\in P\Rightarrow L\in P\). Definition 2.7/Figure 2.1. | Valid; the sketch again uses an untimed existential composition theorem to assert a polynomial bound. Replace it with timed total composition. |
| `P_eq_NP_of_NPHard_mem_P` | \(\operatorname{NPHard}(L)\land L\in P\Rightarrow P=NP\). Theorem 2.8.2. | Valid set-theoretic argument using downward closure and \(P\subseteq NP\). Its hardness premise is impossible under the current definition. |
| `NPComplete.mem_P_iff` | If \(L\) is NP-complete, then \(L\in P\leftrightarrow P=NP\). Theorem 2.8.3. | Valid conditional, but there are currently no NP-complete languages. |
| `HALT_NPHard` | For every effective scheme \(c\), \(\{s:\operatorname{HALT}(c,s)=\mathrm{true}\}\) is NP-hard. Exercise 2.8. | **False** by Argument D. Separately, the divergent searcher does not satisfy the totality hypothesis of the cited one-tape theorem. |
| `HALT_not_mem_NP` | For every effective scheme \(c\), its HALT language does not belong to `NP`. Exercise 2.8. | The supplied proof fails because it uses false `NP_subset_EXP`. I do **not** infer that this conclusion is false. After repairing `NP`, the proposed decidability contradiction is sound. |

The findings table uses the pack’s severity guide. File paths below are relative to `TCSlib/Complexity/`.

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | blocker | `ClassNP/NP.lean · NP`; `ClassNP/EXP.lean · NEXP, NP_subset_EXP` | A polynomial/exponential numerical bound suffices for an exact certificate length. | Argument A puts every language determined solely by input length into both classes, including undecidable languages. The length function can even be strictly increasing. | Restrict the length function to an explicit, effectively evaluable normal form, or require the appropriate uniform computation bound. Repair all equivalent formulations too. Keep `PolyBound`/`ExpBound` as numerical helpers if useful. |
| 2 | blocker | `ClassNP/NP.lean · mem_NP_iff_exists_length_le` | Exact and bounded lengths are equivalent with the displayed plain-concatenation formulas. | Argument B: the bounded form forces a prefix-free language to equal its P verifier. The exact form represents an undecidable prefix-free language. The sketch also changes acceptance when reusing \(V\) or enlarging \(p\). | Use an unambiguous pair/explicit two-input verifier and effective length bounds on both sides. If retaining the present definitions temporarily, only the reverse implication has the reconstruction in Argument C. |
| 3 | blocker | `ClassNP/Reductions.lean · HALT_NPHard` | The current class has HALT as an NP-hard target. | Argument D proves that **no target language at all** is NP-hard for this class. | Repair `NP` before freezing hardness or completeness statements. Do not treat this as merely a searcher implementation problem. |
| 4 | major | `ClassNP/CoNP.lean · compl_mem_P`; `ClassNP/Reductions.lean · mem_P_of_polyTimeReducible` | The polynomial running time follows from `exists_comp_partial`. | Its conclusion is only an equivalence of existential halting/output relations. It contains no time inequality. | Use `computesFunInTime_comp` or `PolyTimeComputable.comp`; convert a decider to the total singleton-indicator function and prove monotonicity of the explicit polynomial budget. |
| 5 | major | `ClassNP/EXP.lean · NP_subset_EXP` | Chapter 1 provides the stated polynomial-width counter and timed search assembly. | `counterTM` and `counterInc` are **private** in `ClassP/TimeConstructible.lean`. The former computes input length in binary; the latter extends on overflow. Neither computes arbitrary \(p\), evaluates arbitrary polynomials, or supplies fixed-width exhaustive search. `exists_cond` is also untimed. | After finding 1, explicitly budget and implement polynomial-width initialization, fixed-width overflow, retained input/counter, repeated verifier reset, and a timed loop invariant. State any new reusable API obligations before assigning the fill. |
| 6 | major | `ClassNP/Reductions.lean · HALT_NPHard` | A divergent searcher can be coded by the `universal_quadratic` normal-form pattern. | `one_work_tape_binary` requires `M.ComputesFunInTime f T` for a **total** \(f\). A machine deliberately diverging on no-instances cannot satisfy it. `exists_codeTM` itself is fine, but only after obtaining one work tape. | Either add a partial-computation normal-form theorem, or first normalize the repaired total NP decider and then modify its one-tape control to loop on rejection. See the concrete alternative below. |
| 7 | minor | `ClassNP/PolyTime.lean · PolyTimeComputable.comp` | The displayed budget has degree \(cc'\), up to constants. | With \(c>0,c'=0\), the first-machine term still grows as \((n+1)^c\). | Use \(\max(c,cc')\), or first enlarge both degrees to positive ones. |
| 8 | minor | `ClassNP/PolyTime.lean · PolyBound`; `ClassNP/EXP.lean · EXP_subset_NEXP` | The bounded function is monotone; exponential padding is strictly monotone for every degree. | A bound by a monotone function does not make \(p\) monotone. At degree 0, \(2^{(n+1)^0}=2\). | Attribute monotonicity only to the majorant. State that \(n+p(n)\), rather than \(p(n)\), is strictly increasing in the exponential padding proof. |
| 9 | minor | `ClassNP/PolyTime.lean · polyTimeComputable_id` and module inventory | The named support/results are available as written. | No attached `FinTM.ComputesFunInTime.mono` declaration exists; the module advertises nonexistent `PolyTimeComputable.output_polyBound` instead of `output_length_le`. | Correct the names and use pointwise `ComputesInTime.mono` when necessary. |
| 10 | note | `ClassNP/NP.lean · NP, P_subset_NP`; `ClassNP/CoNP.lean · compl_mem_P` | A P-language verifier or the empty-string/output conventions might independently invalidate these constructions. | A P-language supplies a uniform total Boolean decider. The \(p=0\) inclusion and Boolean complementation work, including empty inputs. The principal defect is the external length function, not arbitrary off-domain behavior of \(V\). | No change to the language-verifier abstraction is required; repair its surrounding interface. |
| 11 | note | `ClassNP/Reductions.lean · HALT_NPHard` | Effectivity is necessary to encode the fixed searcher. | After repairing `NP` and the coding construction, only a fixed code and `MachineCode.decode_encode` are used. | The intended hardness theorem can be generalized to every `MachineCode`; this does not rescue the currently false theorem. |
| 12 | note | Audit attestations; facade; scoped notation | The bundle independently establishes all reported repository checks. | Static inventory is reproducible. Historical freeze, elaboration, axiom footprints, full lint, root export, and pinned-Mathlib collision checks are not established by the supplied material. | Preserve the evidence distinctions in the attestation table below. Supply the root export or an explicit policy disposition. |

**Argument A establishes the length-function defect.** Let \(A\subseteq\mathbb N\) be any set, and define
\[
p_A(n)=
\begin{cases}
2n,&n\in A,\\
2n+1,&n\notin A,
\end{cases}
\qquad
V_0=\{y:3\text{ divides }\lvert y\rvert\},
\qquad
L_A=\{x:\lvert x\rvert\in A\}.
\]
The verifier \(V_0\) has a finite-state decider: scan the input while recording its length modulo 3, then emit the corresponding Boolean and halt. It takes \(\lvert y\rvert+1\) steps in the supplied model.

For every \(n\),
\[
p_A(n)\le2(n+1),\qquad
p_A(n)\le2n+1<2n+2\le p_A(n+1).
\]
Thus \(\operatorname{PolyBound}(p_A)\), and even strict monotonicity holds. For any \(x\) of length \(n\),
\[
\begin{aligned}
\exists u,\ \lvert u\rvert=p_A(n)\land xu\in V_0
&\iff 3\mid n+p_A(n)\\
&\iff 3\mid
\begin{cases}3n,&n\in A,\\3n+1,&n\notin A\end{cases}\\
&\iff n\in A\\
&\iff x\in L_A.
\end{aligned}
\]
The first equivalence uses existence of a binary string of every prescribed natural length. Consequently \(L_A\in NP\) for **every** \(A\).

Choose undecidable \(A\). A decider for \(L_A\), evaluated on \(0^n\), would decide \(A\), a contradiction. Every `EXP` language has a total decider by the literal `DTIME` definition. Therefore `NP_subset_EXP` is false.

Also
\[
p_A(n)\le2(n+1)\le2\cdot2^{n+1},
\]
so \(\operatorname{ExpBound}(p_A)\) and the same example belongs to the supplied `NEXP`. Its promised interpretation as standard nondeterministic exponential time therefore fails already in phase 1.

This example has strictly increasing \(n+p_A(n)\): accepted and rejected lengths occupy disjoint, computably recognizable slots. Neither adding monotonicity nor worrying only about ambiguous concatenations addresses the defect. Nor does pairing alone suffice: with a paired verifier accepting precisely certificates of length 1, the bound \(p(n)=1\) on \(A\) and \(0\) off \(A\) encodes \(A\) under either an exact or a bounded external length test.

**Argument B refutes the bounded-length equivalence itself.** First observe an invariant of its right-hand side. The empty certificate is always allowed, so
\[
V\subseteq L.
\]
If \(L\) is prefix-free and \(x\in L\), a witnessing \(u\) gives
\[
xu\in V\subseteq L,\qquad x\text{ is a prefix of }xu.
\]
Prefix-freeness implies \(xu=x\), hence \(u=[]\) and \(x\in V\). Thus
\[
L\text{ prefix-free and satisfying the bounded form}
\quad\Longrightarrow\quad L=V\in P.
\tag{1}
\]
This reasoning needs no assumption at all on the numerical bound.

Now choose an undecidable \(A\subseteq\{1,2,\ldots\}\), use \(p_A\) from Argument A, and put
\[
K_A=\{0^{n-1}1:n\ge1,\ n\in A\},\qquad
W=\{0^{r-1}1\,0^{2r}:r\ge1\}.
\]
The language \(W\) is in \(P\). A direct machine places one unary work-tape mark per initial zero and one extra mark at the unique 1, then erases one mark per pair of suffix zeros, accepting exactly when marks and input end together. Malformed strings are rejected. This is a finite-control, linear-time construction.

Every word of \(W\) has length \(3r\). Therefore, for \(\lvert x\rvert=n\),
\[
\exists u,\ \lvert u\rvert=p_A(n)\land xu\in W
\iff n\ge1\land n\in A\land x=0^{n-1}1
\iff x\in K_A.
\]
Indeed, off \(A\) the total length is \(3n+1\), impossible in \(W\); on \(A\), total length \(3n\) forces \(r=n\) and the displayed prefix and suffix. Hence \(K_A\in NP\).

The words \(0^{n-1}1\) are pairwise prefix-incomparable, so \(K_A\) is prefix-free. It is undecidable, since testing \(0^{n-1}1\) decides membership of positive \(n\) in \(A\). Equation (1) excludes the theorem’s right-hand side. This is a counterexample to the **forward implication of the actual theorem**, not merely to its sketch.

Both elementary sketch errors can also be seen without undecidability:

- **Forward “reuse \(p,V\)” error:** take \(p(n)=1\) and \(V=\{[]\}\). The exact form defines the empty language. The bounded form accepts \(x=[]\) via \(u=[]\).
- **Reverse “only gains witnesses” error:** take \(p(n)=0\), \(V=\{[1]\}\), and the valid majorant \(Q(n)=1\). The original bounded form defines \(\{[1]\}\). Replacing its bound by \(Q\) also accepts \(x=[]\) via \(u=[1]\). Under the recorded padding fix, \(p'=2\), the string \([1,1]\) splits uniquely into empty \(x\) and a two-bit certificate; the final 1 is the marker, leaving \(u=[1]\), so the new verifier accepts this false positive.

The recorded split-first fix correctly prevents stripping into \(x\), but it does not preserve the **original** witness-length restriction. Checking \(\lvert u\rvert\le Q(n)\) instead of \(\lvert u\rvert\le p(n)\) is the remaining soundness error. An additional test against \(p(n)\) cannot be assumed computable from `PolyBound p`.

Even after replacing \(p\) by an effective polynomial, plain concatenation leaves invariant (1). A claim that this bounded form represents every standard NP language would imply \(P=NP\): for any standard NP language, its encoding under \(x\mapsto1^{\lvert x\rvert}0x\) is prefix-free and remains in standard NP. Equation (1) would put that encoded language in P; the polynomial-time encoding would then put the original language in P. Thus the pairing issue remains a separate interface defect after the length-function repair.

**Argument C independently reconstructs the reverse implication without pretending that \(p\) is computable.** This repairs that implication under the current definitions, but does not repair the false equivalence or the wrong class.

Suppose the bounded form holds with \(p,V\), and choose
\[
Q(n)=C(n+1)^c\ge p(n),\qquad
R(n)=(n+1)(Q(n)+1),\qquad
p'(n)=R(n)+p(n)-n.
\]
There is no truncated-subtraction issue because \(R(n)\ge n+1\). In fact,
\[
p'(n)=(n+1)Q(n)+1+p(n)\ge p(n)+1
\]
and
\[
p'(n)\le (n+2)Q(n)+1
\le(2C+1)(n+1)^{c+1}.
\]
The intervals
\[
[R(n),R(n)+Q(n)]
\]
are pairwise disjoint, because monotonicity of \(Q\) gives
\[
R(n+1)\ge(n+2)(Q(n)+1)=R(n)+Q(n)+1.
\]

On input \(y\) of length \(m\), the new verifier finds the unique interval containing \(m\), if any, by scanning \(n\le m\) and evaluating the fixed polynomial \(Q\). It sets \(k=m-R(n)\), splits \(y=xv\) at \(n\), and rejects a certificate region \(v\) containing no 1. Otherwise it writes the region uniquely as
\[
v=u\,1\,0^t
\]
using its last 1, checks \(\lvert u\rvert\le k\), and tests \(xu\in V\). These operations take polynomial time in \(m\); a native TM implementation and ledger are new obligations, not already supplied lemmas.

On a correctly sized input for the exact definition,
\[
m=n+p'(n)=R(n)+p(n),
\]
so the recovered interval is exactly \(n\), and **the recovered \(k\) equals the original \(p(n)\)**. Every old witness pads to
\[
u\,1\,0^{p'(n)-\lvert u\rvert-1},
\]
and every accepted new witness yields an old one. This proves the reverse implication semantically, including \(p(n)=0\), \(x=[]\), non-monotone \(p\), and marker-free-region rejection.

The construction deliberately carries the potentially uncomputable length value in the new total length. It explains why this one direction can work without validating the maintainer’s canonical-majorant normalization.

**Argument D refutes `HALT_NPHard`, independently of the coding details.** Fix any target language \(H\). Polynomial-time total string functions are countable: finite machine tables give countably many behaviors. In this development, total-machine normalization followed by `exists_codeTM` also supplies the relevant finite-code argument.

Choose a sequence \((f_i)_{i\in\mathbb N}\) containing every polynomial-time total function. This sequence need not be effectively enumerable. Define
\[
A=\{i:f_i(0^i)\notin H\}.
\]
Argument A gives \(L_A\in NP\). If a polynomial-time \(f_j\) reduced \(L_A\) to \(H\), then
\[
f_j(0^j)\in H
\iff 0^j\in L_A
\iff j\in A
\iff f_j(0^j)\notin H,
\]
a contradiction. Thus
\[
\forall H,\quad\neg\operatorname{NPHard}(H).
\]
In particular `HALT_NPHard` is false for every effective scheme, and the current `NPComplete` predicate has no instances. The attached `exists_effectiveMachineCode` establishes that effective schemes exist, so the quantified theorem has no empty-domain escape. The collapse implications remain logically valid conditionals, but with impossible premises.

The following answers the pack’s **seven specific questions** directly.

| Question | Answer |
|---|---|
| 1. Can a pathological P-verifier change the class? | **The full displayed definition does change the class**, by Argument A. But language-versus-machine rendering itself is sound: `mem_P_iff` supplies one uniform total decider of \(V\) on every string. For fixed \(p\), changing \(V\) off all strings \(xu\) with the prescribed lengths changes no membership statement. There is no off-domain oracle in \(V\); the oracle is the unconstrained \(p\). |
| 2. Does \(p=0,V=L\) break for empty/full languages or empty input? | No. \(\lvert u\rvert=0\iff u=[]\), and \(x[] =x\), for every \(x\). \(\operatorname{PolyBound}(0)\) holds with \(C=0\). The argument applies to \(L=\varnothing\), \(L=\mathrm{univ}\), and \(x=[]\). |
| 3. Can exact lengths be normalized directly to \(C(n+1)^c\)? | **Not for the current class**: such computable lengths make exhaustive decision possible, contradicting Argument A. A bounded-length detour cannot rescue that claim. After imposing polynomial-time evaluability of \(p\), direct normalization is possible: recover \(n\) from a destination length \(n+Q(n)\), take the first \(p(n)\) certificate bits, ignore the rest, and run the old verifier. This requires no bounded-length detour. |
| 4. Does the enumerator obtain the original width \(p(n)\)? | No. Neither `PolyBound` nor `counterTM` computes \(p(n)\). Enumerating up to a majorant and checking equality still requires an effective equality test with \(p(n)\), which is absent. Replace the definition or add the required uniform length computation; then prove enumeration includes exactly the permitted witnesses. Width zero must execute once on the empty certificate. |
| 5. Do zero-length DTIME conventions invalidate EXP? | No. At \(n=0\), the budget function is 2 for \(c=0\) and 1 for \(c>0\), never zero. The external DTIME multiplier absorbs finite-length discrepancies. |
| 6. Does fixed-searcher coding require an effective scheme? | After repairing the class and searcher construction, **no**. For a fixed coded machine \(S\), take the fixed string \(\alpha=c.\mathrm{encode}(S)\). `MachineCode.decode_encode` is sufficient. Computing a decoder on arbitrary varying codes is not part of this reduction. As currently defined, the hardness theorem is false for every target, so it cannot simply be generalized without the repairs. |
| 7. Does the scoped notation collide? | Only one `≤ₚ` declaration occurs in the supplied 40-module source set. It is scoped to `Complexity`, at comparison precedence 50, and its local uses are consistent. I did not independently load/search the complete pinned Mathlib environment or the rest of the repository, so a global collision-free attestation is not reproduced. A scope limits exposure but does not prevent ambiguity if another opened scope declares the same token. |

Several quantitative and construction checks complete the sketch audit.

The **polynomial budget normalization** is sound:
\[
n^c+1\le2(n+1)^c,\qquad
(n+1)^c\le2^c(n^c+1).
\]
The second is exactly the attached `succ_pow_le`; `mem_P_iff` already realizes both directions with constant factors. These inequalities compare running-time budgets. They do not authorize replacing a semantic certificate-length restriction.

For **FP composition**, write the budgets as \(C(n+1)^c\) and \(C'(n+1)^{c'}\). The public timed theorem supplies some overhead constant \(a\). Since \((n+1)^c\ge1\),
\[
\begin{aligned}
a\bigl(C(n+1)^c+C'(C(n+1)^c+1)^{c'}+1\bigr)
&\le a\bigl(C+C'(C+1)^{c'}+1\bigr)
(n+1)^{\max(c,cc')}.
\end{aligned}
\]
This also handles zero degrees. The required monotonicity is that of the explicit second-machine budget. No monotonicity of an arbitrary `PolyBound` function is used.

For **complementation**, `computesFunInTime_ifEq [true] [false] [true]` implements the needed total postprocessor. The original decider outputs exactly one Boolean, so its output becomes the singleton complement indicator. Convert `DecidesInTime` pointwise into `ComputesFunInTime`, apply timed composition, and return via `mem_P_iff`. There is no append-only-output obstruction: buffered composition prevents the original bit from leaking onto the final output.

For the **EXP union**, for every degree \(c\) and every \(n\),
\[
2^{n^c}\le2\cdot2^{n^{\max(c,2)}}.
\]
Thus degrees 0 and 1 are absorbed by degrees at least 2 and the DTIME constant. Also \(z+1\le2^z\) for natural \(z\), so the `P_subset_EXP` comparison is valid, even slightly stronger than its sketch requires.

For **EXP-to-NEXP padding**, retain the proposed \(p(n)=2^{(n+1)^c}\). It is nondecreasing for every \(c\), hence \(n+p(n)\) is strictly increasing. Given input length \(m\), searching \(n\le m\) is polynomial-time: writing \(2^{(n+1)^c}\) in binary requires \((n+1)^c+1\le(m+1)^c+1\) bits, not exponentially many bits in \(m\). Reject if no split exists. On a valid split, the original decider’s bound \(a\,2^{n^c}\) is at most \(am\). This includes \(c=0\) and rejects malformed short strings, including \(m=0\). Fixed-degree arithmetic, split/copy machinery, and the native verifier’s time ledger are not yet present as a ready-made theorem.

For **the repaired NP enumerator**, a complete implementation must retain the original input and candidate between calls, buffer the verifier’s emissions, reinitialize its used work region and heads, and detect fixed-width counter overflow. A conditional on a machine’s original input is not itself a reusable loop on evolving work-tape configurations. The existing `counterInc` extends its word on overflow; using it unchanged does not give a terminating width-\(p(n)\) enumeration. Public `timeConstructible_id` does provide a binary input-length counter, but no general polynomial evaluator.

With an effective polynomial width \(Q(n)\), a suitable total cost bound has the form
\[
a\,2^{Q(n)}(n+Q(n)+1)^d.
\]
It is bounded by a constant times \(2^{n^e}\) for a sufficiently large fixed degree \(e\), with the finitely many small lengths absorbed by the external constant. That numerical estimate is routine; the missing physical loop, reset, and enumeration invariants are the significant fill obligations.

For **HALT**, the deliberately divergent branch exists in the supplied model. Take one live state, emit nothing, move no heads, and always return that same live state. Every run configuration remains unchanged and its state is never `none`.

The searcher’s difficulty is its conversion to one work tape. `one_work_tape_binary` and `alphabet_reduction` have total-function hypotheses; their internal partial simulation constructions are private. A repair avoiding a new partial normal-form theorem is:

1. After repairing `NP_subset_EXP`, obtain a total decider of \(L\).
2. Apply `one_work_tape_binary` to that total decider.
3. On the resulting one-work-tape machine, add a finite control register that remembers the Boolean emission; when the simulated machine halts, halt iff the remembered bit is true, otherwise enter the stationary loop. Include any bit emitted on the halting transition in this update.
4. Apply `exists_codeTM` to this modified machine. No totality hypothesis is required by `exists_codeTM`.

The control modification needs its own run/halting lemma, but the cited normalization API now applies legally.

For fixed \(\alpha\), `pairEncode α x` is a fixed prefix of length \(2\lvert\alpha\rvert+2\), followed by \(x\). An emit-then-copy controller can compute it in
\[
2\lvert\alpha\rvert+\lvert x\rvert+3
\]
steps: emit the prefix without moving the input head, copy each input bit, then halt on the boundary blank. This also handles \(x=[]\). The bundle proves diagonal pairing, not this fixed-prefix function’s time bound; that small machine or an appropriate prefixing lemma still needs to be added. `HALT_pairEncode_eq_true_iff` and `MachineCode.decode_encode` then give the intended reduction equivalence.

Finally, after a correct `NP_subset_EXP` exists, the proposed **HALT nonmembership chain** is valid: an EXP decider for the HALT language computes the total singleton function \(s\mapsto[\operatorname{HALT}(c,s)]\), contradicting `HALT_not_computable`. Off the pair image, HALT is false, so the decider’s rejection bit matches exactly. The present proof cannot use that chain before repairing the false inclusion.

The **repository-side attestations** have the following reproduction status.

| Attestation | Reproduced from supplied material | Not reproduced / challenged |
|---|---|---|
| 1. Chapter-1 freeze | The bundle contains 34 Chapter-1 modules and six new Chapter-2 modules. | No parent tree or authoritative diff for `f7b8ad0a..ab82bb6a` was supplied. I did not reproduce byte identity, the two commits’ changed-path inventory, or the six-line order-file update. Descriptive closure entries in the plan are historical claims, not comparison evidence. |
| 2. Fresh elaboration | Source contains exactly 19 `sorry` terms, distributed 3/2/4/3/7 across PolyTime/NP/CoNP/EXP/Reductions, and none in the 34 supplied Chapter-1 modules. | No fresh 40-module elaboration, error count, gate result, or warning count was independently produced. Source inventory is not an elaboration test. |
| 3. Admissions and sketches | Every new theorem is accompanied by a `Proof sketch`; the 19 placeholders are localized as claimed. | No kernel axiom traversal/prints were reproduced. The assertion that sketches use only available stated results is challenged: `ComputesFunInTime.mono` is missing, the counters are private, and several cited specifications do not provide the needed timing/totality guarantees. |
| 4. Policy | All 29 new definitions/theorems have declaration docstrings; all 19 theorems have sketches; the facade imports all five children. Excluding bundle-separator whitespace, content line counts are 105/97/99/109/149/31. | Full style lint and its six recorded warnings were not rerun. Statement prose contains findings 7–9. The root `TCSlib.lean` is not supplied, so the policy-required facade export is unverified. Moreover, the claimed change inventory of “new files plus the order file” does not establish that export; provide the root import or an explicit policy exception. |
| 5. New surface | Exactly 10 definitions, 19 theorem declarations with `sorry`, and one scoped notation; all declarations lie in `Complexity`. The child files use only the three standard options. No new explicit axiom or instance declaration occurs. Imports are in-repository children or the three named Chapter-1 dependencies. | Repository-wide absence of additional changes, complete imported-environment axiom properties, and notation compatibility with pinned Mathlib remain unverified. |

I did not re-audit Chapter-1 mathematics or dispose of the seeded phase-2/phase-3 design questions.

For a concrete phase-1 repair, retain the P-language abstraction, use `pairEncode x u` or a separately specified two-input verifier, and quantify over **explicit effective length formulas**. For example, the NP interface can quantify over \(C,c,V\) and use exactly \(C(\lvert x\rvert+1)^c\) certificate bits. Its bounded-length companion must impose the same effectiveness discipline. An analogous explicit exponential formula can serve NEXP. Merely requiring that an arbitrary \(p\) be computable is insufficient to guarantee polynomial or exponential evaluation time; merely requiring monotonicity is refuted by Argument A.

These changes also require updating the easy sketches: with actual pairing, \(p=0\) still proves \(P\subseteq NP\), but the verifier must parse the pair rather than literally take \(V=L\). The repaired padding and verifier constructions should be stated with their native machine/time obligations before the next statement gate.

**Notation glossary.** \(xu\) is concatenation; \(\lvert x\rvert\) is string length; \(0,1\) mean `false,true`; \(0^n\) and \(1^n\) are the all-zero and all-one strings of length \(n\); \([]\) is the empty string; \(L^c\) is complement among all binary strings. \(A\) is a set of lengths; \(p_A,L_A,V_0\) are Argument A’s length selector, length language, and modulo-3 verifier. \(K_A,W\) are Argument B’s prefix-free language and verifier. \(Q\) is a polynomial majorant; \(R\) and \(p'\) are Argument C’s interval base and new exact certificate length; \(m=\lvert y\rvert\), \(k=m-R(n)\), and \(t\) counts padding zeros. \(H\) is an arbitrary reduction target; \(f_i\) enumerates polynomial-time total functions. \(L,L\prime,L\prime\prime\) denote languages, \(V\) a verifier language, \(p\) an original certificate-length function, \(M,S\) machines, \(f,g\) string functions, and \(x,y,u,v,s,\alpha\) binary strings, with \(\alpha\) a fixed machine code where specified. \(C,C',a\) are fixed natural coefficients and \(c,c',d,e\) fixed natural degrees; \(n,r,i,j\) are natural indices or lengths, and \(z\) is a natural number in the exponential comparison. Scheme \(c\) in the HALT discussion is the source’s representation-scheme parameter, distinct from a polynomial degree. FP means polynomial-time computable total string functions; \(L\le_p L'\) is the supplied Karp reduction relation.
