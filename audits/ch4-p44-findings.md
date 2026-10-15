# P4.4 statement-gate audit

**Verdict: PASS — 0 blockers, 0 majors, 2 minors, 5 notes.** All six definitions and eleven sorried statements were checked. The two defects are in the `mem_LOGSPACE_of_logspaceReducible` proof sketch; neither requires changing its statement. This is a mathematical statement audit, not a Lean proof certification or permission to treat the pending constructions as proved.

The supplied bundle's SHA-256 is exactly `899d3c43d6576dff48f96dccaee4b56370699563ee03b2cc010eea96072698ca`. The declared baseline is `200f4693a40f30302efed75a4e23ac31216172b7`. The P4.2 surface is treated as supplied, with the upstream observation explicitly prefixed below. This verdict does not close P4.2 or the routine-infrastructure gate.

**Findings**

Paths in this table are relative to `TCSlib/Complexity/SpaceComplexity/`, except where indicated. Line numbers refer to the extracted attachment, not the enclosing bundle.

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | minor | `Logspace/Reductions.lean:106–108` · `mem_LOGSPACE_of_logspaceReducible` | The characteristic function's length language is total. | Its output has length one, so a genuine query is accepted iff `i < 1`, equivalently `i = 0`. The query `pairEncode x [true]`, representing index 1, is rejected for every `x`. Malformed query strings are also rejected. | Say that the length language is exactly `{pairEncode x [] : x : List Bool}`, a regular language. Distinguish this from a total **decider** for that language. |
| 2 | minor | `Logspace/Reductions.lean:110–113` · same declaration | Specializing index 0 is a fixed-suffix specialization. | `pairEncode x [] = dbl x ++ [false,true]`, not `x ++ [false,true]`. For example, input `[true]` must be presented to the query machine as `1101`, not `101`. | Name a fixed-index **paired-input** specialization. Prove it directly by simulating the query decider on the doubled virtual input with its separator; do not invoke the downward-closure theorem being proved. |
| 3 | note | `Logspace/Reductions.lean:76–88` · `ImplicitlyLogspaceComputable.comp` | The virtual-input argument supplies both query languages. | Correct, including empty outputs, but the actual virtual input is `pairEncode (f x) (Nat.bits i)`. Query indices are unbounded in the definition; an arbitrary binary index cannot simply be copied into logarithmic workspace. | Carry malformed-query rejection, index-length/overflow handling, the paired layout, and the length-query boundary test into the fill. Question 2 gives a sufficient ledger. No signature change. |
| 4 | note | `Logspace/Path.lean:111–129` · `PATH_NLComplete`; plan's P4.4 row | Accepting normalization discharges the P0 unique-terminal caveat. | It is a sound **planned** discharge, explicitly listed as a fill obligation. The received `cleanTM` discipline alone is insufficient: the P0 report records that it does not reset the input head. Normalization also changes the machine and potentially its space constant. | Prove preservation of acceptance, all-branch halting, and space; blank all work tapes, park all work heads **and the input head**, preserve the output summary, and use the normalized machine's count/window. Until then, describe the caveat as assigned here, not already proved closed. |
| 5 | note | `Logspace/ImmermanSzelepcsenyi.lean:60–79` · `compl_PATH_mem_NL` | The counting verifier uses one read-once choice word. | Sound with sequentially regenerated path certificates. The negative test must check `A u v = false`, where `u` is enumerated from the previous ball; strict ordering and exact previous counts are indispensable. | Make these predicates and the complete outer enumeration explicit in the fill brief. Include canonical field validation and accept its failure before counting. Question 6 supplies the invariant and stream layout. |
| 6 | note | `Logspace/ImmermanSzelepcsenyi.lean:85–91` · `NL_eq_coNL` | Downward closure of `NL` follows from virtual-input simulation. | True, but not a consequence of the deterministic downward-closure statement alone. The simulation must preserve nondeterministic acceptance and all-branch halting while deterministic query subroutines consume ignored choice bits. | Recommend an additive `mem_NL_of_logspaceReducible` contract before fill. Its promotion is not required to pass this gate: the pack and workflow explicitly permit this named fill obligation. |
| 7 | note | `[P4.2] ConfigGraph.lean` · `coreSum`, `CfgStep`, `configBound`, `reflTransGen_cfgStep_iff` | These declarations are the configuration-graph surface used by P4.4. | The declarations are consistent, but `CfgStep` is on full configurations and `coreSum` is not itself a finite numbered graph. A count and a full-configuration reachability dictionary do not alone provide a numbered-graph codec or path-lifting theorem. | No correction to these signatures is requested. The P4.4 consumer must supply the bounded codec, reject/omit transitions leaving its window, and prove path projection and lifting using `coreSum_stepWith`. Do not claim those interfaces are already exported by P4.2. |

**Evidence and source boundary**

The bundle contains 24 attachments. A comment-stripped inventory of the four target modules confirms exactly six `def`s, eleven theorem declarations, eleven `sorry`s, and the scoped `≤ₗ` notation. Their per-file counts agree with the pack: Reductions 2/5, Path 3/2, Immerman–Szelepcsényi 0/3, Mult 1/1 (definitions/statements).

The supplied sweep names the four modules and the facade, records the declared revision at its start, contains eleven admission warnings and no `error:` lines, and ends with `P4.4_SWEEP_DONE`. The style log reports zero failures/warnings over 42 files. These textual attestations agree with the pack. Neither `lean` nor `lake` is available on PATH here, and the bundle is not a Git checkout: I did not independently elaborate, inspect fresh `.olean`s, reproduce lint, or verify `git diff ec400dc5 200f4693`. The raw NDTM implementation, `ConfigCount` codec implementation, and cited `Machines/*` infrastructure are not separate attachments; their relevant supplied interfaces and the closed-context attestations were used. No GitHub interaction or source modification was performed.

The comparison source was the **2009 book itself**, read from the [AB09 PDF mirror](https://theswissbay.ch/pdf/Gentoomen%20Library/Theory%20Of%20Computation/Sanjeev_Arora%2C_Boaz_Barak-Computational_complexity__a_modern_approach-Cambridge_University_Press%282009%29.pdf), not the differently numbered 2007 draft. Printed-page references:

| Source | Comparison baseline |
|---|---|
| §4.1.2, p. 82, Example 4.7 and (4.1) | Multiplication is in deterministic logspace; bounded nondeterministic walks decide directed reachability. |
| Definition 4.16, Lemma 4.17, Figure 4.3, pp. 88–89 | Polynomial output length plus logspace bit/length queries define reductions; composition and deterministic downward closure hold. |
| Theorem 4.18, p. 89 | Configuration graphs give `NL`-hardness of `PATH`. |
| Definition 4.19, p. 90 | Polynomial read-once certificates characterize `NL`. |
| Theorem 4.20 and Corollary 4.21, pp. 91–92 | Inductive counting gives complement closure, including constructible bounds above logarithmic space. |

The following are independent checks of the supplied formal surface and its implementation obligations, not claims of completed Lean constructions.

**Definition restatements from the Lean bodies**

The received interface must be expanded first. `ImplicitlyLogspaceComputable f` is precisely the conjunction

\[
\begin{aligned}
&\exists C,c\in\mathbb N\;\forall x,\quad |f(x)|\le C(|x|+1)^c,\\
&\{\operatorname{pairEncode}(x,\operatorname{bits}(i)):
                 (f(x)).\operatorname{getD}(i,\mathrm{false})=\mathrm{true}\}
       \in\mathrm{LOGSPACE},\\
&\{\operatorname{pairEncode}(x,\operatorname{bits}(i)):i<|f(x)|\}
       \in\mathrm{LOGSPACE}.
\end{aligned}
\]

Each set has existential membership over genuine encodings: all malformed pairs and noncanonical index representations are excluded. Indices begin at zero; `bits` is canonical little-endian binary, with `bits 0 = []`. The bit query returns false outside the output; the length query separately distinguishes a zero bit from absence. `LOGSPACE` measures workspace against the **entire encoded query's length**.

| Definition | Mathematical restatement | Fidelity check |
|---|---|---|
| `LogspaceReducible B C` | Some total string function satisfying all three conditions above has `x ∈ B ↔ f x ∈ C` for every string `x`. | Correct many-one direction and quantifiers. The two inherited normalizations are discussed in question 1. |
| `NLComplete C` | `C ∈ NL`, and every `B ∈ NL` has such a reduction to `C`. | Both membership and hardness are required; no nontriviality hypothesis is hidden. |
| `GraphReach A s t` | There is a finite sequence of directed edges `A u v = true` from `s` to `t`, allowing zero edges. | Correct reflexive directed reachability, irrespective of self-loops. |
| `encodePATH n A s t` | Pair the all-true word of length `n` with a pair of the row-major `n × n` Boolean matrix and the pair of canonical endpoint representations. | Row `u`, column `v` has matrix index `u*n+v`; the dependent endpoint types enforce `n > 0`. |
| `PATH` | A string belongs exactly when it equals an encoding of some such graph and endpoints with `GraphReach A s t`. | No decoder fallback; malformed strings are outside the language. The witnesses cannot disagree about the decoded graph. |
| `multLang` | A string belongs exactly when it is the nested paired encoding of canonical binary representations of two naturals and their product. | Includes both zero operands. Pair/triple syntax and canonical binary conventions are explicitly fixed rather than supplied by the book. |

**All eleven statement checks**

The constructions referenced below are detailed in the numbered answers. “True” here means the stated mathematical contract is supported, not that its `sorry` has been eliminated.

| # | Sorried declaration | True-as-stated argument |
|---|---|---|
| T1 | `ImplicitlyLogspaceComputable.comp` | The composite output bound is polynomial by the inequality in question 2. Simulating either query decider for `g` on the virtual paired input, and servicing virtual `f`-bits and boundaries with its two supplied deciders, uses logarithmic space. Malformed and oversized queries can be rejected within that bound; each simulation halts. |
| T2 | `LogspaceReducible.trans` | Extract witnesses `f,g` and apply T1. For every `x`, `x ∈ B ↔ f x ∈ C ↔ g(f x) ∈ D`; thus `g ∘ f` has the required membership equivalence. |
| T3 | `mem_LOGSPACE_of_logspaceReducible` | The one-bit characteristic function of `C` has a polynomial bound and the two logspace query languages specified in question 3. Apply T1 to its composition with the reduction, then directly specialize the query decider to `pairEncode x []`. This proves the statement after correcting findings 1–2. |
| T4 | `LogspaceReducible.polyTimeReducible` | Apply the received `ImplicitlyLogspaceComputable.polyTimeComputable` to the same witness. `PolyTimeReducible` requires exactly that resulting computability property and the unchanged membership equivalence. |
| T5 | `NL_eq_LOGSPACE_of_nlComplete_mem_LOGSPACE` | Every member of `NL` reduces to the complete language, so T3 puts it in `LOGSPACE`. The converse inclusion is the supplied `LOGSPACE_subset_NL`. The reverse direction of the book's “iff” remark follows immediately from `NLComplete`'s membership conjunct and the equality. |
| T6 | `PATH_mem_NL` | Validate the complete encoding, check `s=t` immediately, then guess at most `n` edges with bounded vertex registers. A reachable target has a simple path of at most `n−1` edges, and all guessed walks stop at the cap. Space is logarithmic in the actual input length, including validation. |
| T7 | `PATH_NLComplete` | T6 proves membership. A bounded configuration graph retaining the output summary, with a single accepting target, gives a polynomial-size graph whose encoded bits and length are computable in logspace. Projection/lifting proves the membership equivalence; normalization and codec construction remain genuine named fill obligations. |
| T8 | `compl_PATH_mem_NL` | Accept malformed inputs. On valid instances, the induction in question 6 ensures that any surviving branch has the exact ball counts, while true certificates exist for every needed classification. The final exclusion test succeeds exactly when the target is unreachable, using bounded loops and logarithmic workspace. |
| T9 | `NL_eq_coNL` | For `B ∈ NL`, complement the membership equivalence of its reduction to `PATH` to get `Bᶜ ≤ₗ PATHᶜ`. T8 and nondeterministic downward closure give `Bᶜ ∈ NL`. Applying that implication to complements proves the reverse inclusion as well. |
| T10 | `NSPACE_compl_eq` | Compute the window from the constructibility witness and run the same counting algorithm on bounded configuration codes. Their lengths, all counters, and adjacency tests require `O(S n)` space by question 7. This constructs a decider for each complement; applying closure twice gives the displayed set equality. |
| T11 | `multLang_mem_LOGSPACE` | Validate all three canonical number fields and compute product columns with the bounded carry invariant in question 8. Compare every relevant output bit, reject excessive result length, and check that no carry remains. Zero operands and empty binary words need no extra space or hypothesis. |

**Answers to the eight numbered questions**

**1. Reducibility and the received divergences.** Both query languages and the polynomial output bound are present; none is inferred from the others. Reindexing `i` to `i+1` reconciles the zero-based and one-based conventions without changing the intended function class. The polynomial normalization does change a *literal*, all-input reading of the book's bound: the constant function with output `[false,false]` witnesses

\[
\operatorname{Set.univ}\le_l\{[\mathrm{false},\mathrm{false}]\}
\]

here, whereas `|f(x)| ≤ |x|^c` forces length at most one on every one-bit input and cannot witness this reduction. This is an already-declared, appropriate normalization of polynomial boundedness, not an undeclared discrepancy. Neither change damages composition or the intended complexity-theoretic results.

**2. Composition.** Suppose the bounds for `f,g` are `C(|x|+1)^c` and `D(|y|+1)^d`. Since `(|x|+1)^c ≥ 1`,

\[
\begin{aligned}
|g(f(x))|&\le D(|f(x)|+1)^d\\
&\le D\bigl((C+1)(|x|+1)^c\bigr)^d\\
&=D(C+1)^d(|x|+1)^{cd}.
\end{aligned}
\]

This includes zero constants/exponents and empty outputs. On a query word `w`, parse the aligned pair and validate the canonical index. Before storing its numerical value, compare its bit-length and, if necessary, its bits against the displayed polynomial bound: values at or beyond the bound make both queries false. Parsing an arbitrarily long index requires only counters of `O(log(|w|+2))` bits; an index small enough to retain has `O(log(|x|+2))` bits.

Compute `|f(x)|` by sequential length queries up to its polynomial bound. Simulate `g`'s appropriate query machine on `pairEncode (f x) (bits i)`: duplicated data positions use `f`'s bit query, the separator and index suffix use direct arithmetic, and endmarkers use the computed length. The virtual input length is polynomial in `|x|+1` after the index check. The suspended outer workspace, virtual head, inner query workspace, and counters occupy a constant number of logarithmic regions; calls reuse these regions rather than accumulating them. The two machines halt, and inner queries are deterministic. This supplies **both** `indexLang` memberships without storing `f(x)`.

**3. Transitivity, downward closure, polynomial refinement, collapse.** For the one-bit characteristic function `χ_C`, the exact query conditions on genuine pairs are

\[
\begin{aligned}
(\chi_C(x)).\operatorname{getD}(i,\mathrm{false})=\mathrm{true}
   &\iff i=0\ \land\ x\in C,\\
i<|\chi_C(x)|&\iff i=0.
\end{aligned}
\]

The first is decided by checking the paired shape/index and simulating the `C` decider on the decoded first component; the second is regular. For the last specialization step, directly simulate the resulting query decider on `dbl x ++ [false,true]`. A virtual head into this word needs `O(log(|x|+2))` bits and maps each doubled position back to one input bit. This elementary construction is independent of the general downward-closure theorem, avoiding circularity. T2, T4, and T5 then follow by the displayed membership equivalences and received inclusions.

**4. Encoding and `PATH`.** Applying `pairDecode` to equal encodings first gives equal unary words, hence equal vertex counts. Two further pair decodings give equal flattened matrices and endpoint bitstrings; `Nat.bits` injectivity gives equal endpoint values. For the now-common `n`, the matrix's entry at `u*n+v` recovers `A u v`, so function extensionality recovers the entire matrix.

Repeated use of `length_pairEncode` gives

\[
|\operatorname{encodePATH}(n,A,s,t)|
 =2n^2+2n+2|\operatorname{bits}(s)|+|\operatorname{bits}(t)|+6.
\]

Thus every instance is nonempty. `Fin 0` rules out a graph with designated vertices at `n=0`; it does not omit any legitimate empty-graph instance with two actual vertices. The zero-length path is legitimate: `GraphReach A s s` holds even without a loop. An empty endpoint word represents vertex zero unambiguously because the pair separator delimits it.

The validator must check three pair layers, an all-true nonempty unary field, exactly `n²` matrix bits, and canonical endpoint words denoting values below `n`. Canonical words are empty or end in `true`; merely interpreting padded binary numerals numerically is insufficient. Injectivity is useful for proving this validator exact and for lifting the decoded graph's result back to existential language membership. No total decoder fallback is needed.

**5. `PATH` membership and hardness.** Validation uses counters bounded polynomially in input length. After it succeeds, two vertex registers, a round counter, and matrix-address arithmetic remain logarithmic; when `n=1`, the counter still needs a constant number of cells. Test equality with the target before the first guessed edge, enforce guessed vertices `< n`, and halt every branch after at most `n` rounds.

For hardness, enumerate bounded configurations with blank tape outside the chosen window, including input-head position, state, tape contents/heads, and `OutSummary`. An adjacency test checks one possible transition and compares the resulting bounded code; it must not clamp an out-of-window successor into a valid vertex. From the real initial configuration, the space bound ensures every actual reachable configuration stays in the window. Conversely, step compatibility of the summary allows each coded path to be lifted to a real choice-word run. Halted state **and** `.accept` summary are required for acceptance.

An erase-and-park implementation is possible: record enough visited-boundary information during simulation, redirect halts into cleanup, erase the visited regions, return work heads to fixed origins, and return the input head to a fixed boundary. Preserve original output or track its summary without turning a dead output into acceptance. Boundary records and cleanup use `O(c₀ logSpace |x| + logSpace |x|)` space; count the **new** machine with a suitably enlarged constant. `cleanTM` is a model for part of this construction, not a supplied proof of it. Alternatively, a graph-level extra accepting sink would avoid machine cleanup, but would require revising the declared proof route, not the theorem.

The count is polynomial in `|x|+1` for a fixed machine and logarithmic window. Squaring it for an adjacency matrix remains polynomial. The paired encoding's length follows from question 4 and the endpoint-code lengths; its length query is arithmetic in the input length and index (the sketch's “in `i`” suppresses the input-length dependence). The default-false bit query must also handle every out-of-range index. None of this needs the P4.3 adjacency-CNF result.

**6. Counting and the single choice word.** For valid graphs, use the pack's balls `C_i` and counts `c_i`. Their defining recurrence is

\[
C_0=\{s\},\qquad
C_i=C_{i-1}\cup\{v:\exists u\in C_{i-1},\ A(u,v)=\mathrm{true}\}.
\]

Assume the preceding count is correct. A strictly increasing list of `c_{i-1}` vertices, each equipped with a verified path of length at most `i−1`, is a subset of `C_{i-1}` of the same size; hence it is exactly `C_{i-1}`. Therefore requiring, for every listed `u`, both `u ≠ v` and `A(u,v)=false` proves exactly `v ∉ C_i`. Notice the direction `u→v`.

At stage `i`, process **every** vertex `v=0,…,n−1`. Guess its membership flag and check either a length-at-most-`i` path or the preceding negative certificate; count the positive flags and compare that count with the proposed `c_i`. Starting from the verified `c_0=1`, induction forces every retained count to be correct. At the end, enumerate `c_n` distinct certified members of `C_n`, excluding `t`. This succeeds iff `t∉C_n`; finite-graph cycle removal gives `C_n` equal to the reachable set.

The stream order is: stage, next classified vertex, its flag, its positive path **or** its negative list of vertices and fresh positive paths, then the next classified vertex. Store the outer vertex and counter while consuming the inner path; discard each path after checking it. Later certificates may use different paths to the same vertex. No path or prior certificate bit is revisited, and the number of simultaneously stored registers is constant. Bound each list and path length, reject out-of-range values, and use fixed finite loop bounds even on dishonest choices. There are at most `O(n^4 log(n+2))` meaningful certificate bits; input rescans and deterministic microsteps still give a polynomial running bound in encoded input length.

A physical NDTM step consumes a choice bit even during deterministic work. Those bits can be ignored; successful certificate bits occupy the guessing steps, and the word is padded after halting to the common budget. Thus the direct construction needs no separate certificate-tape model. Finally, accept validator failure deterministically: `PATHᶜ` includes **all** malformed words, not just well-formed nonreachable instances.

**7. Complement equalities and the closure obligation.** The deterministic reduction remains unchanged under complementation:

\[
x\in B^c\iff f(x)\in C^c.
\]

For nondeterministic downward closure, retain the target machine's simulated configuration while running deterministic `f`-queries, then resume with the next actual nondeterministic choice. Each host branch projects to a target branch; every target branch can be realized by inserting ignored bits during the deterministic work. The target's all-branch halting budget on the fixed input `f(x)`, together with the finitely many halting query calls needed within that budget, gives a finite common host budget. Polynomial output length makes all workspace logarithmic. An appropriate standalone contract is

```lean
theorem mem_NL_of_logspaceReducible {B C : Language Bool}
    (h : B ≤ₗ C) (hC : C ∈ NL) : B ∈ NL
```

Its explicit promotion would improve the frozen audit surface; the present named-obligation policy does not require it as a condition of PASS.

For the general bound, write `n=|x|`, `s=c₀*S n`, `k=N.k`, and `q=Fintype.card N.State`. The supplied count obeys

\[
\begin{aligned}
N.\operatorname{configBound}(n,s)
 &=3(q+1)(n+2)3^{k(2s+1)}(2s+1)^k\\
 &\le3(q+1)(n+2)2^{5ks+3k}\\
 &\le3(q+1)2^{(5kc_0+1)S(n)+3k+1}.
\end{aligned}
\]

Here `3^r ≤ 2^(2r)`, `2s+1 ≤ 2^(s+1)`, and the bundled logarithmic floor supplies `n+2 ≤ 2^(S n+1)`. Thus vertex codes and counters have `O(S n)` bits, even though the number of vertices can be exponential. Compute and retain the binary window bound using the constructibility witness, then reuse the counting space. Constructibility supplies this effective bound; it is not additionally needed for the combinatorial induction. The separately bundled logarithmic floor pays for input addressing and constant overhead. No monotonicity of `S` is required.

For the exact set equality, closure sends a member of the right-hand side to a member of the left-hand side. If `L` belongs to the left, apply closure to `Lᶜ` and use `(Lᶜ)ᶜ=L` to obtain membership on the right. Empty inputs are harmless because `S 0 ≥ logSpace 0 = 1`.

**8. Multiplication.** Pair injectivity and binary injectivity make the existential language exactly the canonical triples satisfying the product equation. In particular,

\[
\operatorname{pairEncode}([],\operatorname{pairEncode}([],[]))=0101\in\mathrm{multLang};
\]

the whole empty word is not a member. Both `a=0` and `b=0` require the product field to be empty.

For input bits `a_p,b_q`, maintain the carry and column sum via

\[
\begin{aligned}
\operatorname{carry}_0&=0,\\
\operatorname{column}_j&=\sum_{p+q=j}a_p b_q,\\
\operatorname{productbit}_j&=(\operatorname{carry}_j+\operatorname{column}_j)\bmod2,\\
\operatorname{carry}_{j+1}&=\left\lfloor
 (\operatorname{carry}_j+\operatorname{column}_j)/2\right\rfloor.
\end{aligned}
\]

The correctness invariant is

\[
\sum_{r<j}2^r\operatorname{column}_r
 =\sum_{r<j}2^r\operatorname{productbit}_r+2^j\operatorname{carry}_j.
\]

If `m` is the total encoded input length, then `column_j ≤ m`; induction gives `carry_j ≤ m`, and the temporary sum is at most `2m`. All counters and arithmetic therefore use `O(log(m+2))` bits. Validate canonical words, reject a result field longer than the sum of the two operand bit-lengths, and compare through that many columns using zero for missing result bits. This handles products whose bit-length is smaller than the maximum column count, including zero; “simultaneous end” must not mean that these lengths are always equal.

**Adversarial instantiations**

Bitstrings in this table spell Boolean lists with `0=false`, `1=true`.

| Test | Instantiation and calculation | Outcome |
|---|---|---|
| A1 | Empty word `[]`. Every graph encoding has length at least 10; every multiplication encoding at least 4. | Outside `PATH` and `multLang`; inside `PATHᶜ`. |
| A2 | `n=1`, no edges, `s=t=0`; encoding `1101000101`. | In `PATH` by the zero-edge path. A walk requiring a first edge would be wrong. |
| A3 | Same graph with its self-loop; encoding `1101110101`. | Still in `PATH`, with no encoding collision with A2. |
| A4 | Attempted zero-vertex shape `010101` (three nested empty pairs). | No `Fin 0` endpoint exists; reject as an instance and accept in the complement. |
| A5 | A2 with endpoint zero encoded as `[false]` instead of `[]`. | Numerically suggestive but noncanonical: outside `PATH`, inside its complement. |
| A6 | Two vertices, only edge `0→1`. | `(s,t)=(0,1)` is reachable; `(1,0)` is not. Reversing adjacency in the negative certificate fails this test. |
| A7 | `(a,b)=(0,0)` gives `0101`; `(0,1)` gives `011101`. | Both in `multLang`. Empty fields are genuine zero representations. |
| A8 | Triple `⟨0,b,1⟩`, or any correct product field with an extra terminal `false` bit. | Both rejected: the first arithmetically, the second by canonical validation. |
| A9 | `NLComplete ∅` would require the universal language to reduce to the empty language; `NLComplete Set.univ` would require the empty language to reduce to the universal language. | Both impossible. Both source languages have constant-output deciders in `NL`, so the hardness quantifier is not vacuous. |
| A10 | `f x=[]` for every `x`. Its two query languages are empty, and its length bound has `C=0`. | A valid implicit function. It reduces exactly `B=Set.univ` when `[]∈C`, and exactly `B=∅` otherwise. |
| A11 | One-bit characteristic output queried at index 1. | Length query is false for every input, witnessing finding 1. |
| A12 | A bounded function outputs `[false]` on an undecidable language and `[]` otherwise. | Its bit language is empty, but its length query at index 0 is undecidable. The received third conjunct correctly excludes it. |
| A13 | A machine emits `true`, then `false`, then halts. | Its live `.accept` summary is not acceptance; the terminal summary is `.dead`. Hardness must require halting and preserve the summary. |
| A14 | Constant two-bit reduction from `Set.univ` to the singleton containing `00`. | Allowed here, excluded by the literal `length(x)^c` bound on one-bit inputs; confirms the declared normalization's exact effect. |
| A15 | `S=logSpace`, including input length zero; also a zero-work-tape source machine. | The complement construction has positive administrative space available. A zero-tape source does not force its simulator to use zero tapes. |

As independent finite checks, a direct Python translation verified 961 pair round-trips with no collisions; all 4,674 graph encodings for `1≤n≤3`, their lengths, decoding, and injectivity; 13,954 local inductive-counting cases; and 12,288 multiplication checks with `0≤a,b<64` (correct product, padded representation, and incorrect product). All passed. These checks are diagnostic evidence, not Lean tests or substitutes for the general arguments above.

**Suggested additive sanity contracts**

No existing frozen statement needs alteration. Useful permanent checks are: the exact `encodePATH` length; recovery/injectivity of its components; `encodePATH n A s t ∈ PATH ↔ GraphReach A s t`; reflexive membership; exclusion of the empty word; acceptance of every malformed word by `PATHᶜ`; membership of the zero-product encodings; the fixed-index `indexLang` specialization; and the proposed nondeterministic downward-closure contract. The codec, normalization, and compiler proofs remain fill obligations, not new conclusions certified by this report.

**Notation glossary.** `|x|` is word length; `[]` is the empty word; `bits` is `Nat.bits`; `dbl` repeats each bit; `≤ₗ` is the supplied logspace reducibility; `Lᶜ`/`L^c` is language complement; `Set.univ` is all Boolean words. `χ_C` is the one-bit characteristic function of `C`. `C,c,D,d` are the respective output-bound constants/exponents for `f,g`. `C_i,c_i` are the reachable ball and its size. In the configuration calculation, `n=|x|`, `s=c₀S(n)`, `k` is the tape count, and `q` the live-state count. In the multiplication calculation, `m` is encoded input length, `a_p,b_q` are operand bits, and `column_j`, `carry_j`, `productbit_j` are the displayed grade-school quantities. All other identifiers are those of the supplied pack.
