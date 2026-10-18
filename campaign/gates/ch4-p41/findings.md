Input SHA-256: `58bdb7680b3bfe2f888509ed81a0fbc75e15197647c13150f995fc22a30c31de`

**PASS — 0 blockers, 0 majors, 5 minors, 4 notes.**

Chapter 4, phase P4.1, statement-gate audit. Audited snapshot: `edea2663748fe2b1e47636094b95744ed50148f0` on `complexity/arora-barak-ch3-4`. The uploaded bundle has exactly **22 attachments**.

All **10 in-scope definitions**, **14 sorried statements**, and the additional proved lemma `visitedWith_nil` were reviewed. The theorem statements withstand the attacks below. The five minors concern sketches, attribution, a proposed import dependency, and packet completeness; none requires weakening a theorem. The zero-blocker/zero-major gate therefore closes.

This is a statement audit with mathematical derivations and explicit machine-construction obligations, not a kernel certification of the deferred proofs. I did not modify the repository or the uploaded bundle.

**Findings**

File names below are relative to `TCSlib/Complexity/SpaceComplexity/` unless another path is given. Line numbers refer to the source inside the bundle.

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | minor | `Constructible.lean:60–67` · `spaceConstructible_logSpace` sketch | The claimed identity between binary-word length and `logSpace` fails at zero; the described algorithm needs an empty-input case. | `Nat.bits 0 = []`, hence its length is 0, whereas `logSpace 0 = 1`. Counting the length of that empty counter word and emitting its bits outputs `[]`, but the required output is `[true]`. Word length also excludes boundary cells visited by scans. | State the word-length identity for positive inputs, emit the bits of 1 when the input is empty, and bound counter workspace by `logSpace n + O(1)` before absorbing constants. The theorem is unchanged. |
| 2 | minor | `Constructible.lean:71–78` · `spaceConstructible_linear` sketch | The scan counter described in the sketch computes the input length, not its successor. | At empty input, an ordinary length counter holds 0; the specified function must output the bits of 1. For any length, an additional increment or an initial value of 1 is required. The phrase “vacuous zero bound” is also inappropriate for space: zero space is nonempty under P0. | Initialize the counter to 1 and increment once per input symbol, then emit its bits. Include the final counter width and boundary cells in the ledger. Describe `+ 1` as preventing the inherited collapse and satisfying the dominance conjunct. |
| 3 | minor | `Constructible.lean:19–21` · module docstring | The exact-time counterexample does not justify the asserted exact-space counterexample. | The cited argument in the attached `TimeConstructible.lean` forces premature halting from a time deadline. A space deadline does not force that halt; the machine can continue scanning while reusing cells. [AB09, p. 79] already defines constructibility with asymptotic space slack. | Remove the assertion that the exact-space variant was refuted by the time argument. Say that the multiplicative constant implements the book’s space convention; a separate exact-space claim would need its own statement and evidence. |
| 4 | minor | Pack deviation 8; `Examples.lean` · `evenLang_mem_LOGSPACE`; `ZeroSpace.lean:6` | The recommended parity proof route is incompatible with the present import order. | The pack recommends deriving the theorem in `Examples` from `Complexity.evenLang_mem_SPACE_zero` in `ZeroSpace.lean`. But `ZeroSpace` imports `Examples` to obtain `evenLang`. Importing the former back into the latter would create a cycle. There is no current source cycle. | Keep a direct parity proof in `Examples`, or put a shared construction in a genuinely lower module before adopting the proposed dependency. The existing one-work-tape construction is valid; a direct zero-tape construction also suffices. |
| 5 | minor | Pack · inventory and supporting attachments | The pack’s inventory and attachment description are incomplete. | There are 10 definitions: the advertised two measure definitions and six class/predicate definitions, plus `FinNDTM.DecidesInSpace` and `evenLang`. There is also a proved `visitedWith_nil` not explicitly declared as a skeleton-time proof exception. The referenced P0 resolutions and `audits/TEMPLATE.md` are absent; the imported definition of `AcceptsWithin` in `ClassNP/NTIME.lean` is absent too. The 14-sorry count is correct. | Record a packet erratum and complete future manifests. Include the resolutions and acceptance definition, and list the proved lemma as audited surface. I recovered the resolutions and acceptance definition at the exact audited commit; the attached workflow supplies the severity guide. |
| 6 | note | `NSPACE.lean` · `NSPACE` | The zero-bound collapse is real, inherited, and contained by this phase’s normalized classes. An NSPACE sanity twin is useful but is not a prerequisite for this gate. | Every branch visits each work tape’s initial head position. A zero at any input length therefore forces the witness machine to have zero work tapes globally. The derivation below gives the exact class equality. `n ^ c + 1` and `logSpace` are everywhere positive. | Add the tape-count lower bound, collapse, and positive-normalization twins as explicit future sanity obligations; mention the collapse locally in the NSPACE documentation. Preserve the P0 convention. |
| 7 | note | `NondeterministicSpace.lean`; `NSPACE.lean` | Exact-length quantifiers are sound, including shorter runs, with the declared all-branch-halting convention. | Short words extend to length `T`; longer words pass through a halted length-`T` prefix. Acceptance also pads and truncates correctly. All branches, including rejecting branches, are space bounded. | Retain the definitions. Include the short-prefix argument in the fill; post-halt invariance alone explains only longer words. Do not advertise equivalence to the book’s potentially nonhalting convention for arbitrary unqualified bounds. |
| 8 | note | `Inclusions.lean` · `NP_subset_PSPACE` | The statement is true, but the planned fill has a genuine space-composition dependency. | A standalone verifier-space bound does not establish a space bound for a host that repeatedly invokes it. The host must restore scratch, reset heads, preserve the certificate, suppress intermediate physical output, and keep every invocation in fixed tape windows. Summing a per-call space estimate over exponentially many calls is insufficient. | Carry the explicit obligations in question 5 into the fill brief. The modular route needs the relevant §12 R1/R2/R3 contracts, or a separately proved direct simulation. A time-only virtual-input citation does not discharge those obligations. |
| 9 | note | `Inclusions.lean` · `SAT3_mem_PSPACE`; phase scope | The delivered statement establishes polynomial-space membership, not the book example’s sharper linear-space implementation. | The proof routes through arbitrary NP membership. Its resulting polynomial degree need not be one. The packet expressly scopes Example 4.6 to memberships and defers the other listed chapter results. | Describe the result at its actual strength. Keep `MULT`, `PATH`, Theorem 4.2(iii), Savitch, and complement closure in their declared later phases. No strengthening is required for this gate. |

**Evidence and verification limits**

The hash was recomputed from the uploaded bytes and matches the commissioned value. Splitting at the attachment headers gives 22 attachments. The source inventory is:

| In-scope file | Definitions | Sorried theorems | Proved lemmas |
|---|---:|---:|---:|
| `TuringMachine/NondeterministicSpace.lean` | 2 | 2 | 1 |
| `SpaceComplexity/NSPACE.lean` | 2 | 2 | 0 |
| `SpaceComplexity/SpaceClasses.lean` | 4 | 3 | 0 |
| `SpaceComplexity/Constructible.lean` | 1 | 2 | 0 |
| `SpaceComplexity/Inclusions.lean` | 0 | 4 | 0 |
| `SpaceComplexity/Examples.lean` | 1 | 1 | 0 |
| `SpaceComplexity.lean` facade | 0 | 0 | 0 |
| **Total** | **10** | **14** | **1** |

The sweep log contains seven module entries, 14 admission warnings, no `error:` line, and its completion marker. All 14 warning locations match the corresponding theorem declarations in the supplied source, without duplicates. The style log reports 0 FAIL/0 WARN for the 35-file SpaceComplexity tree; its separate TuringMachine sweep reports eight warnings, none on the new NondeterministicSpace file. The claimed SpaceComplexity result is accurate.

The pinned [commit comparison](https://github.com/Shilun-Allan-Li/tcslib/compare/2cf44f1de7e535092454f74d7905926f64c0b4f8...edea2663748fe2b1e47636094b95744ed50148f0) confirms that the six substantive modules did not change between landing and the audited commit. Within the seven-file scope, only the facade changed: the ZeroSpace import and its Contents entry.

The logs do not independently establish fresh object-file creation or working-tree cleanliness. Neither Lean nor Lake was available on PATH in this audit workspace, and I did not reproduce compilation, lint, or axiom inspection. These remain repository-side execution attestations, not independently rerun checks.

I read the supplied P0 definitions and sanity statements as frozen context. To resolve missing evidence, I additionally read the exact-commit [P0 resolutions](https://github.com/Shilun-Allan-Li/tcslib/blob/edea2663748fe2b1e47636094b95744ed50148f0/audits/ch34-p0-resolutions.md), [NTIME acceptance definition](https://github.com/Shilun-Allan-Li/tcslib/blob/edea2663748fe2b1e47636094b95744ed50148f0/TCSlib/Complexity/ClassNP/NTIME.lean), [finite-machine contracts](https://github.com/Shilun-Allan-Li/tcslib/blob/edea2663748fe2b1e47636094b95744ed50148f0/TCSlib/Complexity/TuringMachine/Finite.lean), and [machine-library design §12](https://github.com/Shilun-Allan-Li/tcslib/blob/edea2663748fe2b1e47636094b95744ed50148f0/machine-library-design.md). I did not reopen the closed P0 findings or audit the concurrent §12 implementation.

The source comparison used the published [AB09 text](https://theswissbay.ch/pdf/Gentoomen%20Library/Theory%20Of%20Computation/Sanjeev_Arora%2C_Boaz_Barak-Computational_complexity__a_modern_approach-Cambridge_University_Press%282009%29.pdf), printed pp. 78–82 and §4.3.2, rather than the differently numbered 2007 draft. Definition 4.1 has the declared visited/nonblank wording split; Remark 4.3 supplies the constructible-bound qualification on totality. Page 79 uses asymptotic space for constructibility and a strict logarithmic lower convention. Figure 4.1 depicts read/write output, whereas the frozen model has append-only output; output cannot serve as readable auxiliary storage in this model. Definition 4.5 and the membership claims in Examples 4.6–4.7 agree with the declared normalized targets.

**Blind restatements of all definitions**

These restatements come from the Lean expressions, including their quantifier order.

| Definition | Delivered meaning |
|---|---|
| `NDTM.visitedWith tm w cfg i` | The finite set of head positions on work tape `i` after prefixes of `w` of lengths \(0,1,\ldots,|w|\), starting from `cfg`. Revisited positions count once. Other branches do not contribute. |
| `NDTM.spaceUsedWith tm w cfg` | The sum, over the fixed \(k\) work tapes, of the cardinalities of those visited sets. Equal integer coordinates on different tapes count separately. Input and output are excluded. |
| `FinNDTM.DecidesInSpace N L s` | One fixed finite binary machine \(N\) satisfies: for every binary input \(x\), there exists a natural budget \(T\), common to all branches on that input, such that all length-\(T\) runs halt, every such run uses at most \(s(|x|)\) space, and \(x\in L\) iff some length-\(T\) run halts with output exactly \([true]\). Rejecting runs may have any other output. |
| `NSPACE s` | Languages with one input-independent natural constant and one input-independent finite NDTM deciding them under the preceding predicate at bound \(n\mapsto c\,s(n)\). The constant may be zero. There is no constructibility or logarithmic lower-bound hypothesis. |
| `PSPACE` | Languages in \(\mathrm{SPACE}(n\mapsto n^d+1)\) for some natural degree \(d\), with the multiplicative constant already supplied by SPACE. Degree zero is included. |
| `NPSPACE` | The analogous union of NSPACE classes at the same positive polynomial bounds. This definition asserts no equality with PSPACE. |
| `NL` | Exactly \(\mathrm{NSPACE}(\mathrm{logSpace})\), including this development’s totality and visited-cell conventions. |
| `coNL` | Languages whose complements, taken within all finite binary strings, belong to NL. This is a complement class of languages; it does not complement the set NL within the set of all languages. |
| `SpaceConstructible S` | First, \(\forall n,\ \mathrm{logSpace}(n)\le S(n)\). Second, one positive natural constant and one fixed finite deterministic machine compute the little-endian binary word \(\mathrm{bits}(S(|x|))\) on every binary input \(x\), halting at some per-input time and using at most \(cS(|x|)\) visited work cells. |
| `evenLang` | Binary lists whose number of entries equal to `true` is divisible by two. The empty list belongs. |

The facade adds imports and documentation, not definitions or mathematical statements.

**Statement-by-statement disposition**

Every row is accepted as a statement. Machine-existence rows retain the construction and compilation obligations explained below.

| # | Statement | True-as-stated argument |
|---|---|---|
| 1 | `NDTM.spaceUsedWith_append_of_halt` | Prefixes through \(|w|\) are unchanged; every later prefix runs from the halted configuration reached by \(w\), so its position is already in the old visited set. Equality holds tape by tape, hence after summation. No finiteness of raw states or symbols is needed. |
| 2 | `MultiTapeTM.toNDTM_spaceUsedWith` | For every \(j\le |w|\), the embedded run under \(w.take\,j\) is the deterministic run for \(j\) steps. Both finite images have exactly the domain \(0,\ldots,|w|\). Their cardinality sums agree. |
| 3 | `NSPACE.mono` | Reuse the constant, machine and per-input budgets; \(c\,s_1(n)\le c\,s_2(n)\). Halting and acceptance are unchanged. This includes \(c=0\). |
| 4 | `SPACE_subset_NSPACE` | Embed the deterministic witness, preserving tape count and configurations. Use its per-input halting budget. Every choice word reproduces its output and space; a word of that length always exists. See question 4. |
| 5 | `space_poly_subset_PSPACE` | Insert membership into the defining union at the supplied degree, including degree zero. |
| 6 | `PSPACE_subset_NPSPACE` | Extract a degree witnessing PSPACE membership, apply row 4 at that bound, and insert into the NPSPACE union. |
| 7 | `LOGSPACE_subset_NL` | Apply row 4 to `logSpace`; unfold the two class abbreviations. |
| 8 | `spaceConstructible_logSpace` | Count input length in binary, then compute its binary-word length, with the zero correction in finding 1. Store only a fixed number of logarithmic-width counters and delimiters. The dominance conjunct is reflexivity. See question 3. |
| 9 | `spaceConstructible_linear` | Count from 1, rather than 0, while scanning input. Emit the resulting binary word. Its width plus fixed administrative cells is bounded by a constant times \(n+1\); \(\mathrm{logSpace}(n)\le n+1\). See question 3. |
| 10 | `DTIME_subset_SPACE` | A length-\(cT(n)\) run visits at most \(k(cT(n)+1)\) cells. Absorb the initial \(k\) cells using positivity; if the bound has a zero, DTIME is empty. See question 4. |
| 11 | `P_subset_PSPACE` | Apply row 10 degree by degree to the identical positive polynomial normal forms defining P and PSPACE. |
| 12 | `NP_subset_PSPACE` | Enumerate exactly the certificate strings prescribed by the received NP definition, invoking the polynomial-time verifier in reusable polynomial workspace. The fixed-window construction and full ledger appear in question 5. |
| 13 | `SAT3_mem_PSPACE` | Apply row 12 to the attached, proved `SAT3_mem_NP`. Its total-decoding treatment of malformed strings is inherited unchanged; this theorem introduces no new parser. |
| 14 | `evenLang_mem_LOGSPACE` | A two-live-state finite controller scans the input, toggles on `true`, and emits the correct singleton indicator at the right blank. Zero work tapes suffice; alternatively the stated stationary work tape costs one cell, bounded by `logSpace`. |

The additional proved statement `visitedWith_nil` is correct:
\[
\mathrm{range}(0+1)=\{0\},\qquad [].take\,0=[],
\]
so its image is the singleton containing the initial head position. The displayed `simp` proof is consistent with this unfolding; it was not rerun.

**Answers to the seven questions**

**1. Prefix indexing and branch counting.** The index condition is
\[
j\in\mathrm{range}(|w|+1)\iff 0\le j\le |w|.
\]
Thus \(j=0\) counts the initial position and \(j=|w|\) counts the final position, including a move executed by the halting transition. There is no \(j=|w|+1\) term.

For an extension \(w++w'\), prefixes with \(j\le |w|\) coincide with the old prefixes. For \(j>|w|\),
\[
(w++w').take\,j=w++w'.take(j-|w|).
\]
If the run under \(w\) has halted, append factorization and absorbing halting make the corresponding configuration equal to the configuration at prefix \(w\). This proves equality of the two visited sets, not merely an inequality of total space.

The resource requirement is
\[
\forall w\text{ of the required length},\quad
\sum_{i<k}\bigl|\mathrm{visitedWith}(N,w,\mathrm{initCfg}(x),i)\bigr|
\le s(|x|).
\]
It takes the maximum of total per-run space implicitly through a universal bound. It neither unions branches nor sums separate maxima over branches for different tapes.

**2. Deciding, exact lengths, and the zero-bound twin.** Fix \(x,T\) satisfying the definition. For an arbitrary choice word \(u\):

- If \(|u|\le T\), set \(v=u++[false]^{T-|u|}\). Then \(|v|=T\), and every prefix position of \(u\) occurs among those of \(v\). Consequently
  \[
  \mathrm{spaceUsedWith}(N,u,\mathrm{initCfg}(x))
  \le\mathrm{spaceUsedWith}(N,v,\mathrm{initCfg}(x))
  \le s(|x|).
  \]
- If \(T\le |u|\), the prefix \(v=u.take\,T\) has length \(T\) and has halted. Since \(u=v++u.drop\,T\), row 1 gives
  \[
  \mathrm{spaceUsedWith}(N,u,\mathrm{initCfg}(x))
  =\mathrm{spaceUsedWith}(N,v,\mathrm{initCfg}(x))
  \le s(|x|).
  \]

The acceptance equivalence also cannot be manipulated by choosing \(T\): an earlier accepting run pads to length \(T\), and any later accepting run has the same halted output as its length-\(T\) prefix. Late rejecting branches still contribute their full space. A small budget excluding such a branch violates all-branch halting.

Conversely, all infinite choice streams halting implies a finite common budget on each fixed input: otherwise the finitely branching tree of live prefixes has unbounded depth and, by König’s lemma, an infinite live branch. Thus the existential budget adds no extra uniformity restriction to the declared total-branch convention. At a fixed input length there are also only finitely many inputs, so their budgets have a common maximum. No time-bound witness needs to be moved outside the input quantifier.

For zero collapse, each visited set contains its initial position. Hence, for every word and configuration,
\[
k=\sum_{i<k}1
\le \sum_{i<k}|\mathrm{visitedWith}(N,w,\mathrm{cfg},i)|
=\mathrm{spaceUsedWith}(N,w,\mathrm{cfg}).
\]
If \(s(n_0)=0\), apply a class witness to \(x=[false]^{n_0}\), obtain \(T\), and choose \(w=[false]^T\). Then
\[
0\le N.k\le\mathrm{spaceUsedWith}(N,w,\mathrm{initCfg}(x))
\le c\,s(n_0)=0.
\]
Thus \(N.k=0\), so its space is the empty sum on every input and branch. The same machine witnesses the zero-bound class; the reverse inclusion follows by monotonicity:
\[
(\exists n,\ s(n)=0)\Longrightarrow
\mathrm{NSPACE}(s)=\mathrm{NSPACE}(n\mapsto0).
\]

For everywhere-positive \(s\), \(s(n)\le s(n)+1\le2s(n)\), giving the corresponding normalization equality by constant absorption. These arguments establish the desired sanity twins mathematically. Given the explicit inherited convention and positive class bounds, their absence does not create a new major. They should be recorded for a subsequent additive sanity layer.

**3. Constructibility and small inputs.** For \(n\ge1\) and integer-valued \(S\),
\[
\mathrm{logSpace}(n)\le S(n)
\iff \lfloor\log_2 n\rfloor+1\le S(n)
\iff \log_2 n<S(n).
\]
At a power of two \(n=2^j\), the minimum allowed value is \(j+1\), as required by strict inequality. At \(n=1\), it is 1. At \(n=0\), the real logarithm is undefined; `Nat.log 2 0 = 0` supplies an explicit normalization requiring \(S(0)\ge1\). That is a convention, not an equality with a real-logarithm expression at zero.

For all natural \(n\),
\[
\mathrm{logSpace}(n)=\mathrm{Nat.log}(2,n)+1\le n+1,
\]
including \(1\le1\) at \(n=0\).

For the logarithmic instance, the binary-length identity is
\[
|\mathrm{bits}(n)|=
\begin{cases}
0,&n=0,\\
\mathrm{logSpace}(n),&n>0.
\end{cases}
\]
A corrected controller emits \([true]\) for \(n=0\). Otherwise it counts \(n\), counts the bits of that counter, and emits the latter count in binary. Counter storage, a second counter, and a fixed number of markers occupy at most \(A(\mathrm{logSpace}(n)+1)\) visited cells for a fixed positive constant \(A\). Since \(\mathrm{logSpace}(n)\ge1\),
\[
A(\mathrm{logSpace}(n)+1)\le2A\,\mathrm{logSpace}(n).
\]
All scans terminate and the output is exactly the required bits.

For the linear instance, initialize the first counter to 1. After reading \(n\) symbols it holds \(n+1\). Binary storage and fixed administrative cells fit within \(A(n+2)\) cells for a fixed constant, and
\[
A(n+2)\le2A(n+1).
\]
These constructions establish credible witnesses without changing either statement. Their finite-controller implementation and space lemmas remain fill obligations; this audit has not supplied Lean terms for those machines.

**4. The first two inclusions and constants.** Suppose \(L\in\mathrm{DTIME}(T)\), witnessed by \(c,M\), with \(k=M.k\). If \(T(n_0)=0\), the input \([false]^{n_0}\) would have to halt in \(cT(n_0)=0\) steps. Its initial state is live, a contradiction. Thus a nonempty membership witness forces \(T(n)\ge1\) for every \(n\).

For each input of length \(n\),
\[
\begin{aligned}
\mathrm{spaceUsed}
&\le\sum_{i<k}(cT(n)+1)\\
&=k(cT(n)+1)\\
&=kcT(n)+k\\
&\le kcT(n)+kT(n)\\
&=(kc+k)T(n).
\end{aligned}
\]
The same run at time \(cT(n)\) gives the correct indicator output and halting. For a bound having a zero, the empty-DTIME argument proves the entire inclusion vacuously. This is sound even though SPACE and NSPACE at zero need not be empty.

For the deterministic-to-nondeterministic transfer, choose the same constant and `M.toFinNDTM`. On each input take the time supplied by `M.DecidesInSpace`. Every length-\(T\) word gives the identical deterministic configuration and the identical visited-cell sum. If the input is a member, \([false]^T\) supplies an accepting word; if it is not, all words give \([false]\), so none accepts. There is one trajectory, though generally many choice words.

The dependency direction is sound:
`toNDTM_runWith` → `toNDTM_spaceUsedWith` → `SPACE_subset_NSPACE` → class inclusions.
The transfer theorem’s independent prefix proof does not use the inclusion it supports. Neither inclusion needs constructibility.

**5. NP, 3SAT, and the full space ledger.** The attached NP definition provides a fixed polynomial-time verifier language \(V\) and the exact certificate length
\[
Q(n)=C(n+1)^c,\qquad
x\in L\iff\exists u,\ |u|=Q(|x|)\ \land\ x++u\in V.
\]
Thus the concatenation in the sketch is correct for this received NP definition. Let \(t(m)=a(m^d+1)\) bound one fixed verifier machine’s time on every length-\(m\) input.

A deterministic implementation can retain the current \(Q(n)\)-bit certificate, copy \(x++u\) into a reusable input region, and simulate that fixed verifier. Copying is an optional simpler implementation here because polynomial space can afford it; the stated virtual-input route is also valid with an appropriate simulation contract.

The host must establish all of the following:

1. Construct exactly \(Q(n)\), preserve the certificate width, enumerate every such word once, and detect overflow. When \(Q(n)=0\), there is exactly one candidate, the empty word.
2. Preserve the original input and certificate while simulating the verifier on exactly \(x++u\), including the input-head boundary behavior.
3. Capture the verifier’s one-bit result internally. Emit no trial result on the host’s append-only physical output; emit its own single decision bit only on final termination.
4. Clear the verifier scratch and restore the heads before another trial. A cleanup that retains a whole history of all trials is not acceptable.
5. Prove all invocations and resets stay inside fixed polynomial-size tape windows. Equal per-call cardinality bounds alone do not imply a bound on the union of visited locations across calls.

The certificate uses \(Q(n)+O(1)\) cells. The copied input uses \(n+Q(n)+O(1)\). The verifier runs for at most \(t(n+Q(n))\) steps, so its fixed number of heads and their reset sweeps can be confined to intervals of that polynomial radius about fixed origins. Control counters and delimiter overhead also fit in polynomial space. Consequently a fixed constant \(A\), independent of the input and trial number, can satisfy
\[
\mathrm{hostSpace}(x)
\le A\bigl(n+Q(n)+t(n+Q(n))+1\bigr),\qquad n=|x|.
\]
There is no factor equal to the number of certificates. Fixed windows bound the union over all trials.

The displayed right side is a polynomial in \(n\), so for fixed natural constants \(D,e\) it is at most \(D(n+1)^e\). The required normalization follows from
\[
D(n+1)^e\le D\,2^e(n^e+1)
\quad(n\ge0).
\]
For \(n\ge1\), use \(n+1\le2n\); for \(n=0\), the inequality holds directly, including \(e=0\).

There are finitely many certificates and every verifier call halts, so the host halts. It accepts precisely when one enumerated word verifies, giving the membership equivalence. This proves the mathematical route to the statement. A complete formal fill must still construct and verify that host.

The planned modular proof therefore has a hard dependency on space-preserving bank embedding, seam composition, and suitable primitive/reset contracts (R1/R2/R3). Reading the design document is not a certification that the concurrent implementation already provides the required reusable-window contract. This dependency was declared, and it does not invalidate the statement gate.

Finally, `SAT3_mem_NP` followed by this inclusion proves the exact received SAT3 membership statement. The proof does not establish a linear-space bound.

**6. Class definitions.** The positive normal forms avoid the collapse:
\[
n^d+1\ge1,\qquad \mathrm{logSpace}(n)\ge1.
\]
The natural-degree union includes \(d=0\), where the bound equals 2 even at \(n=0\). This adds no languages beyond the positive-degree union: \(2\le2(n+1)\), and the multiplicative constant is absorbable. Likewise,
\[
n^d+1\le(n+1)^d+1\le2^d(n^d+1)+1
\]
can be absorbed into a constant multiple of \(n^d+1\); the usual positive polynomial formulations therefore agree. No identity with the literal, collapsing unnormalized SPACE/NSPACE functions at zero is being asserted.

`coNL` has the correct language-complement meaning:
\[
L\in\mathrm{coNL}\iff L^c\in\mathrm{NL}
\iff\exists K\in\mathrm{NL},\ L=K^c.
\]
The last equivalence uses involutivity of complement. It requires no theorem about NL being closed under complement. The two deterministic-to-nondeterministic class inclusions are exactly rows 6–7 above.

**7. Adversarial instantiations.** These attacks use explicit boundary values or finite-control machine behaviors. They are mathematical checks, not claims of executed Lean tests.

| Test | Instantiation and calculation | Outcome |
|---|---|---|
| Empty choice word | Two tapes with initial heads at \(-3,5\); \(w=[]\). The visited sets are \(\{-3\},\{5\}\), so total space is 2. With zero tapes, the sum is 0. | Initial positions are counted exactly once; empty words do not mean zero space for positive tape count. |
| Final move and halt | One tape starts at 0. In one transition, move right and halt. Its visited set is \(\{0,1\}\). Every extension has the same set. | The post-transition position is counted, including on a halting transition; later choices add nothing. |
| Different branch durations | On first choice false, halt and accept without moving. On true, move right twice and halt rejecting on step 3; subsequent choices are ignored. With \(T=3\), branch spaces are 1 and 3. | A bound of 2 fails despite the early accepting branch. \(T=1\) fails totality. A larger budget preserves both spaces. |
| Stationary infinite rejecting branch | First choice false halts accepting; true enters a stationary live loop. Every finite run uses one cell. | No \(T\) satisfies all-branch halting. This machine fails the deciding predicate; it does not imply its recognized language lacks some other total decider. |
| Branch union overcounts | First choice selects a left move or a right move, then halts. Each branch visits two cells, while their union is \(\{-1,0,1\}\). | Bound 2 is allowed. A union over branches would incorrectly demand 3. |
| A zero at a nonempty length | Let \(s(7)=0\), with arbitrary values elsewhere. Apply any proposed witness to \([false]^7\), then to the word \([false]^T\). | \(N.k\le c\,s(7)=0\), so the collapse is global, not confined to length 7. |
| Zero constant | A zero-work-tape machine emits `true` and halts in one step; another halts with `[]`. Both use zero cells. | They decide the full and empty languages respectively with \(c=0\). Unlike zero-time classes, zero-space classes are nonempty. |
| NL on lengths 0 and 1 | \(\mathrm{logSpace}(0)=\mathrm{logSpace}(1)=1\). A two-tape witness needs class coefficient at least 2 at those lengths; a zero-tape witness needs none. | Short-input space is positive and meaningful; machine existence is not vacuous. |
| Constructible linear at zero | Required dominance: \(1\le0+1\). Required output: \(\mathrm{bits}(1)=[true]\). | The theorem passes; an uncorrected length counter gives the wrong output, as finding 2 records. |
| Logarithmic powers and zero | At \(n=0,1,2,4\), `logSpace` is \(1,1,2,3\); binary-word lengths of \(n\) are \(0,1,2,3\). | Strict-log rounding is correct, and exactly the zero case refutes the sketch’s unconditional bit-length identity. |
| coNL constants | The full language and empty language are in NL by the one-step zero-tape witnesses; their complements are each other. | Both belong to coNL without using NL = coNL. |
| A vanishing time bound | Let \(T(5)=0\). Every proposed DTIME witness must halt on \([false]^5\) at time 0. | Impossible from a live initial state; the vacuity branch in `DTIME_subset_SPACE` is airtight. |
| Degree zero | \(n^0+1=2\), including \(0^0+1=2\). Also \(2\le2(n+1)\). | Degree zero is safe and redundant at the class-union level. |
| Empty certificate | Let \(C=0\), so \(Q(n)=0\). There is one candidate \(u=[]\), and \(x++u=x\). At \(n=0\) with \(C>0\), \(Q(0)=C\). | Enumeration must execute one verifier call in the zero-width case and must not assume empty input forces empty certificates. |

**Disposition**

The P4.1 public mathematical statements pass at their declared strength. Findings 1–5 should be swept into the documentation, sketches, and packet errata; findings 6–9 should remain explicit obligations or scope notes in the fill brief. The inherited P0 gate remains closed.

**Notation glossary.** \(x\) is a binary input; \(n=|x|\) is its length; \(L,V,K\) are languages; \(L^c\) is language complement. \(M,N\) are fixed deterministic/nondeterministic machines; \(k\) is their work-tape count; \(i\) indexes a tape; \(j\) indexes a prefix or a power of two; \(\mathrm{cfg}\) is a configuration. \(w,w',u,v\) denote finite choice words in branch arguments; \(u\) denotes a certificate in the NP argument. \(|\cdot|\) means word length or finite-set cardinality as appropriate; \(++\) is list concatenation; \([false]^r\) is a list of \(r\) false bits. \(s,s_1,s_2,S\) are space bounds; \(T\) is a branch budget or time-bound function as locally specified; \(n_0\) is a length where a bound vanishes. \(a,c,C,A,D\) are fixed natural constants (with \(c\) also used for the certificate exponent in the received NP formula); \(d,e\) are natural polynomial degrees. \(Q(n)=C(n+1)^c\) is certificate length; \(t(m)=a(m^d+1)\) is the verifier time bound at input length \(m\); \(m\) is an auxiliary input length; \(\mathrm{hostSpace}(x)\) is the total visited work-cell count of the constructed enumerating decider. Existing Lean identifiers retain their source meanings.

