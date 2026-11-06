# Gate 03b, round 3: external delta findings

**The delta meets the closing condition: 0 blockers, 0 majors, 1 minor.** All three requested round 2 resolutions are fixed. The minor is inherited wording in an unchanged bridge docstring, not a regression or a false theorem statement.

Audited the supplied bundle, identified by the pack as commit `4769fe88d6894a62c87a19bc524088c5a2c99e0b`, with Lean files from PR #204 at `08fa1185903968af42937cfb2532c45c33721d25`. Bundle SHA-256: `fa465a29ced4f662654f9a10fa8c269f1c65a2e4768a57e52fd0b3bd0007c056`. Date: 2026-11-05.

This is the requested audit of two docstrings, one records correction, and the completeness of the supplied diff. The attached [PS10] was checked directly, including rendered book pp. 26–28 / PDF pp. 38–40. No tactic-proof audit or independent Lean replay was performed. Line numbers refer to the extracted files; `OneWay.lean` means `TCSlib/Cryptography/Asymptotic/OneWay.lean`.

## Findings

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| R3-1 | minor, inherited; outside the two edited docstrings | `OneWay.lean:283–285` · `WorstCaseOneWayLit.toParam` docstring | The parenthetical still calls injective output length “the case of every family of the text.” | Def. 26.1 imposes no such restriction. The constant-empty-output family has noninjective output length and separates the two typed worst-case predicates, as calculated below. This repeats the overgeneralization removed from the definition's docstring. The theorem at lines 298–299 correctly requires `Function.Injective 𝓕.outLen.eval`; neither it nor this docstring changed. | In a wording cleanup, replace the parenthetical with “injective `outLen`, equivalently nonconstant output length for these polynomial lengths.” This does not block this delta. |
| R3-2 | note | `OneWay.lean:196–216` · `FunFamily.ofString` | The repaired example respects the actual zero-padding implementation. | The calculation below proves the claimed bound for the same inverter, with additive term at most $2^{-n/2}$ at positive even lengths and zero otherwise. It also handles empty strings and defeats the previous collision attack. | None. The construction remains explicitly informal and conditional on the stipulated one-way function. |
| R3-3 | note | `OneWay.lean` · supplied repair diff | Exactly the two specified docstrings changed. | Both hunks match the final file. Reversing them reconstructs the old blob named by the diff; removing the two target comment blocks from both versions leaves byte-identical content, including all other docstrings. Details below. | None. |

R2-1: fixed — the final-bit marker prevents the padding collision; the same-inverter probability bound and the unrestricted inverse are valid at every length, as shown below.

R2-2: fixed — `WorstCaseOneWayLit`'s own docstring, lines 180–183, now restricts coincidence to nonconstant output length and correctly allows a difference at constant output length. R3-1 identifies a separate, unchanged occurrence of the old wording.

R2-3: fixed — `resolutions-03b-r1.md:52`, M6, now calls the `GGMRed` copy public and retains the DL-15 schedule. This agrees with the ledger evidence quoted in the verbatim round 2 findings. The ledger itself is not bundled in round 3; this verifies the records correction, not execution of the scheduled cleanup.

## R2-1: calculation and counterexample attempt

**Definition and empty input.** Since $h$ and $g$ are length-preserving, necessarily

\[
h(\varepsilon)=g(\varepsilon)=\varepsilon,
\qquad g(x\mathbin\Vert b)=h(x)\mathbin\Vert1.
\]

Thus the docstring's rule on nonempty inputs has a unique length-preserving completion at the empty string. Its special branch explicitly requires $k\ge1$, so $f(\varepsilon)=\varepsilon$.

For the length $n$ domain, define the special inputs and the implemented string output by

\[
S_n=
\begin{cases}
\{0^k\mathbin\Vert w:w\in\{0,1\}^k\},&n=2k,\ k\ge1,\\
\varnothing,&n=0\text{ or }n\text{ odd},
\end{cases}
\qquad
F_n(x)=\operatorname{List.ofFn}((\operatorname{ofString}f\ .\mathrm{var}).f\ n\ x).
\]

Here the bit vector and its corresponding string are identified. The `getD i false` implementation at line 216 gives, without truncating any nonempty branch,

\[
F_n(x)=
\begin{cases}
w\mathbin\Vert0^k,&n=2k\ge2,\ x=0^k\mathbin\Vert w,\\
g(x),&x\notin S_n.
\end{cases}
\]

At a fixed positive even length, the special outputs end in $0$, and every ordinary output ends in $1$. Their images are disjoint. At odd lengths there are no special inputs; at zero there is just the empty input and output. Disjointness is needed only within the current typed domain, not across different input lengths.

**Unrestricted inversion.** For every nonempty string $y$, the special rule with $k=|y|\ge1$ yields

\[
f(0^{|y|}\mathbin\Vert y)=y.
\]

For $y=\varepsilon$, the same equality is $f(\varepsilon)=\varepsilon$. Consequently the polynomial-time map $y\mapsto0^{|y|}\mathbin\Vert y$ inverts every challenge with probability one. Its possibly different output length is allowed by [PS10, Def. 27.3, pp. 27–28], whose success event is $f(A(1^n,y))=y$, with no same-length-preimage condition.

**Typed inversion.** Fix any inverter $A$, with the same advice and random tape $r$ in both experiments. Let $s_F(A,n)$ and $s_g(A,n)$ denote its respective typed success probabilities on a uniform length $n$ input. Wrong-length answers fail in both experiments, as expressed by `invProbAt_eq_uprob`, lines 249–251.

If $n=2k\ge2$, $x\notin S_n$, and the answer $z=A(1^n,F_n(x);r)$ is a successful typed preimage, then

\[
\begin{aligned}
F_n(x)&=g(x),\\
|z|=n\quad\text{and}\quad F_n(z)=g(x)
&\Longrightarrow z\notin S_n &&\text{(different final bits)},\\
&\Longrightarrow g(z)=g(x).
\end{aligned}
\]

The same run of $A$ therefore succeeds against $g$. Success against $F_n$ can exceed success against $g$ only when the sampled input belongs to $S_n$. Since the sample space has $2^{2k}$ strings and $S_{2k}$ has $2^k$ strings,

\[
s_F(A,2k)\le s_g(A,2k)+\frac{2^k}{2^{2k}}
=s_g(A,2k)+2^{-k}\qquad(k\ge1).
\]

For odd $n$, $F_n=g$, so the success probabilities are equal. For $n=0$, both experiments present the empty challenge and succeed exactly when $A$ returns the empty string; they are again equal. In particular, $k=0$ introduces no special branch or exception. Altogether,

\[
s_F(A,n)\le s_g(A,n)+
\begin{cases}
2^{-n/2},&n>0\text{ even},\\
0,&n=0\text{ or }n\text{ odd}.
\end{cases}
\]

This proves the stated $O(2^{-n/2})$ bound with constant $1$.

The stipulated hardness also transfers to $g$: given an $h$-challenge $y=h(x)$ with $|x|=m$, run an inverter for $g$ at parameter $m+1$ on $y\Vert1$. A successful reply $z\Vert b$ satisfies

\[
h(z)\Vert1=g(z\Vert b)=y\Vert1
\quad\Longrightarrow\quad h(z)=y.
\]

The challenge distribution is exact because the last input bit of $g$ is ignored. This polynomial-time reduction preserves success, and shifting the parameter by one preserves negligibility. Computing $f$, including testing its special branch, is polynomial-time. Thus the claimed separation follows conditional on the assumed length-preserving strong one-way $h$. This is a mathematical verification of the informal example, not a new Lean formalization or an unconditional existence claim.

**Attempted counterexample.** Reuse the round 2 attack at positive even length:

\[
A(1^{2k},y)=0^k\Vert\operatorname{take}_k(y).
\]

On a special challenge $w\Vert0^k$, its answer is $0^k\Vert w$, a valid inverse. On an ordinary challenge, its answer is still special, so its padded image ends in $0$ while the challenge ends in $1$. Hence this attack has success exactly $2^{-k}$, not one. No choice of the base function restores its former collision under the new marker condition.

As an additional finite check, exhaustive enumeration covered all 262 base-function cases at domain lengths $n=0,1,2,3$, including noninjective and constant maps, and 16,453 input/reply pairs. The maximum success difference over all deterministic reply rules was respectively $0,0,1/2,0$, agreeing with the bound. Randomized rules are mixtures of those rules. This checks finite algebra, not cryptographic hardness; the argument above covers all lengths.

## R2-2: equivalence and the constant-output boundary

The unchanged signatures give

\[
\mathcal F.\mathrm{WorstCaseOneWay}
\Longrightarrow\mathcal F.\mathrm{WorstCaseOneWayLit},
\]
\[
\operatorname{Injective}(\mathcal F.\mathrm{outLen.eval})
\Longrightarrow
\bigl(\mathcal F.\mathrm{WorstCaseOneWayLit}
\Longrightarrow\mathcal F.\mathrm{WorstCaseOneWay}\bigr).
\]

For these polynomial lengths, “nonconstant” is semantic: the evaluated polynomial is nonconstant. A nonconstant polynomial with nonnegative integer coefficients is strictly increasing on the natural numbers, hence injective. The repaired definition docstring states the appropriate restriction.

The constant family $x\mapsto\varepsilon$, with `inLen = .var` and `outLen = .const 0`, verifies the warning and R3-1. A parameter-aware inverter returns $0^n$, so `WorstCaseOneWay` is false. A literal inverter has the same empty challenge, advice activation and coin distribution at every $n$. Success probability one at both $n=0$ and $n=1$ would require that same output distribution to have length both zero and one almost surely, which is impossible. Thus `WorstCaseOneWayLit` is true. The source definition does not impose a nonconstant-output restriction.

## Change and execution evidence

- The supplied diff contains precisely two hunks, both within the requested docstrings. Its reconstructed old Git blob is `d4b35d6f0c82872ec8c37099328f3640d05d83a4`; the supplied new file's blob is `b2445e445af153413499f396ad3b2411254af5dd`. Both match the corresponding eight-digit identifiers in the diff. All bytes outside those two comment blocks are identical. No definition, theorem statement, proof, attribute, import or other docstring changed in this comparison. This validates the bundled diff and blob identities; repository commit provenance remains the pack's attestation.
- The bundled round 2 findings reproduce their recorded SHA-256, `924a93b01d6ee976c86f602701dbd67f2e77d908b6a1eed264cd46b3a77fbf2a`.
- The supplied replay log contains 44 module checks, all with `rc=0` and zero errors, and a total of 61 `sorry` warnings. The supplied lint log reports zero findings in one file. These are checked log contents, not independently rerun checks. The before-repair replay and inherited axiom log are not bundled here, so their attestations are not independently renewed.

## Notation

`ε` / $\varepsilon$: empty string; $\Vert$: concatenation; $0^k$: $k$ zero bits; $|x|$: string length; $\{0,1\}^n$: length $n$ bit strings. $n,k,m$: nonnegative lengths; $x,w,y,z$: strings; $b$: a bit. $h,g,f$: the docstring's base, marked and modified functions; $S_n$: special inputs; $F_n$: the implemented padded output at length $n$; $A$: an inverter; $r$: its random tape; $s_F,s_g$: its typed success probabilities; $\operatorname{take}_k$: the first $k$ bits; $\mathcal F$: a `FunFamily`.
