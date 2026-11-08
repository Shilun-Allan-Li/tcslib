<!-- generated-by: proofmatch Claude repair -->
<!-- source-pdf-sha256: c8033d2fd70553fb96969a3e3923f8ca9112f6e635667da8a3cecd473f5c5bc3 -->

<a id="pdf-c8033d2fd705-p001-b001"></a>
<!-- pdf-source: page=1; block=1; confidence=0.98 -->
Savitch studies deterministic simulation of nondeterministic tape-bounded computation. The abstract states that an NTM using storage L(n) can be simulated deterministically in L(n)^2 storage for L(n) ≥ log₂ n, and introduces maze threadability as a candidate language distinguishing the corresponding complexity classes.

<a id="pdf-c8033d2fd705-p001-b002"></a>
<!-- pdf-source: page=1; block=2; confidence=0.98 -->
**Introduction.** The motivating question is how much deterministic storage is needed to recognize a set accepted by a nondeterministic tape-bounded machine. The article announces a quadratic-storage simulation for L(n) ≥ log₂ n and a resulting deterministic n²-storage bound for context-sensitive languages.

<a id="pdf-c8033d2fd705-p002-b001"></a>
<!-- pdf-source: page=2; block=1; confidence=0.96 -->
The introduction additionally claims an n(log n)² deterministic-storage bound for languages accepted by nondeterministic linear-bounded automata in polynomial time, and states that equality of deterministic and nondeterministic tape-complexity classes for small bounds implies equality for larger bounds. It previews a maze characterization and a set of encodings of threadable mazes: nondeterministic recognition uses log S(n) storage, and deterministic recognition at that same bound would imply equal-power simulations for every L(n) ≥ log S(n). The final implication is printed as “stimulated” in the source and summarized here as simulation.

<a id="pdf-c8033d2fd705-p002-b002"></a>
<!-- pdf-source: page=2; block=2; confidence=0.98 -->
**Machine Model.** A multitape Turing machine has finite control, a read-only input tape bounded by endmarkers, and finitely many read/write storage tapes. Each tape is divided into squares; storage squares hold symbols from a finite alphabet. In one step, based on the scanned symbols and current state, the machine changes state, may overwrite scanned storage symbols, and moves heads at most one square. A deterministic machine has one available action per step; a nondeterministic machine has finitely many. Acceptance means reaching an accepting state after finitely many steps; for an NTM, at least one finite computation must accept.

<a id="pdf-c8033d2fd705-p003-b001"></a>
<!-- pdf-source: page=3; block=1; confidence=0.99 -->
**Definition.** A function $L(n)$ accepts a set $A$ within storage $L(n)$ if (i) for each string $w\in A$, there is at least one possible accepting computation in which each storage-tape head scans at most $L(|w|)$ squares, and (ii) $Z$ accepts no string not in $A$.

<a id="pdf-c8033d2fd705-p003-b002"></a>
<!-- pdf-source: page=3; block=2; confidence=0.97 -->
Only asymptotic growth rates are considered: L(n) and cL(n) are identified for every constant c > 0, since arbitrary finite tape alphabets permit constant-factor tape reductions.

<a id="pdf-c8033d2fd705-p003-b003"></a>
<!-- pdf-source: page=3; block=3; confidence=0.99 -->
**Definition.** A function $L(n)$ is measurable if there is a Turing machine with just one storage tape such that, given any input of length $n$, the machine halts after a computation in which the storage-tape head scans exactly $L(n)$ squares. Apparently, all common storage functions $L(n)\ge\log_2 n$ are measurable. In particular, any polynomial in $n$ and $\log_2 n$ is measurable.

<a id="pdf-c8033d2fd705-p003-b004"></a>
<!-- pdf-source: page=3; block=4; confidence=0.99 -->
**Deterministic Simulation of Nondeterministic Turing Machines.**

<a id="pdf-c8033d2fd705-p003-b005"></a>
<!-- pdf-source: page=3; block=5; confidence=0.99 -->
**Theorem 1.** If A is accepted by a nondeterministic Turing machine within storage L(n) ≥ log₂ n, then some deterministic Turing machine accepts A within storage L(n)².

<a id="pdf-c8033d2fd705-p003-b006"></a>
<!-- pdf-source: page=3; block=6; confidence=0.99 -->
Suppose the Turing machine $Z_N$ has $k$ storage tapes, storage-tape alphabet $\Gamma$, and internal state set $Q$. Let $\Delta=Q\cup\Gamma\cup\{1,2,*,\downarrow\}$, where $\downarrow$ and $*$ are two new symbols. An instantaneous description (ID) of $Z_N$ is a string over $\Delta$ of the form …

<a id="pdf-c8033d2fd705-p004-b001"></a>
<!-- pdf-source: page=4; block=1; confidence=0.97 -->
Since $Z_N$ accepts the set $A$ within storage $L(n)\ge\log_2 n$, for each string $w$ of length $n$ accepted by $Z_N$, there is an accepting computation in which every ID has length at most $cL(n)$. Furthermore, since each ID is of length at most $cL(n)$, the computation need take no more than $2^{c'L(n)}$ steps. Here $c$ and $c'$ depend only on $Z_N$, not on the input $w$.

For measurable $L(n)$, $Z_D$ divides one storage tape into $[c'L(n)]+1$ blocks called registers, each of length $[cL(n)]$, followed by $[c'L(n)]+1$ one-bit blocks called tags. Its recursive reachability check tests paths of at most $2^m$ steps using $m$ registers: it enumerates intermediate IDs and checks paths of at most $2^{m-1}$ steps on either side, recursively reducing the number of registers. The final one-step check uses zero storage. Thus, $Z_D$ can simulate the accepting computation using $c'L(n)$ registers, or about $[L(n)]^2$ squares of storage tape. IDs are treated as integers in base $m=|\Delta|$; the input-head position is written in dyadic notation.

<a id="pdf-c8033d2fd705-p005-b001"></a>
<!-- pdf-source: page=5; block=1; confidence=0.97 -->
**Definition.** For IDs $I,I'$ of $Z_N$, write $I\,\vdash\,I'$ when, on input $w$, one machine step takes configuration $I$ to $I'$, or when $I=I'$. The algorithm tests this relation on arbitrary strings over $A$; the test fails if either string is not an ID.

<a id="pdf-c8033d2fd705-p005-b002"></a>
<!-- pdf-source: page=5; block=2; confidence=0.94 -->
Register $i$ contains $x_i$ and tag $i$ contains $T_i$. Computations of $Z_N$ are on input $w$ and constrained so each work tape's nonblank segment has length at most $L(|w|)$. The stated invariant is: if $T_i=1$, then $x_i$ is reachable from the initial ID of $Z_N$.

<a id="pdf-c8033d2fd705-p005-b003"></a>
<!-- pdf-source: page=5; block=3; confidence=0.99 -->
$r$ is the least integer such that $r\ge c'L(n)$. $c'$ is such that, with $w$ as input, if $Z_N$ accepts $w$ at all, then $Z_N$ accepts $w$ in $2^{c'L(n)}$ steps. $I_0$ is the initial ID of $Z_N$. $N$ is the largest integer whose $m$-adic representation can be stored in a register. $x_i$ is the contents of the $i$-th register; $T_i$ is the contents of the $i$-th tag.

<a id="pdf-c8033d2fd705-p005-b004"></a>
<!-- pdf-source: page=5; block=4; confidence=0.83 -->
**Algorithm.** Initialize $r+1$ registers and tags: for $i\le r$, set $x_i=1,T_i=0$; set $x_{r+1}=I_0,T_{r+1}=1$. At test step D1, if all tags are 1, go to D3; otherwise choose the least $j$ with $T_j=0$ and check whether some tagged register $h$ has $x_h\vdash x_j$. If so, go to D2; otherwise go to D3. In D2, accept if $x_j$ is an accepting ID; otherwise set $T_j=1$, and reset each earlier register $i<j$ to $x_i=1,T_i=0$, then return to D1. In D3, reject if every $x_i=N$ for $i\le r$. Otherwise choose the least $k$ with $x_k\ne N$, increment $x_k$, clear $T_k$, reset all earlier registers and tags to $1$ and $0$, respectively, and return to D1. The text asserts storage $O(L(n)^2)$, with a standard technique reducing the constant factor to one; the referenced technique is not detailed here.

<a id="pdf-c8033d2fd705-p006-b001"></a>
<!-- pdf-source: page=6; block=1; confidence=0.94 -->
An induction on the number of completed steps is said to show that if $Z_D$ accepts $w$, then $Z_N$ accepts it. It remains to prove the converse. For the lemmas, modify D2 by removing its immediate acceptance check, so the simulator does not halt upon finding an accepting ID. A configuration of $Z_D$ is the pair of register contents and tag contents just before D1.

<a id="pdf-c8033d2fd705-p006-b002"></a>
<!-- pdf-source: page=6; block=2; confidence=0.96 -->
**Lemma 1 (for modified D2).** For each index $i$ ($i=1,2,\ldots,r$) and each integer $x$ ($x=1,2,\ldots,N$), if at some time the configuration is
\[
\langle\underbrace{1,1,\ldots,1}_{i},x_{i+1},x_{i+2},\ldots,x_r,I_0\rangle,\quad
\langle\underbrace{0,0,\ldots,0}_{i},T_{i+1},T_{i+2},\ldots,T_r,1\rangle,
\tag{1}
\]
then at some later time the configuration will be
\[
\langle\underbrace{1,1,\ldots,1}_{i-1},x,x_{i+1},x_{i+2},\ldots,x_r,I_0\rangle,\quad
\langle\underbrace{0,0,\ldots,0}_{i},T_{i+1},T_{i+2},\ldots,T_r,1\rangle
\tag{2}
\]
or
\[
\langle\underbrace{1,1,\ldots,1}_{j-1},x_j,x_{j+1},\ldots,x_r,I_0\rangle,\quad
\langle\underbrace{0,0,\ldots,0}_{j-1},1,T_{j+1},\ldots,T_r,1\rangle,
\tag{3}
\]
where $j$ is the least index in (1) such that $j>i$ and $T_j=0$. If no such $j$ exists, then (2) happens.

<a id="pdf-c8033d2fd705-p006-b003"></a>
<!-- pdf-source: page=6; block=3; confidence=0.86 -->
The lemma describes how the simulator attempts to place a desired ID in a register while using only the available registers, with reachability from the start as its guiding invariant.

<a id="pdf-c8033d2fd705-p006-b004"></a>
<!-- pdf-source: page=6; block=4; confidence=0.99 -->
**Proof.** A formal proof would use induction on $i$ and $x$. Since $N$ is a string all of whose digits are the same, $N$ is not an ID and hence $x\not\vdash_w N$ for any integer $x$. Suppose $Z_D$ is started in configuration (1) and that at no later time does it assume configurations (3). $Z_D$ will then assume the following configurations: …

<a id="pdf-c8033d2fd705-p007-b001"></a>
<!-- pdf-source: page=7; block=1; confidence=0.96 -->
If at no later time does $Z_D$ assume configurations (3), it will assume
\[
\langle\underbrace{1,1,\ldots,1}_{i-1},x-1,x_{i+1},x_{i+2},\ldots,x_r,I_0\rangle,\quad
\langle\underbrace{0,0,\ldots,0}_{i-1},T_{i+1},T_{i+2},\ldots,T_r,1\rangle,
\]
\[
\langle\underbrace{1,1,\ldots,1}_{i-2},N,x-1,x_{i+1},x_{i+2},\ldots,x_r,I_0\rangle,\quad
\langle\underbrace{0,0,\ldots,0}_{i-1},T_i,T_{i+1},T_{i+2},\ldots,T_r,1\rangle,
\]
where $T_i=0$ or $1$, and then
\[
\langle\underbrace{N,N,\ldots,N}_{i-1},x-1,x_{i+1},x_{i+2},\ldots,x_r,I_0\rangle,\quad
\langle\underbrace{0,0,\ldots,0}_{i-1},T_i,T_{i+1},T_{i+2},\ldots,T_r,1\rangle.
\]
Finally, via D3, $Z_D$ assumes (2).

<a id="pdf-c8033d2fd705-p007-b002"></a>
<!-- pdf-source: page=7; block=2; confidence=0.99 -->
**Lemma 2 (for modified D2).** Suppose that at some time the configuration of $Z_D$ is (4), with $T_j=0$ and any values for the $x$’s and remaining $T$’s. If for some index $q$, $T_q=1$ and there is a computation of $Z_N$ of at most $2^j$ steps from $x_q$ to $x$, then at some later time the configuration of $Z_D$ will be (4) with $T_j=1$. The lemma says that $j$ registers suffice for $Z_D$ to check a computation of $2^j$ steps of $Z_N$.

<a id="pdf-c8033d2fd705-p007-b003"></a>
<!-- pdf-source: page=7; block=3; confidence=0.70 -->
**Lemma 3.** From configuration (5), if `T_q=1` and the nondeterministic machine has a computation of at most `2^j` steps from `x_q` to `x`, then later the deterministic machine reaches configuration (6).

<a id="pdf-c8033d2fd705-p008-b001"></a>
<!-- pdf-source: page=8; block=1; confidence=0.70 -->
**Proof.** Prove both lemmas simultaneously by induction on `j`; the case `j=1` is immediate. For Lemma 2 at `j`, split a computation of at most `2^j` steps at an intermediate ID `y` into two computations of at most `2^{j-1}` steps. Lemma 1 yields either the desired configuration (4) with `T_j=1`, or configuration (7) with `T_{j-1}=0`. In the latter case, apply the induction hypothesis for Lemma 2 to set `T_{j-1}=1`, then that for Lemma 3 to reach (4) with `T_j=1`. Lemma 3 follows by the analogous argument.

<a id="pdf-c8033d2fd705-p008-b002"></a>
<!-- pdf-source: page=8; block=2; confidence=0.74 -->
If the nondeterministic machine accepts `w`, an accepting ID `x` is reachable from the initial ID within `2^n` steps. Lemma 1 gives deterministic configuration (8) with `T_r=0`; Lemma 2 later gives (8) with `T_r=1`. The unmodified D2 accepts at this point. This proves Theorem 1 when `L(n)` is measurable.

<a id="pdf-c8033d2fd705-p008-b003"></a>
<!-- pdf-source: page=8; block=3; confidence=0.99 -->
If $L(n)$ is not measurable, then the above algorithm must be altered, since $Z_D$ cannot necessarily mark off blocks of length $cL(n)$ within storage proportionate to $[L(n)]^2$. However, if $Z_D$ were somehow given the value of $L(n)$, then by the above procedure it could determine whether or not $Z_N$ accepts the input $w$ within storage $L(n)$. So $Z_D$ first assumes $L(n)=1$, then tries $L(n)=2,3,\ldots$. If $Z_N$ accepts $w$, $Z_D$ will eventually find the correct value for $L(n)$ and accept $w$ within storage proportionate to $[L(n)]^2$. If $Z_N$ does not accept $w$, then $Z_D$ computes forever on input $w$.

<a id="pdf-c8033d2fd705-p009-b001"></a>
<!-- pdf-source: page=9; block=1; confidence=0.99 -->
The increasing-candidate procedure completes the proof of Theorem 1. The context-sensitive languages are precisely those sets accepted by nondeterministic Turing machines within storage $L(n)=n$. Setting $L(n)=n$ in Theorem 1 gives: **Corollary 1.** Every context-sensitive language is accepted by some deterministic Turing machine within storage $n^2$.

<a id="pdf-c8033d2fd705-p009-b002"></a>
<!-- pdf-source: page=9; block=2; confidence=0.94 -->
Context-sensitive languages are exactly those accepted by nondeterministic Turing machines using linear storage.

<a id="pdf-c8033d2fd705-p009-b003"></a>
<!-- pdf-source: page=9; block=3; confidence=0.95 -->
**Corollary 1.** Every context-sensitive language is accepted by a deterministic Turing machine using storage `n^2`.

<a id="pdf-c8033d2fd705-p009-b004"></a>
<!-- pdf-source: page=9; block=4; confidence=0.99 -->
**Theorem 2.** If a set $A$ is accepted by a nondeterministic Turing machine within storage $L(n)$ and time $T(n)$, then $A$ is accepted by some deterministic Turing machine within storage $L(n)\log_2 T(n)$.

<a id="pdf-c8033d2fd705-p009-b005"></a>
<!-- pdf-source: page=9; block=5; confidence=0.97 -->
**Definition.** A Turing machine `Z` accepts `A` within storage `L(n)` and time `T(n)` if (i) for every `w∈A`, some accepting computation takes at most `T(n)` steps and each work-tape head scans at most `L(n)` squares, where `n=|w|`; and (ii) `Z` accepts no string outside `A`.

<a id="pdf-c8033d2fd705-p009-b006"></a>
<!-- pdf-source: page=9; block=6; confidence=0.73 -->
**Proof.** Theorem 1’s simulation uses the storage bound to obtain an exponential time bound, then uses about `log^2 T(n)` storage blocks. If `T(n)` is easy to compute, use it directly as the time bound; otherwise apply the increasing-candidate method used for nonmeasurable storage functions.

<a id="pdf-c8033d2fd705-p009-b007"></a>
<!-- pdf-source: page=9; block=7; confidence=0.99 -->
**Corollary 2.** If a context-sensitive language is accepted by a nondeterministic Turing machine within linear storage and polynomial time, then it is accepted by some deterministic Turing machine within storage $n\log_2 n$.

<a id="pdf-c8033d2fd705-p009-b008"></a>
<!-- pdf-source: page=9; block=8; confidence=0.78 -->
A following theorem asserts that for suitably well-behaved `L(n)`, if every nondeterministic `L(n)`-space-bounded Turing machine has a deterministic simulation with the same bound, then nondeterministic and deterministic tape complexities agree for all larger storage bounds.

<a id="pdf-c8033d2fd705-p010-b001"></a>
<!-- pdf-source: page=10; block=1; confidence=0.99 -->
**Theorem 3.** Suppose that $L(n)$ and $H(n)$ are measurable, that $L(n)$ is monotone increasing and unbounded, and that $\log_2 n\le L(n)\le H(n)$, for all $n$. Let $k(n)$ be defined as follows: for each natural number $n$, $k(n)$ is the least natural number such that $H(n)\le L(k(n))$. Suppose further that for any set $A$, if $A$ is accepted by a nondeterministic Turing machine within storage $L(n)$, then $A$ is accepted by a deterministic Turing machine within storage $L(n)$. It then follows that for any set $B$, if $B$ is accepted by a nondeterministic Turing machine within storage $H(n)$, then $B$ is accepted by a deterministic Turing machine within storage $L(k(n))$.

<a id="pdf-c8033d2fd705-p010-b002"></a>
<!-- pdf-source: page=10; block=2; confidence=0.81 -->
For common storage bounds, the iterated bound $L(k(n))$ is within a constant factor of $H(n)$, yielding deterministic simulation within $H(n)$ under the theorem’s hypothesis.

<a id="pdf-c8033d2fd705-p010-b003"></a>
<!-- pdf-source: page=10; block=3; confidence=0.99 -->
**Corollary 3.** Suppose $L(n)$ is a polynomial in $\log_2 n$, $n$ and $c^n$, for some constant $c$. Suppose further that for any set $A$, if $A$ is accepted by a nondeterministic Turing machine within storage $L(n)$, then $A$ is accepted by some deterministic Turing machine within storage $L(n)$. It then follows that for any measurable function $H(n)\ge L(n)$ and any set $B$, if $B$ is accepted by a nondeterministic Turing machine within storage $H(n)$, then $B$ is accepted by some deterministic Turing machine within storage $H(n)$.

<a id="pdf-c8033d2fd705-p010-b004"></a>
<!-- pdf-source: page=10; block=4; confidence=0.86 -->
If every context-sensitive language has a deterministic linear-space recognizer, then deterministic and nondeterministic tape complexity agree for every measurable space bound $H(n)\ge n$.

<a id="pdf-c8033d2fd705-p010-b005"></a>
<!-- pdf-source: page=10; block=5; confidence=0.99 -->
For any such polynomial $L(n)$, there is a constant $c$ such that $L(n)/L(n+1)\ge c$ for all $n$. Thus $cL(k(n))\le L(k(n)-1)\le H(n)$. By Theorem 3, $B$ is accepted by a deterministic Turing machine within storage $L(k(n))$. By standard tape reduction techniques, it follows that $B$ is accepted by a deterministic Turing machine within storage $cL(k(n))\le H(n)$.

<a id="pdf-c8033d2fd705-p010-b006"></a>
<!-- pdf-source: page=10; block=6; confidence=0.98 -->
**Proof.** Assume the hypotheses and let $B$ be accepted nondeterministically in space $H(n)$. The construction continues on page 11.

<a id="pdf-c8033d2fd705-p011-b001"></a>
<!-- pdf-source: page=11; block=1; confidence=0.98 -->
Let $\beta$ be a new symbol. Let $A=\{w\beta^h:w\in B\text{ and }|w|+h\ge k(|w|)\}$. A nondeterministic Turing machine $Z_N^L$ accepts $A$ within storage $L(n)$ as follows. Given input $w\beta^h$, $Z_N^L$ first marks off $L(n)$ squares of storage, where $n=|w\beta^h|$. It then checks whether $L(n)\ge H(|w|)$. If this is not the case, then $n=|w|+h<k(|w|)$ and the computation halts. If $L(n)\ge H(|w|)$, then $Z_N^L$ mimics $Z_N^H$ to see if $w$ is in $B$.

<a id="pdf-c8033d2fd705-p011-b002"></a>
<!-- pdf-source: page=11; block=2; confidence=0.98 -->
Given an input $w$, $Z_D^H$ mimics $Z_D^L$ operating on $w\beta^h$ for successive values of $h$, starting with $h=0$. If $Z_D^L$ accepts, then $Z_D^H$ accepts. If not, it tries $h=1$, then $h=2$, and so on. If $w\in B$, it eventually finds the least $h$ such that $|w|+h\ge k(|w|)$, and the simulated input $w\beta^h$ has length $k(|w|)$. Thus it accepts within storage $L(k(|w|))$.

<a id="pdf-c8033d2fd705-p011-b003"></a>
<!-- pdf-source: page=11; block=3; confidence=0.94 -->
Blum showed that arbitrarily large, nonmeasurable storage bounds can make deterministic and nondeterministic acceptance classes coincide; Theorem 3 does not apply to these bounds.

<a id="pdf-c8033d2fd705-p011-b004"></a>
<!-- pdf-source: page=11; block=4; confidence=0.94 -->
Whether some sufficiently large storage bound has different deterministic and nondeterministic classes remains open. The next section recasts nondeterministic acceptance as reachability in a directed maze.

<a id="pdf-c8033d2fd705-p011-b005"></a>
<!-- pdf-source: page=11; block=5; confidence=0.99 -->
Mazes and Turing Machines

<a id="pdf-c8033d2fd705-p011-b006"></a>
<!-- pdf-source: page=11; block=6; confidence=0.94 -->
A maze is a directed graph with a designated start and goal vertices; it is threadable when some directed path leads from the start to a goal. A nondeterministic machine’s configurations and one-step transitions form such a graph.

<a id="pdf-c8033d2fd705-p012-b001"></a>
<!-- pdf-source: page=12; block=1; confidence=0.99 -->
The set of threadable mazes, suitably coded, can be recognized by a nondeterministic Turing machine within storage $\log_2 n$. This set can be recognized by some deterministic Turing machine within storage $\log_2 n$ if and only if deterministic $L(n)$-tape-bounded Turing machines can simulate nondeterministic $L(n)$-tape-bounded Turing machines, for all $L(n)\ge\log_2 n$.

<a id="pdf-c8033d2fd705-p012-b002"></a>
<!-- pdf-source: page=12; block=2; confidence=0.98 -->
**Definition.** A maze over a finite alphabet $\Sigma$ is a quadruple $\mathcal M=(X,R,s,G)$, where $X$ is a finite set of strings over $\Sigma$ (rooms), $R$ is a binary relation on $X$ (corridors), $s\in X$ is the start, and $G\subseteq X$ is the set of goals.

<a id="pdf-c8033d2fd705-p012-b003"></a>
<!-- pdf-source: page=12; block=3; confidence=0.97 -->
**Definition.** The maze $\mathcal M=(X,R,s,G)$ is threadable if there is a finite room sequence $r_1,\ldots,r_\ell$ with $r_1=s$, $r_\ell\in G$, and $R(r_i,r_{i+1})$ for $1\le i<\ell$.

<a id="pdf-c8033d2fd705-p012-b004"></a>
<!-- pdf-source: page=12; block=4; confidence=0.96 -->
**Definition.** Let $], [, *$ be three new symbols. A coding of the maze $\mathcal M=(X,R,s,G)$ is a string of the form
\[
s[x_1*y_1^1*\cdots*y_{n(1)}^1][x_2*y_1^2*y_2^2*\cdots*y_{n(2)}^2]\cdots[x_l*y_1^l*\cdots*y_{n(l)}^l]u_1*u_2*\cdots*u_g,
\tag{1}
\]
where $s$ is the start room; $x_1,\ldots,x_l$ enumerate the rooms in $X$ without repetitions; for each $i$, $y_1^i,\ldots,y_{n(i)}^i$ enumerate without repetitions all $y$ in $X$ such that $R(x_i,y)$; and $u_1,\ldots,u_g$ enumerate without repetitions the rooms in $G$.

<a id="pdf-c8033d2fd705-p012-b005"></a>
<!-- pdf-source: page=12; block=5; confidence=0.95 -->
Let $M_\Sigma$ denote the set of codes of threadable mazes over $\Sigma$.

<a id="pdf-c8033d2fd705-p012-b006"></a>
<!-- pdf-source: page=12; block=6; confidence=0.99 -->
**Theorem 4.** For any finite alphabet $\Sigma$, there is a nondeterministic Turing machine which accepts $M_\Sigma$ within storage $\log_2 n$.

<a id="pdf-c8033d2fd705-p013-b001"></a>
<!-- pdf-source: page=13; block=1; confidence=0.96 -->
**Proof.** A maze of length $n$ has at most $n$ rooms, each encoded by its index in $O(\log_2 n)$ tape squares. A nondeterministic machine stores the current room code, guesses a successor, and accepts upon reaching a goal room; its work storage is $O(\log_2 n)$. A crossing-sequence argument gives a matching logarithmic lower bound up to a constant factor.

<a id="pdf-c8033d2fd705-p013-b002"></a>
<!-- pdf-source: page=13; block=2; confidence=0.99 -->
**Corollary 4.** For any finite alphabet $\Sigma$, there is a deterministic Turing machine which accepts $M_\Sigma$ within storage $(\log_2 n)^2$.

<a id="pdf-c8033d2fd705-p013-b003"></a>
<!-- pdf-source: page=13; block=3; confidence=0.98 -->
**Lemma 4.** For finite alphabets $\Gamma$ and $A$, with $|A|\ge 2$, $M_\Gamma$ is accepted by a deterministic Turing machine in storage $\log_2 n$ iff $M_A$ is.

<a id="pdf-c8033d2fd705-p013-b004"></a>
<!-- pdf-source: page=13; block=4; confidence=0.96 -->
**Lemma 4.** For any finite alphabets $\Sigma$ and $\Delta$ with at least two elements, $M_\Sigma$ is accepted by some deterministic Turing machine within storage $\log_2 n$ if and only if $M_\Delta$ is. For every coding $w$ of a maze over $\Sigma$, there is a coding $\delta(w)$ of a maze over $\Delta$ isomorphic to it, so $w\in M_\Sigma$ iff $\delta(w)\in M_\Delta$. In the displayed coding, replace each room symbol $x_i$ by its $k$-adic representation, where $k$ is the number of symbols in $\Delta$; the same applies to the $y$’s, $u$’s, and $s$. A deterministic machine deciding $M_\Delta$ within storage $\log_2 n$ can be simulated on $\delta(w)$ within storage $c\log_2 n$ for some constant $c$, by maintaining the encoded component under the simulated input head and computing adjacent encodings symbol by symbol. The symmetric argument proves the converse.

<a id="pdf-c8033d2fd705-p014-b001"></a>
<!-- pdf-source: page=14; block=1; confidence=0.95 -->
When the simulated input head leaves the current encoded component at either end, the simulator moves to the adjacent original component, computes and stores its encoding, then continues. It finds the corresponding room code by symbolwise comparison, using $O(\log_2 n)$ storage. Reversing the roles of the alphabets proves the lemma.

<a id="pdf-c8033d2fd705-p014-b002"></a>
<!-- pdf-source: page=14; block=2; confidence=0.91 -->
**Theorem 5.** For every finite alphabet $\Gamma$ with at least two symbols, the following are equivalent: (1) $M_\Gamma$ is decidable deterministically in storage $\log_2 n$. (2) For every finite input alphabet $F$, language $A\subseteq F^*$, and function $L(n)\ge \log_2 n$, if $A$ is accepted nondeterministically within storage $L(n)$, then it is accepted deterministically within the same storage bound.

<a id="pdf-c8033d2fd705-p014-b003"></a>
<!-- pdf-source: page=14; block=3; confidence=0.99 -->
The encoding $m(w)$ has length at most $h^{L(n)}$, where $n=|w|$ and $h$ is a constant depending only on $Z_N$. Except for the tape used to store $m(w)$, $Z_D$ operates in storage $\log_2 h^{L(n)}$, which is proportionate to $L(n)$. To simulate within that storage, $Z_D$ generates $m(w)$ from right to left, one symbol at a time, while keeping track of the symbol position.

<a id="pdf-c8033d2fd705-p015-b001"></a>
<!-- pdf-source: page=15; block=1; confidence=0.97 -->
Fix $m(w)$ to be the following coding of the maze $\mathcal M(w)$:
\[
s[x_1*y_1^1*y_2^1*\cdots*y_{n(1)}^1][x_2*y_1^2*y_2^2*\cdots*y_{n(2)}^2]
\cdots[x_l*y_1^l*\cdots*y_{n(l)}^l]u_1*u_2*\cdots*u_g,
\]
where $x_1<x_2<\cdots<x_l$; for each $i$, $y_1^i<y_2^i<\cdots<y_{n(i)}^i$; and $u_1<u_2<\cdots<u_g$, using the usual ordering on natural numbers. The $x$’s, $y$’s, and $u$’s are strings over a finite alphabet and may be regarded as numbers in $k$-adic notation. $Z_D$ generates $m(w)$ symbol by symbol in the allotted storage: it writes the initial ID $s$, enumerates valid IDs in numerical order to obtain $x_1,\ldots,x_l$, generates each ID’s successors, then enumerates accepting IDs $u_1,\ldots,u_g$.

<a id="pdf-c8033d2fd705-p015-b002"></a>
<!-- pdf-source: page=15; block=2; confidence=0.92 -->
If $L$ is not measurable, try candidate bounds $1,2,3,\ldots$ in order and test whether $Z_N$ accepts $w$ within each candidate bound. If it accepts within the true bound $L(n)$, the process eventually reaches that value and accepts using storage proportional to $L(n)$.

<a id="pdf-c8033d2fd705-p015-b003"></a>
<!-- pdf-source: page=15; block=3; confidence=0.94 -->
It is open whether some language and space bound $L(n)\ge\log_2 n$ are accepted nondeterministically within $L(n)$ but not deterministically within it. Theorem 5 implies that if such a pair exists, then $M_\Gamma$ is such a language and the bound can be taken to be $\log_2 n$.

<a id="pdf-c8033d2fd705-p016-b001"></a>
<!-- pdf-source: page=16; block=1; confidence=0.99 -->
## Acknowledgment

<a id="pdf-c8033d2fd705-p016-b002"></a>
<!-- pdf-source: page=16; block=2; confidence=0.99 -->
The author credits Stephen A. Cook for assistance and encouragement.

<a id="pdf-c8033d2fd705-p016-b003"></a>
<!-- pdf-source: page=16; block=3; confidence=0.99 -->
## References

<a id="pdf-c8033d2fd705-p016-b004"></a>
<!-- pdf-source: page=16; block=4; confidence=0.98 -->
Nine references on computational complexity, automata, formal languages, grammar theory, and machine simulation. No mathematical statements or proof steps occur on this page.
