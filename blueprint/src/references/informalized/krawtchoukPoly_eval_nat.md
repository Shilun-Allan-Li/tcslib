<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/MRRW.lean :: krawtchoukPoly_eval_nat -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: claude-opus-4-8; confidence: high -->

# Krawtchouk Polynomials Evaluate to the Alternating Binomial Sum

**Claim.** Fix a natural number $n$, and let $j,x$ be natural numbers with $j\le n$ and $x\le n$. Then the Krawtchouk polynomial $K_j^{(n)}$ — defined by the recursion $K_0^{(n)}=1$, $K_1^{(n)}=n-2X$, and $K_{j+2}^{(n)}=\tfrac{1}{j+2}\big((n-2X)\,K_{j+1}^{(n)}-(n-j)\,K_j^{(n)}\big)$ — when evaluated at the real number $x$ returns the explicit alternating sum $\sum_{i=0}^{j}(-1)^i\binom{x}{i}\binom{n-x}{j-i}$. In other words, the recursively-defined polynomial and the combinatorial closed form agree at every integer point in range.

**Proof.** Write $S_j(x):=\sum_{i=0}^{j}(-1)^i\binom{x}{i}\binom{n-x}{j-i}$ for the alternating sum (the quantity `krawtchouk n j x`), so the goal is $K_j^{(n)}(x)=S_j(x)$.

The argument is an induction on the degree $j$. Because the defining recursion for $K_{j+2}^{(n)}$ looks back **two** steps — it refers to both $K_{j+1}^{(n)}$ and $K_j^{(n)}$ — ordinary induction on $j$ would not hand us $K_j^{(n)}(x)$ in the step for $K_{j+2}^{(n)}(x)$. The proof therefore uses *strong* induction on $j$, which makes the result available for every smaller index simultaneously; the point $x$ is kept general throughout, so the inductive hypothesis is a statement about all arguments at once. One then splits the induction according to whether $j$ is $0$, $1$, or of the form $j+2$, matching the three branches of the definition.

1. **Base case $j=0$.** Here $K_0^{(n)}$ is the constant polynomial $1$, so its value at $x$ is $1$. On the combinatorial side, the sum $S_0(x)$ has only the term $i=0$, namely $\binom{x}{0}\binom{n-x}{0}=1$. The two agree. (This is the identity $S_0(x)=1$, `krawtchouk_zero`.)

2. **Base case $j=1$.** Here $K_1^{(n)}=n-2X$, which evaluates to $n-2x$. The sum $S_1(x)$ is $\binom{x}{0}\binom{n-x}{1}-\binom{x}{1}\binom{n-x}{0}=(n-x)-x=n-2x$; the hypothesis $x\le n$ is what guarantees $\binom{n-x}{1}=n-x$ takes its honest value. The two agree. (This is $S_1(x)=n-2x$ for $x\le n$, `krawtchouk_one`, the one place the base cases consume $x\le n$.)

3. **Inductive step, index $j+2$.** Unfolding the definition and evaluating at $x$ gives
\[
K_{j+2}^{(n)}(x)=\frac{1}{j+2}\Big((n-2x)\,K_{j+1}^{(n)}(x)-(n-j)\,K_{j}^{(n)}(x)\Big).
\]
Both indices $j+1$ and $j$ are strictly smaller than $j+2$, so the strong induction hypothesis applies at the point $x$ and lets us replace $K_{j+1}^{(n)}(x)$ by $S_{j+1}(x)$ and $K_j^{(n)}(x)$ by $S_j(x)$. The goal is thereby reduced to the purely combinatorial identity
\[
S_{j+2}(x)=\frac{1}{j+2}\Big((n-2x)\,S_{j+1}(x)-(n-j)\,S_j(x)\Big).
\]

4. **Closing the step via the three-term recurrence.** The sums $S_m(x)$ satisfy their own recurrence (`krawtchouk_recurrence`): for $1\le m$ and $m+1\le n$ and $x\le n$,
\[
(m+1)\,S_{m+1}(x)=(n-2x)\,S_m(x)-(n-m+1)\,S_{m-1}(x).
\]
Instantiating at $m=j+1$ turns this into
\[
(j+2)\,S_{j+2}(x)=(n-2x)\,S_{j+1}(x)-\big(n-(j+1)+1\big)\,S_{j}(x),
\]
and since $n-(j+1)+1=n-j$ this is exactly the numerator of the reduced goal. The side conditions needed to invoke the recurrence — $1\le j+1$ and $(j+1)+1\le n$ — follow from $j+2\le n$, which is the hypothesis $j\le n$ in this branch, while $x\le n$ is given. Finally, $j+2>0$ as a real number, so dividing the recurrence through by $j+2$ yields precisely the identity required in step 3. This completes the induction.

**Key facts.** `krawtchouk_zero`, `krawtchouk_one`, `krawtchouk_recurrence`.
