<!-- generated-by: proofmatch Claude repair -->
<!-- source-pdf-sha256: 1a201b3020697c11026a8960d25aa9c472f55d033017ef3ddb0948be261f2347 -->

<a id="pdf-1a201b302069-p001-b001"></a>
<!-- pdf-source: page=1; block=1; confidence=0.99 -->
# Some Consequences of Nonuniform Conditions on Uniform Classes

<a id="pdf-1a201b302069-p001-b002"></a>
<!-- pdf-source: page=1; block=2; confidence=0.99 -->
**Abstract.** We obtain some results of the form: If certain complexity classes satisfy a non-uniform condition, then some unlikely consequences follow. More precisely:

(1) If the “non-uniform polynomial-time hierarchy” collapses at level $i>0$, i.e., $\Sigma_i/\mathrm{poly}=\Pi_i/\mathrm{poly}$, then the Meyer–Stockmeyer hierarchy collapses at level $i+2$, i.e., $\Sigma_{i+2}=\Pi_{i+2}$. This strengthens a generalization of a result of Karp and Lipton (1980).

(2) If co-NP is conjunctively reducible to a sparse set, then P = NP. This generalizes a theorem of Fortune (1979).

(3) If NP is conjunctively and disjunctively reducible to a sparse NP-complete set, then P = NP. This is a partial generalization of a result of Mahaney (1980). Conjunctive and disjunctive reducibility were introduced by Ladner, Lynch and Selman (1975).

(4) If co-NP is $\gamma$-reducible to a sparse set, then NP = co-NP. $\gamma$-reducibility was introduced by Adleman and Manders (1977).

<a id="pdf-1a201b302069-p001-b003"></a>
<!-- pdf-source: page=1; block=3; confidence=0.99 -->
## 1. Introduction

<a id="pdf-1a201b302069-p001-b004"></a>
<!-- pdf-source: page=1; block=4; confidence=0.91 -->
The paper studies consequences of imposing nonuniform complexity conditions on uniform complexity classes, building on circuit-complexity and polynomial-isomorphism research. It notes that NP being many-one reducible to a sparse set would imply P = NP.

<a id="pdf-1a201b302069-p002-b001"></a>
<!-- pdf-source: page=2; block=1; confidence=0.96 -->
The paper continues the study of how nonuniform conditions on uniform classes yield complexity-class consequences, introducing a nonuniform polynomial-time hierarchy and extending earlier results.

<a id="pdf-1a201b302069-p002-b002"></a>
<!-- pdf-source: page=2; block=2; confidence=0.97 -->
**Notation.** For $x,y\in\{0,1\}^*$, let $x\cdot y\in\{0,1\}^*$ refer to the result of applying a fixed “pairing” function “$\cdot$” to $x$ and $y$. We require that “$\cdot$” be polynomial-time computable. We conveniently write $x_1\cdot x_2\cdots x_k$ or $x_1x_2\cdots x_k$ instead of $x_1\cdot(x_2\cdot(\cdots(x_{k-1}\cdot x_k)\cdots))$. The projection functions are implicit, e.g., we can extract $x$ from $x\cdot y$.

To conserve symbols, we adopt $p^*(\cdot)$ as a “generic polynomial”. Thus if the function $f$ is bounded by some polynomial, we write “$f(n)\le p^*(n)$”. The asterisk has properties like Kleene’s star, as in $f(n)\le p^*(p^*(n))\Rightarrow f(n)\le p^*(n)$.

For polynomially bounded quantifiers, instead of writing $(\exists x)[|x|\le p^*(n)\vee\cdots]$ or $(\forall x)[|x|\le p^*(n)\to\cdots]$, we write $(\exists_{p^*x})[\cdots]$ and $(\forall_{p^*x})[\cdots]$.

<a id="pdf-1a201b302069-p002-b003"></a>
<!-- pdf-source: page=2; block=3; confidence=0.99 -->
## 2. Nonuniform Conditions

<a id="pdf-1a201b302069-p002-b004"></a>
<!-- pdf-source: page=2; block=4; confidence=0.99 -->
For a set $S\subseteq\{0,1\}^*$, let $S^{(n)}=S\cap\{0,1\}^n$. Recently, two “non-uniform” conditions on $S$ were studied:

(1) **Sparseness:** $|S^{(n)}|\le p^*(n)$.

(2) **Small circuits:** The characteristic function of $S^{(n)}$ can be computed by a circuit of size $\le p^*(n)$.

<a id="pdf-1a201b302069-p002-b005"></a>
<!-- pdf-source: page=2; block=5; confidence=0.94 -->
These nonuniform conditions can hold even for nonrecursive sets; complexity theory focuses on uniform, machine-recognizable sets and studies nonuniform sets through results relating them to such classes.

<a id="pdf-1a201b302069-p003-b001"></a>
<!-- pdf-source: page=3; block=1; confidence=0.87 -->
The cited examples are Mahaney’s theorem, NP ≤ₘ^P S for sparse S implies NP = P, and Karp–Lipton, small circuits for every S ∈ NP implies Σ₂ = Π₂. The paper omits the superscript P from polynomial-time reductions and treats classes as families of subsets of {0,1}^n.

<a id="pdf-1a201b302069-p003-b002"></a>
<!-- pdf-source: page=3; block=2; confidence=0.94 -->
An advice function α:{0,1}*→{0,1}* satisfies |x|=|y| ⇒ α(x)=α(y), so its value depends only on input length; α(n) denotes that value. It is polynomial advice when |α(n)| ≤ p*(n). For a language L, L/α = {x : x·α(|x|) ∈ L}; K/poly consists of languages L/α with L ∈ K and α a polynomial advice function.

<a id="pdf-1a201b302069-p003-b003"></a>
<!-- pdf-source: page=3; block=3; confidence=0.84 -->
The nonuniform polynomial-time (advice) hierarchy is the hierarchy obtained from the usual polynomial-time hierarchy by replacing each class K with K/poly. PH denotes ⋃_{i≥0} Σᵢ. The usual hierarchy collapses if Σᵢ = Πᵢ for any i>0.

<a id="pdf-1a201b302069-p003-b004"></a>
<!-- pdf-source: page=3; block=4; confidence=0.99 -->
**Theorem 1.** For $i>0$, $\Sigma_i/\mathrm{poly}=\Pi_i/\mathrm{poly}\;\Rightarrow\;\Sigma_i/\mathrm{poly}=\mathrm{PH}/\mathrm{poly}=\Pi_i/\mathrm{poly}$.

<a id="pdf-1a201b302069-p003-b005"></a>
<!-- pdf-source: page=3; block=5; confidence=0.87 -->
**Theorem 2.** For i>0, if Σᵢ/poly = Πᵢ/poly, then Σᵢ₊₂ = Πᵢ₊₂. This gives a partial converse to the implication that Σᵢ = Πᵢ entails Σᵢ/poly = Πᵢ/poly.

<a id="pdf-1a201b302069-p003-b006"></a>
<!-- pdf-source: page=3; block=6; confidence=0.96 -->
To see the connection of (4) to this theorem, recall that $S$ has small circuits iff $S\in\mathrm{P}/\mathrm{poly}=\Pi_0/\mathrm{poly}$. Thus (4) is equivalent to $\Sigma_1\subseteq\Pi_0/\mathrm{poly}\;\Rightarrow\;\Sigma_2=\Pi_2$. This generalizes to: For $i\ge0$, $\Sigma_{i+1}\subseteq\Pi_i/\mathrm{poly}\;\Rightarrow\;\Sigma_{i+2}=\Pi_{i+2}$.

<a id="pdf-1a201b302069-p004-b001"></a>
<!-- pdf-source: page=4; block=1; confidence=0.76 -->
Theorem 2 strengthens (*) for positive indices: the stated containment implies equality of the corresponding polynomial-hierarchy levels. The text also notes open questions about replacing the reduction in (3) by truth-table reducibility and about conjunctive reductions.

<a id="pdf-1a201b302069-p004-b002"></a>
<!-- pdf-source: page=4; block=2; confidence=0.78 -->
Finite subsets of $\{0,1\}^n$ are assumed canonically encoded as strings. For a polynomial-time function $f$ whose output encodes a set $f(x)$, define $L\leq_{\mathrm{con}}L'$ when $x\in L$ iff $f(x)\subseteq L'$; require $f(x)\neq\varnothing$ for every $x$.

<a id="pdf-1a201b302069-p004-b003"></a>
<!-- pdf-source: page=4; block=3; confidence=0.91 -->
**Theorem 3.** If $\mathrm{coNP}\leq_{\mathrm{con}}S$ for a sparse set $S$, then $\mathrm{NP}=\mathrm{P}$.

<a id="pdf-1a201b302069-p004-b004"></a>
<!-- pdf-source: page=4; block=4; confidence=0.99 -->
If $\mathrm{co}-L\le_{\mathrm{con}}\mathrm{co}-L'$, we say $L$ is disjunctively reducible to $L'$, denoted $L\le_{\mathrm{dis}}L'$. This was also introduced in [9]. Note that $\mathrm{NP}\le_m S$ implies that $\mathrm{NP}\le_{\mathrm{con}}S$ and $\mathrm{NP}\le_{\mathrm{dis}}S$.

<a id="pdf-1a201b302069-p004-b005"></a>
<!-- pdf-source: page=4; block=5; confidence=0.93 -->
**Theorem 4.** If $S\in\mathrm{NP}$ is sparse and both $\mathrm{NP}\leq_{\mathrm{con}}S$ and $\mathrm{NP}\leq_{\mathrm{dis}}S$, then $\mathrm{P}=\mathrm{NP}$.

<a id="pdf-1a201b302069-p004-b006"></a>
<!-- pdf-source: page=4; block=6; confidence=0.88 -->
This would fully generalize result (3) if the condition $S\in\mathrm{NP}$ could be removed; the text contrasts its hypotheses with those of Theorem 3.

<a id="pdf-1a201b302069-p004-b007"></a>
<!-- pdf-source: page=4; block=7; confidence=0.83 -->
For a nondeterministic transducer $M$, let $G(M)=\{(x,y): M\text{ outputs }y\text{ on some computation on input }x\}$. Write $L\leq_y L'$ if some polynomial-time nondeterministic transducer $M$ satisfies: (i) for every $x$, at least one output $y$ has $(x,y)\in G(M)$; and (ii) for every such pair, $x\in L$ iff $y\in L'$. The transducer may be assumed to halt in polynomial time, with or without output.

<a id="pdf-1a201b302069-p004-b008"></a>
<!-- pdf-source: page=4; block=8; confidence=0.91 -->
**Theorem 5.** If $\mathrm{coSAT}\leq_y S$ for a sparse set $S$, then $\mathrm{NP}=\mathrm{coNP}$.

<a id="pdf-1a201b302069-p004-b009"></a>
<!-- pdf-source: page=4; block=9; confidence=0.89 -->
The cited earlier results do not yield this particular conclusion.

<a id="pdf-1a201b302069-p005-b001"></a>
<!-- pdf-source: page=5; block=1; confidence=0.99 -->
## 3. Collapse of the advice hierarchy

<a id="pdf-1a201b302069-p005-b002"></a>
<!-- pdf-source: page=5; block=2; confidence=0.95 -->
The section proves Theorems 1 and 2, beginning with a useful elementary result.

<a id="pdf-1a201b302069-p005-b003"></a>
<!-- pdf-source: page=5; block=3; confidence=0.77 -->
**Lemma 6.** $(\mathrm{co}K)/\mathrm{poly}=\mathrm{co}(K/\mathrm{poly})$.

<a id="pdf-1a201b302069-p005-b004"></a>
<!-- pdf-source: page=5; block=4; confidence=0.94 -->
**Lemma 6.** $(\mathrm{co}-K)/\mathrm{poly}=\mathrm{co}-(K/\mathrm{poly})$.

**Proof.** Let $L\in\mathrm{co}-(K/\mathrm{poly})$. Then
\[
x\in L\iff x\notin\mathrm{co}-L\in K/\mathrm{poly}\iff x\cdot\alpha(x)\in L'\in K\quad(\text{where }\mathrm{co}-L=L'/\alpha)
\]
\[
\iff x\cdot\alpha(x)\in\mathrm{co}-L'\iff x\in(\mathrm{co}-L')/\alpha\in(\mathrm{co}-K)/\mathrm{poly}.
\]

<a id="pdf-1a201b302069-p005-b005"></a>
<!-- pdf-source: page=5; block=5; confidence=0.73 -->
Consequently, if $K$ is closed under complementation, then the corresponding polynomial-advice class is also closed under complementation.

<a id="pdf-1a201b302069-p005-b006"></a>
<!-- pdf-source: page=5; block=6; confidence=0.99 -->
**Lemma 7.** $\forall i>0,\;\Pi_i\subseteq\Sigma_i/\mathrm{poly}\text{ implies }\Sigma_{i+1}/\mathrm{poly}=\Sigma_i/\mathrm{poly}$.

<a id="pdf-1a201b302069-p005-b007"></a>
<!-- pdf-source: page=5; block=7; confidence=0.96 -->
**Proof.** The proof here for $i=1$ extends mutatis mutandis for all $i>1$. Assume $\Pi_1\subseteq\Sigma_1/\mathrm{poly}$ and $L\in\Sigma_2/\mathrm{poly}$. The lemma follows if we show $L\in\Sigma_1/\mathrm{poly}$. So:

(1) Since $L\in\Sigma_2/\mathrm{poly}$,
\[
(\exists S_2\in\Sigma_2,\alpha\in\mathrm{poly})(\forall x)[x\in L\iff x\cdot\alpha(x)\in S_2].
\]

(2) Since $S_2\in\Sigma_2$,
\[
(\exists P_1\in\Pi_1)(\forall x)[x\cdot\alpha(x)\in S_2\iff(\exists_{|x|,a})\,x\cdot a\cdot\alpha(x)\in P_1].
\]

(3) Since $\Pi_1\subseteq\Sigma_1/\mathrm{poly}$,
\[
(\exists S_1\in\Sigma_1,\alpha'\in\mathrm{poly})(\forall x,a)[x\cdot a\cdot\alpha(x)\in P_1\iff x\cdot a\cdot\alpha(x)\cdot\alpha'(x\cdot a\cdot\alpha(x))\in S_1].
\]
Let $y_{x,a}$ denote $x\cdot a\cdot\alpha(x)\cdot\alpha'(x\cdot a\cdot\alpha(x))$.

(4) Since $S_1\in\Sigma_1$,
\[
(\exists P_0\in\Pi_0)(\forall x,a\text{ where }|a|\le p^*(|x|))[y_{x,a}\in S_1\iff(\exists_{|y_{x,a}|,b})\,y_{x,a}\cdot b\in P_0].
\]

We “telescope” (1)–(4) into the following:

(5) From (1) and (2),
\[
(\exists P_1\in\Pi_1,\alpha\in\mathrm{poly})(\forall x)[x\in L\iff(\exists_{|x|,a})\,x\cdot a\cdot\alpha(x)\in P_1].
\]

<a id="pdf-1a201b302069-p006-b001"></a>
<!-- pdf-source: page=6; block=1; confidence=0.91 -->
(6) From (5) and (3),
\[
(\exists S_1\in\Sigma_1,\alpha,\alpha'\in\mathrm{poly})(\forall x)[x\in L\iff(\exists_{|x|,a})\,y_{x,a}\in S_1].
\]

(7) From (6) and (4),
\[
(\exists P_0\in\Pi_0,\alpha,\alpha'\in\mathrm{poly})(\forall x)[x\in L\iff(\exists_{|x|,a,b})\,y_{x,a}\cdot b\in P_0].
\]

Simplifying (7) we obtain
\[
(8)\quad(\exists P'_1\in\Pi_1,\alpha''\in\mathrm{poly})(\forall x)[x\in L\iff(\exists_{|x|,c})\,x\cdot\alpha''(x)\cdot c\in P'_1].
\]

In (7), by definition, $y_{x,a}$ contains the advice $\alpha'(x\cdot a\cdot\alpha(x))$, but in (8) we have an advice $\alpha''(x)$ which apparently does not depend on $|a|$. The trick is to let $\alpha''(x)$ encode all the advices $\alpha'(x\cdot 0^i\cdot\alpha(x))$ for each possible value of $|a|=i$. More precisely, define $P'_1$ to consist of strings
\[
x\cdot\alpha(x)\cdot 0^k\cdot z_0\cdots z_k\cdot c
\]
for $|z_i|,k\le p^*(|x|)$ and $x\cdot a\cdot u\cdot z_{|a|}\cdot b\in P_0$ where $c=a\cdot b$. It is not hard to see that $P'_1\in\Pi_1$. Next define $\alpha''$ by $\alpha''(x)=\alpha(x)\cdot0^k\cdot z_0\cdots z_k$, where $z_i=\alpha'(x\cdot0^i\cdot\alpha(x))$ and $k=p_1(|x|)$ for a polynomial $p_1(\cdot)$. This polynomial $p_1$ is the implicit bound on $|a|$ when we write $(\exists_{|x|}a)$ in (2). Clearly $\alpha''\in\mathrm{poly}$. Now (7) implies (8) since
\[
y_{x,a}\cdot b=x\cdot a\cdot\alpha(x)\cdot\alpha'(x\cdot a\cdot\alpha(x))\cdot b\in P_0
\]
iff $x\cdot\alpha(x)\cdot0^k\cdot z_0\cdots z_k\cdot c\in P'_1$, where $c=a\cdot b$, $k=p_1(|a|)$, and $z_i=\alpha'(x\cdot0^i\cdot\alpha(x))$. From (8) we get
\[
(9)\quad(\exists S'_1\in\Sigma_1,\alpha''\in\mathrm{poly})(\forall x)[x\in L\iff x\cdot\alpha''(x)\in S'_1],
\]
which proves $L\in\Sigma_1/\mathrm{poly}$.

<a id="pdf-1a201b302069-p007-b001"></a>
<!-- pdf-source: page=7; block=1; confidence=0.91 -->
Assuming (ii), every $Z_i$ lies in $\mathrm{poly}$, so by Lemma 7, $X_{i+1}/\mathrm{poly}=X_i/\mathrm{poly}$. Therefore $Z_i/\mathrm{poly}=\bigcup_j(X_j/\mathrm{poly})=(\bigcup_j S_j)/\mathrm{poly}=PH/\mathrm{poly}$, yielding (iii). The other cases are asserted to follow similarly.

<a id="pdf-1a201b302069-p007-b002"></a>
<!-- pdf-source: page=7; block=2; confidence=0.97 -->
Theorem 1 follows from the corollary; the proof of Theorem 2 follows.

<a id="pdf-1a201b302069-p007-b003"></a>
<!-- pdf-source: page=7; block=3; confidence=0.99 -->
Condition (iii): If $x$ is a $<$-minimal element, then $B(F_1(x),\ldots,F_r(x),y_1,\ldots,y_s)=B(F_1(x),\ldots,F_r(x),y'_1,\ldots,y'_s)$ for all $y_k,y'_k$, $k=1,\ldots,s$.

<a id="pdf-1a201b302069-p007-b004"></a>
<!-- pdf-source: page=7; block=4; confidence=0.98 -->
Let $A_i$ be any reasonable encoding of the set of true prenex sentences of the form
\[
Q_1\bar{x}_1Q_2\bar{x}_2\cdots Q_i\bar{x}_i M(\bar{x}_1,\ldots,\bar{x}_i),
\]
where $M(\bar{x}_1,\ldots,\bar{x}_i)$ is a quantifier-free Boolean formula whose variables are included in $\bar{x}_1,\ldots,\bar{x}_i$, for $j=1,\ldots,i$, $Q_j=\forall$ if $j$ is odd, $Q_j=\exists$ otherwise, and $\bar{x}_i$ is a sequence of Boolean variables. $E_i$ is similarly defined except the roles of $\forall$ and $\exists$ are reversed.

<a id="pdf-1a201b302069-p007-b005"></a>
<!-- pdf-source: page=7; block=5; confidence=0.96 -->
The text states that $A_i$ and $E_i$ have polynomial recursive structures and sketches one for $A_i$.

<a id="pdf-1a201b302069-p007-b006"></a>
<!-- pdf-source: page=7; block=6; confidence=0.98 -->
The structure is $(B;F_1,F_2;G_0,G_1)$ where $F_1(x)=1$ iff $x$ encodes a sentence of the form (10) in which $M$ is nonconstant; $F_2(x)=1$ iff $x$ encodes a sentence of the form (10) and either $M\equiv1$ or the leftmost variable in the sequence $(\bar{x}_1,\ldots,\bar{x}_i)$ which actually occurs in $M$ is bounded by an existential quantifier. $G_0(x)=x$ if $F_1(x)=0$, otherwise $G_0(x)$ is the sentence obtained by substituting 0 for all occurrences of the leftmost variable in the sequence which actually occurs in $M$. $G_1$ is similar to $G_0$ except the occurrences are replaced by 1.

<a id="pdf-1a201b302069-p008-b001"></a>
<!-- pdf-source: page=8; block=1; confidence=0.99 -->
$G_1$ is similar to $G_0$ except the occurrences are replaced by 1. With a suitable encoding scheme, we can further assume that the $G_k$'s are length preserving, i.e., $|G_k(x)|=|x|$. It should be clear how $B(x_1,x_2,y_1,y_2)=z$ is defined:
\[
z=\begin{cases}x_2&\text{if }x_1=0,\\y_1\lor y_2&\text{if }x_1=1\land x_2=1,\\y_1\land y_2&\text{if }x_1=1\land x_2=0.\end{cases}
\]

<a id="pdf-1a201b302069-p008-b002"></a>
<!-- pdf-source: page=8; block=2; confidence=0.78 -->
**Proof.** Assume $S_i/\mathrm{poly}=S_{i+1}/\mathrm{poly}$. It suffices to prove $A_{i+2}\in S_{i+1}$, since $A_i$ is complete for the relevant class under $\mathrm{poly}$-reductions. By the corollary to Lemma 7, $A_{i+2}\in S_i/\mathrm{poly}$. Thus for some $P_i\in H_i$ and $\alpha\in\mathrm{poly}$, $A_{i+2}=P_i/\alpha$. Use the polynomial recursive structure $(B;F_1,F_2;G_0,G_1)$ for $A_{i+2}$.

<a id="pdf-1a201b302069-p008-b003"></a>
<!-- pdf-source: page=8; block=3; confidence=0.99 -->
Define the predicate $W(x,w)$ by
\[
(\forall y)[|y|=|x|\to\mathrm{ch}_{P_i}(y\cdot w)=B(F_1(y),F_2(y),\mathrm{ch}_{P_i}(G_0(y)\cdot w),\mathrm{ch}_{P_i}(G_1(y)\cdot w))].
\]
Note that, for all $x$, $W(x,\alpha(x))$ is true. If $W(x,w)$ holds, we say $w$ is a witness for $x$.

<a id="pdf-1a201b302069-p008-b004"></a>
<!-- pdf-source: page=8; block=4; confidence=0.71 -->
**Theorem (12).** $x\in A_{i+2}$ iff $(\exists w)[\,x\cdot w\in P_i\land W(x,w)\,]$.

<a id="pdf-1a201b302069-p008-b005"></a>
<!-- pdf-source: page=8; block=5; confidence=0.97 -->
Conversely, let the right-hand side of (12) hold, and let $w$ be a witness for $x$. It is sufficient to show
\[
\forall y,\quad |y|=|x|\Rightarrow(y\cdot w\in P_i\text{ iff }y\in A_{i+2}).
\]
Since the $G_k$'s are length preserving, there is a $y$ which is $<$-minimal and $|y|=|x|$.

<a id="pdf-1a201b302069-p008-b006"></a>
<!-- pdf-source: page=8; block=6; confidence=0.98 -->
For such a $y$,
\[
(13)\quad\mathrm{ch}_{P_i}(y\cdot w)=1\text{ iff }y\in A_{i+2}.
\]
This is because $\mathrm{ch}_{P_i}(y\cdot\alpha(y))=1$ iff $y\in A_{i+2}$. But
\[
\mathrm{ch}_{P_i}(y\cdot w)=\mathrm{ch}_{P_i}(y\cdot\alpha(y))=B(F_1(y),F_2(y),z_1,z_2),
\]
which is independent of the $z_k$'s. By induction on $<$, we see that (13) holds for all $y$, $|y|=|x|$.

<a id="pdf-1a201b302069-p008-b007"></a>
<!-- pdf-source: page=8; block=7; confidence=0.77 -->
Because $P_i\in H_i$, the predicate $W(x,w)$ is in $H_{i+1}$. Hence the right side of (12) belongs to $S_{i+1}$, proving $A_{i+2}\in S_{i+1}$ and Theorem 2.

<a id="pdf-1a201b302069-p008-b008"></a>
<!-- pdf-source: page=8; block=8; confidence=0.98 -->
Section heading: “Conjunctive reduction.”

<a id="pdf-1a201b302069-p008-b009"></a>
<!-- pdf-source: page=8; block=9; confidence=0.98 -->
The section will prove Theorems 3 and 4.

<a id="pdf-1a201b302069-p008-b010"></a>
<!-- pdf-source: page=8; block=10; confidence=0.98 -->
Define the census function $c_S(n)$ of a set $S$ by
\[
c_S(n)=\sum_{i=0}^{n}|S^{(i)}|.
\]

<a id="pdf-1a201b302069-p009-b001"></a>
<!-- pdf-source: page=9; block=1; confidence=0.99 -->
**Proof of Theorem 3.** Let SAT be any reasonable encoding of the satisfiable Boolean formulas without quantifiers (SAT is essentially $E_1$ in the last section). Let $\mathrm{coSAT}\leq_{\mathrm{con}} S$ via $g$. Given a Boolean formula $F$, we show how to test if $F\in\mathrm{SAT}$ in time $p^*(|F|)$, which will prove our theorem.

<a id="pdf-1a201b302069-p009-b002"></a>
<!-- pdf-source: page=9; block=2; confidence=0.92 -->
Nodes are partially instantiated formulas. A nonconstant node branches by assigning $0$ or $1$ to its leftmost variable; leaves are constant true or false formulas. The potentially exponential tree is generated as needed during depth-first search, avoiding descent below nodes already declared dead.

<a id="pdf-1a201b302069-p009-b003"></a>
<!-- pdf-source: page=9; block=3; confidence=0.96 -->
Maintain throughout the search a set $\hat S$ of elements where $\hat S\subseteq S$. Initially $\hat S$ is empty. The following subroutine is used to visit a node $G$.

**VISIT**$(G)$

Step 1. If $G\equiv 1$, declare $F$ satisfiable. Halt.

Step 2. Compute the label $\hat g(G)$ of $G$.

Step 3. If $G\equiv 0$, then do: $\hat S:=\hat S\cup\hat g(G)$ and declare $G$ “dead”.

Step 4. (Propagate Death). For each previously visited node $G'$ which is still alive, test if either $\hat g(G')\subseteq\hat S$ or both $G'_0$ and $G'_1$ are dead. If so, do: $\hat S:=\hat S\cup\hat g(G')$ and declare $G'$ “dead”.

<a id="pdf-1a201b302069-p009-b004"></a>
<!-- pdf-source: page=9; block=4; confidence=0.86 -->
Inductively, every dead node is unsatisfiable, so declaring $F$ dead is correct; a true leaf certifies satisfiability. The finite search tree ensures termination, ruling out visiting every node without a declaration.

<a id="pdf-1a201b302069-p009-b005"></a>
<!-- pdf-source: page=9; block=5; confidence=0.96 -->
Polynomial running time follows from (A) the number of visited nodes being polynomial in $|F|$, and (B) the time to visit each node being polynomial in $|F|$.

<a id="pdf-1a201b302069-p009-b006"></a>
<!-- pdf-source: page=9; block=6; confidence=0.99 -->
Fix an arbitrary instant during the search procedure. Let $N$ be the set of already visited nodes and $D\subseteq N$ be those nodes which are either dead or lie below a dead node. In particular, if $F$ is dead, then $D=N$. We shall show $|N|\leq p(|F|)$.

<a id="pdf-1a201b302069-p010-b001"></a>
<!-- pdf-source: page=10; block=1; confidence=0.94 -->
It is easy to show by induction that if $N-D$ is nonempty, then the nodes $N-D$ form a single path from the root $F$. This implies $|N-D|\leq n<|F|$, where $n$ is the number of variables in $F$. Let $v$ be the root $F$ if $N=D$, otherwise $v$ is any node whose parent is in $N-D$. Let $T$ be the subtree whose nodes are all the elements in $D$ which are descendants of $v$.

There are at most $1+|N-D|\leq |F|$ such trees $T$. Therefore, (A) follows if we can show $|T|\leq p^*(|F|)$. Call node $G\in T$ penultimate if both $G_0$ and $G_1$ are leaves in $T$. The number of leaves in $T$ is $\leq(n+1)u$, where $u$ is the number of penultimate nodes in $T$. So $|T|\leq2(n+1)u$ and it suffices to show that $u\leq p^*(|F|)$. We totally order the penultimate nodes by defining $G<G'$ if $G$ was visited before $G'$. Note that $G<G'$ implies $\hat g(G')-\hat g(G)$ is nonempty, otherwise $G'$ would be declared dead when it was visited and would be in a leaf in $T$. Hence $u$ is bounded by the census number $c_S(k)$ where $k$ is a bound on the lengths of elements in $\hat g(G)$ for $G$ in $T$. But $k\leq p^*(|G|)\leq p^*(|F|)$ so $c_S(k)\leq p^*(|F|)$. This proves (A).

Finally, (B) follows from the observation that $|\hat S|\leq p^*(|F|)$ and at most $n$ live nodes are examined during the propagation of death.

<a id="pdf-1a201b302069-p010-b002"></a>
<!-- pdf-source: page=10; block=2; confidence=0.86 -->
**Proof of Theorem 4.** Define the pseudo-complement of $S$ by
\[
pc\text{-}S=\{0^n\cdot1^k\cdot x: |x|\leq n\text{ and either }(k=c_S(n)\text{ and }x\notin S)\text{ or }k<c_S(n)\}.
\]
To show that $pc\text{-}S\in NP$, consider the nondeterministic algorithm: “On input $0^n\cdot1^k\cdot x$, reject if $|x|>n$. Guess and verify $k$ distinct members of $\bigcup_{i=0}^{n}S^{(i)}$. Accept iff $x$ is distinct from each of the $k$ elements.” This algorithm is in NP since $S\in NP$. It is easy to see that if $k<c_S(n)$, the input is accepted and if $k=c_S(n)$, then the input is accepted iff $x\notin S$.

By hypothesis, there exist $p$-time functions $g$ and $h$ such that
\[
pc\text{-}S\leq_{\mathrm{con}}S\quad(\text{via }g),\qquad \mathrm{SAT}\leq_{\mathrm{lin}}S\quad(\text{via }h).
\]
Define, for each $n,k>0$, the function $f_{n,k}:\{0,1\}^*\to\{0,1\}^*$ where
\[
f_{n,k}(F)=\bigcup_{x:\,h(x)=F}g(0^n\cdot1^k\cdot x).
\]
Suppose $n$ and $k$ satisfy (C) with respect to $F$:
\[
\left\{\begin{array}{l}
n=\max\{|x|:\exists G,\ |G|\leq|F|,\ x\in\hat h(G)\},\\
k=c_S(n).
\end{array}\right.
\]
There is a polynomial $q(\cdot)$, depending only on $g,h$ and $S$, such that (D) holds: $q(|F|)\geq n,k$, and at most $q(|F|)$ nodes are visited when $f_{n,k}$ is used to compute labels during the search of $F$. Run the search for each pair $(n,k)$ with $n,k\leq q(|F|)$, terminating a stage if it attempts to visit more than $q(|F|)$ nodes. If any stage declares $F$ satisfiable, declare it satisfiable; if all stages finish without that declaration, declare it unsatisfiable. The declaration is correct, and a satisfiable $F$ is declared at the stage whose $n,k$ satisfy (C). Thus the theorem follows.

<a id="pdf-1a201b302069-p011-b001"></a>
<!-- pdf-source: page=11; block=1; confidence=0.98 -->
## 5. Proof of Theorem 5

<a id="pdf-1a201b302069-p011-b002"></a>
<!-- pdf-source: page=11; block=2; confidence=0.93 -->
**Proof of Theorem 5.** We shall describe a non-deterministic search, such that, on an input formula $F$, $F\in\mathrm{SAT}$ iff every computation accepts. This search always halts in $p^*(|F|)$ steps, thereby establishing $\mathrm{SAT}\in\mathrm{co\text{-}NP}$.

Let $\mathrm{co\text{-}SAT}\leq_s S$ via $M$. We will perform the tree search as in [4] and Theorem 3 except that the label on each node $G$ is computed nondeterministically by running $M$ on $G$. If $M$ produces no output, we halt the search and accept. If $M$ produces any output, this becomes the label of $G$ and we proceed as before. As in the proof of Theorem 3, we can show that at most $p^*(|F|)$ nodes will be visited.

<a id="pdf-1a201b302069-p012-b001"></a>
<!-- pdf-source: page=12; block=1; confidence=0.99 -->
## 6. Final remarks

<a id="pdf-1a201b302069-p012-b002"></a>
<!-- pdf-source: page=12; block=2; confidence=0.98 -->
Theorem 2 implies that the uniform and non-uniform hierarchies are either both finite or both infinite, despite the non-uniform hierarchy including sets beyond the recursively enumerable ones.

<a id="pdf-1a201b302069-p012-b003"></a>
<!-- pdf-source: page=12; block=3; confidence=0.98 -->
A $k$-generator for a set $S^{(n)}\subseteq\{0,1\}^n$ is a circuit which computes some $f:\{0,1\}^k\to\{0,1\}^n$ such that $S^{(n)}$ is the range of $f$. We say $S$ has small generators if, for all $n$, $S^{(n)}$ has a $p^*(n)$-generator of size $\leq p^*(n)$. Note that if $S$ has small circuits, then it has small generators. The converse is unlikely.

<a id="pdf-1a201b302069-p012-b004"></a>
<!-- pdf-source: page=12; block=4; confidence=0.99 -->
We present another view of generators. For a complexity class $K$, let $NP(K)$ denote the class of languages $L$ such that, for some $A\in K$ and non-deterministic polynomial-time oracle machine $M$, $L$ is accepted by $M$ using oracle $A$. For instance, $\Sigma_{i+1}=NP(\Sigma_i)$, $i\geq0$.

<a id="pdf-1a201b302069-p012-b005"></a>
<!-- pdf-source: page=12; block=5; confidence=0.95 -->
The discussion considers consequences of the assumption that `L` has small generators, denoted (*).

<a id="pdf-1a201b302069-p012-b006"></a>
<!-- pdf-source: page=12; block=6; confidence=0.78 -->
**Fact 1.** Assumption (*) implies `L ∈ NP(Ξ/poly)`.

<a id="pdf-1a201b302069-p012-b007"></a>
<!-- pdf-source: page=12; block=7; confidence=0.90 -->
**Proof.** From (*) we have, for some $\alpha\in\mathrm{poly}$, $S\in\Sigma_0$,
\[
x\in L\iff(\exists_{|x|}y)(x\cdot y\cdot\alpha(x)\in S)
\]
\[
\iff(\exists_{|x|}y)((x\cdot y)\cdot\alpha'(x\cdot y)\in S')
\quad(\text{where }\alpha'(x\cdot y)=\alpha(x),\text{ and for some }S'\in\Sigma_0)
\]
\[
\iff(\exists_{|x|}y)(x\cdot y\in S'/\alpha'),
\]
which proves $L\in NP(\Sigma_0/\mathrm{poly})$.

<a id="pdf-1a201b302069-p012-b008"></a>
<!-- pdf-source: page=12; block=8; confidence=0.98 -->
The converse of Fact 1 is stated to be unknown.

<a id="pdf-1a201b302069-p012-b009"></a>
<!-- pdf-source: page=12; block=9; confidence=0.99 -->
**Fact 2.** $NP(\Sigma_i)/\mathrm{poly}=NP(\Sigma_i/\mathrm{poly})$, $i\geq0$.

<a id="pdf-1a201b302069-p012-b010"></a>
<!-- pdf-source: page=12; block=10; confidence=0.98 -->
**Proof.** $(\subseteq)$ Let $L\in NP(\Sigma_i)$, $\alpha\in\mathrm{poly}$.
\[
x\in L/\alpha\iff x\cdot\alpha(x)\in L
\]
\[
\iff(\exists_{|x|}y)(x\cdot\alpha(x)\cdot y\in L')\quad\text{for some }L'\in\Sigma_i
\]
\[
\iff(\exists_{|x|}y)(x\cdot y\in L''/\alpha')
\]
for some $L''\in\Sigma_i$, and $\alpha'$ is given by $\alpha'(x\cdot y)=\alpha(x)$.

<a id="pdf-1a201b302069-p013-b001"></a>
<!-- pdf-source: page=13; block=1; confidence=0.79 -->
## Consequences of non-uniform conditions

<a id="pdf-1a201b302069-p013-b002"></a>
<!-- pdf-source: page=13; block=2; confidence=0.91 -->
Let $\alpha\in\mathrm{poly}$, $L'\in\Sigma_i$, and $L\in NP(\Sigma_i/\mathrm{poly})$ such that
\[
x\in L\iff(\exists_{|x|}y)(x\cdot y\in L'/\alpha)
\]
\[
\iff(\exists_{|x|}y)(x\cdot y\cdot\alpha(x\cdot y)\in L').
\]
Define $\alpha'$ by $\alpha'(n)=\alpha(n)\cdot\alpha(n+1)\cdots\alpha(n+p'(n))$ for some suitable polynomial $p'(n)$, and let
\[
L''=\{x\cdot(z_0\cdot z_1\cdots z_{p'(n)})\cdot y:\ |x|=n,\ |z_i|\leq p^*(n),
\ |y|\leq p^*(n),\text{ and }x\cdot y\cdot z_{|x\cdot y|}\in L'\}.
\]
Clearly, $\alpha'\in\mathrm{poly}$ and $L''\in\Sigma_i$. Observe that
\[
(\exists_{|x|}y)(x\cdot y\cdot\alpha(x\cdot y)\in L')\iff(\exists_{|x|}y)(x\cdot y\cdot\alpha'(x)\in L'')
\]
\[
\iff x\cdot\alpha'(x)\in L''\text{ for some }L''\in NP(\Sigma_i).
\]
Thus $L\in NP(\Sigma_i)/\mathrm{poly}$.

<a id="pdf-1a201b302069-p013-b003"></a>
<!-- pdf-source: page=13; block=3; confidence=0.80 -->
**Theorem.** If every set in $\Pi_1$ has a small generator, then $\Xi=\Pi_1$.

<a id="pdf-1a201b302069-p013-b004"></a>
<!-- pdf-source: page=13; block=4; confidence=0.97 -->
Other open questions raised by this paper are the following.

(1) Is the converse of Theorem 2 true?

(2) Can Theorem 4 be made a full generalization of Mahaney’s result?

(3) Related to (2), obtain consequences of $\mathrm{co\text{-}NP}\leq_{\mathrm{dis}}S$, where $S$ is sparse.

(4) What is the analogue of advice if we consider circuit depth or width instead of size?

(5) **Conjecture:** Every NP-complete set (with respect to $\leq_m$) has a polynomial recursive structure. Note that the Berman–Hartmanis conjecture [3] that all NP-complete sets are isomorphic implies our conjecture.

<a id="pdf-1a201b302069-p013-b005"></a>
<!-- pdf-source: page=13; block=5; confidence=0.94 -->
The author thanks the referees for constructive comments and references, and notes that Theorem 3 also appeared in a cited work.

<a id="pdf-1a201b302069-p014-b001"></a>
<!-- pdf-source: page=14; block=1; confidence=0.98 -->
[1] L. Adleman and K. Manders, “Reducibility, randomness and intractability,” *Proc. 9th ACM STOC* (1977), pp. 151–163.

[2] P. Berman, “Relationship between density and deterministic complexity of NP-complete languages,” *5th Internat. Coll. on Automata, Languages and Programming*, Udine, Lecture Notes in Comput. Sci. 62 (Springer, Berlin, 1978).

[3] L. Berman and J. Hartmanis, “On isomorphisms and density of NP and other complete sets,” *SIAM J. Comput.* 6(2) (1977), 305–322.

[4] S. Fortune, “A note on sparse complete sets,” *SIAM J. Comput.* 8 (1979), 431–433.

[5] Jia-Wei Hong, “On similarity and duality of computation,” *21st Symp. FOCS* (1980), pp. 348–359.

[6] N. Immerman, “Upper and lower bounds for first order expressibility,” *21st Symp. FOCS* (1980), pp. 74–82.

[7] D.R. Jefferson, *Type reduction and program verification*, CMU Ph.D. Thesis, 1980.

[8] K.M. Karp and R.J. Lipton, “Some connections between non-uniform and uniform complexity classes,” *Proc. 12th Ann. ACM STOC* (1980), pp. 302–309.

[9] R.E. Ladner, N.A. Lynch and A.L. Selman, “A comparison of polynomial time reducibilities,” *Theoret. Comput. Sci.* 1 (1975), 103–123.

[10] T.J. Long, “A note on co-sparse polynomial time Turing complete sets for NP,” *J. Comput. Systems Sci.* (1981), submitted.

[11] S.R. Mahaney, “Sparse complete sets for NP: Solution of a conjecture of Berman and Hartmanis,” *Proc. 21st Ann. Symp. FOCS* (1980), pp. 54–58.

[12] A.R. Meyer and M.S. Paterson, “With what frequency are apparently intractable problems difficult,” MIT Tech. Memo. 126, 1979; *Theoret. Comput. Sci.*, to appear.

[13] L.J. Stockmeyer, “The polynomial-time hierarchy,” *Theoret. Comput. Sci.* 3 (1977), 1–22.

[14] E. Ukkonen, “Two results on polynomial-time Turing reductions to sparse sets,” *SIAM J. Comput.*, to appear.

[15] Y. Yesha, “On certain polynomial-time truth table reducibilities of complete sets to sparse sets,” Tech. Rept. 152/81, Department of Computer Science, Univ. of Toronto, Canada, 1981.
