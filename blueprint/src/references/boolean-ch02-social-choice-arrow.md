<!-- generated-by: proofmatch Codex repair -->
<!-- source-pdf-sha256: 352ab7ff3113b27350fd645bdd03eb022164cc878f8ab7f025811981643322ba -->

<a id="pdf-352ab7ff3113-p001-b001"></a>
<!-- pdf-source: page=1; block=1; confidence=1.00 -->
# Chapter 2. Basic concepts and social choice

<a id="pdf-352ab7ff3113-p001-b002"></a>
<!-- pdf-source: page=1; block=2; confidence=0.99 -->
This chapter introduces influences, noise stability, and related concepts, motivated through social choice, and concludes with Kalai’s Fourier-based proof of Arrow’s Theorem.

<a id="pdf-352ab7ff3113-p001-b003"></a>
<!-- pdf-source: page=1; block=3; confidence=1.00 -->
## 2.1. Social choice functions

<a id="pdf-352ab7ff3113-p001-b004"></a>
<!-- pdf-source: page=1; block=4; confidence=0.99 -->
A Boolean function $f:\{-1,1\}^n\to\{-1,1\}$ can be viewed as a voting rule for an election with two candidates and $n$ voters. The majority function is the familiar example.

<a id="pdf-352ab7ff3113-p001-b005"></a>
<!-- pdf-source: page=1; block=5; confidence=0.99 -->
For odd $n$, the majority function $\operatorname{Maj}_n:\{-1,1\}^n\to\{-1,1\}$ is defined by
\[
\operatorname{Maj}_n(x)=\operatorname{sgn}(x_1+\cdots+x_n).
\]
Occasionally, for even $n$, a function is called a majority function if $f(x)$ equals the sign of $x_1+\cdots+x_n$ whenever this number is nonzero.

<a id="pdf-352ab7ff3113-p002-b001"></a>
<!-- pdf-source: page=2; block=1; confidence=0.98 -->
The Boolean AND and OR functions correspond to voting rules in which a candidate is always elected unless all voters are unanimously opposed. The convention is that $-1$ represents True and $1$ represents False.

<a id="pdf-352ab7ff3113-p002-b002"></a>
<!-- pdf-source: page=2; block=2; confidence=0.99 -->
The functions $\operatorname{AND}_n,\operatorname{OR}_n:\{-1,1\}^n\to\{-1,1\}$ are defined by
\[
\operatorname{AND}_n(x)=\begin{cases}-1&x=(-1,\ldots,-1),\\1&\text{otherwise},\end{cases}
\quad
\operatorname{OR}_n(x)=\begin{cases}1&x=(1,\ldots,1),\\-1&\text{otherwise}.
\end{cases}
\]
The $i$th dictator is $\chi_i(x)=x_i$. A function $f:\{-1,1\}^n\to\{-1,1\}$ is a $k$-junta for $k\in\mathbb N$ if it depends on at most $k$ input coordinates; i.e., $f(x)=g(x_{i_1},\ldots,x_{i_k})$ for some $g:\{-1,1\}^k\to\{-1,1\}$ and $i_1,\ldots,i_k\in[n]$. Informally, we say that $f$ is a “junta” if it depends on only a “constant” number of coordinates.

<a id="pdf-352ab7ff3113-p002-b003"></a>
<!-- pdf-source: page=2; block=3; confidence=0.99 -->
There are $2n+2$ one-juntas: the $n$ dictators, their $n$ negations, and the two constant functions.

<a id="pdf-352ab7ff3113-p002-b004"></a>
<!-- pdf-source: page=2; block=4; confidence=0.93 -->
A weighted majority, or linear threshold function, is a function $f:\{-1,1\}^n\to\{-1,1\}$ of the form
\[
f(x)=\operatorname{sgn}(a_0+a_1x_1+\cdots+a_nx_n)
\]
for real coefficients $a_0,\ldots,a_n$. Majority, AND, OR, dictators, and constants are all linear threshold functions.

The depth-$d$ recursive majority $\operatorname{Maj}_n^{\otimes d}$ is defined on $n^d$ bits by $\operatorname{Maj}_n^{\otimes1}=\operatorname{Maj}_n$ and
\[
\operatorname{Maj}_n^{\otimes d}(x^{(1)},\ldots,x^{(n)})
=\operatorname{Maj}_n\bigl(\operatorname{Maj}_n^{\otimes(d-1)}(x^{(1)}),\ldots,\operatorname{Maj}_n^{\otimes(d-1)}(x^{(n)})\bigr).
\]

<a id="pdf-352ab7ff3113-p003-b001"></a>
<!-- pdf-source: page=3; block=1; confidence=0.98 -->
For width $w$ and size $s$, the tribes function is
\[
\operatorname{Tribes}_{w,s}(x^{(1)},\ldots,x^{(s)})
=\operatorname{OR}_s\bigl(\operatorname{AND}_w(x^{(1)}),\ldots,\operatorname{AND}_w(x^{(s)})\bigr),
\]
where each $x^{(i)}\in\{-1,1\}^w$.

<a id="pdf-352ab7ff3113-p003-b002"></a>
<!-- pdf-source: page=3; block=2; confidence=0.98 -->
A function $f:\{-1,1\}^n\to\{-1,1\}$ is:

- monotone if $f(x)\le f(y)$ whenever $x\le y$ coordinatewise;
- odd if $f(-x)=-f(x)$;
- unanimous if $f(1,\ldots,1)=1$ and $f(-1,\ldots,-1)=-1$;
- symmetric if $f(x^\pi)=f(x)$ for every permutation $\pi\in S_n$; equivalently, it depends only on the number of $1$’s.

<a id="pdf-352ab7ff3113-p003-b003"></a>
<!-- pdf-source: page=3; block=3; confidence=0.98 -->
Majority for odd $n$ has all four properties and, by May’s Theorem, is the only monotone, odd, symmetric function. Dictators and recursive majorities have the first three properties. AND and OR are monotone, unanimous, and symmetric but not odd. Tribes is monotone and unanimous but not symmetric.

<a id="pdf-352ab7ff3113-p003-b004"></a>
<!-- pdf-source: page=3; block=4; confidence=0.98 -->
A function is transitive-symmetric if, for every $i,i'\in[n]$, there is a permutation $\pi\in S_n$ taking $i$ to $i'$ such that $f(x^\pi)=f(x)$ for all $x$. Thus any two coordinates are equivalent.

<a id="pdf-352ab7ff3113-p003-b005"></a>
<!-- pdf-source: page=3; block=5; confidence=0.99 -->
The impartial culture assumption says that voters’ preferences are independent and uniformly random. It is a useful comparison model despite being somewhat unrealistic.

<a id="pdf-352ab7ff3113-p004-b001"></a>
<!-- pdf-source: page=4; block=1; confidence=1.00 -->
## 2.2. Influences and derivatives

<a id="pdf-352ab7ff3113-p004-b002"></a>
<!-- pdf-source: page=4; block=2; confidence=0.99 -->
Coordinate $i$ is pivotal for $f$ on input $x$ if $f(x)\ne f(x\oplus i)$, where $x\oplus i$ denotes $x$ with its $i$th bit flipped. Its influence is
\[
\operatorname{Inf}_i[f]=\Pr_{x\sim\{-1,1\}^n}[f(x)\ne f(x\oplus i)].
\]

<a id="pdf-352ab7ff3113-p004-b003"></a>
<!-- pdf-source: page=4; block=3; confidence=0.99 -->
For $f:\{-1,1\}^n\to\{-1,1\}$, $\operatorname{Inf}_i[f]$ equals the fraction of dimension-$i$ edges of the Hamming cube that are boundary edges, i.e. edges $(x,x\oplus i)$ with $f(x)\ne f(x\oplus i)$.

<a id="pdf-352ab7ff3113-p004-b004"></a>
<!-- pdf-source: page=4; block=4; confidence=0.96 -->
For dictator $\chi_i$, coordinate $i$ is pivotal everywhere, so $\operatorname{Inf}_i[\chi_i]=1$, while $\operatorname{Inf}_j[\chi_i]=0$ for $j\ne i$. The same holds for negated dictators. Constants have all influences $0$. Coordinate $1$ of $\operatorname{OR}_n$ is pivotal on exactly two inputs, so $\operatorname{Inf}_1[\operatorname{OR}_n]=2^{1-n}$, and similarly for every coordinate. For $\operatorname{AND}_n$, each influence is also $2^{1-n}$.

<a id="pdf-352ab7ff3113-p005-b001"></a>
<!-- pdf-source: page=5; block=1; confidence=0.98 -->
For $\operatorname{Maj}_3$, there are two boundary edges in each dimension out of four, hence $\operatorname{Inf}_i[\operatorname{Maj}_3]=1/2$. For odd $n$, $\operatorname{Inf}_i[\operatorname{Maj}_n]$ is the probability that among the other $n-1$ bits exactly half are $1$, asymptotically $\sqrt{2/\pi n}$.

<a id="pdf-352ab7ff3113-p005-b002"></a>
<!-- pdf-source: page=5; block=2; confidence=0.98 -->
For $f:\{-1,1\}^n\to\mathbb R$, the discrete derivative is
\[
D_i f(x)=\frac{f(x_{i\to1})-f(x_{i\to-1})}{2}.
\]
It does not depend on $x_i$, and $D_i$ is linear. If $f$ is Boolean-valued, then $D_i f(x)=0$ when $i$ is not pivotal and $D_i f(x)=\pm1$ when it is; therefore $(D_i f(x))^2$ is the pivotality indicator.

<a id="pdf-352ab7ff3113-p005-b003"></a>
<!-- pdf-source: page=5; block=3; confidence=0.99 -->
For real-valued $f$, define
\[
\operatorname{Inf}_i[f]=\mathbb E[(D_i f(x))^2].
\]
Coordinate $i$ is relevant if and only if $\operatorname{Inf}_i[f]>0$, equivalently if changing coordinate $i$ changes $f$ for some input.

<a id="pdf-352ab7ff3113-p005-b004"></a>
<!-- pdf-source: page=5; block=4; confidence=0.99 -->
If $f(x)=\sum_{S\subseteq[n]}\widehat f(S)\chi_S(x)$, then
\[
D_i f(x)=\sum_{S\ni i}\widehat f(S)\chi_{S\setminus\{i\}}(x).
\]
Proof: apply linearity to each monomial; $D_i\chi_S=\chi_{S\setminus\{i\}}$ if $i\in S$, and $0$ otherwise.

<a id="pdf-352ab7ff3113-p006-b001"></a>
<!-- pdf-source: page=6; block=1; confidence=0.98 -->
For $f:\{-1,1\}^n\to\mathbb R$ and $i\in[n]$,
\[
\operatorname{Inf}_i[f]=\sum_{S\ni i}\widehat f(S)^2.
\]
Thus influence is the total Fourier weight on sets containing $i$. For monotone Boolean $f$, influence equals the degree-one coefficient $\widehat f(\{i\})$, denoted $\widehat f(i)$.

<a id="pdf-352ab7ff3113-p006-b002"></a>
<!-- pdf-source: page=6; block=2; confidence=0.99 -->
If $f:\{-1,1\}^n\to\{-1,1\}$ is monotone, then
\[
\operatorname{Inf}_i[f]=\widehat f(i).
\]
Proof: monotonicity makes $D_i f(x)$ the $0$–$1$ pivotality indicator, so $\operatorname{Inf}_i[f]=\mathbb E[D_i f]$; Proposition 2.19 identifies this expectation with $\widehat f(i)$.

<a id="pdf-352ab7ff3113-p006-b003"></a>
<!-- pdf-source: page=6; block=3; confidence=0.98 -->
If $f:\{-1,1\}^n\to\{-1,1\}$ is transitive-symmetric and monotone, then $\operatorname{Inf}_i[f]\le1/\sqrt n$ for every $i$. Proof: transitive symmetry gives $\widehat f(i)=\widehat f(i')$ for all $i,i'\in[n]$. By Proposition 2.21, $\operatorname{Inf}_i[f]=\widehat f(i)$. Parseval gives
\[
1=\sum_S\widehat f(S)^2\ge\sum_{i=1}^n\widehat f(i)^2=n\widehat f(1)^2,
\]
hence $\widehat f(1)\le1/\sqrt n$.

<a id="pdf-352ab7ff3113-p006-b004"></a>
<!-- pdf-source: page=6; block=4; confidence=0.99 -->
The expectation operator is
\[
E_i f(x)=\mathbb E_{x_i}[f(x_1,\ldots,x_{i-1},x_i,x_{i+1},\ldots,x_n)].
\]
It isolates the part of $f$ independent of coordinate $i$.

<a id="pdf-352ab7ff3113-p007-b001"></a>
<!-- pdf-source: page=7; block=1; confidence=0.98 -->
For $f:\{-1,1\}^n\to\mathbb R$,
\[
E_i f(x)=\sum_{S\not\ni i}\widehat f(S)\chi_S(x),
\qquad
f(x)=E_i f(x)+x_iD_i f(x).
\]
Neither term on the right depends on $x_i$. This decomposition is useful for induction on $n$.

<a id="pdf-352ab7ff3113-p007-b002"></a>
<!-- pdf-source: page=7; block=2; confidence=0.99 -->
The coordinate Laplacian is $L_i f=f-E_i f$. The book notes that other sources may use the negated convention.

<a id="pdf-352ab7ff3113-p007-b003"></a>
<!-- pdf-source: page=7; block=3; confidence=0.96 -->
For $f:\{-1,1\}^n\to\mathbb R$,
\[
L_i f(x)=\frac{f(x)-f(x\oplus i)}2=x_iD_i f(x),
\]
\[
L_i f=\sum_{S\ni i}\widehat f(S)\chi_S,
\qquad
\langle f,L_i f\rangle=\langle L_i f,L_i f\rangle=\operatorname{Inf}_i[f].
\]

<a id="pdf-352ab7ff3113-p007-b004"></a>
<!-- pdf-source: page=7; block=4; confidence=1.00 -->
## 2.3. Total influence

<a id="pdf-352ab7ff3113-p007-b005"></a>
<!-- pdf-source: page=7; block=5; confidence=1.00 -->
The total influence is
\[
I[f]=\sum_{i=1}^n\operatorname{Inf}_i[f].
\]

<a id="pdf-352ab7ff3113-p007-b006"></a>
<!-- pdf-source: page=7; block=6; confidence=0.99 -->
For Boolean-valued $f$, $I[f]=\mathbb E_x[\operatorname{sens}f(x)]$, where sensitivity is the number of pivotal coordinates at $x$.

<a id="pdf-352ab7ff3113-p008-b001"></a>
<!-- pdf-source: page=8; block=1; confidence=0.99 -->
\[
I[f]=\sum_i\Pr[f(x)\ne f(x\oplus i)]
=\mathbb E_x\left[\sum_i1_{f(x)\ne f(x\oplus i)}\right]
=\mathbb E_x[\operatorname{sens}f(x)].
\]

<a id="pdf-352ab7ff3113-p008-b002"></a>
<!-- pdf-source: page=8; block=2; confidence=0.99 -->
The fraction of Hamming-cube edges that are boundary edges for Boolean $f$ is $I[f]/n$.

<a id="pdf-352ab7ff3113-p008-b003"></a>
<!-- pdf-source: page=8; block=3; confidence=0.98 -->
For Boolean functions, $0\le I[f]\le n$. Constants have total influence $0$, parity and negated parity have total influence $n$, dictators have total influence $1$, AND and OR have total influence $n2^{1-n}$, and majority has total influence asymptotic to $\sqrt{2n/\pi}$.

<a id="pdf-352ab7ff3113-p008-b004"></a>
<!-- pdf-source: page=8; block=4; confidence=0.99 -->
For monotone Boolean $f$,
\[
I[f]=\sum_{i=1}^n\widehat f(i).
\]

<a id="pdf-352ab7ff3113-p008-b005"></a>
<!-- pdf-source: page=8; block=5; confidence=0.98 -->
For a monotone voting rule $f$ and $w$ equal to the number of votes agreeing with the outcome,
\[
\mathbb E[w]=\frac n2+\frac12\sum_{i=1}^n\widehat f(i).
\]
Proof: $\sum_i\widehat f(i)=\mathbb E[f(x)(x_1+\cdots+x_n)]$. The sum of votes equals the difference between votes for the two candidates; multiplying by $f(x)$ gives $2w-n$.

<a id="pdf-352ab7ff3113-p009-b001"></a>
<!-- pdf-source: page=9; block=1; confidence=0.99 -->
The unique maximizers of $\sum_{i=1}^n\widehat f(i)$ among all $f:\{-1,1\}^n\to\{-1,1\}$ are the majority functions. In particular,
\[
\mathbf I[f]\le \mathbf I[\operatorname{Maj}_n]=\sqrt{\frac{2}{\pi}}\sqrt n+O(n^{-1/2})
\]
for all monotone $f$.

<a id="pdf-352ab7ff3113-p009-b002"></a>
<!-- pdf-source: page=9; block=2; confidence=0.98 -->
Using Proposition 2.32’s Fourier identity and $|f(x)|=1$,
\[
\sum_i\widehat f(i)=\mathbb E[f(x)(x_1+\cdots+x_n)]
\le\mathbb E|x_1+\cdots+x_n|.
\]
Equality holds exactly when $f(x)=\operatorname{sgn}(x_1+\cdots+x_n)$ whenever the sum is nonzero. The asymptotic follows from Proposition 2.31 and the majority influence estimate.

<a id="pdf-352ab7ff3113-p009-b003"></a>
<!-- pdf-source: page=9; block=3; confidence=0.98 -->
The discrete gradient is
\[
\nabla f(x)=(D_1f(x),\ldots,D_nf(x)).
\]
For Boolean $f$, $\|\nabla f(x)\|_2^2=\operatorname{sens}f(x)$, and generally
\[
I[f]=\mathbb E[\|\nabla f(x)\|_2^2].
\]
The Laplacian is $L=\sum_iL_i$.

<a id="pdf-352ab7ff3113-p009-b004"></a>
<!-- pdf-source: page=9; block=4; confidence=0.97 -->
The Laplacian satisfies
\[
Lf(x)=\sum_{i=1}^n\frac{f(x)-f(x\oplus i)}2,
\qquad
Lf=\sum_S|S|\widehat f(S)\chi_S,
\qquad
\langle f,Lf\rangle=I[f].
\]

<a id="pdf-352ab7ff3113-p010-b001"></a>
<!-- pdf-source: page=10; block=1; confidence=0.98 -->
For $f:\{-1,1\}^n\to\mathbb R$,
\[
I[f]=\sum_{S\subseteq[n]}|S|\widehat f(S)^2
=\sum_{k=0}^n kW_k[f].
\]
For Boolean $f$, this equals $\mathbb E[|S_f|]$, the expected degree of the spectral sample.

<a id="pdf-352ab7ff3113-p010-b002"></a>
<!-- pdf-source: page=10; block=2; confidence=0.98 -->
For every $f:\{-1,1\}^n\to\mathbb R$,
\[
\operatorname{Var}[f]\le I[f].
\]
This follows by comparing $\operatorname{Var}[f]=\sum_{k>0}W_k[f]$ with Theorem 2.38. Equality holds exactly when Fourier weight is concentrated in degrees $0$ and $1$; for Boolean functions this means $f=\pm1$ or $f=\pm\chi_i$.

<a id="pdf-352ab7ff3113-p010-b003"></a>
<!-- pdf-source: page=10; block=3; confidence=0.96 -->
If $f:\{-1,1\}^n\to\{-1,1\}$ and $\alpha=\min\{\Pr[f=-1],\Pr[f=1]\}$, then
\[
2\alpha\log(1/\alpha)\le I[f].
\]
This expresses that the Hamming cube is a small-set expander.

<a id="pdf-352ab7ff3113-p011-b001"></a>
<!-- pdf-source: page=11; block=1; confidence=1.00 -->
## 2.4. Noise stability

<a id="pdf-352ab7ff3113-p011-b002"></a>
<!-- pdf-source: page=11; block=2; confidence=0.99 -->
For fixed $x\in\{-1,1\}^n$ and $\rho\in[-1,1]$, write $y\sim N_\rho(x)$ when the bits are independent and
\[
y_i=\begin{cases}x_i&\text{with probability }(1+\rho)/2,\\-x_i&\text{with probability }(1-\rho)/2.
\end{cases}
\]
A pair $(x,y)$ is $\rho$-correlated if $x$ is uniform and $y\sim N_\rho(x)$; equivalently $\mathbb E[x_i]=\mathbb E[y_i]=0$ and $\mathbb E[x_iy_i]=\rho$.

For $f:\{-1,1\}^n\to\mathbb R$, define
\[
\operatorname{Stab}_\rho[f]=\mathbb E[f(x)f(y)].
\]

<a id="pdf-352ab7ff3113-p011-b003"></a>
<!-- pdf-source: page=11; block=3; confidence=0.99 -->
For Boolean-valued $f$,
\[
\operatorname{Stab}_\rho[f]=\Pr[f(x)=f(y)]-\Pr[f(x)\ne f(y)]=2\Pr[f(x)=f(y)]-1.
\]

<a id="pdf-352ab7ff3113-p012-b001"></a>
<!-- pdf-source: page=12; block=1; confidence=0.99 -->
For $\delta\in[0,1]$, the noise sensitivity $\operatorname{NS}_\delta[f]$ is the probability that $f(x)\ne f(y)$ when $x$ is uniform and each bit is independently reversed with probability $\delta$. Thus
\[
\operatorname{NS}_\delta[f]=\frac12-\frac12\operatorname{Stab}_{1-2\delta}[f].
\]

<a id="pdf-352ab7ff3113-p012-b002"></a>
<!-- pdf-source: page=12; block=2; confidence=0.99 -->
Constants have stability $1$. Dictators satisfy $\operatorname{Stab}_\rho[\chi_i]=\rho$ and $\operatorname{NS}_\delta[\chi_i]=\delta$. More generally,
\[
\operatorname{Stab}_\rho[\chi_S]=\rho^{|S|},
\]
by independence of the coordinate pairs.

<a id="pdf-352ab7ff3113-p012-b003"></a>
<!-- pdf-source: page=12; block=3; confidence=0.98 -->
For $\rho\in[-1,1]$,
\[
\lim_{n\to\infty,\,n\text{ odd}}\operatorname{Stab}_\rho[\operatorname{Maj}_n]=\frac2\pi\arcsin\rho
=1-\frac2\pi\arccos\rho.
\]
Equivalently, for $\delta\in[0,1]$,
\[
\lim_{n\to\infty}\operatorname{NS}_\delta[\operatorname{Maj}_n]=\frac1\pi\arccos(1-2\delta).
\]
As $\delta\to0$, this is $\sqrt{2\delta/\pi}+O(\delta^{3/2})$.

<a id="pdf-352ab7ff3113-p013-b001"></a>
<!-- pdf-source: page=13; block=1; confidence=0.99 -->
Theorem 2.45 is proved later. The Fourier connection begins with the noise operator.

<a id="pdf-352ab7ff3113-p013-b002"></a>
<!-- pdf-source: page=13; block=2; confidence=0.99 -->
For $\rho\in[-1,1]$, the noise operator is
\[
T_\rho f(x)=\mathbb E_{y\sim N_\rho(x)}[f(y)].
\]

<a id="pdf-352ab7ff3113-p013-b003"></a>
<!-- pdf-source: page=13; block=3; confidence=0.99 -->
If $f=\sum_S\widehat f(S)\chi_S$, then
\[
T_\rho f=\sum_S\rho^{|S|}\widehat f(S)\chi_S
=\sum_{k=0}^n\rho^k f_k.
\]
Proof: by linearity it suffices to check $T_\rho\chi_S=\rho^{|S|}\chi_S$. The bits are independent and $\mathbb E[y_i\mid x]=\rho x_i$.

<a id="pdf-352ab7ff3113-p013-b004"></a>
<!-- pdf-source: page=13; block=4; confidence=0.99 -->
Noise stability is the inner product
\[
\operatorname{Stab}_\rho[f]=\langle f,T_\rho f\rangle.
\]

<a id="pdf-352ab7ff3113-p014-b001"></a>
<!-- pdf-source: page=14; block=1; confidence=0.99 -->
For $f:\{-1,1\}^n\to\mathbb R$,
\[
\operatorname{Stab}_\rho[f]=\sum_S\rho^{|S|}\widehat f(S)^2
=\sum_{k=0}^n\rho^kW_k[f].
\]
For Boolean $f$,
\[
\operatorname{NS}_\delta[f]=\frac12\sum_k(1-(1-2\delta)^k)W_k[f].
\]

<a id="pdf-352ab7ff3113-p014-b002"></a>
<!-- pdf-source: page=14; block=2; confidence=0.99 -->
If $0<\rho<1$ and $f$ is unbiased, then $\operatorname{Stab}_\rho[f]\le\rho$, with equality exactly for $f=\pm\chi_i$. Since $W_0[f]=0$ and $\rho^k\le\rho$ for $k\ge1$, equality requires all Fourier weight to be at degree $1$.

<a id="pdf-352ab7ff3113-p014-b003"></a>
<!-- pdf-source: page=14; block=3; confidence=0.98 -->
Theorem 2.49 gives
\[
\left.\frac d{d\rho}\operatorname{Stab}_\rho[f]\right|_{\rho=0}=W_1[f],
\qquad
\left.\frac d{d\rho}\operatorname{Stab}_\rho[f]\right|_{\rho=1}=I[f].
\]
For Boolean $f$, $\operatorname{NS}_\delta[f]$ is increasing on $[0,1/2]$ and $\left.\frac d{d\delta}\operatorname{NS}_\delta[f]\right|_{\delta=0}=I[f]$.

<a id="pdf-352ab7ff3113-p015-b001"></a>
<!-- pdf-source: page=15; block=1; confidence=0.99 -->
The $\rho$-stable influence is
\[
\operatorname{Inf}^{(\rho)}_i[f]=\operatorname{Stab}_\rho[D_if]
=\sum_{S\ni i}\rho^{|S|-1}\widehat f(S)^2,
\]
with $0^0=1$, and
\[
I^{(\rho)}[f]=\sum_i\operatorname{Inf}^{(\rho)}_i[f].
\]

<a id="pdf-352ab7ff3113-p015-b002"></a>
<!-- pdf-source: page=15; block=2; confidence=0.98 -->
\[
I^{(\rho)}[f]=\frac d{d\rho}\operatorname{Stab}_\rho[f]
=\sum_{k\ge1}k\rho^{k-1}W_k[f].
\]
As $\rho$ increases from $0$ to $1$, stable influence increases from $\widehat f(i)^2$ to ordinary influence.

<a id="pdf-352ab7ff3113-p015-b003"></a>
<!-- pdf-source: page=15; block=3; confidence=0.96 -->
If $\operatorname{Var}[f]\le1$, $0<\delta,\varepsilon\le1$, and
\[
J=\{i:\operatorname{Inf}^{(1-\delta)}_i[f]\ge\varepsilon^2\},
\]
then $|J|\le1/(\delta\varepsilon^2)$. Proof: $|J|\varepsilon^2\le I^{(1-\delta)}[f]$; compare Fact 2.53 termwise with $\operatorname{Var}[f]=\sum_{k>0}W_k[f]$ and use $(1-\delta)^k\le1/\delta$.

<a id="pdf-352ab7ff3113-p015-b004"></a>
<!-- pdf-source: page=15; block=4; confidence=1.00 -->
## 2.5. Highlight: Arrow’s Theorem

<a id="pdf-352ab7ff3113-p015-b005"></a>
<!-- pdf-source: page=15; block=5; confidence=0.99 -->
With two candidates, majority has desirable properties. With three or more candidates, voters’ rankings must be aggregated across pairwise elections, and Condorcet cycles can arise.

<a id="pdf-352ab7ff3113-p016-b001"></a>
<!-- pdf-source: page=16; block=1; confidence=0.98 -->
For candidates $a,b,c$, let $x,y,z\in\{-1,1\}^n$ encode the pairwise elections $a$ versus $b$, $b$ versus $c$, and $c$ versus $a$. Each voter’s ranking gives one of the six triples satisfying the not-all-equal predicate $\operatorname{NAE}_3$.

<a id="pdf-352ab7ff3113-p016-b002"></a>
<!-- pdf-source: page=16; block=2; confidence=0.99 -->
In a Condorcet election using $f:\{-1,1\}^n\to\{-1,1\}$, a candidate is a Condorcet winner if it wins every pairwise election in which it participates.

<a id="pdf-352ab7ff3113-p016-b003"></a>
<!-- pdf-source: page=16; block=3; confidence=0.98 -->
A Condorcet winner need not exist: the societal outcome can be a cycle in which $a$ beats $b$, $b$ beats $c$, and $c$ beats $a$. This occurs when $(f(x),f(y),f(z))$ is one of the two all-equal triples.

<a id="pdf-352ab7ff3113-p016-b004"></a>
<!-- pdf-source: page=16; block=4; confidence=0.99 -->
Suppose $f:\{-1,1\}^n\to\{-1,1\}$ is unanimous and used in a three-candidate Condorcet election. If there is always a Condorcet winner, then $f$ is a dictatorship.

<a id="pdf-352ab7ff3113-p017-b001"></a>
<!-- pdf-source: page=17; block=1; confidence=0.98 -->
Under the impartial culture assumption, for a three-candidate Condorcet election using $f$,
\[
\Pr[\exists\text{ Condorcet winner}]=\frac34-\frac34\operatorname{Stab}_{-1/3}[f].
\]

<a id="pdf-352ab7ff3113-p017-b002"></a>
<!-- pdf-source: page=17; block=2; confidence=0.99 -->
The six possible voter triples are exactly the inputs satisfying $\operatorname{NAE}_3$. A Condorcet winner exists iff $\operatorname{NAE}_3(f(x),f(y),f(z))=1$. Its multilinear expansion is
\[
\operatorname{NAE}_3(w_1,w_2,w_3)=\frac34-\frac14w_1w_2-\frac14w_1w_3-\frac14w_2w_3.
\]
For the jointly distributed strings, the coordinate pairs are independent and have correlation $-1/3$, so each pairwise expectation equals $\operatorname{Stab}_{-1/3}[f]$. Substitution gives the formula.

<a id="pdf-352ab7ff3113-p017-b003"></a>
<!-- pdf-source: page=17; block=3; confidence=0.99 -->
If a Condorcet winner always exists, Theorem 2.56 gives
\[
1=\frac34-\frac34\operatorname{Stab}_{-1/3}[f]
=\frac34-\frac34\sum_{k=0}^{\infty}(-1/3)^kW^k[f].
\]
Since $(-1/3)^k\ge-1/3$ for all $k$, equality can only occur if all of $f$'s Fourier weight is on degree $1$; i.e., $W^1[f]=1$. By Exercise 1.19(a) this implies that $f$ is either a dictator or a negated-dictator. Since $f$ is unanimous, it must in fact be a dictator.

<a id="pdf-352ab7ff3113-p018-b001"></a>
<!-- pdf-source: page=18; block=1; confidence=0.99 -->
In a 3-candidate Condorcet election using $\operatorname{Maj}_n$, the probability of a Condorcet winner tends to
\[
\frac{3}{2\pi}\arccos(-1/3)\approx91.2\%
\]
as $n\to\infty$.

<a id="pdf-352ab7ff3113-p018-b002"></a>
<!-- pdf-source: page=18; block=2; confidence=0.94 -->
If all degree-one Fourier coefficients $\widehat f(i)$ are equal, then the probability of a Condorcet winner is at most
\[
\frac79+\frac4{9\pi}+o(1)\approx91.9\%.
\]

<a id="pdf-352ab7ff3113-p018-b003"></a>
<!-- pdf-source: page=18; block=3; confidence=0.96 -->
If $f:\{-1,1\}^n\to\{-1,1\}$ has all $\widehat f(i)$ equal, then
\[
W_1[f]\le\frac2\pi+o(1).
\]

<a id="pdf-352ab7ff3113-p018-b004"></a>
<!-- pdf-source: page=18; block=4; confidence=0.94 -->
For any $f:\{-1,1\}^n\to\{-1,1\}$, the probability of a Condorcet winner is at most
\[
\frac79+\frac49W_1[f].
\]

<a id="pdf-352ab7ff3113-p018-b005"></a>
<!-- pdf-source: page=18; block=5; confidence=0.91 -->
Expand $\operatorname{Stab}_{1/3}[f]=\sum_k(1/3)^kW_k[f]$ in Theorem 2.56, group the even and odd terms, and use $W_0[f],W_2[f],\ldots\ge0$ to obtain the bound $\frac79+\frac49W_1[f]$.

<a id="pdf-352ab7ff3113-p018-b006"></a>
<!-- pdf-source: page=18; block=6; confidence=0.96 -->
If the probability of a Condorcet winner is $1-\varepsilon^2$, then $f$ is $O(\varepsilon^2)$-close to $\pm\chi_i$ for some $i$. Proof: Corollary 2.59 gives $W_1[f]\ge1-\frac92\varepsilon^2$; apply the FKN Theorem.

<a id="pdf-352ab7ff3113-p019-b001"></a>
<!-- pdf-source: page=19; block=1; confidence=0.99 -->
If $f:\{-1,1\}^n\to\{-1,1\}$ satisfies $W_1[f]\ge1-\delta$, then $f$ is $O(\delta)$-close to $\pm\chi_i$ for some $i$.

<a id="pdf-352ab7ff3113-p019-b002"></a>
<!-- pdf-source: page=19; block=2; confidence=1.00 -->
## 2.6. Exercises and notes

<a id="pdf-352ab7ff3113-p019-b003"></a>
<!-- pdf-source: page=19; block=3; confidence=0.00 -->


<a id="pdf-352ab7ff3113-p020-b001"></a>
<!-- pdf-source: page=20; block=1; confidence=0.00 -->


<a id="pdf-352ab7ff3113-p021-b001"></a>
<!-- pdf-source: page=21; block=1; confidence=0.00 -->


<a id="pdf-352ab7ff3113-p022-b001"></a>
<!-- pdf-source: page=22; block=1; confidence=0.00 -->


<a id="pdf-352ab7ff3113-p023-b001"></a>
<!-- pdf-source: page=23; block=1; confidence=0.00 -->


<a id="pdf-352ab7ff3113-p024-b001"></a>
<!-- pdf-source: page=24; block=1; confidence=0.00 -->


<a id="pdf-352ab7ff3113-p025-b001"></a>
<!-- pdf-source: page=25; block=1; confidence=0.00 -->


<a id="pdf-352ab7ff3113-p026-b001"></a>
<!-- pdf-source: page=26; block=1; confidence=0.97 -->
The notes discuss the history of influence (Penrose, Banzhaf, Coleman), edge-isoperimetry and total influence, the Poincaré inequality, noise stability and the noise operator, Kalai’s Fourier proof of Arrow’s Theorem, FKN, polarizations, Hamming-cube embeddings, Khintchine–Kahane, and correlation distillation, with the cited references preserved in the source.
