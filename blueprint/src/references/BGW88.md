<!-- generated-by: proofmatch Claude repair -->
<!-- source-pdf-sha256: b3f55f2a43328aca91e075d51ea095aec08ec5ef522814d751e6192376c9e8a9 -->

<a id="pdf-b3f55f2a4332-p001-b001"></a>
<!-- pdf-source: page=1; block=1; confidence=0.99 -->
# Completeness Theorems for Non-Cryptographic Fault-Tolerant Distributed Computation

*(Extended Abstract)*

<a id="pdf-b3f55f2a4332-p001-b002"></a>
<!-- pdf-source: page=1; block=2; confidence=0.98 -->
The paper claims efficient computation of every function by a complete network of n processors: with no faults, privacy holds against coalitions of size t<n/2; with Byzantine faults, coalitions of size t<n/3 cannot disrupt computation or gain extra information. It asserts both thresholds are tight.

<a id="pdf-b3f55f2a4332-p001-b003"></a>
<!-- pdf-source: page=1; block=3; confidence=1.00 -->
## Introduction

<a id="pdf-b3f55f2a4332-p001-b004"></a>
<!-- pdf-source: page=1; block=4; confidence=0.94 -->
The introduction contrasts cryptographic computation, which assumes computationally bounded processors and one-way functions, with the non-cryptographic model, which imposes no computational bound and uses a stronger, information-theoretic notion of privacy. Secure pairwise channels are assumed. Prior cryptographic completeness results motivate the comparison; the paper studies the capabilities and limits of the non-cryptographic model.

<a id="pdf-b3f55f2a4332-p002-b001"></a>
<!-- pdf-source: page=2; block=1; confidence=0.99 -->
For two players with secure channels, computing OR privately is possible in the information-theoretic setting, while the stated lower bounds distinguish the Byzantine thresholds: $t<n/2$ cryptographically versus $t<n/3$ without computational assumptions. The authors’ constructions use generalized BCH codes and require polynomial player work; they also describe arithmetic simulation over large finite fields and related applications.

<a id="pdf-b3f55f2a4332-p002-b002"></a>
<!-- pdf-source: page=2; block=2; confidence=1.00 -->
## Definitions and Results

<a id="pdf-b3f55f2a4332-p002-b003"></a>
<!-- pdf-source: page=2; block=3; confidence=0.96 -->
**Definition (model).** Computation takes place in a synchronous complete network of n processors with secure pairwise channels. In each round, a processor performs arbitrary local computation, sends a message to each processor, and reads messages addressed to it. Each processor initially holds its input and is required to obtain its corresponding output for a probabilistic function from n inputs to n outputs.

<a id="pdf-b3f55f2a4332-p002-b004"></a>
<!-- pdf-source: page=2; block=4; confidence=0.95 -->
**Definition (protocol, privacy, and resilience).** A protocol specifies one program per player. Gossip faults share information received in order to learn more; Byzantine faults may use different programs, collaborate, and sabotage. A protocol is t-private if every coalition of at most t players learns from its view no more than it could compute from its own private inputs and outputs. It is t-resilient if at most t players cannot affect the correctness of the remaining players’ outputs; the function definition must specify behavior when players omit inputs or are caught cheating.

<a id="pdf-b3f55f2a4332-p002-b005"></a>
<!-- pdf-source: page=2; block=5; confidence=0.96 -->
**Theorem 1.** For every function f and every t<n/2, there exists a t-private probabilistic protocol.

<a id="pdf-b3f55f2a4332-p002-b006"></a>
<!-- pdf-source: page=2; block=6; confidence=0.95 -->
**Theorem 2.** There are functions for which no n/2-private protocol exists.

<a id="pdf-b3f55f2a4332-p002-b007"></a>
<!-- pdf-source: page=2; block=7; confidence=0.88 -->
The paper proceeds to define the model and state results, with generalizations and extensions noted for the full version.

<a id="pdf-b3f55f2a4332-p003-b001"></a>
<!-- pdf-source: page=3; block=1; confidence=0.98 -->
**Theorem 3.** For every probabilistic function and every t<n/3, there exists a protocol that is both t-resilient and t-private.

<a id="pdf-b3f55f2a4332-p003-b002"></a>
<!-- pdf-source: page=3; block=2; confidence=0.98 -->
**Theorem 4.** There are functions for which no n/3-resilient protocol exists.

<a id="pdf-b3f55f2a4332-p003-b003"></a>
<!-- pdf-source: page=3; block=3; confidence=1.00 -->
## Proof of Theorem 1

<a id="pdf-b3f55f2a4332-p003-b004"></a>
<!-- pdf-source: page=3; block=4; confidence=0.98 -->
**Proof of Theorem 1.** Let $P_0,\ldots,P_{n-1}$ be a set of players, and let $n\ge 2t+1$. Let $F$ be the function they wish to compute $t$-privately. Let $E$ be a finite field with $|E|>n$. Without loss of generality, assume all inputs are elements of $E$, that $F$ is a polynomial in the input variables over $E$, and that we are given an arithmetic circuit computing $F$ using $+$, $\times$, and constants from $E$. The computation is divided into three stages: the input stage, where each player enters its input using a secret-sharing procedure; the computation stage, where the players simulate the circuit gate by gate, keeping each computed gate value secret-shared by all players; and the final stage, where the secret shares of the final value are revealed to one or all players.

<a id="pdf-b3f55f2a4332-p003-b005"></a>
<!-- pdf-source: page=3; block=5; confidence=0.97 -->
**Proof step (input sharing).** Choose distinct nonzero α₀,…,αₙ₋₁∈E. A player holding s chooses independent uniform a₁,…,a_t∈E, forms f(x)=s+a₁x+⋯+aₜxᵗ, and sends share sᵢ=f(αᵢ) to Pᵢ. By Shamir sharing, any t shares are independent of s.

<a id="pdf-b3f55f2a4332-p003-b006"></a>
<!-- pdf-source: page=3; block=6; confidence=0.99 -->
**The final stage.** To keep the $t$-privacy condition, the set of messages received by any set of $t$ players is made completely independent of all inputs. Each gate value $s\in E$ is shared using a random polynomial $f(x)$ of degree $t$ with $f(0)=s$. At the end of the computation, the value of $F$ is shared in the same manner. If just one player is to learn the output, all players send their shares to that player, who computes the interpolation polynomial $f(x)$ and uses its free coefficient as the result. There is a one-to-one correspondence between shares and the coefficients of $f(x)$; all coefficients except the free coefficient are uniform random variables independent of the inputs. Thus the shares contain no information about the inputs beyond what follows from $f(0)$.

<a id="pdf-b3f55f2a4332-p003-b007"></a>
<!-- pdf-source: page=3; block=7; confidence=1.00 -->
## The Computation Stage

<a id="pdf-b3f55f2a4332-p003-b008"></a>
<!-- pdf-source: page=3; block=8; confidence=0.99 -->
**Linear operations.** If $a,b\in E$ are shared using the polynomials $f(x),g(x)$, respectively, and $c\in E$ is a constant, then $ca$ and $a+b$ are shared by $cf(x)$ and $f(x)+g(x)$, respectively. Each player can compute the corresponding polynomial value at its point using its local shares, without communication.

<a id="pdf-b3f55f2a4332-p003-b009"></a>
<!-- pdf-source: page=3; block=9; confidence=0.97 -->
**Lemma (Linear Functional).** For t≤n−1, every linear functional F(x₀,…,xₙ₋₁)=a₀x₀+⋯+aₙ₋₁xₙ₋₁, with known coefficients aᵢ and each player holding input xᵢ, can be computed t-privately.

<a id="pdf-b3f55f2a4332-p004-b001"></a>
<!-- pdf-source: page=4; block=1; confidence=0.97 -->
**Corollary (Matrix Multiplication).** Let $A$ be a constant $n\times n$ matrix, and let each $P_i$ have an input variable $x_i$. Let $X=(x_0,\ldots,x_{n-1})$ and define $Y=(y_1,\ldots,y_n)$ by $Y=X\cdot A$. Then for any $t$ with $t\le n-1$, the vector $Y$ can be computed $t$-privately so that the only information given to $P_i$ is the value of $Y_i$, for $i=0,\ldots,n-1}$. Matrix multiplication is just the evaluation of $n$ linear functionals; each can be computed $t$-privately and revealed only to its corresponding player.

In the multiplication step, if $a$ and $b$ are encoded by $f(x)$ and $g(x)$, their product polynomial $h(x)=f(x)g(x)$ has degree $2t$ and free coefficient $ab$. The degree must be reduced to $t$ before further multiplication, and the other coefficients must be randomized.

<a id="pdf-b3f55f2a4332-p004-b002"></a>
<!-- pdf-source: page=4; block=2; confidence=0.75 -->
Let $h(x)=h_0+h_1x+\cdots+h_{2t}x^{2t}$ and let $s_i=h(\alpha_i)=f(\alpha_i)g(\alpha_i)$ for $i=0,\ldots,n-1$. Define the truncation $k(x)=h_0+h_1x+\cdots+h_tx^t$ and $r_i=k(\alpha_i)$ for $i=1,\ldots,n-1$. The claimed linear transformation takes the vector of evaluations of $h$ to that of $k$ using a fixed matrix.

<a id="pdf-b3f55f2a4332-p004-b003"></a>
<!-- pdf-source: page=4; block=3; confidence=0.99 -->
Let $H=(h_0,\ldots,h_t,\ldots,h_{2t},0,\ldots,0)$ and $K=(h_0,\ldots,h_t,0,\ldots,0)$. Let $B=(b_{i,j})$ be the $n\times n$ Vandermonde matrix, where $b_{i,j}=\alpha_i^j$ for $i,j=0,\ldots,n-1$, and let $P$ be the linear projection $P(x_0,\ldots,x_{n-1})=(x_0,\ldots,x_t,0,\ldots,0)$. Then $H\cdot B=S$, $H\cdot P=K$, and $K\cdot B=R$. Since $B$ is nonsingular, $S\cdot(B^{-1}PB)=R$. Thus $A=B^{-1}PB$ is a fixed constant matrix implementing the reduction.

<a id="pdf-b3f55f2a4332-p004-b004"></a>
<!-- pdf-source: page=4; block=4; confidence=0.99 -->
To randomize the coefficients, each player $P_i$ randomly selects a polynomial $q_i(x)$ of degree $2t$ with zero free coefficient and distributes its shares among the players. Use
\[
\tilde h(x)=h(x)+\sum_{i=0}^{n-1}q_i(x).
\]
Then $\tilde h(0)=h(0)$, while the other coefficients are randomized. The players evaluate their shares and apply the truncation procedure using the matrix multiplication lemma, obtaining a randomized polynomial $\tilde k(x)$ of degree $t$ with the same free coefficient.

<a id="pdf-b3f55f2a4332-p004-b005"></a>
<!-- pdf-source: page=4; block=5; confidence=0.72 -->
**Theorem 1.** For every probabilistic function $F$ and $t<n/2$, there exists a $t$-private protocol for computing $F$.

<a id="pdf-b3f55f2a4332-p005-b001"></a>
<!-- pdf-source: page=5; block=1; confidence=0.98 -->
The complexity of computing $F$ $t$-privately is bounded by a polynomial in $n$ times the complexity of computing $F$. If $F$ has an arithmetic circuit of depth $d$, with unbounded fan-in linear operations and bounded fan-in multiplication, then $F$ can be computed $t$-privately in $O(d)$ rounds. If $t=O(n^{1-\epsilon})$ for fixed $\epsilon>0$, players can simulate many steps on their shares before reducing the degree. The examples are: any Boolean function, represented as a multilinear polynomial and evaluated in $O(1)$ rounds (possibly with exponentially long messages); and Boolean majority, which has a polynomial-size, depth-$O(\log n)$ circuit and can be computed in a constant number of rounds with polynomially long messages for the stated range of $t$.

<a id="pdf-b3f55f2a4332-p005-b002"></a>
<!-- pdf-source: page=5; block=2; confidence=0.83 -->
**Theorem 2.** There are functions for which no $n/2$-private protocol exists.

<a id="pdf-b3f55f2a4332-p005-b003"></a>
<!-- pdf-source: page=5; block=3; confidence=0.71 -->
**Proof.** Two players, each holding one input bit, cannot compute OR without revealing some information about one player's bit; the text says this argument generalizes immediately.

<a id="pdf-b3f55f2a4332-p005-b004"></a>
<!-- pdf-source: page=5; block=4; confidence=0.96 -->
Sharing a secret with cheaters

<a id="pdf-b3f55f2a4332-p005-b005"></a>
<!-- pdf-source: page=5; block=5; confidence=0.95 -->
For $n=3t+1$ players, the goal is a sharing scheme such that (A) any set of at most $t$ players has no information about the secret, and (B) the secret is recoverable from all shares even when up to $t$ shares are erroneous or missing.

<a id="pdf-b3f55f2a4332-p005-b006"></a>
<!-- pdf-source: page=5; block=6; confidence=0.87 -->
Let $E$ be a finite field containing a primitive $n$th root of unity $\omega$, with $\omega^n=1$ and $\omega^j\ne1$ for $1\le j<n$. For secret $s\in E$, choose uniformly random $a_1,\ldots,a_t\in E$, set $a_0=s$ and $a_i=0$ for $i>t$, and define $f(x)=a_0+a_1x+\cdots+a_tx^t$. Player $i$ receives $s_i=f(\omega^i)$, for $i=0,\ldots,n-1$. The text asserts these shares are $t$-wise independent and uniformly distributed, giving privacy condition (A).

<a id="pdf-b3f55f2a4332-p005-b007"></a>
<!-- pdf-source: page=5; block=7; confidence=0.97 -->
Let $n=3t+1$, and let $\omega$ be a primitive $n$th root of unity in $E$. Choose a random polynomial $f(x)=a_0+a_1x+\cdots+a_tx^t$ with $a_0=s$, and give player $P_i$ the share $s_i=f(\omega^{-i})$. The inverse-transform formula gives $\sum_{i=0}^{n-1}\omega^{ri}s_i=0$ for $r=1,\ldots,2t$. Thus the share vector is a codeword in the cyclic code generated by $g(x)=\prod_{i=t+1}^{n-1}(x-\omega^{-i})$, identified in the text as a generalized Reed-Miller code. The stated procedure corrects $\frac12\deg g(x)=t$ errors.

<a id="pdf-b3f55f2a4332-p005-b008"></a>
<!-- pdf-source: page=5; block=8; confidence=0.94 -->
Verifying a secret

<a id="pdf-b3f55f2a4332-p005-b009"></a>
<!-- pdf-source: page=5; block=9; confidence=0.91 -->
Before using a dealer's sharing, the players seek to check that their values come from a degree-$t$ secret polynomial without revealing the secret or its shares.

<a id="pdf-b3f55f2a4332-p006-b001"></a>
<!-- pdf-source: page=6; block=1; confidence=0.99 -->
To handle $n=3t+1$, the dealer makes public the values sent to each player who filed a complaint, then repeats the test using new random $\alpha$ values. Each player checks its point and all points that were made public, filing a complaint if an error is found. If more than $t+1$ players have complained, the players decide that the secret is bad and take the default zero polynomial; otherwise, the claim is that with very high probability all good players lie on a polynomial of degree $t$.

<a id="pdf-b3f55f2a4332-p006-b002"></a>
<!-- pdf-source: page=6; block=2; confidence=0.80 -->
**Claim.** With very high probability, all noncomplaining (good) players' shares lie on a degree-$t$ polynomial.

<a id="pdf-b3f55f2a4332-p006-b003"></a>
<!-- pdf-source: page=6; block=3; confidence=0.98 -->
Let $f_0$ be the original polynomial. Let $f_1,\ldots,f_m$, where $m=3n$, be random polynomials of degree $t$ generated by $P$, and have $P$ send player $P_i$ the values $f_j(\omega^i)$ for $j=1,\ldots,m$. Each $P_i$ selects a random $\alpha_i\ne0$ from $E$ and sends it to all the players. After agreement on the set of $\alpha$'s, the dealer broadcasts the polynomials $f^\alpha=\sum_{k=0}^{m}\alpha^k f_k$ to all players. Each player checks that the shares it received satisfy the required equations for all the $\alpha$'s. If $t+1$ or more players file a complaint, the dealer is faulty and the default zero polynomial is used.

<a id="pdf-b3f55f2a4332-p006-b004"></a>
<!-- pdf-source: page=6; block=4; confidence=0.99 -->
**Claim.** Let $T$ be a set of good players that did not complain, and let $f_T^T$ be the interpolation polynomial through the points in $T$ of the original polynomial $f_0$. Then with probability at least $1-m2^n/|E|$, all the polynomials $f_T^T$ are of degree $t$.

<a id="pdf-b3f55f2a4332-p006-b005"></a>
<!-- pdf-source: page=6; block=5; confidence=0.99 -->
If $n\ge5t+1$, the secret-sharing scheme can correct $2t$ errors. If a secret is accepted, at most $t$ good players may have wrong values, and at most $t$ further wrong values may come from bad players, for at most $2t$ errors total. Error correction then uniquely determines the secret. For $n=3t+1$, the verification procedure ensures that all pieces held by good players lie on a polynomial of degree $t$; the text claims the verification polynomials are independent of the secret polynomial, so bad players gain no information.

<a id="pdf-b3f55f2a4332-p006-b006"></a>
<!-- pdf-source: page=6; block=6; confidence=0.95 -->
Absolute verification of a secret

<a id="pdf-b3f55f2a4332-p006-b007"></a>
<!-- pdf-source: page=6; block=7; confidence=0.90 -->
The preceding check has a small nonzero error probability. The next procedure is stated to have no probability of error.

<a id="pdf-b3f55f2a4332-p006-b008"></a>
<!-- pdf-source: page=6; block=8; confidence=0.99 -->
The dealer selects random polynomials $f_0(x),\ldots,f_{n-1}(x)$ such that $s_i=f_i(0)$ for $i=0,\ldots,n-1$, and $\sum_{i=0}^{n-1}\omega^{ri}f_i(x)=0$ for $r=1,\ldots,2t$. Equivalently, the dealer chooses a random polynomial $f(x,y)$ of degree $t$ in each variable, with $f(0,0)=s$, and sends $f_i(x)=f(x,\omega^i)$ to player $P_i$.

<a id="pdf-b3f55f2a4332-p006-b009"></a>
<!-- pdf-source: page=6; block=9; confidence=0.98 -->
The dealer also sends player $P_i$ the polynomial $g_i(y)=f(\omega^i,y)$. At this point each player sends the values $s_{i,j}=f_i(\omega^j)=f(\omega^j,\omega^i)=g_j(\omega^i)$ to each player $P_j$. A player compares incoming values with its own computation and can identify incorrect values. It is clear that no good player will have to correct any value coming from another good player.

<a id="pdf-b3f55f2a4332-p007-b001"></a>
<!-- pdf-source: page=7; block=1; confidence=0.99 -->
**Lemma.** If no correct player has to correct a value given by a correct player, then there is a polynomial of degree $t$ that passes through the interpolation points of all the correct players.

<a id="pdf-b3f55f2a4332-p007-b002"></a>
<!-- pdf-source: page=7; block=2; confidence=0.67 -->
**Proof.** The source labels the interpolation claim as following by simple algebra and omits the details. During verification, players request that the dealer reveal information when their received values or polynomials appear inconsistent. The dealer makes requested information public. Each player then checks public and private information; an inconsistency triggers a request to reveal that player's private information. If at least \(t+1\) players request revelation, the dealer is declared faulty and the default zero polynomial is used. Otherwise, at least \(t+1\) satisfied players determine a unique polynomial consistent with their shares and the information requested during verification. The text concludes that a correct dealer's distributed values lie on the public polynomial; if the dealer is faulty, privacy of that dealer's information need not be protected.

<a id="pdf-b3f55f2a4332-p007-b003"></a>
<!-- pdf-source: page=7; block=3; confidence=0.88 -->
Two additional tools are introduced for the \(n=3t+1\) case; the text says they are unnecessary when \(n\ge 4t+1\): (I) generate and verify a random degree-\(2t\) polynomial with zero constant term; (II) distribute secrets \(a,b,c\) and verify \(c=a\cdot b\).

<a id="pdf-b3f55f2a4332-p007-b004"></a>
<!-- pdf-source: page=7; block=4; confidence=0.99 -->
Each player $P_i$ distributes $t$ random polynomials $g_{i,k}(x)$, $k=1,\ldots,t$, of degree $t$, including the free coefficient. Define $f_i(x)=\sum_{k=1}^{t}x^k g_{i,k}(x)$. The players evaluate the $g_{i,k}$ at their corresponding points. Since $\deg g_{i,k}\le t$, we have $\deg f_i(x)\le2t$ and $f_i(0)=0$. The coefficient vector of the coefficients of $x,x^2,\ldots,x^t$ in $f_i(x)$ is uniformly distributed and independent of the information held by any set of at most $t$ players that does not include $P_i$.

<a id="pdf-b3f55f2a4332-p007-b005"></a>
<!-- pdf-source: page=7; block=5; confidence=0.94 -->
Let $D(x)=A(x)B(x)=c+c_1x+\cdots+c_{2t}x^{2t}$, and let
\[
\begin{aligned}
D_t(x)&=r_{t,0}+r_{t,1}x+\cdots+r_{t,t-1}x^{t-1}+c_{2t}x^t,\\
D_{t-1}(x)&=r_{t-1,0}+\cdots+r_{t-1,t-1}x^{t-1}+[r_{2t-1}-r_{t,t-1}]x^t,\\
&\ \vdots\\
D_1(x)&=r_{1,0}+\cdots+r_{1,t-1}x^{t-1}+[c_t-r_{1,t-1}-r_{t-1,t-2}-\cdots-r_{2t,1}]x^t.
\end{aligned}
\]
Here the $r_{i,j}$ are random elements from $E$. The dealer distributes the $D_i(x)$ and their shares to all players.

<a id="pdf-b3f55f2a4332-p008-b001"></a>
<!-- pdf-source: page=8; block=1; confidence=0.99 -->
After verifying that $A(x)$, $B(x)$, and all the $D_i(x)$ are of degree $t$, define
\[
C(x)=D(x)-\sum_{i=1}^{t}x^iD_i(x).
\]
Then $C(x)$ is a random polynomial of degree $t$ with the only restriction that $C(0)=a\cdot b$.

<a id="pdf-b3f55f2a4332-p008-b002"></a>
<!-- pdf-source: page=8; block=2; confidence=0.93 -->
**Proof of Theorem 3.** The protocol is divided into input, computation, and final stages.

<a id="pdf-b3f55f2a4332-p008-b003"></a>
<!-- pdf-source: page=8; block=3; confidence=0.84 -->
In the input stage, each player secret-shares its input and the protocol verifies that each sharing is a degree-at-most-\(t\) polynomial; this alone does not check whether a Byzantine player's input lies in the function's domain. Domain checks, such as checking a bit input in a \(0\)-\(1\) vote, are deferred to computation. In the final stage, after simulating the circuit, players send output shares to one or all players; because at most \(t\) shares are wrong, error correction recovers the result.

<a id="pdf-b3f55f2a4332-p008-b004"></a>
<!-- pdf-source: page=8; block=4; confidence=0.99 -->
Let $a_i=f(\omega^i)$, $b_i=g(\omega^i)$, and $c_i=h(\omega^i)=a_i b_i$ be the points of $P_i$ on these polynomials. Player $P_i$ distributes $a_i$ using a random polynomial $A_i(x)$, $b_i$ using $B_i(x)$, and $c_i$ using $C_i(x)$, verifying that $A_i(x),B_i(x),C_i(x)$ are all of degree $t$ and that $C_i(0)=A_i(0)B_i(0)$.

<a id="pdf-b3f55f2a4332-p008-b005"></a>
<!-- pdf-source: page=8; block=5; confidence=0.98 -->
The free coefficients of the $A_i(x)$ are a codeword with at most $t$ errors. Since the $A_i(x)$ are properly distributed, they can be used to compute any linear functional; in particular, compute $S_r(x)=\sum_{i=0}^{n-1}\omega^{ri}A_i(x)$ for $r=1,\ldots,2t$. The players reveal their points on these polynomials and recover $s_r=S_r(0)$. If all $A_i(0)$ are correct, then $s_r=0$ for all $r$. Thus the $s_r$ depend only on errors and reveal no information held by good players. The syndrome vector identifies erroneous coordinates, whose values can be corrected. The same procedure checks and corrects $B_i(x)$ and $C_i(x)$.

<a id="pdf-b3f55f2a4332-p008-b006"></a>
<!-- pdf-source: page=8; block=6; confidence=0.87 -->
The source says much of this correction procedure is unnecessary when \(n\ge 4t+1\), since degree-\(2t\) polynomials can then be corrected directly from their points.

<a id="pdf-b3f55f2a4332-p008-b007"></a>
<!-- pdf-source: page=8; block=7; confidence=0.85 -->
**Theorem 3.** For every probabilistic function and every \(t<n/3\), there exists a protocol that is both \(t\)-resilient and \(t\)-private. (The OCR truncates the final phrasing, but these properties are legible.)

<a id="pdf-b3f55f2a4332-p009-b001"></a>
<!-- pdf-source: page=9; block=1; confidence=0.94 -->
**Theorem 4.** There are functions for which no \(n/3\)-resilient protocol exists.

<a id="pdf-b3f55f2a4332-p009-b002"></a>
<!-- pdf-source: page=9; block=2; confidence=0.99 -->
**Proof.** This follows immediately from the lower bound for Byzantine Agreement in this model. Even with broadcast as a primitive, there are functions for three players that cannot be computed resiliently when one player is bad. This generalizes immediately to $n/3$.

<a id="pdf-b3f55f2a4332-p009-b003"></a>
<!-- pdf-source: page=9; block=3; confidence=0.96 -->
The remarks following Theorem 1 also apply to Theorem 3.

<a id="pdf-b3f55f2a4332-p009-b004"></a>
<!-- pdf-source: page=9; block=4; confidence=0.99 -->
Let $F$ be a field. Let $U=F^n$ denote the standard $n$-dimensional vector space over $F$, and $M_n(F)$ the ring of $n\times n$ matrices over $F$. Let $R$ be a random variable with distribution $D$ over $F$. Then $R^k$ (also written $R^*$) denotes $k$ independent draws from $D$. Unless otherwise specified, $F$ is finite and $D$ is the uniform distribution over $F$.

<a id="pdf-b3f55f2a4332-p009-b005"></a>
<!-- pdf-source: page=9; block=5; confidence=0.90 -->
Fix \(n>0\) and a field \(F\). Informally, an \((n,F)\)-network is a complete synchronous network of probabilistic machines \(P_0,\ldots,P_{n-1}\). Each round, each player sends one field element to every player, receives one from every player, and performs arbitrary computation. A round's messages are represented by a matrix in \(M_n(F)\), with rows corresponding to senders and columns to recipients; this models private channels.

<a id="pdf-b3f55f2a4332-p009-b006"></a>
<!-- pdf-source: page=9; block=6; confidence=0.97 -->
Formally, an $T$-round $(n,F)$-network is a set of players $\{P_0,P_1,\ldots,P_{n-1}\}$. Each $P_i$ is a tuple $\langle Q_i,q_i^{(0)},R_i,\delta_i\rangle$, where $Q_i$ is a set of states, $q_i^{(0)}$ the initial state, $R_i$ a random variable over $F$ distributed like $R$, and
\[
\delta_i:[T]\times Q_i\times F^n\times R_i^*\to Q_i\times F^n
\]
is a transition function. A protocol is $\delta=\langle\delta_0,\delta_1,\ldots,\delta_{n-1}\rangle$. A run is a sequence $(M_1,M_2,\ldots,M_T)$ of matrices in $M_n(F)$ describing communication in rounds $1,\ldots,T$. The run is a random variable depending on the initial states and the random draws $\{R_i\}$, with $R_i\sim R$.

<a id="pdf-b3f55f2a4332-p010-b001"></a>
<!-- pdf-source: page=10; block=1; confidence=0.99 -->
A (probabilistic) function is a function $f:F^n\times R^m\to F^n$. Intuitively, a protocol computes $f$ if, for all $v\in F^n$, when player $P_i$ is given $v_i\in F$ before round 1, after round $T$ it knows $u_i$ such that $u=\langle u_0,\ldots,u_{n-1}\rangle$ is distributed exactly like $f(v\times R^m)$. For each player $P_i$, let $I_i,O_i:Q_i\to F$ be its input and output functions.

<a id="pdf-b3f55f2a4332-p010-b002"></a>
<!-- pdf-source: page=10; block=2; confidence=0.86 -->
A coalition may coordinate its actions. For a coalition \(C\subseteq[n]\), its members' protocol functions can be replaced by arbitrary functions of the joint current states, prior messages, and random choices of players in \(C\).

<a id="pdf-b3f55f2a4332-p010-b003"></a>
<!-- pdf-source: page=10; block=3; confidence=0.77 -->
**Definition.** Protocols \(\delta\) and \(\delta'\) look alike when their runs have the same distribution of all players' states for every fixed initial state. A coalition \(C\) is gossip if its modified protocol \(\delta_C\) looks like the original \(\delta\); otherwise it is Byzantine. Gossip behavior preserves the run distribution, while Byzantine behavior permits arbitrary actions.

<a id="pdf-b3f55f2a4332-p010-b004"></a>
<!-- pdf-source: page=10; block=4; confidence=0.82 -->
Privacy asks whether a coalition learns more about the computed function than its own inputs and output components reveal. Correctness requires good players to compute an appropriate function despite bad inputs or behavior.

<a id="pdf-b3f55f2a4332-p010-b005"></a>
<!-- pdf-source: page=10; block=5; confidence=0.98 -->
Let $Q_C=\prod_{i\in C}Q_i$, and let $u_C$ denote the subvector of $u$ containing the coordinates $u_i$ for $i\in C$. A set $C$ is ignorant in a protocol $\delta$ computing $f$ if, for every set of initial states $\langle q_i^{(0)}\rangle$, every protocol $\delta_C$ that looks like $\delta$, and every function $g':Q_C\to A$, there exists a function $g:Q_C\times F^{|C|}\to A$ satisfying
\[
g'(q_C^{(T)})=g\bigl(q_C^{(0)},f(\langle I_i(q_i^{(0)})\rangle)_C\bigr). \tag{*}
\]
A protocol $\delta$ is $t$-private if every coalition $C$ with $|C|\le t$ is ignorant.

<a id="pdf-b3f55f2a4332-p010-b006"></a>
<!-- pdf-source: page=10; block=6; confidence=0.72 -->
With Byzantine faults, bad players may destroy the meaning of the original function on the full input. For each bad set \(B\subseteq[n]\), correctness therefore uses a function \(f_B\) depending only on input coordinates outside \(B\), with default values or agreement given as possible examples.

<a id="pdf-b3f55f2a4332-p010-b007"></a>
<!-- pdf-source: page=10; block=7; confidence=0.96 -->
A coalition $C$ is harmless if for every set of initial states and every protocol $\delta_C$, there is some $B\subseteq C$ such that
\[
\langle O_i(q_i^{(T)})\rangle_{[n]\setminus C}=f_B\bigl(\langle I_i(q_i^{(0)})\rangle_{[n]\setminus B}\bigr)_{[n]\setminus C}.
\]
A protocol is $t$-resilient if every coalition $C$ with $|C|\le t$ is harmless.

<a id="pdf-b3f55f2a4332-p010-b008"></a>
<!-- pdf-source: page=10; block=8; confidence=0.69 -->
For Byzantine coalitions, the indistinguishability condition used in the preliminary ignorance definition is inappropriate. The text proposes replacing the original function \(f\) in (*) by the function \(f_B\) actually computed by the good players for a harmless coalition.

<a id="pdf-b3f55f2a4332-p010-b009"></a>
<!-- pdf-source: page=10; block=9; confidence=0.85 -->
The text concludes that a protocol that is both \(t\)-private and \(l\)-resilient is well-defined under the revised privacy notion.
