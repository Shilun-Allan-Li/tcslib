<!-- generated-by: proofmatch local extraction -->
<!-- source-pdf-sha256: d5b902970e6158d5f4b3fd1c6dd3d6a5e461a2b47427860662ce85739e106ab3 -->
<!-- extractor: pdfminer.six v20260107 -->

<!-- pdf-page: 1 -->
SIAM J. COMPUT.
Vol. 27, No. 4, pp. 1203–1220, August 1998

c(cid:176) 1998 Society for Industrial and Applied Mathematics
015

A CHERNOFF BOUND FOR RANDOM WALKS ON EXPANDER
GRAPHS∗

DAVID GILLMAN†

Abstract. We consider a ﬁnite random walk on a weighted graph G; we show that the fraction of
time spent in a set of vertices A converges to the stationary probability π(A) with error probability
exponentially small in the length of the random walk and the square of the size of the deviation
from π(A). The exponential bound is in terms of the expansion of G and improves previous results
of [D. Aldous, Probab. Engrg. Inform. Sci., 1 (1987), pp. 33–46], [L. Lov´asz and M. Simonovits,
Random Structures Algorithms, 4 (1993), pp. 359–412], [M. Ajtai, J. Koml´os, and E. Szemer´edi,
Deterministic simulation of logspace, in Proc. 19th ACM Symp. on Theory of Computing, 1987].

We show that taking the sample average from one trajectory gives a more eﬃcient estimate of
π(A) than the standard method of generating independent sample points from several trajectories.
Using this more eﬃcient sampling method, we improve the algorithms of Jerrum and Sinclair for
approximating the number of perfect matchings in a dense graph and for approximating the partition
function of a ferromagnetic Ising system, and we give an eﬃcient algorithm to estimate the entropy
of a random walk on an unweighted graph.

Key words. random walk, graph, eigenvalue, expander, large deviations, approximate counting,

matching, Ising system, partition function, Markov source, entropy

AMS subject classiﬁcations. 60F10, 60J10, 62M05, 68Q25, 94A29

PII. S0097539794268765

1. Introduction. Let G be a connected undirected graph with positive weights
on the edges. We consider the random walk on G, which at each time step chooses
an edge leaving the current vertex with probability proportional to the weight on the
edge. The random walk converges to a limiting distribution π on the vertices of G.1
This model is equivalent to a ﬁnite reversible Markov chain.

Let A be a subset of vertices of G. We consider the amount of time tn the
random walk spends in A during the ﬁrst n steps. It is well known that for almost
every trajectory of the random walk, the fraction of time spent in A, tn/n, converges
to the limiting probability of A, π(A) [Do, Theorem 6.1].

We quantify this rate of convergence. We are concerned with the probability
that for a given n-step trajectory of the random walk, tn/n will deviate by some
speciﬁed amount from π(A) (the deviation probability). Theorem 2.1 shows that this
probability decays exponentially in the square of the amount of deviation, as a multiple
n. This bound is of a similar form to that given by Chernoﬀ [Ch] for the case
of 1/
of independent random variables (a very special case of random walk).

√

The exponent in the bound of Theorem 2.1 is proportional to the eigenvalue gap
of the transition matrix of the random walk, which is directly related to the expansion
of G [AM, Ta, Alo, SJ]. The bound also depends on the starting distribution of the
random walk, which may introduce a factor of |G|. In this case O(log |G|) random

∗Received by the editors June 1, 1994; accepted for publication (in revised form) June 17, 1996;
published electronically May 19, 1998. The research and writing of this paper were supported by
NSF grant 9212184-CCR and DARPA contract N00014-92-J-1799.

http://www.siam.org/journals/sicomp/27-4/26876.html
†Iterated Systems, Inc., 3525 Piedmont Road, Building 7, Suite 600, Atlanta, GA 30305 (dgill-

man@iterated.com).

y
c
a
v
i
r
p
-
s
m
r
e
t
/
g
r
o
.
m
a
i
s
.
s
b
u
p
e
/
/
:
s
p
t
t
h
e
e
s

;
t
h
g
i
r
y
p
o
c

r
o

e
s
n
e
c
i
l

M
A
I
S
o
t

t
c
e
j
b
u
s

n
o
i
t
u
b
i
r
t
s
i
d
e
R

.

2
5
.
4
1
2
.
2
5
1
.
6
3
1

o
t

6
2
/
5
0
/
1
1

d
e
d
a
o
l
n
w
o
D

1We are interested in convergence in the following weak sense: let P (k) be the distribution of the

random walk after k steps. Then 1
n

(cid:80)n

k=1

P (k) → π. This holds even when G is bipartite.

1203

 
 
 
 
 
 
 
 
 
 
 
 
 


<!-- pdf-page: 2 -->
1204

DAVID GILLMAN

walk steps suﬃce to get a good estimate of π(A). When the random walk starts close
to the stationary distribution the bound does not depend on |G|.

Theorem 2.1 is the ﬁrst exponential bound on the deviation probability in terms
of a computable quantity (in this case the eigenvalue gap). This result implies bounds
on all higher moments of the fraction of time spent in A, and it quantiﬁes the rate of
convergence to π(A) in each Lp norm, 1 ≤ p < ∞ [Kah]. It also sharpens a theorem of
Ajtai, Koml´os, and Szemer´edi [AKS] (see also [CW] and [IZ]), which showed that the
probability of a deviation of constant size decays exponentially in n. Aldous [Ald87]
bounded the variance of the fraction of time spent in A in terms of the eigenvalue gap.
Lov´asz and Simonovits [LS] gave a similar result for arbitrary measure spaces. Those
results give quadratic bounds on the deviation probability via Chebyshev’s inequality.
Goldreich et al. [G∗] have given a bound on the probability of not hitting A in n steps
which decays exponentially in nπ(A).

Theorem 2.1 applies more generally to estimating the expectation of a nonnegative
function on the vertices of G. π(A) is the expectation of χA, the indicator function of
A, and Theorem 2.1 states that the fraction of time spent in A is a good estimate of
this expectation. We establish the analogous result for estimating the expectation Ef
of an arbitrary nonnegative function f on the vertices of G. In this case the bound
depends on maxx |f (x)| as well as on the eigenvalue gap.

Approximation algorithms. Estimating π(A) (or in some applications, Ef ) is
a fundamental problem for approximation algorithms in which A and G are exponen-
tially large combinatorial sets such as sets of matchings of a graph [JS89]. The basic
strategy is to generate random sample points in G and compute the fraction that are
in A. The standard procedure is to use the rapid mixing property of the random walk
on G to generate a single nearly random sample point from π. The random walk
is repeated to generate the number of independent sample points Chernoﬀ’s bound
requires [DFK, JS89, LS]. We compare this with the alternative procedure analyzed
by Aldous in [Ald87], which was the ﬁrst to generate a nearly random point in G and
then to continue the random walk from that point, sampling every subsequent vertex.
This procedure is commonly used in statistical biology and physics, usually without
rigorous analysis of its reliability; for convenience we will refer to it as “Aldous’s
procedure” (AP).

We show in this paper that AP (sometimes in a modiﬁed form) requires fewer
random walk steps than the standard procedure to ensure the same conﬁdence in the
resulting estimate of π(A). A little intuition here will show why one would expect
this to be the case. Let τ be the “relaxation time” of the random walk, which is the
number of steps required to generate a single random point. The standard procedure
picks up l sample points by taking τ l random walk steps. We may as well assume that
these sample points come from a single long random walk on the graph which visits the
vertices x1, x2, . . .. Then the sample points are xτ , x2τ , . . . , xlτ . Now consider using
AP on the same random walk. The estimate it gives is an average from the (highly
dependent) sample points xτ +1, xτ +2, . . . , xlτ . But this estimate is just an average
of τ diﬀerent estimates, each using the standard procedure with l − 1 samples: for
each ﬁxed i ≤ τ the ith estimate uses the sample points xτ +i, x2τ +i, . . . , x(l−1)τ +i.
It should not hurt each estimate much that it only samples l − 1 points instead of l,
whereas it should help that τ diﬀerent (admittedly dependent) estimates are being
averaged.

Stating the results more quantitatively, we analyze these procedures within the
framework of (β, δ)-approximation algorithms; i.e., algorithms with input parameters



<!-- pdf-page: 3 -->
CHERNOFF BOUND FOR RANDOM WALKS

1205

β and δ that with probability 1 − δ output an approximation of π(A) with relative
error β [KL]. We assume throughout that we can eﬃciently ﬁnd one point s ∈ G from
which to start a random walk.

The main consequence of Theorem 2.1 for (β, δ)-approximation algorithms is that
AP requires O(log(1/π(s)) + log(1/δ)/β2) random walk steps. The ﬁrst term is the
relaxation time. The standard procedure (SP) requires O(log(1/π(s)) log(1/δ)/β2).
The constants in both cases depend on the eigenvalue gap and π(A).

Unfortunately, the dependence on π(A) favors the standard procedure when π(A)
is small (often in practice π(A) is O(1/n)). This is because the bound in Theorem
2.1 is not optimal for small π(A) in comparison with either the Chernoﬀ bound for
independent random variables or the variance bound of Aldous for Markov chains.
For this reason the best procedure when π(A) is small is to use AP with δ replaced
by a constant, say 1/4, to repeat this estimate log(1/δ) times, and to take the median
of the answers. The technique of using the median of several estimates is well known
and was introduced by Jerrum, Valiant, and Vazirani in [JVV]. Our analysis of this
modiﬁed procedure depends on an extension of the variance bound of Aldous.

We present a modiﬁed version of an approximation algorithm, due to Jerrum and
Sinclair, for evaluating the partition function of a ferromagnetic Ising system. Our new
version of the algorithm improves the running time from O(|E|3m7) to O(|E|2m6),
where m is the number of vertices and E is the edge set of the system [JS91]. This
algorithm makes calls to a (β, δ)-approximation routine for Ef for diﬀerent functions
f . Part of the improved running time of the algorithm comes from replacing the
standard sampling procedure by AP. The rest of the improvement comes from the
observation that the errors from the diﬀerent calls to the (β, δ)-approximation routine
are independent and cancel one another out to some extent. Dyer and Frieze used
the same observation in their algorithm for computing the volume of a convex body
in Euclidean n-space [DF].

We are also able to improve an approximation algorithm, due to Jerrum and
Sinclair, for counting the number of perfect matchings in a graph. Suppose the graph
H = (V, E) has 2m vertices. Our new version of the algorithm improves the running
time from O(q3m6|E| log2 m) to O(q2m5|E| log m), where q is an a priori upper bound
on the ratio of the number of matchings with m−1 edges to the number of perfect (m-
edge) matchings [JS89]. Polynomial bounds on q are known for large classes of graphs;
for example, q(m) = m2 for dense bipartite graphs and for regular periodic lattices
[JS89, KRS]. Part of the improved running time of our new version of the algorithm
comes from implementing AP. The algorithm makes calls to a (β, O(1))-approximation
routine for diﬀerent sets A. In addition, the new algorithm introduces a strategy of
selecting only those sets A for which π(A) is not too small. The importance of this
is that the running time of the (β, O(1))-approximation routine depends inversely on
π(A).

Entropy estimation. In the special case where the edges of G are not weighted,
Theorem 2.1 shows that one can compute the entropy of the random walk accurately
from a very short realization of it. We view the random walk on G as an information
source whose alphabet is the vertex set of G. It is convenient to state the result in this
form, although it applies to any labelling of the vertices such that the Markov chain
is uniﬁlar. (A uniﬁlar Markov chain is one in which each state has nonzero transition
probability to at most one state of each label.) If G has constant eigenvalue gap and
bounded degree then a good entropy estimate requires only O(log |G|) steps of the
random walk.

y
c
a
v
i
r
p
-
s
m
r
e
t
/
g
r
o
.
m
a
i
s
.
s
b
u
p
e
/
/
:
s
p
t
t
h
e
e
s

;
t
h
g
i
r
y
p
o
c

r
o

e
s
n
e
c
i
l

M
A
I
S
o
t

t
c
e
j
b
u
s

n
o
i
t
u
b
i
r
t
s
i
d
e
R

.

2
5
.
4
1
2
.
2
5
1
.
6
3
1

o
t

6
2
/
5
0
/
1
1

d
e
d
a
o
l
n
w
o
D

 
 
 
 
 
 
 
 
 
 
 
 
 


<!-- pdf-page: 4 -->
1206

DAVID GILLMAN

This result quantiﬁes the rate of convergence of the classical Shannon–McMillan
asymptotic equipartition property [Ash]. The classical result assumes an ergodic
information source with entropy H. It says, intuitively, that for large n, roughly 2Hn
of the n-bit strings each have probability roughly 2−Hn. For purposes of encoding
n-bit blocks of output from the source into blocks of some ﬁxed shorter length greater
than Hn, we give a bound on the exponent of the error probability. This is the
ﬁrst bound on the error exponent for ﬁxed-length noiseless source coding in terms
of a computable property of the underlying Markov chain. Previous bounds on the
error exponent have been based on divergence and retain an asymptotic ﬂavor. Large
deviation methods for the source coding problem were used in [Nat, An].

Methods. The proof of Theorem 2.1 begins with Theorem 2.2, due to H¨oglund,
which follows the method of Cram´er [Cr] and Chernoﬀ [Ch] of estimating the devia-
tion probability in terms of the moment generating function of the number of visits to
A [H, Theorem 5.5] (see also Nagaev [Nag, Theorem 6]). H¨oglund writes the moment
generating function as an expression involving the largest eigenvalue of a perturbation
of the transition matrix for the random walk. How hard it is to ﬁnd a quantitative
bound for this expression can depend on the transition matrix. Generally, the eigen-
values of a matrix may vary wildly under small perturbations of the matrix [SS, p.
166]. H¨oglund was able to use his method to derive a bound similar to Chernoﬀ’s for
the case of Bernoulli trials (in which the transition matrix has identical rows).

Theorem 2.1 demonstrates the applicability of H¨oglund’s approach to random
walks on weighted graphs, where the transition matrix is similar to a symmetric
matrix. We ﬁrst bound the logarithm of the largest eigenvalue of a perturbation of
the transition matrix by estimating its second derivative with respect to a perturbation
parameter r. This bound uses Cauchy’s estimate and the observation that the largest
eigenvalue is an analytic function of r [Ahl, Kat]. The ﬁrst bound leads to a bound
on the probability of deviation in terms of r, and Theorem 2.1 follows by optimizing
over r.

Overview. In section 2 we state and prove our main theorem. At the end of
the section we compare similar recent results due to Kahale [Kah] and Dinwoodie
[Di95a, Di95b]. In section 3 we give a general comparison of sampling procedures.
There we prove an extension of the variance bound of Aldous (Proposition 3.2). In
section 4 we describe an improved version of an approximation algorithm for the
partition function of an Ising system, and we summarize our improvements to an
algorithm for counting perfect matchings in a graph. Finally, in section 5 we discuss
the use of random walks to estimate entropy of an information source generated by a
random walk.

(cid:80)

2. The main theorem. Let G = (V, E) be a connected undirected graph. Let
each edge {x, y} in the edge set E be assigned a positive weight wxy. We deﬁne the
weight wx of the vertex x by the formula wx =

{x,y}∈E wxy.

A random walk on such a weighted graph is equivalent to a time-reversible ﬁnite
Markov chain. The states of the Markov chain are the vertices of the graph. The
Markov chain is deﬁned by its transition matrix P = (pxy); pxy is the probability
(independent of time) of moving to state y after entering state x, given by
(cid:26) wxy
wx
0

if {x, y} ∈ E,
if not.

pxy =

By the classical theory of nonnegative matrices, the eigenvalues of P are 1 = λ1 >



<!-- pdf-page: 5 -->
CHERNOFF BOUND FOR RANDOM WALKS

1207

λ2 ≥ · · · ≥ λ|V | ≥ −1, and λ|V | = −1 if and only if G is bipartite [Se]. The strict
separation of λ1 and λ2 follows from the connectedness of G. Let π denote the unique
y∈V wy for all
left eigenvector with eigenvalue 1. Properly normalized, π(x) = wx/
x ∈ V , and π is a probability distribution. We refer to π as the stationary distribution.
k=0 P kd = π. (When G is not
For all probability distributions d on V , limn→∞
bipartite, we have the stronger property that P nd → π for all d.) Let (cid:15) := 1 − λ2
denote the eigenvalue gap of P . The eigenvalue gap is directly related to the expansion
of G [AM, Ta, Alo, SJ]. In particular, if G is an expander (cid:15) will be large.

(cid:80)n−1

(cid:80)

1
n

Let x0, x1, . . . be the sequence of vertices visited by the random walk on G, where
x0 is chosen according to some distribution q on the vertices. Let A ⊆ V . Let χA
denote the indicator function χA(x) = 1 if x ∈ A, and 0 otherwise. Let tn :=
χA(x1) + · · · + χA(xn), the number of visits to A in n random walk steps.

We introduce some special notation. Let
(x) = q(x)√
, and let Nq = (cid:107) q√
π
π(x)
Logarithms are in base e unless otherwise subscripted.

q√
π

q√
π

denote the vector with entries

(cid:107)2. Let 1 = (11 · · · 1) be the vector of all 1’s.

We now state our main result, a large deviation bound for a random walk on a

weighted graph, in terms of the eigenvalue gap.

Theorem 2.1. Consider the random walk on a weighted graph G = (V, E) with
initial distribution q. Let A ⊆ V . Let tn be the number of visits to A in n steps. For
any γ ≥ 0,

(2.1)

Pr[tn − nπ(A) ≥ γ] ≤ (1 + γ(cid:15)/10n) Nqe−γ2(cid:15)/20n.

Remarks. (i) We may write EπχA for π(A) in Theorem 2.1. As we will see, the
proof of this theorem uses only that χA is a nonnegative function on the vertices of
G such that (cid:107)χA(cid:107)∞ ≤ 1. For an arbitrary nonnegative function f on the vertices of
G, we may substitute f for χA in the deﬁnition of tn. Equation (2.1) becomes

(2.2)

Pr[tn − nEπf ≥ γ] ≤ (1 + γ(cid:15)/10n) Nqe−(γ/(cid:107)f (cid:107)∞)2(cid:15)/20n.

(ii) Applying the theorem to G \ A gives the same bound on Pr[tn−nπ(A) ≤ −γ ].
Before proving Theorem 2.1, we lay the groundwork for our proof with Theorem
2.2, a simpliﬁed version of a result of H¨oglund [H, Theorem 5.5]. This result follows
the strategy of Cram´er [Cr] and Chernoﬀ [Ch], which is to estimate the deviation
probability in terms of the moment generating function m(r) = Eertn, evaluated at
some r > 0. We will see that this strategy reduces the problem of estimating the left-
hand side of (2.1) to a problem of analyzing a perturbation of the transition matrix
P .

Let P (r) = P Er, where Er = diag(erχA ) and r is any complex number (we will
often restrict r to the nonnegative real line). P (r) is equal to P except that for j ∈ A
the jth column vector of P is multiplied by er.

P and P (r) are similar to symmetric matrices. Let M be the (symmetric)
weighted adjacency matrix of G: the ijth entry of M is wij if {i, j} ∈ E and 0
otherwise. Let D = diag(1/wi). Then
√

√

(2.3)

P (r) =

√

√

P =

DS

(cid:112)

D−1, and
(cid:112)

r S(r)

DE−1
√

√

ErD−1 ,

DEr are symmetric. By (2.3) the
where S :=
eigenvalues of P (r) are real for r ≥ 0, and they are equal to the eigenvalues of S(r);

D and S(r) :=

DErM

DM

y
c
a
v
i
r
p
-
s
m
r
e
t
/
g
r
o
.
m
a
i
s
.
s
b
u
p
e
/
/
:
s
p
t
t
h
e
e
s

;
t
h
g
i
r
y
p
o
c

r
o

e
s
n
e
c
i
l

M
A
I
S
o
t

t
c
e
j
b
u
s

n
o
i
t
u
b
i
r
t
s
i
d
e
R

.

2
5
.
4
1
2
.
2
5
1
.
6
3
1

o
t

6
2
/
5
0
/
1
1

d
e
d
a
o
l
n
w
o
D

 
 
 
 
 
 
 
 
 
 
 
 
 


<!-- pdf-page: 6 -->
1208

DAVID GILLMAN

in this case let λ(r) and λ2(r) denote the largest and second largest eigenvalues of
P (r), respectively. Note that P (0) = P , λ(0) = 1 (with left eigenvector πT and right
eigenvector 1), and λ2(0) = λ2. For r ≥ 0, let the eigenvalue gap of P (r) be denoted
by (cid:15)r = λ(r) − λ2(r).

Theorem 2.2. Consider the random walk on a weighted graph G = (V, E) with
initial distribution q. Let A ⊆ V . Let tn be the number of visits to A in n steps. For
any γ ≥ 0 and r ≥ 0,

(2.4)

Pr[tn − nπ(A) ≥ γ] ≤ e−r(nπ(A)+γ) + n log λ(r) (q P (r)n 1)/λ(r)n .

Proof. By Markov’s inequality,

(2.5)

Pr[tn ≥ nπ(A) + γ] = Pr[ertn ≥ er(nπ(A)+γ)]

≤ e−r(nπ(A)+γ)Eqertn ,

where Eq denotes the expectation given that x0 is chosen according to q. This ex-
pectation can be evaluated by summing over all possible trajectories x0, x1, . . . , xn
(where tn is understood to be a function of the trajectory):

(2.6)

Eqertn =

(cid:88)

x0,...,xn

ertnq(x0)

n(cid:89)

i=1

pxi−1xi = q P (r)n 1 .

Combining (2.6) with inequality (2.5) we obtain

(2.7)

Pr[tn ≥ nπ(A) + γ] = e−r(nπ(A)+γ) + n log λ(r) (q P (r)n 1)/λ(r)n.

Here are the reasons that this theorem is useful.
1. For matrices P (r) satisfying (2.3), the fraction (q P (r)n 1)/λ(r)n on the right-
hand side of (2.4) is close to 1. In fact, this fraction turns out to measure how close
the starting distribution q is to the stationary distribution π. We have the following
lemma.

Lemma 2.3. For 0 ≤ r ≤ 1, (q P (r)n 1)/λ(r)n ≤ (1 + r) Nq .
2. The exponent −r(nπ(A) + γ) + n log λ(r) in the right-hand side of (2.4) is
negative for small r because, as we show below, d log λ
|r=0 = π(A), and because
log λ(0) = 0. Our goal then is to bound this exponent away from zero for some r in
order that a meaningful bound on Pr[tn − nπ(A) ≥ γ] will follow from Theorem 2.2.
This is accomplished by Lemma 2.4.

dr

Lemma 2.4. If r is a real number such that 0 ≤ er − 1 ≤ (cid:15)/4, then

log λ(r) ≤ rπ(A) + 5r2/(cid:15) .

Proof of Theorem 2.1. We combine (2.4), Lemma 2.3, and Lemma 2.4 to get

(2.8)

Pr[tn − nπ(A) ≥ γ] ≤ (1 + r) Nq e−n(rγ/n−5r2/(cid:15)) .

The expression rγ/n−5r2/(cid:15) is quadratic in r and is maximized when r = γ(cid:15)/10n ,
which satisﬁes the condition of Lemma 2.4 that er − 1 ≤ (cid:15)/4 (we can assume γ < n,
because otherwise Theorem 2.1 is trivially true). The maximum value is γ2(cid:15)/20n2.
Substituting into (2.8),

Pr[tn − nπ(A) ≥ γ] ≤ (1 + γ(cid:15)/10n) Nq e−γ2(cid:15)/20n.

y
c
a
v
i
r
p
-
s
m
r
e
t
/
g
r
o
.
m
a
i
s
.
s
b
u
p
e
/
/
:
s
p
t
t
h
e
e
s

;
t
h
g
i
r
y
p
o
c

r
o

e
s
n
e
c
i
l

M
A
I
S
o
t

t
c
e
j
b
u
s

n
o
i
t
u
b
i
r
t
s
i
d
e
R

.

2
5
.
4
1
2
.
2
5
1
.
6
3
1

o
t

6
2
/
5
0
/
1
1

d
e
d
a
o
l
n
w
o
D

 
 
 
 
 
 
 
 
 
 
 
 
 


<!-- pdf-page: 7 -->
CHERNOFF BOUND FOR RANDOM WALKS

1209

This completes the proof.

Proof of Lemma 2.3. Since the matrix S(r) of (2.3) is symmetric, (cid:107)S(r)(cid:107)2 = λ(r).

We have

(q P (r)n 1)/λ(r)n = (q

(cid:112)

DE−1

r S(r)n √
(cid:107)2 (cid:107)S(r)n(cid:107)2 (cid:107)

ErD−1 1)/λ(r)n
π(cid:107)2 )/λ(r)n

√

≤ er/2 ( (cid:107) q√
π

≤ er/2 Nq
≤ (1 + r) Nq .

In the remainder of this section we prove Lemma 2.4. For each r ≥ 0 we deﬁne
the matrix B(r) = 1
e−1 (S(r +1)−S(r)). B(r) ≤ S(r) in each entry. Also, (B(r))i,j =
(S(r))i,j whenever i ∈ A and j ∈ A, and (B(r))i,j = 0 whenever i /∈ A and j /∈ A.
Fix r, 0 ≤ er − 1 ≤ (cid:15)/4. We may expand the function log λ(y) in a Taylor series of
the following form about the point y = r (see [W]):

(2.9)

log λ(y) = log λ(r) + mr(y − r) + (y − r)2

(cid:90) 1

0

(1 − t)Vr+(y−r)tdt ,

√

where mz and Vz are the ﬁrst and second derivatives, respectively, of log λ(y) at the
point y = z. m0 is equal to
π = π(A), the limit of the mean of tn/n
as n → ∞. This follows from letting 1(r) be the right eigenvector of P (r) with
eigenvalue λ(r) and equating coeﬃcients in the power series expansions of both sides
of P (r)1(r) = λ(r)1(r) [W, p. 69]. V0 is the limit of the variance of tn/n as n → ∞
[Nag, equation (2.5)].

πB(0)

√

The lemma follows from (2.9) and the second part of the following.
Claim 1. If 0 ≤ er − 1 ≤ (cid:15)/4, then
(i) (cid:15)r ≥ 3(cid:15)/4,
(ii) Vr ≤ 10/(cid:15).
Proof. For part (i), it is enough to show that (cid:15)r ≥ (cid:15) − (er − 1). Note that for
r ≥ 0, the matrices P (r) and S(r) have the same eigenvalues, S(r) is nonnegative,
and S(r) ≥ S in each entry. By the Perron–Frobenius theorem, λ(r) ≥ 1 [Se]. Let
µ < λ(r) be any other eigenvalue of S(r). It will suﬃce to show that µ ≤ λ2 + er − 1.
The matrix S is diagonalizable; there exist a unitary matrix U and diagonal

matrices D(cid:48) and DA such that

B(0) = 1/2(SDA + DAS) ,
and
(cid:107)D(cid:48)(cid:107)2 = (cid:107)DA(cid:107)2 = 1 .

D(cid:48) = U T SU,

If not, the matrix product U T (S + (er − 1)B(0) − µI)U ,
If µ ≤ λ2 we are done.
which is equal to (D(cid:48) − µI)[I + (D(cid:48) − µI)−11/2(er − 1)(D(cid:48)U T DAU + U T DAU D(cid:48))] , is
singular. Therefore,

1 ≤ 1/2(cid:107)(D(cid:48) − µI)−1(er − 1)D(cid:48)U T DAU (cid:107)2

+ 1/2(cid:107)(D(cid:48) − µI)−1(er − 1)U T DAU D(cid:48)(cid:107)2

≤ (er − 1)/(µ − λ2) .

(The ﬁrst inequality uses the continuity of the function λ2(·).) This proves part (i).
Our strategy for part (ii) is to use Cauchy’s estimate from complex analysis to
bound Vr in terms of the maximum value attained by λ(z) in a complex neighborhood

y
c
a
v
i
r
p
-
s
m
r
e
t
/
g
r
o
.
m
a
i
s
.
s
b
u
p
e
/
/
:
s
p
t
t
h
e
e
s

;
t
h
g
i
r
y
p
o
c

r
o

e
s
n
e
c
i
l

M
A
I
S
o
t

t
c
e
j
b
u
s

n
o
i
t
u
b
i
r
t
s
i
d
e
R

.

2
5
.
4
1
2
.
2
5
1
.
6
3
1

o
t

6
2
/
5
0
/
1
1

d
e
d
a
o
l
n
w
o
D

 
 
 
 
 
 
 
 
 
 
 
 
 


<!-- pdf-page: 8 -->
1210

DAVID GILLMAN

of r [Ahl]. We bound this maximum value indirectly: the convergence of a certain
loop integral will imply that λ(z) lies inside the loop.

For z in a small complex neighborhood of r we may write S(z) = S(r) + (ez−r −
1)B(r). A fundamental theorem of perturbation theory says that the matrix for
the projection onto the eigenspace for λ(z) is given by the operator-valued complex
integral

− 1
2πi

(cid:90)

Γ

(S(z) − ζI)−1 dζ ,

where Γ is any circle with λ(r), and no other eigenvalues of S(r), in its interior [Kat,
section II.1.4]. The important fact for us is that if λ(z) ∈ Γ then the integrand will
have a singularity at λ(z). To avoid this we choose Γ to have center λ(r) and radius
(cid:15)r/2. The norm of the integrand is ﬁnite on Γ as long as the following holds [Kat,
section II.3.1]:

|ez−r − 1| < (cid:107)B(r)(S(r) − (λ(r) − (cid:15)r/2)I)−1(cid:107)−1
2

(2.10)

≤ 2/(cid:15)r .

For the range of r we are interested in, in order for (2.10) to hold it is enough that

(2.11)

|z − r| < 3(cid:15)r/8 .

Whenever (2.11) holds λ(z) does not lie on Γ. But by continuity of λ(z), (2.11)
2 . Comparing
dz2 |z=r. Cauchy’s estimate
then
8 )2 = 64/9(cid:15)r. By part (i), Vr ≤ 10/(cid:15), and this completes the proof of

must imply that λ(z) lies inside Γ, and therefore |λ(z) − λ(r)| ≤ (cid:15)r
Taylor series for λ(z) and log λ(z), we see that Vr ≤ 2 d2λ
says that d2λ
Vr ≤ 2 (cid:15)r
2 /( 3(cid:15)r
Claim 1.

|z − r| < ρ})/ρ2. If we let ρ = 3(cid:15)r
8

dz2 |z=r is at most (max{λ(z) :

Recent work of Dinwoodie [Di95a, Di95b] has improved the exponent in the bound
of Theorem 2.1 by a factor of 20/π(A) for γ/n less than a small constant and has
extended it to nonreversible Markov chains for γ/n dependent on the eigenvalue gap.
This resolves an open question in the earlier version of this paper [G93b]. These
results use perturbation theory and power series expansions of the perturbed matrix
P (r), eigenvalue λ(r), and eigenvector 1(r). These results also extend to estimates of
Ef for real-valued functions f on V . In [Kah], Kahale has also improved the exponent
in the bound of Theorem 2.1. The exponent in the bound in [Kah] is given as the
largest zero of a polynomial in λ2, γ/n, and π(A) and is shown to be optimal on two-
state Markov chains for each triple of values of λ2, γ/n, and π(A). This result uses
perturbation theory and a proof that a certain two-state Markov chain is extremal
for the deviation probability being estimated.

3. (β, δ)-approximation algorithms for π(A). In this section we compare
diﬀerent (β, δ)-approximation algorithms for π(A) that use random walks to generate
sample points from G. Formally, the output t of a (β, δ)-approximation algorithm for
π(A) must satisfy, with probability at least 1 − δ, π(A)(1 − β) ≤ t ≤ π(A)(1 + β). The
cost of an algorithm will be the total number of random walk steps taken (see the
discussion of measures of cost at the end of the section). We assume we can eﬃciently
ﬁnd one point s in G from which to start a random walk.

Below we deﬁne SP, AP, and a modiﬁed Aldous’s procedure (APm). We analyze
the eﬃciency of AP in Proposition 3.1. APm uses a technique for increasing the

y
c
a
v
i
r
p
-
s
m
r
e
t
/
g
r
o
.
m
a
i
s
.
s
b
u
p
e
/
/
:
s
p
t
t
h
e
e
s

;
t
h
g
i
r
y
p
o
c

r
o

e
s
n
e
c
i
l

M
A
I
S
o
t

t
c
e
j
b
u
s

n
o
i
t
u
b
i
r
t
s
i
d
e
R

.

2
5
.
4
1
2
.
2
5
1
.
6
3
1

o
t

6
2
/
5
0
/
1
1

d
e
d
a
o
l
n
w
o
D

 
 
 
 
 
 
 
 
 
 
 
 
 


<!-- pdf-page: 9 -->
CHERNOFF BOUND FOR RANDOM WALKS

1211

conﬁdence of estimates introduced by Jerrum, Valiant, and Vazirani in [JVV, Lemma
6.1]. This technique, the so-called “median trick,” improves an arbitrary (β, 1/4)-
approximation algorithm to a (β, δ)-approximation algorithm by taking 12 log(1/δ)
independent estimates and using the median of the estimates. We use Proposition 3.2
and Lemma 6.1 of [JVV] to analyze APm.
Standard procedure (SP). Start the random walk at s and simulate it for k(cid:48) steps,
so that the ﬁnal state is distributed according to q’. Take the ﬁnal state as a
sample point. Repeat this l(cid:48) times by choosing the same starting point s and
taking a walk of length k(cid:48) each time. Let tl(cid:48) be the number of sample points
in A, and let t = tl(cid:48) /l(cid:48).

Aldous’s procedure (AP). Choose positive integers k and l. Start the random
walk at s and simulate it for k steps (the “delay”), so that the ﬁnal state x0
is distributed according to q. Starting from x0, continue the random walk
l more steps taking each subsequent point as a sample point. Let tl be the
number of sample points in A, and let t = tl/l.

Aldous’s procedure, modiﬁed (APm). Choose k and l and follow AP to get an
estimate of π(A). Repeat 12 log(1/δ) times and let t be the median of the
estimates.

For a distribution d on the vertices of G, let the chi-square distance from π be
s denote the chi-square distance from π of

x π(x)( d(x)

deﬁned by χ2
the initial distribution concentrated at s.

π(x) − 1)2. Let χ2

d =

(cid:80)

Proposition 3.1. The cost of estimating π(A) to within βπ(A) with probability

1 − δ using AP is at most

log(1/π(s)) / (cid:15) + 20 log(8/δ) / ((cid:15)β2π(A)2) .

Proof. Let k = log(1/π(s)) / (cid:15) and l = 20 log(8/δ) / ((cid:15)β2π(A)2). In the notation
q. According to a result of Fill [Fi, equation (2.11)],
s(1 − (cid:15))k ≤ e−(cid:15)k/π(s) ≤ 2.2 By Theorem

s(1 − (cid:15))k. Therefore, Nq ≤ 1 + χ2

of Theorem 2.1, Nq = 1 + χ2
χ2
q ≤ χ2
2.1 and the ensuing remark (ii),

Pr[|tl/l − π(A)| ≥ βπ(A)] ≤ 4Nqe−β2π(A)2(cid:15)l/20 ≤ δ.

Let πmin = minx π(x). Proposition 4.2 of Aldous [Ald87] and Lemma 6.1 of Jer-
rum, Valiant, and Vazirani [JVV] show that the cost of AP, modiﬁed, is O[(log(1/δ) / (cid:15))
(log(1/πmin) + 1 / (β2π(A)))]. The following proposition and its corollary serve to re-
place πmin by π(s). This will be useful in the applications of the next section.

Proposition 3.2. Let β > 0 and α ≤ β2. Let AP be used with parameters

k = log(20/(π(s)απ(A)2))/(cid:15) and l = 10/((cid:15)β2π(A)) to generate an estimate t. Then

and

|E[t − π(A)]| ≤ απ(A)2/20

E(t − π(A))2 ≤ β2π(A)2/4 .

2Fill’s result actually depends on the larger of λ2 and |λ|V ||, but it is possible to modify any
random walk so that in fact λ2 is the larger of the two. One converts it to a so-called “lazy” random
walk which with probability 1/2 stays put at each step [LS]. The values of k and l increase by at
most a factor of 2. The same remark applies to the application of [JS91, Theorem 6.1] below.

y
c
a
v
i
r
p
-
s
m
r
e
t
/
g
r
o
.
m
a
i
s
.
s
b
u
p
e
/
/
:
s
p
t
t
h
e
e
s

;
t
h
g
i
r
y
p
o
c

r
o

e
s
n
e
c
i
l

M
A
I
S
o
t

t
c
e
j
b
u
s

n
o
i
t
u
b
i
r
t
s
i
d
e
R

.

2
5
.
4
1
2
.
2
5
1
.
6
3
1

o
t

6
2
/
5
0
/
1
1

d
e
d
a
o
l
n
w
o
D

 
 
 
 
 
 
 
 
 
 
 
 
 


<!-- pdf-page: 10 -->
1212

DAVID GILLMAN

Table 3.1
Costs of procedures for estimating π(A).

Algorithm

Cost

SP

AP

APm

1
(cid:15)

log 1
δ

log 1

π(s)

1
β2π(A)

1
(cid:15)

(log 1

π(s)

+ log 1
δ

1
β2π(A)2 )

1
(cid:15)

log 1
δ

(log 1

π(s)

+

1
β2π(A)

)

Proof. Let (cid:107)q − π(cid:107) denote the total variation distance between q and π. Citing,
for example, [JS91, Theorem 6], we have that (cid:107)q − π(cid:107) < 1
20 απ(A)2. Let x1, . . . , xl
be the random vertices of G sampled. Each xi is distributed according to some qi,
which also satisﬁes (cid:107)qi − π(cid:107) < 1

20 απ(A)2. By linearity of expectations,

|E[tl/l − π(A)]| ≤ 1
l

l(cid:88)

i=1

|qi(A) − π(A)| ≤ 1

20 απ(A)2.

Now deﬁne a vector b by letting bj = E[(tl/l − π(A))2 | x0 = j]. Observe that

(cid:107)b(cid:107)∞ ≤ 1; therefore, by Proposition 4.1 of [Ald87], Eπb ≤ 2π(A)/((cid:15)l). We have

E(t − π(A))2 ≤ Eqb

≤ [Eπb + |Eqb − Eπb|]
≤ [2π(A)/((cid:15)l) + απ(A)2/20]
≤ β2π(A)2/4 .

Corollary 3.3. The cost of estimating π(A) to within βπ(A) with probability

1 − δ using APm is at most

12 log(1/δ)[log(20/(π(s)απ(A)2))/(cid:15) + 10/((cid:15)β2π(A))] .

Proof. Set k and l as in Proposition 3.2 with α = β2. By Chebyshev’s inequality,

Pr[|t − π(A)| ≥ βπ(A)] ≤ ( E(t − π(A))2 )/(β2π(A)2)
≤ 1/4.

The corollary follows from Lemma 6.1 of [JVV].
The standard procedure can be used to estimate π(A) to within βπ(A) with prob-
ability 1 − δ by choosing k(cid:48) = O((log(1/πmin)) / (cid:15)) and l(cid:48) = O(log(1/δ) / (β2π(A))).
This value of k(cid:48) comes from the analysis of Sinclair and Jerrum in [SJ], and the value
of l(cid:48) comes from Chernoﬀ’s bound. The method used in Lemma 3 of [JS91] is easily
seen to be generally applicable; this improves the πmin to π(s) in the expression for
k(cid:48).

The costs of the three procedures disregarding constants are shown in Table 3.1.
APm improves SP by a factor of min(log(1/π(s)), 1/(β2π(A))). AP is within a factor
of O(1/π(A)) of APm. APm incurs extra cost by repeating the initial stage of ﬁnding
a nearly random starting point; therefore, AP becomes better for small δ when β and
A are such that 1/(β2π(A)2) < log(1/π(s)).

y
c
a
v
i
r
p
-
s
m
r
e
t
/
g
r
o
.
m
a
i
s
.
s
b
u
p
e
/
/
:
s
p
t
t
h
e
e
s

;
t
h
g
i
r
y
p
o
c

r
o

e
s
n
e
c
i
l

M
A
I
S
o
t

t
c
e
j
b
u
s

n
o
i
t
u
b
i
r
t
s
i
d
e
R

.

2
5
.
4
1
2
.
2
5
1
.
6
3
1

o
t

6
2
/
5
0
/
1
1

d
e
d
a
o
l
n
w
o
D

 
 
 
 
 
 
 
 
 
 
 
 
 


<!-- pdf-page: 11 -->
CHERNOFF BOUND FOR RANDOM WALKS

1213

Remarks. (i) The recent work of Dinwoodie [Di95b] has improved the exponent
in the bound of Theorem 2.1 by a factor of 20/π(A) for γ/n less than some small
constant. This makes the cost of AP proportional to 1/π(A) and not 1/π(A)2, for β
less than some small constant.

(ii) The results of this section all have analogues for estimating the expectation
Ef of a nonnegative function f on the vertices of G. Corresponding to Proposition
3.2 is the following, which we state without proof.

Proposition 3.4. Let β > 0 and α ≤ β2. Let k = log(20/(απ(s)(Ef )2))/(cid:15) and
l = 10Var(f )/((cid:15)β2(Ef )2) . Take a random walk on G starting in s, and let xi, i ≥ 1,
stand for the (i + k)th vertex of the random walk. Let t = 1
l (f (x1) + · · · + f (xl)).
Then

and

|E[t − Ef ]| ≤ α(Ef )2/20

E(t − Ef )2 ≤ β2(Ef )2/4 .

The running time for AP is proportional to (cid:107)f (cid:107)∞/(Ef )2 instead of 1/π(A)2, and
the running time of SP has the same dependence as APm on Var(f ) and (Ef )2 [JS91,
Lemma 3].

(iii) Measures of cost. It can be argued that SP has the advantage of taking only
a small fraction (around (cid:15)) of the number of sample points of either AP or APm. We
have not considered the number of sample points in our measure of cost because in the
cases we know of the cost of sampling a point is dominated by the cost of taking one
step of the random walk. For example, in the case of the random walk on matchings
treated below, to determine the transition probability from one matching to another
it is necessary to know whether the number of edges is going up or down by one, or
staying the same. Therefore, it adds only a constant cost to keep track of the size of
the current matching (see [JS89]). The same sort of justiﬁcation holds for the case of
the Ising model considered below. Computing the value of f at a vertex is no more
diﬃcult than computing the next transition probability (see [JS91]). Situations may
yet arise of having to estimate Ef for complicated f , where the number of sample
points will be an important part of the cost of an algorithm.

(iv) Nondelayed samples. Suppose instead of generating a random initial point we
had begun sampling immediately from s. The question is raised in [Ald87, Example
4.2] whether such nondelayed samples give good estimates in polynomial time. Setting
k = 0 in Proposition 3.1 yields l = 20(log(1/π(s)) + log(1/δ))/((cid:15)β2π(A)2). An upper
bound on log(1/π(s)) is log |G|+log maxx,y(π(x)/π(y)), which is typically polynomial
in the data. This shows that nondelayed samples give good estimates in polynomial
time, as long as π(A) is not too small. It is not hard to see that the most eﬃcient
estimate, using our analysis, comes from letting k be equal to the relaxation time as
in the proof of Proposition 3.1.

4. Applications: Two approximation algorithms.

The subgraphs random walk for the Ising model. In this section we give
a modiﬁed version of an algorithm, due to Jerrum and Sinclair, for computing the
partition function Z of a ferromagnetic Ising system I on m points (deﬁnitions below).
Our new version of the algorithm improves the running time from O(|E|3m7) to
O(|E|2m6), where m is the number of vertices and E is the edge set of the system
[JS91].

y
c
a
v
i
r
p
-
s
m
r
e
t
/
g
r
o
.
m
a
i
s
.
s
b
u
p
e
/
/
:
s
p
t
t
h
e
e
s

;
t
h
g
i
r
y
p
o
c

r
o

e
s
n
e
c
i
l

M
A
I
S
o
t

t
c
e
j
b
u
s

n
o
i
t
u
b
i
r
t
s
i
d
e
R

.

2
5
.
4
1
2
.
2
5
1
.
6
3
1

o
t

6
2
/
5
0
/
1
1

d
e
d
a
o
l
n
w
o
D

 
 
 
 
 
 
 
 
 
 
 
 
 


<!-- pdf-page: 12 -->
1214

DAVID GILLMAN

Our algorithm is a fully polynomial randomized approximation scheme (fpras) as
described in [KL] and in subsequent work on approximation algorithms. That is, on
input I and a real number a > 0 it runs in time polynomial in m and 1/a and outputs
a number that with probability at least 3/4 approximates Z with relative error of a.
The algorithm of Jerrum and Sinclair was the ﬁrst fpras for this problem.

Consider a graph I = ([m], E), [m] = {1, 2, . . . , m}, with a positive interaction
energy Vij associated to each edge {i, j} ∈ E. A conﬁguration σ = {σi}m
i=1 is an
assignment of positive (σi = +1) or negative (σi = −1) spin to each site i ∈ [m]. The
energy of a conﬁguration is given by the Hamiltonian

H(σ) = −

(cid:88)

{i,j}∈E

Vijσiσj − B

(cid:88)

k∈[m]

σk,

where B is an external ﬁeld.

This is a ferromagnetic Ising system; the positivity constraint on the Vij models
the behavior of a ferromagnet. A central problem for Bayesian inference in statistical
physics is to compute a probability normalizing constant called the partition function:

Z = Z(Vij, B, βT ) :=

(cid:88)

e−βT H(σ) ,

σ∈{−1,+1}m

where βT is related to the temperature. For further motivation we refer to [JS91] and
the references therein.

Physicists have long used random walks on the set of spin conﬁgurations to es-
timate Z, but these random walks are not rapidly mixing for certain values of βT .
However, the partition function has an alternate characterization. Consider the set of
all subsets X of the edge set E. Each subset X can be identiﬁed with a subgraph of I
(which may contain isolated vertices). Let odd(X) stand for the set of all odd-degree
vertices in the subgraph identiﬁed with X. Let λij = tanh βT Vij and µ = tanh βT B.
The weight of X is deﬁned by

(4.1)

w(X) = µ|odd(X)|

(cid:89)

λij .

{i,j}∈X

The “subgraphs-world” partition function is
(cid:88)

(4.2)

Z (cid:48) =

w(X).

X⊆E

The two partition functions are related by the formula

(4.3)

Z = AZ (cid:48) ,

(cid:81)

where A = (2 cosh βT B)m

{ij}∈E cosh βT Vij (see [NM]).
Although the subgraphs have no physical meaning, it is natural in light of (4.3)
to compute Z indirectly by computing Z (cid:48). We deﬁne a random walk on the set G of
all subsets X ⊆ E. Fix µ = µ(βT ). For each X the transition probabilities out of
X are given by the following rules [JS91, p. 16]: pick an edge e ∈ E uniformly at
random, and then

1. set Y = X⊕e (the symmetric diﬀerence of X and e);
2. if w(Y ) ≥ w(X) then move to Y with probability 1;

y
c
a
v
i
r
p
-
s
m
r
e
t
/
g
r
o
.
m
a
i
s
.
s
b
u
p
e
/
/
:
s
p
t
t
h
e
e
s

;
t
h
g
i
r
y
p
o
c

r
o

e
s
n
e
c
i
l

M
A
I
S
o
t

t
c
e
j
b
u
s

n
o
i
t
u
b
i
r
t
s
i
d
e
R

.

2
5
.
4
1
2
.
2
5
1
.
6
3
1

o
t

6
2
/
5
0
/
1
1

d
e
d
a
o
l
n
w
o
D

 
 
 
 
 
 
 
 
 
 
 
 
 


<!-- pdf-page: 13 -->
y
c
a
v
i
r
p
-
s
m
r
e
t
/
g
r
o
.
m
a
i
s
.
s
b
u
p
e
/
/
:
s
p
t
t
h
e
e
s

;
t
h
g
i
r
y
p
o
c

r
o

e
s
n
e
c
i
l

M
A
I
S
o
t

t
c
e
j
b
u
s

n
o
i
t
u
b
i
r
t
s
i
d
e
R

.

2
5
.
4
1
2
.
2
5
1
.
6
3
1

o
t

6
2
/
5
0
/
1
1

d
e
d
a
o
l
n
w
o
D

(1) A := (2 cosh βT B)m
A × Z (cid:48)(1);

CHERNOFF BOUND FOR RANDOM WALKS
(cid:81)

(cid:81)

{ij}∈E cosh βT Vij; and Z (cid:48)(1) :=

{i,j}∈E(1 + λij); Π :=

1215

(2) r := the natural number satisfying m−r
(3) µ0 := 1; for j = 0, 1, . . . , r, do begin

m > tanh βT B ≥ m−r−1
m ;

m ; else µj+1 := tanh βT B;

(4) if j ≤ r, then µj+1 := m−j
(5) Make a call to AP with parameters k and l and t as in Proposition 3.4:
let α = a2/2m2 and β = a/
2m, and assume a lower bound of 1/10
on Ef . Use the random walk on G with parameter µj, and obtain an
estimate t for Eµj f ;

√

(6) Π := Π × t;

end;

(7) halt with output Π;

Fig. 4.1. Algorithm for computing the partition function.

3. if w(Y ) < w(X) then move to Y with probability w(Y )/w(X), and stay at

X otherwise.

It is easy to see that G is connected by the transitions that have positive proba-
bility. It is not hard to check that the unique stationary distribution π = πµ is given
by π(X) = w(X)/Z (cid:48) (the transition probabilities were chosen with this goal in mind,
according to the well-known Metropolis rule).

(cid:81)

We adhere to the strategy of Jerrum and Sinclair for computing Z (cid:48) = Z (cid:48)(µ).
This is to notice that Z (cid:48)(1) =
{i,j}∈E(1 + λij), which is easy to compute. Then
for a general µ ∈ [0, 1], one bootstraps from Z (cid:48)(1) down to Z (cid:48)(µ) by computing
successive ratios Z (cid:48)(µ(cid:48))/Z (cid:48)(µ) as follows. Let Eµf be the expectation under πµ. For
0 ≤ µ1 < µ0 ≤ 1 deﬁne the function f (X) = (µ1/µ0)|odd(X)| . The expectation of f
satisﬁes Eµ0f = Z (cid:48)(µ1)/Z (cid:48)(µ0) [JS91, p. 11]. Furthemore, Lemma 4 of [JS91] says
that if µ0 ≤ µ1 + 1/m, then Eµ0f ≥ 1/10.

Our (a, 1/4) approximation scheme for computing the partition function is shown
in Fig. 4.1. We let step (5) assume a lower bound of (cid:15) ≥ (2m4|E|2)−1, as given by
Sinclair in [Si]. This algorithm diﬀers from the algorithm of Jerrum and Sinclair [JS89,
p. 12] in two ways. First, we use AP rather than SP in step (5). Second, we choose
m) instead of β = θ(a/m) in step (5) and we observe that the accumulated
β = θ(a/
errors in Π tend to cancel one another out. This observation has been used before by
Dyer and Frieze. We formalize it in the following lemma, which essentially appears
in [DF, page 10].

√

Lemma 4.1. Let z1, . . . , zm be independent nonnegative random variables with
i=1(1 + zi).

i ≤ ν/m for some ν ≤ 1. Let Y =

Ezi ≤ η/2m2 for some η ≤ 1, and Ez2
Then E(Y − 1)2 ≤ η/m + ν + (η/m + ν)2.

(cid:81)m

Proof. Since Y ≥ 1, E(Y − 1)2 = E[Y 2 − 2Y + 1] ≤ EY 2 − 1. Therefore,

E(Y − 1)2 ≤ E[
(cid:81)

(cid:81)

i(1 + zi)2] − 1
i(1 + 2Ezi + Ez2
i ) − 1
=
≤ (1 + η/m2 + ν/m)m − 1
≤ eη/m+ν − 1
≤ η/m + ν + (η/m + ν)2.

Theorem 4.2. Let a ∈ (0, 1). The output Π of our algorithm satisﬁes Π(1 − a) <
Z < Π(1 + a) with probability at least 3/4. The running time is at most 500m6|E|2/a2
random walk steps.

 
 
 
 
 
 
 
 
 
 
 
 
 


<!-- pdf-page: 14 -->
1216

DAVID GILLMAN

Remark. Theorem 2, Lemmas 3 and 4, and the remark at the end of section 4
of [JS91] give a bound of O(m7|E|3/a2) random walk steps to estimate Z with the
algorithm of Jerrum and Sinclair.

Proof. Let tj be the estimate of Eµj f from the jth iteration of the do loop. Let

(cid:81)

zj = tj/Ef − 1. Let Y =

j(1 + zj) = Π/Z. By Proposition 3.4,

and

|Eµj zj| ≤ a2/40m2

Eµj

j ≤ a2/8m.
z2

Assuming in the worst case that r = m, the zj satisfy the assumptions of Lemma 4.1
with η = a2/20 and ν = a2/8. By Chebyshev’s inequality, Pr[|(Π/Z) − 1| ≥ a] ≤
E(Y − 1)2/a2; so by the lemma,

Pr[|(Π/Z) − 1| ≥ a] ≤ [a2/20 + a2/8 + (a2/20 + a2/8)2]/a2 ≤ 1/4 .

Perfect matchings. In this subsection we summarize the improvements we have
made to an approximation algorithm, due to Jerrum and Sinclair, for counting the
number of perfect matchings in a graph H = (V, E) on 2m vertices. A matching is a
subset of E such that no two edges share a common endpoint. A perfect matching is
a matching that contains m edges. Let Mj denote the set of matchings of size j in H.
In [Br] Broder gave the ﬁrst fpras for counting perfect matchings in dense graphs.
A full proof of the correctness of this algorithm awaited Jerrum and Sinclair, who also
gave a faster algorithm in [JS89].

An upper bound q(m) > |Mm−1|/ max(1, |Mm|) is assumed to be known for some
ﬁxed polynomial q. Thus H is said to be q-amenable. Jerrum and Sinclair have shown
that all dense graphs are m2-amenable and almost every random bipartite graph is
m10-amenable in the B(n, p) model for any density p above the threshold for the
existence of a perfect matching [JS89]. Kenyon, Randall, and Sinclair have shown
that all bipartite Cayley graphs and all regular periodic lattices of any dimension are
O(m2)-amenable [KRS]. In general, q(m) ≥ m.

(cid:83)

Jerrum and Sinclair deﬁne a random walk on a weighted graph G whose vertex
1≤j≤m Mj. The transition probabilities depend upon a
set is all matchings of H:
certain real parameter c which varies at diﬀerent stages in the algorithm. In each stage
the transition probabilities are chosen according to the Metropolis rule to ensure that
the stationary probabilities π(Mj) are proportional to cj|Mj| for all j. See [JS89] for
more details.

Our modiﬁed version of the algorithm of [JS89] also uses a random walk on G,
and like the original algorithm, our version proceeds in m − 1 stages, each using a
diﬀerent value c(j) for c. Stage j ≥ 1 calculates the ratio |Mj+1|/|Mj|. The algorithm
multiplies the ratios together to obtain an estimate of |Mm| (|M1| is simply the number
of edges of H). Since each of these ratios satisﬁes |Mj+1|/|Mj| = cπ(Mj+1)/π(Mj),
the essential step of the algorithm is to estimate π(Mj+1) and π(Mj).

Our version modiﬁes the algorithm of Jerrum and Sinclair [JS89, Figure 2] in two
ways. First, we use APm in our random walk calls to estimate the π(Mj)’s, instead
of SP. Second, we introduce a new strategy for choosing the values of c which allows
the algorithm to assume that both π(Mj+1) and π(Mj) are Ω(1/m).

The idea behind the new strategy is as follows. By Theorem 5.1 of [JS89], the se-
quence |M1|, |M2|, . . . , |Mm| is log-concave. This means that log |E|−1 = log(|M0|/|M1|)

y
c
a
v
i
r
p
-
s
m
r
e
t
/
g
r
o
.
m
a
i
s
.
s
b
u
p
e
/
/
:
s
p
t
t
h
e
e
s

;
t
h
g
i
r
y
p
o
c

r
o

e
s
n
e
c
i
l

M
A
I
S
o
t

t
c
e
j
b
u
s

n
o
i
t
u
b
i
r
t
s
i
d
e
R

.

2
5
.
4
1
2
.
2
5
1
.
6
3
1

o
t

6
2
/
5
0
/
1
1

d
e
d
a
o
l
n
w
o
D

 
 
 
 
 
 
 
 
 
 
 
 
 


<!-- pdf-page: 15 -->
CHERNOFF BOUND FOR RANDOM WALKS

1217

≤ log(|M1|/|M2|) ≤ · · · ≤ log(|Mm−1|/|Mm|) ≤ log q(m). Put cj = |Mj−1|/|Mj| for
each j, and cm+1 = q(m). Whenever c ∈ [cj, cj+1], π(Mj) ≥ π(Mi) for all i.
In
particular, when c = cj+1, π(Mj) and π(Mj+1) are each at least 1/m. Since all of
our sampling procedures are more eﬃcient when sampling large sets, we would like
to choose c = cj+1 at stage j of the algorithm. What our algorithm does is to in-
crease c by a constant factor at each stage, so that log c is incremented through the
range [log |E|−1, log q(m)] in constant-size steps. However, the algorithm also detects
those areas of this range where the log(π(Mj)/π(Mj+1))’s are clumped together, and
in those areas it takes smaller steps.
In the end the algorithm needs to try only
m + O(log m) diﬀerent values of c to ensure that each cj+1 is approximated well by
one of them.

Theorem 4.3. Let a ∈ (0, 1/2]. If H is q-amenable then the output Π of our
algorithm satisﬁes Π(1 − a) < Mm < Π(1 + a) with probability at least 3/4. Our
algorithm uses O(q2m5|E| log m/a2) random walk steps.

Remarks. (i) The algorithm of Jerrum and Sinclair uses O(q3m6|E| log2 m/a2)
random walk steps, assuming the lower bound on the eigenvalue gap given later by
Sinclair in [Si].

(ii) We have tried to reduce the running time of our algorithm by another factor of
O(m) using Lemma 4.1. The problem we face is that we need very reliable estimates
of each c(j) (as did Jerrum and Sinclair) to make sure that Mj and Mj+1 would be
large enough sets (in stationary probability) to sample from. The cost of these reliable
estimates dominates the cost of each stage of the algorithm.

5. Entropy of sources. We now consider the special case of a random walk
on an unweighted undirected graph G. We view the random walk as an information
source whose alphabet is the vertex set V of G. Theorem 2.1 enables us to quantify
the rate of convergence of the classical Shannon–McMillan asymptotic equipartition
property for this information source. We will then be able to estimate the entropy
of the source very quickly, in O(log |G|) steps when G has constant expansion and
constant nonuniformity (deﬁned below). For purposes of ﬁxed-length noiseless coding
of the source, this result will imply a bound on the error exponent in terms of the
expansion of G.

Let G have eigenvalue gap (cid:15). Deﬁne the nonuniformity ν of G by

ν = max
x,y

π(x)/π(y).

Let M be twice the number of edges of G. Let P = (pij) be the transition matrix
for the random walk on G. For all i, j, pij = 1/di, where di is the degree of vertex
i. π(i) = di/
j dj = di/M ; therefore, M ≥ maxi 1/π(i) ≥ ν. Let x0, x1, . . . be
a random walk on G starting from the stationary distribution. Consider the random
sequence X = x1, x2, . . . an information source.

(cid:80)

The random walk as an information source. In general, the entropy H(Y )
of an information source Y = y1, y2, . . . is deﬁned in terms of the ordinary Shannon
entropy: H(Y ) = limn→∞ E H[yn|y1, . . . , yn−1]. In our case, in which there is an
underlying stationary random walk on an unweighted graph, there is a simple formula:

(5.1)

H(X) = E H(x1|x0) = −E log2 px0x1
= Eπ log2 dx0 .

The Shannon–McMillan theorem [Ash, Theorem 6.6.1] states that under an ergod-
icity assumption which is satisﬁed here, an information source Y has the asymp-

y
c
a
v
i
r
p
-
s
m
r
e
t
/
g
r
o
.
m
a
i
s
.
s
b
u
p
e
/
/
:
s
p
t
t
h
e
e
s

;
t
h
g
i
r
y
p
o
c

r
o

e
s
n
e
c
i
l

M
A
I
S
o
t

t
c
e
j
b
u
s

n
o
i
t
u
b
i
r
t
s
i
d
e
R

.

2
5
.
4
1
2
.
2
5
1
.
6
3
1

o
t

6
2
/
5
0
/
1
1

d
e
d
a
o
l
n
w
o
D

 
 
 
 
 
 
 
 
 
 
 
 
 


<!-- pdf-page: 16 -->
1218

DAVID GILLMAN

totic equipartition property (AEP): for a ﬁxed length n of source sequences, there are
asymptotically 2nH(Y ) source sequences each of asymptotic probability 2−nH(Y ), and
the probability of the “bad” set of remaining sequences tends to zero as n tends to
inﬁnity. The next theorem establishes an upper bound on the probability of the “bad”
set.

Consider the particular information source X and a ﬁnite sequence x1, . . . , xn,
generated by X. Deﬁne the empirical entropy Vn of this ﬁnite sequence by Vn = − 1
n
log2 Pr[x1, . . . , xn].

Theorem 5.1. Let X be the information source generated by the random walk
on G. Let x1, . . . , xn be a ﬁnite sequence generated by X, with empirical entropy Vn.
Then

(5.2)

≤ 4e−(γ−(log2 M )/n)2n(cid:15)/20log2

2ν .

Pr[|Vn − H(X)| ≥ γ]

Proof. Deﬁne a nonnegative function g on the vertices of G by g(x) = log2 dx. Set
f (x) = g(x)−miny g(y). Then (cid:107)f (cid:107)∞ = log2 ν and by (5.1), Eπf = H(X)−miny g(y).
Let tn = f (x1) + · · · + f (xn). Then Vn − miny g(y) = tn/n + (log2 1/π(x1))/n −
(log2 dxn

)/n. Using (2.2) and remark (i) following Theorem 2.1,

Pr[Vn − H(X) ≥ γ]

= Pr[tn/n − (H(X) − min

y

g(y))

≥ γ − (log2 1/π(x1))/n + (log2 dxn

)/n]

(cid:34)

(cid:18)

≤ 2 exp

−

γ − (log2 M )/n
(log2 ν)/n

(cid:19)2

(cid:35)

(cid:15)/20n

The inequality in the other direction is similar.

≤ 2e−(γ−(log2 M )/n)2n(cid:15)/20log2

2ν.

Uniﬁlar sources. Let χ : V (G) → {0, 1, . . . , k − 1} be any labelling of the
vertices of G such that the random walk on G is uniﬁlar; that is, no vertex G is
adjacent to two or more vertices of the same label. Let Y = y1, y2, . . . be the sequence
of labels: yi = χ(xi). Then the entropy of the information source Y still satisﬁes (5.1):
H(Y ) = Eπ log2 dx0
. The deﬁnition of empirical entropy for Y is also the same, and
we immediately have the following generalization.

Corollary 5.2. Let Vn denote the empirical entropy of y1, . . . , yn. Then

(5.3)

≤ 4e−(γ−(log2 k|G|)/n)2n(cid:15)/20log2

2k .

Pr[|Vn − H(Y )| ≥ γ]

Remarks. (i) The logarithm of the right-hand side of (5.3) gives an upper bound
on the error exponent for ﬁxed-length coding of the source Y . This appears to be
the ﬁrst such bound which applies for all n and is given in terms of a computable
quantity (the eigenvalue gap). Large deviation methods were used in [Nat, An], giving
asymptotic estimates of the error exponent.

(ii) Corollary 5.2 can be restated as follows: to estimate H(Y ) to within an
additive error γ with probability at least 1 − δ requires a random walk of length
O(log2 k log(1/δ) log k|G|/(cid:15)γ2). When the number of labels k is constant and G has
constant expansion, this simpliﬁes to O(log(1/δ) log |G|/γ2).

y
c
a
v
i
r
p
-
s
m
r
e
t
/
g
r
o
.
m
a
i
s
.
s
b
u
p
e
/
/
:
s
p
t
t
h
e
e
s

;
t
h
g
i
r
y
p
o
c

r
o

e
s
n
e
c
i
l

M
A
I
S
o
t

t
c
e
j
b
u
s

n
o
i
t
u
b
i
r
t
s
i
d
e
R

.

2
5
.
4
1
2
.
2
5
1
.
6
3
1

o
t

6
2
/
5
0
/
1
1

d
e
d
a
o
l
n
w
o
D

 
 
 
 
 
 
 
 
 
 
 
 
 


<!-- pdf-page: 17 -->
CHERNOFF BOUND FOR RANDOM WALKS

1219

6. Further work. The main open problem is to give a lower bound on the
probability of deviation estimated in Theorem 2.1. A lower bound must depend on
the set A and not only on π(A). For example, in the usual barbell graph, if A is all
on one side of the “handle,” the deviation probability will actually be larger than if
A is equally distributed between the two sides of the graph [G93a, pp. 56–57].

It would be nice to be able to estimate the entropy of a random walk on a
weighted graph. In [G93a], the author has shown that such a generalization would
have applications to the problem of discriminating two hidden Markov chains from
their output. The immediate diﬃculty is not the lack of a nice formula for entropy
in this case, but the problem of estimating the expected value of a function on the
edges of G. The random walk on G induces a Markov chain on the edges of G. The
induced Markov chain is not time-reversible, so the Chernoﬀ bound does not apply
as it stands.

Ultimately it would be nice to be able to estimate the entropy of a 0-1 source
generated by a (possibly nonuniﬁlar) Markov chain whose states are labelled 0 and 1.

Acknowledgments. My advisor Mike Sipser helped to formulate the problem
of a central limit theorem for expander graphs and continually discussed the issues
of this paper with me while my work progressed. Johan H˚astad drew my attention
to the paper of T. H¨oglund. L´aszl´o Lov´asz pointed out the potential application of
a Chernoﬀ bound to approximation algorithms. Nabil Kahale, Miklos Simonovits,
Alistair Sinclair, and David Zuckerman, and Svante Janson made helpful comments.
It is my pleasure to thank these people.

REFERENCES

[Ahl]
[AKS] M. Ajtai, J. Koml´os, and E. Szemer´edi, Deterministic simulation of logspace, in Proc.

L. Ahlfors, Complex Analysis, 2nd ed., McGraw-Hill, New York, 1966.

19th ACM Symp. on Theory of Computing, 1987.

[Ald87] D. Aldous, On the Markov chain simulation method for uniform combinatorial distribu-

tions and simulated annealing, Probab. Engrg. Inform. Sci., 1 (1987), pp. 33–46.

[Alo]
[AM]

N. Alon, Eigenvalues and expanders, Combinatorica, 6 (1986), pp. 83–96.
N. Alon and V. D. Milman, λ1, isoperimetric inequalities for graphs, and superconcen-

trators, J. Combin. Theory B, 38 (1985), pp. 73–88.

[An]

V. Anantharam, A large deviation approach to error exponents in source coding and

hypothesis testing, IEEE Trans. Inform. Theory, 36 (1990), pp. 938–943.

[Ash]
[Br]

R. Ash, Information Theory, Interscience, New York, 1965.
A. Z. Broder, How hard is it to marry at random? (on the approximation of the perma-

nent), in Proc. 18th ACM Symp. on Theory of Computing, 1986, pp. 50–58.

[Ch]

H. Chernoff, A measure of asymptotic eﬃciency for tests of a hypothesis based on the

sum of observations, Ann. Math. Statist., 23 (1952), pp. 493–507.

[Cr]

H. Cram´er, Sur un nouveau th´eor`eme de la th´eorie des probabilit´es, Actualit´es Scien-

tiﬁques et Industrielles, 736 (1938).

[CW]

[Di95a]

[Di95b]
[Do]
[DF]

A. Cohen and A. Wigderson, Dispersers, deterministic ampliﬁcation, and weak random
sources, in Proc. 30th IEEE Symp. on Foundations of Computer Science, 1989.
I. H. Dinwoodie, A probability inequality for the occupation measure of a reversible

Markov chain, Ann. Appl. Probab., 5 (1995), pp. 37–43.

I. H. Dinwoodie, Expectations for Nonreversible Markov Chains, preprint, 1995.
J. L. Doob, Stochastic Processes, Wiley, New York, 1953.
M. Dyer and A. Frieze, Computing the volume of convex bodies: A case where ran-
domness provably helps, in Proc. AMS Symp. on Probabilisitc Combinatorics and Its
Application, 1991, pp. 123–170.

[DFK] M. Dyer, A. Frieze, and R. Kannan, A random polynomial time algorithm for approx-
imating the volume of convex bodies, in Proc. 21st Annual ACM Symp. on Theory of
Computing, 1989, pp. 375–381.



<!-- pdf-page: 18 -->
1220

[Fi]

DAVID GILLMAN

J. A. Fill, Eigenvalue bounds on convergence to stationarity for nonreversible Markov
chains, with an application to the exclusion process, Ann. Appl. Probab., 1 (1991),
pp. 62–87.

[G93a]

D. Gillman, Hidden Markov Chains: Convergence Rates and the Complexity of Inference,

Ph.D. Thesis, Massachusetts Institute of Technology, Cambridge, MA, 1993.

[G93b]

D. Gillman, A Chernoﬀ bound for random walks on expander graphs, in Proc. 34th IEEE

[G∗]

[H]

[IZ]

Symp. on Foundations of Computer Science, 1993, pp. 680–691.

O. Goldreich, R. Impagliazzo, L. Levin, R. Venkatesan, and D. Zuckerman, Security
preserving ampliﬁcation of hardness, in Proc. 31st IEEE Symp. on Foundations of
Computer Science, 1990, pp. 318–326.

T. H¨oglund, Central limit theorems and statistical inference for ﬁnite Markov chains, Z.

Wahr. Gebiete, 29 (1974), pp. 123–151.

R. Impagliazzo and D. Zuckerman, How to Recycle Random Bits, in Proc. 30th IEEE

Symp. on Foundations of Computer Science, 1989.

[JS89] M. Jerrum and A. Sinclair, Approximating the permanent, SIAM J. Comput., 18 (1989),

pp. 1149–1178.

[JS91] M. Jerrum and A. Sinclair, Polynomial-time approximation algorithms for the Ising

model, SIAM J. Comput., 22 (1993), pp. 1087–1116.

[JVV]

[Kah]

M. Jerrum, L. Valiant, and V. Vazirani, Random generation of combinatorial struc-
tures from a uniform distribution, Theoret. Comput. Sci., 43 (1986), pp. 169–188.
N. Kahale, Large Deviation Bounds for Markov Chains, DIMACS Technical Report,

DIMACS, Rutgers University, New Brunswick, NJ, 1994, pp. 94–39.

[KL]

R. Karp and M. Luby, Monte Carlo algorithms for enumeration and reliablity problems,

in Proc. 15th ACM Symp. on Theory of Computing, 1983.

[Kat]

T. Kato, A Short Introduction to Perturbation Theory for Linear Operators, Springer-

Verlag, New York, 1982.

[KRS]

C. Kenyon, D. Randall, and A. Sinclair, Matchings in lattice graphs, in Proc. 25th

ACM Symp. on Theory of Computing, 1993, pp. 738–746.

[LS]

L. Lov´asz and M. Simonovits, Random walks in a convex body and an improved volume

algorithm, Random Structures Algorithms, 4 (1993), pp. 359–412.

[Nat]

S. Natarajan, Large deviations, hypothesis testing, and source coding for ﬁnite Markov

chains, IEEE Trans. Inform. Theory, 31 (1985), pp. 360–365.

[Nag]

S. V. Nagaev, More exact statements of limit theorems for homogeneous Markov chains,

Theory Probab. Appl., 6 (1961), pp. 62–81.

[NM]

G. F. Newell and E. W. Montroll, On the theory of the Ising model of ferromagnetism,

[Se]
[Si]

[SJ]

[SS]

[Ta]

[W]

Rev. Modern Phys., 25 (1953), pp. 353–389.

E. Seneta, Nonnegative Matrices, Wiley, New York, 1973.
A. Sinclair, Improved Bounds for Mixing Rates of Markov Chains and Multicommodity
Flow, Technical Report ECS-LFCS-91-178, Department of Computer Science, Univer-
sity of Edinburgh, Scotland, October 1991.

A. Sinclair and M. Jerrum, Approximate counting, uniform generation, and rapidly

mixing Markov chains, Inform. and Comput., 82 (1989), pp. 93–113.

G. W. Stewart and J.-G. Sun, Matrix Perturbation Theory, Academic Press, New York,

1990.

R. M. Tanner, Explicit construction of concentrators from generalized n-gons, SIAM J.

Algebraic Discrete Meth., 5 (1984), pp. 287–294.

J. H. Wilkinson, The Algebraic Eigenvalue Problem, Clarendon Press, Oxford, UK, 1965.

y
c
a
v
i
r
p
-
s
m
r
e
t
/
g
r
o
.
m
a
i
s
.
s
b
u
p
e
/
/
:
s
p
t
t
h
e
e
s

;
t
h
g
i
r
y
p
o
c

r
o

e
s
n
e
c
i
l

M
A
I
S
o
t

t
c
e
j
b
u
s

n
o
i
t
u
b
i
r
t
s
i
d
e
R

.

2
5
.
4
1
2
.
2
5
1
.
6
3
1

o
t

6
2
/
5
0
/
1
1

d
e
d
a
o
l
n
w
o
D

 
 
 
 
 
 
 
 
 
 
 
 
 

