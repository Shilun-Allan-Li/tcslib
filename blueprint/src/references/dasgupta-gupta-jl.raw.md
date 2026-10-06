<!-- generated-by: proofmatch local extraction -->
<!-- source-pdf-sha256: a6706e37c21a69694f85415c162324ed031eb33e675367aa04ee6abdf37ada97 -->
<!-- extractor: pdfminer.six v20260107 -->

<!-- pdf-page: 1 -->
An Elementary Proof of a Theorem of
Johnson and Lindenstrauss

Sanjoy Dasgupta,1 Anupam Gupta2
1AT&T Labs Research, Room A277, Florham Park, New Jersey 07932; e-mail:

dasgupta@research.att.com

2Lucent Bell Labs, Room 2C-355, 600 Mountain Avenue, Murray Hill,

New Jersey 07974; e-mail: anupamg@research.bell-labs.com

Received 16 December 2001; accepted 11 July 2002

DOI 10.1002/rsa.10073

ABSTRACT: A result of Johnson and Lindenstrauss [13] shows that a set of n points in high
dimensional Euclidean space can be mapped into an O(log n/(cid:1)2)-dimensional Euclidean space such
that the distance between any two points changes by only a factor of (1 (cid:1) (cid:1)). In this note, we prove
this theorem using elementary probabilistic techniques. © 2003 Wiley Periodicals, Inc. Random Struct.
Alg., 22: 60 – 65, 2002

1. INTRODUCTION

A fundamental result of Johnson and Lindenstrauss [13] says that any n point subset of
Euclidean space can be embedded in k (cid:2) O(log n/(cid:1)2) dimensions without distorting the
distances between any pair of points by more than a factor of (1 (cid:1) (cid:1)), for any 0 (cid:3) (cid:1) (cid:3)
1. In recent work, Noga Alon has shown that this result is essentially tight: His result
shows that any set of n points with inter-point distances lying in the range [1 (cid:4) (cid:1), 1 (cid:5)
(cid:1)] requires at least (cid:6)(log n/((cid:1)2log 1/(cid:1))) dimensions [1, Section 9].

In recent years, the Johnson–Lindenstrauss theorem has found numerous applications
that include bi-Lipschitz embeddings of graphs into normed spaces [14], searching for

Correspondence to: A. Gupta
© 2002 Wiley Periodicals, Inc.

60



<!-- pdf-page: 2 -->
ELEMENTARY PROOF OF JOHNSON AND LINDENSTRAUSS

61

approximate nearest neighbors in high-dimensional Euclidean space [12], learning mix-
tures of Gaussians [5], and dimension reduction in databases [2].

The original proof of Johnson and Lindenstrauss is probabilistic, showing that project-
ing the n-point subset onto a random subspace of O(log n/(cid:1)2) dimensions only changes
the interpoint distances by (1 (cid:1) (cid:1)) with positive probability. Their proof was subsequently
simpliﬁed by Frankl and Maehara [7, 8]. The proof given in this note uses elementary
probabilistic techniques to obtain the result. Indyk and Motwani [12], Arriaga and
Vempala [3], and Achlioptas [2] have also given similar proofs of the theorem using
simple randomized algorithms. (A discussion of some of these proofs is given in Section
3.) Many of these randomized algorithms have recently been derandomized by [6, 15].

2. THE JOHNSON-LINDENSTRAUSS THEOREM

The main result of this paper is the following:

Theorem 2.1. For any 0 (cid:3) (cid:1)(cid:3) 1 and any integer n, let k be a positive integer such that

k (cid:2) 4(cid:7)(cid:1)2/2 (cid:3) (cid:1)3/3(cid:8)(cid:4)1ln n.

(2.1)

Then for any set V of n points in Rd, there is a map f : Rd 3 Rk such that for all u,
v (cid:1) V,

(cid:7)1 (cid:3) (cid:1)(cid:8)(cid:1)u (cid:3) v(cid:1)2 (cid:4) (cid:1) f(cid:7)u(cid:8) (cid:3) f(cid:7)v(cid:8)(cid:1)2 (cid:4) (cid:7)1 (cid:5) (cid:1)(cid:8)(cid:1)u (cid:3) v(cid:1)2.

Furthermore, this map can be found in randomized polynomial time.

The original paper of Johnson and Lindenstrauss [13] proved a version of this result
with the lower bound on k being O(log n). In their paper, Frankl and Maehara [7] showed
that k (cid:2) 9((cid:1)2 (cid:4) 2(cid:1)3/3)(cid:4)1ln n (cid:5) 1 dimensions are sufﬁcient; the papers of Indyk and
Motwani [12] and Achlioptas [2] give essentially the same bounds for k as we do. (For a
discussion on these proofs, the reader is pointed to Section 3.)

Our proof of the theorem follows a fairly standard line of reasoning which has been
used before for this problem (e.g., in [7]): It shows that the squared length of a random
vector is sharply concentrated around its mean when the vector is projected onto a random
k-dimensional subspace. Speciﬁcally, with probability O(1/n2), its (scaled) length is not
distorted by more than (1 (cid:1) (cid:1)). The theorem then follows from a union bound.

Hence the aim is to estimate the length of a unit vector in Rd when it is projected onto
a random k-dimensional subspace. However, this length has the same distribution as the
length of a random unit vector projected down onto a ﬁxed k-dimensional subspace. Here
we take this subspace to be the space spanned by the ﬁrst k coordinate vectors, for
simplicity.

Let X1, . . . , Xd be d independent Gaussian N(0, 1) random variables, and let
Y(cid:2) 1
(cid:1)X(cid:1) (cid:7)X1, . . . , Xd(cid:8). It is easy to see that Y is a point chosen uniformly at random from
the surface of the d-dimensional sphere Sd(cid:4)1. Let the vector Z (cid:1) Rk be the projection of
Y onto its ﬁrst k coordinates, and let L (cid:2) (cid:1)Z(cid:1)2. Clearly the expected squared length of Z



<!-- pdf-page: 3 -->
62

DASGUPTA AND GUPTA

is (cid:6) (cid:2) E[L] (cid:2) k/d. The following lemma shows that L is also fairly tightly concentrated
around (cid:6).

Lemma 2.2. Let k (cid:3) d. Then

a. If (cid:7) (cid:3) 1, then

b. If (cid:7) (cid:9) 1, then

Pr(cid:2)L (cid:4)
Pr(cid:2)L (cid:2)

(cid:3) (cid:4) (cid:7)k/ 2(cid:4)1 (cid:5)
(cid:3) (cid:4) (cid:7)k/ 2(cid:4)1 (cid:5)

(cid:7)k
d

(cid:7)k
d

(cid:7)1 (cid:3) (cid:7)(cid:8)k

(cid:7)d (cid:3) k(cid:8) (cid:5)(cid:7)d(cid:4)k(cid:8)/ 2
(cid:7)d (cid:3) k(cid:8) (cid:5)(cid:7)d(cid:4)k(cid:8)/ 2

(cid:7)1 (cid:3) (cid:7)(cid:8)k

2

(cid:4) exp(cid:4)k
(cid:4) exp(cid:4)k

2

(cid:7)1 (cid:3) (cid:7)(cid:5) ln (cid:7)(cid:8)(cid:5).
(cid:7)1 (cid:3) (cid:7)(cid:5) ln (cid:7)(cid:8)(cid:5).

Before we prove this lemma, let us see how it implies Theorem 2.1.

Proof of Theorem 2.1.
subspace S, and let v(cid:10)
(cid:1)2 and (cid:6) (cid:2) (k/d)(cid:1)vi
v(cid:10)
j

If d (cid:4) k, the theorem is trivial. Else take a random k-dimensional
(cid:4)

(cid:1) V into S. Then, setting L (cid:2) (cid:1)v(cid:10)
i

i be the projection of point vi

(cid:4) vj

(cid:1)2 and applying Lemma 2.2(a), we get that

Pr(cid:11)L (cid:4) (cid:7)1 (cid:3) (cid:1)(cid:8)(cid:6)(cid:12) (cid:4) exp(cid:4)k
(cid:4) exp(cid:4)k

2

(cid:7)1 (cid:3) (cid:7)1 (cid:3) (cid:1)(cid:8) (cid:5) ln(cid:7)1 (cid:3) (cid:1)(cid:8)(cid:8)(cid:5)
(cid:5)(cid:5)(cid:5) (cid:8) exp(cid:4)(cid:4)
(cid:4)(cid:1)(cid:3)(cid:4)(cid:1)(cid:5)

(cid:1)2

2

2

(cid:5)

k(cid:1)2
4

(cid:4) exp(cid:7)(cid:4)2 ln n(cid:8) (cid:8) 1/n2,

where, in the second line, we have used the inequality ln(1 (cid:4) x) (cid:4) (cid:4)x (cid:4) x2/ 2, valid
for all 0 (cid:4) x (cid:3) 1.

Similarly, we can apply Lemma 2.2(b) and the inequality ln(1 (cid:5) x) (cid:4) x (cid:4) x2/ 2 (cid:5)

x3/3 (which is valid for all x (cid:2) 0) to get

Pr(cid:11)L (cid:2) (cid:7)1 (cid:5) (cid:1)(cid:8)(cid:6)(cid:12) (cid:4) exp(cid:4)k
(cid:4) exp(cid:4)k

2

2

(cid:7)1 (cid:3) (cid:7)1 (cid:5) (cid:1)(cid:8) (cid:5) ln(cid:7)1 (cid:5) (cid:1)(cid:8)(cid:8)(cid:5)
(cid:4)(cid:4)(cid:1)(cid:5)(cid:4)(cid:1)(cid:3)

(cid:5)

(cid:1)2

(cid:1)3

2

3

(cid:5)(cid:5)(cid:5) (cid:8) exp(cid:4)(cid:4)

k(cid:7)(cid:1)2/2 (cid:3) (cid:1)3/3(cid:8)
2

(cid:5)

(cid:4) exp(cid:7)(cid:4)2 ln n(cid:8) (cid:8)

1
n2 .

Now set the map f(vi) (cid:2) ((cid:13)d/k)v(cid:10)

i. By the above calculations, for some ﬁxed pair i,
j, the chance that the distortion (cid:1) f(vi) (cid:4) f(vj)(cid:1)2/(cid:1)vi
(cid:1)2 does not lie in the range [(1 (cid:4)
(cid:1)), (1 (cid:5) (cid:1))] is at most 2/n2. Using the trivial union bound, the chance that some pair of
n) (cid:14) 2/n2 (cid:2) 1 (cid:4) 1/n. Hence f has the desired
points suffers a large distortion is at most (2
properties with probability at least 1/n. Repeating this projection O(n) times can boost the
success probability to the desired constant, giving us the claimed randomized polynomial
time algorithm.
(cid:1)

(cid:4) vj



<!-- pdf-page: 4 -->
ELEMENTARY PROOF OF JOHNSON AND LINDENSTRAUSS

63

To ﬁnish off, let us prove Lemma 2.2. The proof uses by now standard techniques used

for proving large deviation bounds on sums of random variables [4, 9].

Proof of Lemma 2.2(a). We use the easily-proved fact that if X (cid:15) N(0, 1), then E[esX2
(cid:2) 1/(cid:13)1 (cid:4) 2s, for (cid:4)(cid:16) (cid:3) s (cid:3) 1
2 . We now prove that

]

Pr(cid:11)d(cid:7)X1

2 (cid:5) · · · (cid:5) Xk

2(cid:8) (cid:4) k(cid:7)(cid:7)X1

2 (cid:5) · · · (cid:5) Xd

2(cid:8)(cid:12) (cid:4) (cid:7)k/2(cid:4)1 (cid:5)

(cid:5)(cid:7)d(cid:4)k(cid:8)/2

.

k(cid:7)1 (cid:3) (cid:7)(cid:8)
d (cid:3) k

(2.2)

Note that this is just another way of stating Lemma 2.2(a). However, this can be shown
by the following algebraic manipulations:

Pr(cid:11)d(cid:7)X1

2 (cid:5) · · · (cid:5) Xk

2(cid:8) (cid:4) k(cid:7)(cid:7)X1

2 (cid:5) · · · (cid:5) Xd

2(cid:8)(cid:12)

(cid:2) Pr(cid:11)k(cid:7)(cid:7)X1

2 (cid:5) · · · (cid:5) Xd

2(cid:8) (cid:3) d(cid:7)X1

2 (cid:5) · · · (cid:5) Xk

2(cid:8) (cid:2) 0(cid:12)

(cid:2) Pr(cid:11)exp(cid:17)t(cid:7)k(cid:7)(cid:7)X1

2 (cid:5) · · · (cid:5) Xd

2(cid:8) (cid:3) d(cid:7)X1

2 (cid:5) · · · (cid:5) Xk

2(cid:8)(cid:8)(cid:18) (cid:2) 1(cid:12)

(cid:7)for t (cid:9) 0(cid:8)

(cid:4) E(cid:11)exp(cid:17)t(cid:7)k(cid:7)(cid:7)X1

2 (cid:5) · · · (cid:5) Xd

2(cid:8) (cid:3) d(cid:7)X1

2 (cid:5) · · · (cid:5) Xk

2(cid:8)(cid:8)(cid:18)(cid:12)

(cid:7)by Markov’s inequality(cid:8)

(cid:2) E(cid:11)exp(cid:17)tk(cid:7)X2(cid:18)(cid:12)(cid:7)d(cid:4)k(cid:8)E(cid:11)exp(cid:17)t(cid:7)k(cid:7)(cid:3) d(cid:8)X2(cid:18)(cid:12)k

(cid:7)where X (cid:6) N(cid:7)0, 1(cid:8)(cid:8)

(cid:2) (cid:7)1 (cid:3) 2tk(cid:7)(cid:8)(cid:4)(cid:7)d(cid:4)k(cid:8)/2(cid:7)1 (cid:3) 2t(cid:7)k(cid:7)(cid:3) d(cid:8)(cid:8)(cid:4)k/2.

We will refer to this last expression as g(t). The last line of the derivation gives us the
2 and t(k(cid:7) (cid:4) d) (cid:3) 1
additional constraints that tk(cid:7) (cid:3) 1
2 . The latter constraint is subsumed
by the former (since t (cid:2) 0), and so 0 (cid:3) t (cid:3) 1/ 2k(cid:7). Now, to minimize g(t), we maximize

f(cid:7)t(cid:8) (cid:8) (cid:7)1 (cid:3) 2tk(cid:7)(cid:8)(cid:7)d(cid:4)k(cid:8)(cid:7)1 (cid:3) 2t(cid:7)k(cid:7) (cid:3) d(cid:8)(cid:8)k

in the interval 0 (cid:3) t (cid:3) 1/ 2k(cid:7). Differentiating f, we get that the maximum is achieved
at

(cid:8)

t0

(cid:7)1 (cid:3) (cid:7)(cid:8)
2(cid:7)(cid:7)d (cid:3) k(cid:7)(cid:8) ,

which lies in the permitted range (0, 1/ 2k(cid:7)). Hence we have

(cid:8) (cid:8)(cid:4) d (cid:3) k

(cid:7)(cid:5) k
d (cid:3) k(cid:7)(cid:5) d(cid:4)k(cid:4) 1

f(cid:7)t0

and the fact that g(t0) (cid:2) 1/(cid:13)f(t0) proves the inequality (2.2).

(cid:1)

Proof of Lemma 2.2(b). The proof is almost exactly the same as that of Lemma 2.2(a).
The same calculations show

Pr(cid:11)d(cid:7)X1

2 (cid:5) · · · (cid:5) Xk

2(cid:8) (cid:2) k(cid:7)(cid:7)X1

2 (cid:5) · · · (cid:5) Xd

2(cid:8)(cid:12)
(cid:4) (cid:7)1 (cid:5) 2tk(cid:7)(cid:8)(cid:4)(cid:7)d(cid:4)k(cid:8)/2(cid:7)1 (cid:5) 2t(cid:7)k(cid:7)(cid:3) d(cid:8)(cid:8)(cid:4)k/2 (cid:8) g(cid:7)(cid:4)t(cid:8)



<!-- pdf-page: 5 -->
64

DASGUPTA AND GUPTA

for 0 (cid:3) t (cid:3) 1/ 2(d (cid:4) k(cid:7)). But this is minimized at (cid:4)t0, where t0 is as deﬁned in the
previous proof. This does lie in the desired range (0, 1/ 2(d (cid:4) k(cid:7))) for (cid:7) (cid:9) 1, which
gives us that

Pr(cid:11)d(cid:7)X1

2 (cid:5) · · · (cid:5) Xk

2(cid:8) (cid:2) k(cid:7)(cid:7)X1

2 (cid:5) · · · (cid:5) Xd

2(cid:8)(cid:12) (cid:4) (cid:7)k/2(cid:4)1 (cid:5)

(cid:5)(cid:7)d(cid:4)k(cid:8)/2

.

k(cid:7)1 (cid:3) (cid:7)(cid:8)
d (cid:3) k

(cid:1)

3. DISCUSSION

The reader may ﬁnd it interesting to compare the results of this paper with the alternate
proofs given by Indyk and Motwani in [12], and by Achlioptas in [2].

The algorithm in former paper does not choose a random k-dimensional subspace per
se; it instead picks k independent random vectors {Ui}i(cid:2)1
from the d-dimensional normal
distribution (with the unit covariance matrix), and sets the i-th coordinate of the map f( x)
(cid:19)Ui, x(cid:20). The proof follows by formalizing the intuition that these random vectors
to be 1
(cid:7)d
are almost orthogonal to each other, and hence this mapping is almost the same as
projecting onto a random k-dimensional subspace.

k

The statement in [12] analogous to our Lemma 2.2 is somewhat weaker in the sense
that the lower bound for k contains some lower order terms, as a result of which one has
to assume a lower bound for k larger by an additive factor of roughly O(log log n).
However, their algorithm is substantially simpler, since it just has to populate all the
entries of a k (cid:14) d matrix A by independent N(0, 1) random variables, whereupon the
images of x (cid:1) V are given by f(x)(cid:2) 1
(Ax).
(cid:7)d

The latter paper [2] takes this idea even further and shows that, instead of using
Gaussians, one can pick the entries of A to be uniformly and independently drawn from
{1, (cid:4)1}. With a tighter analysis than that of [12], this paper gives the same bound for k
as Theorem 2.1.

REFERENCES

[1] N. Alon, Problems and results in extremal combinatorics, Part I, unpublished manuscript.
[2] D. Achlioptas, Database friendly random projections, Proc 20th ACM Symp Principles of

Database Systems, Santa Barbara, CA, 2001, 274 –281.

[3] R. I. Arriaga and S. Vempala, An algorithmic theory of learning: Robust concepts and random
projection, Proc 40th Annu IEEE Symp Foundations of Computer Science, New York, NY,
1999, pp. 616 – 623.

[4] H. Chernoff, A measure of asymptotic efﬁciency for tests of a hypothesis based on the sum of

observations, Ann Math Stat 23 (1952), 493–507.

[5] S. Dasgupta, Learning mixtures of Gaussians, Proc 40th Annu IEEE Symp Foundations of

Computer Science, New York, NY, 1999, pp. 634 – 644.

[6] L. Engebretsen, P. Indyk, and R. O’Donnell, Derandomized dimensionality reduction with
applications, Proc 13th Annu ACM SIAM Symp Discrete Algorithms, San Francisco, CA,
2002, pp. 705–712.



<!-- pdf-page: 6 -->
ELEMENTARY PROOF OF JOHNSON AND LINDENSTRAUSS

65

[7] P. Frankl and H. Maehara, The Johnson-Lindenstrauss lemma and the sphericity of some

graphs, J Combin Theory Ser B 44(3) (1988), 355–362.

[8] P. Frankl and H. Maehara, Some geometric applications of the beta distribution, Ann Inst Stat

Math 42(3) (1990), 463– 474.

[9] W. Hoeffding, Probability inequalities for sums of bounded random variables, J Am Stat Assoc

58 (1963), 13–30.

[10] P. Indyk and R. Motwani, Approximate nearest neighbors: Towards removing the curse of
dimensionality, Proc 30th Annu ACM Symp Theory of Computing, Dallas, TX, 1998, pp.
604 – 613.

[11] W. B. Johnson and J. Lindenstrauss, Extensions of Lipschitz maps into a Hilbert space,

Contemp Math 26 (1984), 189 –206.

[12] N. Linial, F. London, and Y. Rabinovich, The geometry of graphs and some of its algorithmic
applications, Combinatorica 15(2) (1995), 215–245 (preliminary version in 35th Annu Symp
Foundations of Computer Science, 1994, pp. 577–591).

[13] D. Sivakumar, Algorithmic derandomization using complexity theory, Proc 34th Annu ACM

Symp Theory of Computing, Montre´al, Canada, 2002, pp. 619 – 626.


