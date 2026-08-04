<!-- generated-by: proofmatch local extraction -->
<!-- source-pdf-sha256: 24e94ad30862bd5bfdcf7bc92b779a2cf08729fe673e43ecda7378fe593c36f6 -->
<!-- extractor: tesseract OCR at 300dpi (PDF is an image scan with no text layer); SELECTIVE: pp.18-26 (§3.3.1 Elias, §3.3.2 linear-programming bound, §4.1.1 eigenmatrices & Krawtchouk polynomials) of 54 -->

<!-- pdf-page: 18 -->
— 2% —

matrices D, of the R, by eqs (3.3) and (3.4), respectively:
a, = |¥|~* dy7 Di oy, (3.3)

B= [Do $y, D, $y, «.-, Da dy]. (3.4)

Clearly, a is obtained from B by the formula a = | Y|~! ¢y7 B. The next three
results give, for the association schemes, more interesting relations between a
and B.

Theorem 3.1, Let (X,R) be an association scheme and let Y be a subset of XY.
Then the inner and outer distributions of Y with respect to R satisfy

BT B=|X|-*|Y|P4,,P, (3.5)
where P and Q are the eigenmatrices ofthe scheme and 4, is defined as in
(2.20), ;

Proof. For ij N, let us calculate the (ij)-entry of B7 B from (3.4). Using
(2.5) and (3,3) we readily obtain, for R, = R,-!:

(BT B) (ij) = dy" D,” D, dy ;
= [YS as ay. (3.6)

Defining b= aQ, we have |X/a= bP, by (2.15). Hence (3.6) becomes,
according to (2.19):

(BT B) ij) = [X14 |¥| Eb, PAG) PA.
Since P,(u) = P,*(u) for R, = R,~1, this is exactly the desired formula (3.5).

Corollary 3.2. The rank of the matrix B is equal to the number of nonzero
components of aQ.

Proof. Since P is nonsingular we have, by (3.5), rank (B) == rank (BT B) =
rank (4,4), from which the corollary follows.

Theorem 3,3, The components aQ, of the row vector 2Q are nonnegative
real numbers. Moreover, for a given k, the component aQ, is zero if and
only if B Q, is the zero vector.

Proof. Multiplying both members of (3.5) to the left by @ and to the right
by Q we obtain 0 B7 BQ =|X||Y¥| 4,,, by (2.15). Equality between the
corresponding diagonal entries can be written as follows:

|B Qal]? = {X]]¥] a O,, VkeN, (3.7)

where || |{ stands for the Hermitian norm. This clearly leads to the conclu-’
sions of the theorem.

—2

Remark. The inequalities aQ, > 0, wl
this work, can be derived in a more dir
(2.9) and (2.16) we obtain

a Oy = |X| |¥|~* dy? J

for an orthogonal matrix S diagonaliz
obviously imply aQ, > 0. Together v
given k, the following four equations a:
fied;

aQ,=0, BQ,=0,

3.2. Linear programming
The conditions aQ, > 0 suggest usi
the study of subsets Y S X whose spe
tions (or inequalities) satisfied by the
“cliques” and “designs” examined in s
First, we shall recall some well-kno
(cf. Simonnard **)), with notations ada
be a matrix of R(N,N) such that Ao/(
On the other hand, let M be a subset of /
Thon we define the linear-programming
variables b,, i¢ M*, and n inequalities,
x b, A,(i

(aM
(4,M) b, 20

maxim

An (n + 1)-tuple b = (bo, 1, .. «5 By) i
fies (3,9) and (3.10) with bp = 1 and
(1, 0, ..., 0) is a program with g = |

In our applications, the set of progra
3.5); equivalently, it will be a convex pc
at least one maximal program, i.o. a pro
mal. We shall denote by g(4,M) the ms
grams. (Clearly, g(4,M) = 1.)

It is useful to examine the dual problen
Bu ke N*, and m inequalities:

<!-- pdf-page: 19 -->
— 28 ~

x 6, Afi) <0, ie M*, (3.12)
wan
(A,M)y’ Br = 0, keN*, (3.13)
minimize y = 2 By Ay (0). (3.14)
An (n + I}-tuple B = (fo, By, ..., By) is a program of (A,M)' if it satisfies

(3.12) and (3.13) with Bo = 1; it is a minimal program if, besides, it gives the
smallest value to the function y.

The most important theoretical results about duality in linear programming
can be summarized as follows, in the case of a bounded set of programs of
(A.M):

Theorem 3.4. (i) The problems (4,M) and (4,M)’ admit at least one extremal
program (i.e. a maximal and a minimal program, respectively). Each pair of

programs b of (4,M) and B of (4,M)’ satisfies g < y. Moreover, the extremal

values of g and y are equal.
(ii) For each pair (b,B) of extremal programs, the following two sets of equa-
tions hold; ‘ ‘

of Py by Axo ) =0, WkeN*, (3.15)

of = Be 4x) =0, VieM*, (3.16)

Conversely, if a pair (b,8) of programs satisfies (3.15) and (3,16), then it is a
pair of extremal programs.

To conclude this section, let us give two results about the problems (4,4)
and (4,M) when A is taken to be one of the eigenmatrices, P or Q, of a
symmetric association scheme with n classes.

Lemma 3.5, The set of programs of (P,M) is bounded by b, < 4, and the one
of (Q,M) by b, <»,, for all ie M.
Proof. We shall prove the second part. From (2.15) we readily obtain the fol-
lowing identity, for an arbitrary (n + 1)-tuple b:

x (%— P,(k)) 2 b, QC) = |x| (bo 1: — i).

By (2.29) and (3.9) the left-hand member is nonnegative when b is a program
of (Q,M). Hence, with by = 1, we deduce b, < 4. \

Lemma 3.6. Each minimal program PB of (P,M)’ satisfies 8, < 1 for all je N.

— 2

Moreover, it satisfies 8, = 1 for a give
tions holds, for every maximal progra)

Pus af x by P(e) |

The same proposition remains valid w
a4.

Proof. Let b and B be two extremal pr
tively. By use of (3.14) and (3.16), with.

yoy yo >
= ir

1%
according to (2.19). Since b is a m
Db, = g=y. Hence, using p,,, =

yy a— 8) = y;

GAG

As each term of the right-hand sum i
yields the desired results about (P,M)
(Q,M)’; it is essentially based on lem

3.3, Cliques in association schemes
Let R = {R,| fe N} be a family of

A’2 (sec. 2.1) and let M be a subset of

Y¥ of X will be called an M-clique with

RNY? =,

ie, equivalently, if any two points ¢
The main problem we shall now con
number of points in M-cliques.

3.3.1. The Elias theorem

In this section, all relations R, are
not necessarily is an association sche
mation about cliques Y = X from res
of X. Essentially, the argument is du
bound in coding theory (cf. Berlekax

<!-- pdf-page: 20 -->
— 30 —

Let L be a nonempty subset of NV, Then, for a point ee X, we define a sub-
set C,(e) of X as follows:

Ci(e) = U {zEX| (e,z) € Ri}.

This could be called a crown of centre e. By assumption, the cardinality of C,(e)
is independent of e: if v, denotes the valence of R,, then

[CLO] = Z %. (3.18)
feL

Theorem 3.7. Let L and M be subsets of N, with Oc M. If Y is an M-clique
with respect to R, then there exists a crown X’ = C,(e) and an M-clique
Y' & X’ satisfying |X|“? |Y| <|X'1-" ||’.
Proof. Let us first establish the following identity, for an arbitrary subset Y
of X:
DYN Cyd] =|¥| Bm. (3.19)
wex teL

The left-hand member is the number of pairs (x,y) with x eX, ye Y, y € Cz(x).
The relations R, being symmetric, condition y € C,(x) is equivalent to
x €C,(y). Hence the number of pairs to be counted is equal to the sum of
|C.()| for y running through Y, that is, by (3.18), to the right-hand member
of (3.19).

Next, from (3.19) we immediately deduce

|X} max [YO C,(x)| >{¥] Dv (3.20)
wax ieL

Let us choose a point ee X for which | ¥ A C,(e)| is maximal and define
X' = Cx(e), Y' = YOX". Then (3.20) becomes |X| | ¥’| = |¥| [X’|. Since ¥
obviously is an M-clique whenever Y itself is an M-clique, this proves the
theorem.

Example. Let (F*,R) = H(n,2) be the Hamming scheme of length n over a
set F of two elements (cf. sec. 2.5). For some integer n', with 1 <n! < n/2,
we define L == {n'}; then the crown C;,(e) is a sphere of centre ¢ and radius n’
in the Hamming metric space. The nonempty restrictions of the distance rela-
tions R, to the sphere X’ = C,(e) are the following subsets of (X")?:

Ry = (EX) | duly’) = 4}, f= 0,1,..., 0"

It can be shown that (X’,{R,’}) is an association scheme, with n' classes, which,
up to isomorphism, is independent of the centre e; this scheme will be examined
in detail in sec. 4.2 under the name of Johnson scheme, with the notation,
J(n'n). At the present, we only want to emphasize theorem 3.7: it shows how

— 31

upper bounds to the cardinality of clique
bounds of the same type for the Hamm

3.3.2. The linear-programming bound

It is obvious, by (3.1) and (3.17), thi
terms of its inner distribution a by the

a,=0, Vv

Henceforth we assume (X,R) to be a
theorem 3.3 implies a strong necessary
M-clique; in the terminology of sec. 3.

Theorem 3.8. Let Q be the second eis
scheme. Then the inner distribution of
program of (Q,M) such that g = |Y|.
Proof. This is an immediate consequen
aQ, > 0 of theorem 3.3 and the obviot
fied by the inner distribution a.

Since, by lemma 3.5, the programs of {
g(Q,M) of g is well defined and theore:

lY| <e

for every M-clique Y with respect to
linear-programming bound for cliques. Th
for discussion of M-cliques achieving tt

Example. Let us apply (3.22) to the sir
regular graphs (cf. sec. 2.4), For n = 2
M-clique with respect to R = {Ro, Ri,
clique (== complete subgraph) in the st
to the reader to verify, by use of (2.30
(3.22) for such cliques is

|¥|<1+

Let us also check theorem 3,4. We
a = (1, 0, —v,/s,42) are programs of |
fying (3.15) and (3.16) with A = Q. I
has g = y = 1— v,/s, for these extren

To conclude this section about cliqu
quence of theorems 3.4 and 3.8, showi

<!-- pdf-page: 21 -->
ro

—32—

Theorem 3.9. Let M be a subset of N, with 0 ¢ M, and let M@ = N— M*. If Yis
an M-clique and Z an M-clique in an association scheme, then | Y||Z| < ||
holds,

Proof. Let b and c be the inner distributions of Y and Z, respectively. Then
from the eigenmatrix Q and the multiplicities 4, we define real numbers
Bo, «++» By a& follows:

Be = ((2Z| pa)-* x cy Qx()). (3.24)

Clearly (cf. for instance theorem 3.8), the 6, are nonnegative with Bo = 1.
On the other hand, using (2.22) we readily obtain

x Bx Qn(i) = [Z| |X] 117" cy, (3.25)

with v, = valence of R,. Since Z is an M-clique, ¢, is zero for each i in M*.
Therefore, (3.25) shows that B is a program of (Q,M)’, the conditions (3.12)
being satisfied with equality.

Next, we observe that b is a program of (Q,M) with g =|Y|, by theorem
3.8. Hence the inequality g < y for the programs b, 8 becomes

ivl< 2 Bs Q(0) = |2Z|-* |x|, (3.26)
according to (3.25) with i = 0, and the theorem is proved.

Certain classical inequalities of coding theory can be derived from theorem
2.9, for instance the Hamming bound (cf. secs 4.3.3 and 5.2.2), The interesting
point about the linear-programming method is the fact that it also gives neces-
sary conditions on the distributions b, ¢ for pairs (Y = M-clique, Z = M-clique)
satisfying equality in (3.26). Indeed, the reasoning has shown that equality
holds if and only if (b,8) is a pair of extremal programs. Hence theorem 3.4(ii)
with A = Q, when applied to this pair, yields, by (3.24):

(Eb, Ox) (Z ey Ox) = 0,

These conditions (to be compared with 5, c, = 0) could be very useful in a
study of pairs (Y,Z) achieving the bound of theorem 3.9; they would lead, for
instance, to the Lloyd theorem on perfect codes (cf. sec, 5.2.2),

k=1,...,"

3.4. Designs in association schemes

Let (X,R) be a symmetric association scheme with n classes and let T be any
subset of N* = {1, 2,..., }. Then a nonempty subset Y of X will be called
a T-design with respect to R if its inner distribution a satisfies

Ea, Q()=0, Ve. (3.27)

where Q is the second eigeomatrix of the scheme. In other words, a T-design

— 33

has the following extremal properties |
conditions aQ, > 0 of theorem 3.3 hol

In general, we can give no clear “con
cept of T-design. However, as we shal
Hamming and Johnson schemes are ar
configurations. This motivates the prese
being that T-designs will often have inter
the formal duality between the notions
(3.21) and (3,27)). This duality will apr

Several equivalent forms of the con
in sec, 3,1. One of them leads to the f

Theorem 3.10. Let Jo, Ji, ..-, Iq b
Bose-Mesner algebra of (X,R). Then a :
if J, dy = 0 holds for each k in T.
Proof. The defining equations of a 7
according to (3.8), the condition aQ,
ie. to Jy dy = 0, since J, is positive
proved.

The condition ¢y7 J, dy = 0 (Vke!
pared with the definition dy" D, ¢y =
analogy to sec. 3.2.2, let us now app
order to obtain a lower bound to the

Theorem 3.11. Let Y be a T-design in «
P and Q. If a denotes the inner distrit

b=17|

is a program of (P, N—T) such that ;
Proof. From (2.15) and (3.28) we deduci
bP, > 0 for all k. On the other hand,
of b are nonnegative, by theorem 3.3.
of (P, N—T). Finally, for this proj
which concludes the proof.

According to lemma 3.5, the prograi
maximal value g(P,M) of g is well defis
programming bound for designs:

|¥| > |X |/s
Example, Let us examine the combinat

<!-- pdf-page: 22 -->
— 34 —

regular graph (X,R,) and apply the linear-programming bound in this simple
case (cf. sec. 2.4), Let {Y,Z} be a bipartition of X such that (Y,R, 9 ¥?) and
(Z,R, © Z?) are regular subgraphs of (X,R,), and assume the valences satisfy
val (R, © Y2) + val (R, © Z?) > val (R,). Then {Y¥,Z} will be called a
regular bipartition.

On the other hand, for 7 = {2}, we consider the 7-designs Y (# X) in the
association scheme (X,R) with R = {Ro, Ry, R2}. It is not difficult to show
that these two concepts are equivalent: Y is a T-design if and only if {Y, ¥— Y}
is a regular bipartition of X.

Using (2.30) we easily obtain the maximal value of g for the problem (P,M)
with M = {0,1}; the result is g(P,M) = 1— v,/r,. Hence, using the identity
(0, — 5) (v2 — rz) = U5, rg, We can write (3.29) as follows:

[P| 21 + of—54). (3.30)

It turns out that the (unique) maximal program b of (P,M) satisfies bP, = 0,
Therefore, if a regular bipartition {Y, X-- Y} achieves (3,30), then the inner
distribution of Y is a = (J, —,/s;, 0), i.e., equivalently, Y is a clique in the
graph (X,R,) achieving the linear-programming bound (3.23).

Remark, The definition of T-designs in a symmetric association scheme (X,R)
can be extended so as to admit the possibility of “repeated points”. Let us
briefly outline this generalization. For a nonzero vector ¢ € R(X) with inte-
gral nonnegative components ¢(x), we define the distribution of ¢ to be the
(n + 1)-tuple a = (ao, a1, ..., @,) of rational numbers a, given by

a, = ($7 4)-* (¢" Dy 9), (3.31)

where D, is the adjacency matrix of R,. In particular, when all components
(x) are O or 1, this is exactly the concept of the inner distribution (3.3) for the
subset Y & X such that ¢y = ¢. For any ¢, the same argument as the one
leading to (3.8) shows that the numbers aQ, are nonnegative when a is de-
fined by (3.31).

Given a subset 7 of N*, the vector ¢ will be called a 7-design if its distri-
bution a satisfies (3.27). In the case ¢ = ¢y for some subset Y & X, the de-
sign is said to be simple (without repeated points). In the general case, consid-
ering ¢(x) as “the number of occurrences of a point x in the design”, one is
interested in the total number of points, i.e, the integer A = $7 dx.

Given a T-design ¢ of distribution a, it is not difficult to show, like in
theorem 3.11, that the (# +-1)-tuple b = h7? (47 4) aQ is a program of
(P, N—T) with g = h-* (47 4) |X|. It follows that the linear-programming
bound (3.29) is valid in the general case when |Y| is replaced by h. Indeed
we can write :

heh? (GT 6"? > [X[/eP, N— 1);

— 35

the right-hand inequality is simply g
inequality, it follows from the obviou
consequence, we observe that a T-desi
bound, i.e. A = |X|/g(P, N— 7), must
alently, ¢ must be simple.

3.5. Characteristic matrices

For an association scheme (X,R) with
onal matrix diagonalizing the Boso-M:
be the classes of the partition (X’,S)
subset Y of X, we shall denote by H, tt
of XxX". In particular, Ho is the all-o
characteristic matrices of Y, will be a
some T-designs (see sec, 5.3). We now §
an equivalent formulation of theorem |

Theorem 3.12. Let Ho, Hi,-. +, H, be |
of X for a symmetric association sche
respect to R if and only if H,7? Hy =

Next, we shall derive some formul:
A, Hy. We use the notation D,| Y for
for the restriction of D, to Y?. For the
ch. 1.

Theorem 3.13. The characteristic matri
adjacency matrices D,| Y are related |

H, A, = %

Proof. This is an immediate consequet
matrix Q since, by (2.9), Hy ff, is the

Lemma 3.14, Let a be the inner dist
matrices of Y satisfy

(4. Aull? = 171 x 92

Proof. Let us substitute $y for ¢ in th
diately the desired result by using (3.8)
of S, to YxX/’.

Theorem 3.15. For given integers i, t €
satisfies 9,,°%(a Q.) = 0 for k= 1, 2

<!-- pdf-page: 23 -->
— 36 —

holds, for Q, = Q,*:
0 if ix),

fA, H, = { 3.34,

ee  Uypr if ies. (34)
Conversely, (3.34) implies q,,-(a Q,) = 0 for Q, = Q,* and all k > 1.
Proof. Assuming q,,,""(a Qx) = 0 for k = 1, 2,..., ”, we can write (3.33) as
follows, using (2.27):

This proves (3.34) for ij. Let us now examine the case i = j. By theorem
3.13 we have tr (ff, H,) = tr (H, A,) = a, |¥|. It is easily seen that this,
together with (3.35), implies ||A, H,—|Y¥|Z|| =0 and, consequently,

In order to prove the converse result, we first observe that all terms
11a Q,) of the sum Lin (3.33) are nonnegative real numbers, by lemma 2.4
and theorem 3.3. On the other hand, condition (3.34) exactly means that
reduces to its term |¥| 4, 6,,, of index k = 0. Hence all terms with k > 1
must be zero whenever (3.34) is satisfied.

To conclude this section let us indicate, without proof, how the distribution
matrix B introduced in sec. 3.1 can be expressed in terms of the matrices S, P
and H;,; it is given by

B= |X|"! S (Ao Ho ® A, Ho ©... OA, Ho) P,

where ® stands for the direct sum. This equation, together with (3.8), could
be used to give another proof of theorem 3.1.

— 31
4. AN INTRODUCTION TO AI

In the present chapter we shall exami
spaces having the structure of associatio
the Johnson schemes, which we already
appear to be the natural frameworks fc
combinatorial aspects.

4.1, The Hamming schemes

Let F be a finite set of cardinality q
We make the nth Cartesian power X =
Hamming distance dy(x,y) between tw
(1s +++ Ya) OF X as follows:

dy(x,y) = | 1 <

In other words, the distance between tv
places in which they differ. Next, we

..., R, in an obvious way; two points
are at distance /:

R, = {(x,y) eX?

It is easy to show, by verification of tl
association scheme for R == {Ro, Ry, .
result is implicitly contained in the ar,
and q, we call (X,R) the Hamming schen
H(n,q).

4.1.1. Eig ices and Kr houk po

Let us provide F with the structure of :
We shall use an additive notation for th
bol 0 (zero) for the identity. The Hammil
X = F* then by definition is the num!
This allows to write (4.1) as follows:

dyf x,y) = Wal —

Consequently, the distance relations (4.2
ice, they satisfy (2.43), and it is well kno’
ters of X diagonalizes the Bose~Mesner :
this more closely in order to obtain an |

Let (a,8) t+ (a,B> be an inner prods
mapping of F? into C such that, wh
B + (a,6> runs through the group of co

<!-- pdf-page: 24 -->
— 38 —

uct is described more in detail in sec, 6.1. We shall need the following result
(cf. theorem 6.2):

q—-1 for a=0,
xX (ap) = { 4.4)
aes * -1 for aeF*, 44)
with F* = F— {0}, Next, keeping the same notation (x,y), let us extend the
inner product to the group X = F* by defining, for x = (x, ..., %,) and

Y= (Yu oer EX,

(xy) = TT wn, (4.5)
fel

from the inner product <x;,,y,) of the components x,y, ¢ F. It can easily be
verified that (4.5) is then itself an inner product on X; we shall call it the
natural product on X,

Let us briefly apply these notions to the binary case (g = 2), which might
be more familiar to the reader. For «,8 € F = {0,1}, we have (a,B) = (—1)".
Hence the natural product of two binary n-tuples x and y can be written as
<x,y) = (—1)*"), where [x,y] = x11 +... + %e%s (mod 2) is the scalar prod-
uct of x and y considered as vectors over the binary field. ;

We now go back to an arbitrary g 22 and define the weight partition
o = {Xo, Xi, ..., Xa} to be formed by the classes of elements having a con-
stant weight:

X, = (xeX| mals) =k}, kK =0,1,...,m (4.6)

The cardinality of XY, (= valence of R,) is equal to o, = (1) (¢—4)*. On the
other hand, with a normalization adapted to our problem, we introduce the
Krawtchouk polynomials (cf. Szeg5 7°)) as follows: for given m and g, and an
integer kK = 0, 1,..., m, the polynomial

&

Kw = Seay @—ye(“)("™ (4)
i) \eea

Jno
in the indeterminate u, will be called the Krawtchouk polynomial of degree k.
(We use the notation (1) = u(u—1)...(¢—j + Lil.) It is easy to check
that K,(u) actually is a polynomial of degree k in the variable u. This fact
appears even better from an equivalent expression of the Krawtchouk poly-
nomials, the verification of which is left to the reader:

. n—-i\ /u
Kw = Ycora-v'(? “YC
(#0

Before deriving the eigenmatrices of the Hamming scheme (theorem 4.2), we

— 39

give a relation between the concepts intre
partition and Krawtchouk polynomials).

Theorem 4.1, The natural product (4.5) :
telated by the following equation, for u,

ZX <x,x’> == Kylu
waXy

Proof. First, we consider a fixed subset .
we compute the contribution c(J) to th
by the (q — 1)* elements x’ ¢ X, such thi

~ oT]

fey
By (4.4) we see that the number under br:
ing to whether x, is zero or not. Hence
zeto components x, with ie J, we have
On the other hand, the number of ch
is equal to (%) ({3), for wu(x) = u. Ther
obtain exactly the right-hand member o

Theorem 4.2. The eigenmatrices P and |
given in terms of the Krawtchouk poly:
PA) = O.0) = KC),

Moreover, H(n,q) is self-dual with respe
Se C(X,X) defined from the natural pr
Proof. Let us consider the weight part
corresponding submatrices S, ¢ C(X,X;
the following formula for the (x,y)-ent

(S80 Gy) =

According to (4.2) and (4.3), Wa(x — y) i
to R,. Hence, using the incidence matri
follows:

55,=3

On the other hand, the matrices J,
form a set of mutually orthogonal ide

<!-- pdf-page: 25 -->
— 40 —

the J, belong to the BM algebra of the scheme, they are the minimal idem-
potents of it. Comparing (4,10) to the definition (2.16) of the eigenmatrix Q,
we deduce Q,(i) == K,(i) for all i,k.

Finally, with the definitions of sec. 2.6, it can easily be shown that (X,R)
is dual to itself with respect to e = 0 and to S, the partitions «(X,S) and
1(X,e) being both the weight partition o. The details of the argument are
omitted. Then it follows from theorem 2.8 that the eigenmatrices P and Q
are equal, which concludes the proof.

Applying theorem 2.3 to the Hamming scheme H(n,q), we obtain the well-
known orthogonality relations on the Krawtchouk polynomials:

* n n
y. K(0 K,0( "@— i= (") @—1 byw

{#0
for r,s = 0, 1,..., ”. Consequently, the polynomials Ko(u), Ki(u), ..., K,(u)
form “the” family of orthogonal polynomials on the set N = {0, 1,..., m}
with respect to the weight function w defined by w(i) = 9, = 4, = () (q—1)'.
From a classical result about orthogonal polynomials (cf. Szeg6 7°), p. 42),
we deduce the following useful recurrence relation on the K,(u):

(k + 1) Keg 1(e) =
+ Q—D@—K—9u) Ku) —Q—1) @—k + 1) Ky). (4.11)

4.1.2. Codes in Hamming schemes L

A code of length n over an alphabet F by definition is a nonempty subset Y
of X = F" provided with the Hamming distance (4.1). The elements of Y¥ are
called the codewords. The linear-programming bound (3.22) yields an upper
bound to the number of codewords in codes submitted to restrictions of the
following type: the distance between codewords can only assume some specified
values. Indeed, if M is this set of values, such a code is nothing but an M-clique
in the Hamming scheme.

Particular cases, being most important in theory of error detecting or cor-
recting codes, are provided by sets M of the form

M = {0,6,8+1,..., 7}, (4.12)

‘for some integer 6 with 1 <d <n. An M-clique in H(n,g) then is a g-ary

code of length m having the property that the minimum distance between dis-
tinct codewords is at least equal to 4, Since the best code of given parameters
n, q, 6 is the one containing the largest number of words, many authors were
interested in obtaining upper ‘bounds to the number of codewords in such

— 4]

codes. As for the binary case (q = 2),
point of view, let us especially refer to

The numerical values computed up to.
|¥| <g(Q,M) lead to the hope that it \
bounds (cf. also sec. 4.3). McEliece, R
linear-programming bound for codes i
tained more than promising results in
by R. J. McEliece). Unfortunately, a
seems to be out of the question; each cas
ly large values of n, one needs a comp

Before giving an example treatable b;
allows to simplify the computation of
cases, A subset M of N= {0, 1,..-,
it contains only even numbers and odd

(ie M, i=0(mod 2),
(ie M, i=1 (mod 2),

For instance, the set (4.12) is odd whe

Next, let us define the set N’ = {0, |
set M of N we associate the even subs

M' = {ie N’| i=0(mo

It is easy to show that M +> M’ is in|
odd subsets of N and the even subsets
tween cardinalities: m’ = [(m + 1)/2]

Theorem 4.3. Let M be an odd subset ¢
subset (4.13) of NV’. On the other hanc
the Hamming schemes H(n,2) and A(?
2(Q',M’) holds, for q = 2.

Proof. The theorem follows from two
(Q,M), the (1 + 2)-tuple b’ = (b0', . .

bj = {?- a 5,

with b_, == 6,4, = 0, is a program of (
any program b’ of (Q’,Af") the (n + 1

(n—i+ 1).
+ 1) Biya
is a program of (Q,M), satisfying 2b

w+ no—{

<!-- pdf-page: 26 -->
— 42 — — 4

from the properties of Krawtchouk polynomials with q = 2; the details of l 4.1.3. Orthogonal arrays
the argument will not be given. Since the eigenmatrices P and Q of |
It is obvious that such a double correspondence with Lb, = Lb,’ between tical, the problem of codes with a des
the programs of (0,M) and (Q’,M’) suffices to prove that the maximal values i least formally, to the problem of T-desi
of g = Lb, and g’ = ¥b;’ are equal.
T= {1,2,...,%-!
The above result shows that, for g = 2 and an odd subset M of N, we may in particular, the linear-programmii
replace the linear-programming problem (Q,M) by the simpler problem ' |¥| > "/e(Q,M) where M is the set (
(Q’,M’), provided we are only interested in knowing g(Q,M) and at least one In this section it will be shown that s
maximal program of (Q,M). binatorial configurations, namely the ort
On the other hand, for g = 2 and an even subset M’ of N’, we observe the { introduced by Rao 5%).
following: any (n + 2)-tuple b’ such that 5,’ = 0 for all ig N’—M’ satis-
fies b’ Q,’ = b' Q,,1-4’ for all k € N’. Hence the even problem (Q’,M") con- Definition. To a code Y of length n ove
tains in fact only [(m + 1)/2] inequalities b’ QO,’ >0 in the [(m + 1)/2] are the words of Y. Let r and 4 be pc
variables b,'. ‘ said to form an orthogonal array of str
of distinct columns of the array, all r-
Example. Let us examine the binary codes Y of length n = 13 and de- A times. Then, obviously, | ¥| == Ag" hi
signed minimum distance 45 = 5, i.e, the M-cliques in H(13,2) with
M = {0, 5, 6,..., 13}. To the odd subset M of N corresponds the even sub- ; Before showing the equivalence betw
set M’ == {0, 5, 8, 10, 12, 14} of N’. According: to theorem 4.3, the linear- T-design, we need some notations. For
programming bound is | Y] < g(Q’,M’). The inequalities b’ QO,’ > 0 of the i sider a t-tuple (w,, w,..., @,) of syr
problem (Q',M") are the following: .. +) 4) of distinct integers i,, with 1 <
over F we shall denote by m,(w,, ...,
2be =——2be’ =——6byo’ 38610 B,,’ 4 yy’ BS 14, , ; such that
—S be = —Sbe’ +11 big’ +433,’ $9154’ 2 91, °° | x =o, x. =a
, ’ ’ ty ty la
—I2 be’ +126’ +449’ —1005,,' —364b,,' > —364,
9be’ = +9b,’ —39 dio’ +1215,,’ +1001 5,,' 2 —1001, : The above definition means that Y for
30 bg’ —30 bg’ +38 bio’ —22b,,' —~20025,,’ > —2002, ' if and only if the following equation hx
—Sbe’ = —Sby’ +27 bio’ —165b,,' +3003 b,,’ = —3003, Mz(Wty ay «+;
~A0 be’ +40b,’ —72 bio’ 4+-2645,,' —34326,,' > —3432,
for each choice of the w, € F and of L.
the function to be maximized being g’ = 1 +b,’ +... -+ by4’. The easiest ( the structure of an Abelian group.
way for obtaining the coefficients Q,'(i) in the above system is to use the
recurrence relation (4.11) on the Krawtchouk polynomials; this yields Theorem 4.4, For a given set T= {, |
(k + 1) Qna1‘(i) = (14 ~ 22) Oy) — (15 — k) Q- 1/0. { is a 7-design in A(n,q) if and only if it fc
One can solve the problem (Q’,M’) by hand, using the simplex algorithm. Proof. For a t-tuple L = (i,, i,..., 4)
It turns out that there is a unique maximal program, namely b’ = (1, 0, 0, 0, and an integer k, with O << k < 1, we «

9, 0, 42, 0, 7, 0, 14, 0, 0, 0, 0). Hence we deduce 8(Q',M’) = 64. In fact the XL) = {x eX] x = 0
linear-programming bound | Y| < 64 is the best possible since there actually

exists a binary code Y of length 13 and minimum distance 5 containing 64 code- ; where X, is the weight class (4.6) of 2
words; such a code can be derived from the Nordstrom-Robinson code 5%) X,(D)U...UX(L) of these sets is ¢
(cf. also Goethals 2*)). elements x’ satisfying x,’ = 0 for i # i,
