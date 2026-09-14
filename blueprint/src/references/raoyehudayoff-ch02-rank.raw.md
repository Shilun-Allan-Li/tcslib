<!-- generated-by: proofmatch local extraction -->
<!-- source-pdf-sha256: d59395db8359158c43964dec5232f4ca198d78b013f382980a9867f4fd9d47d9 -->
<!-- extractor: pdfminer.six v20260107 -->

<!-- pdf-page: 1 -->
Sometimes it is convenient to use
1)g(i,j) instead.
Mij = (

−

If there the function depends on
the inputs of k parties, the natural
representation is by a k-tensor.

Abusing notation, we shall sometimes
refer to the communication complexity
of M when we really mean to refer to
the communication complexity of the
associated boolean function.

2
Rank

X × Y → {
is the number of rows and n =

Matrices give a powerful way to represent functions that depend
on two inputs. We can represent g :
n
×
matrix M, where m =
is the
number of columns, and the (i, j)’th entry is Mij = g(i, j). Given this
interpretation of g, one can think of the inputs to the parties as unit
column vectors ei, ej. The parties are trying to compute eT
i Mej. This
view allows us to bring in the many tools of linear algebra to bear on
understanding communication complexity.

by an m

|X |

|Y |

0, 1

}

Basic Properties of Rank

The most basic quantity associated with a matrix is its rank. The
rank of a matrix is the maximum size of a set of linearly independent
rows in the matrix. Its versatility stems from the fact that it has many
interpretations:

Fact 2.1. For an m

×

n matrix M, rank(M) = r if and only if:

• r is the smallest number such that M can be expressed as M = AB,

where A is an m

×

r matrix, and B is an r

n matrix.

×

• r is the smallest number such that M can be expressed as the sum of r

matrices of rank 1.

• r is the largest number such that M has r linearly independent columns

(or rows).

A useful property of rank that follows immediately from the

deﬁnitions:

Fact 2.2. If M0 is a submatrix of M, then rank(M0)

rank(M).

≤



<!-- pdf-page: 2 -->
34 communication complexity

Another nice feature of the rank of matrices is that it behaves
nicely under basic matrix operations. Since the rank of M is the
minimum number of rank 1 matrices that add up to M, we get:

Fact 2.3.

rank(A)

|

−

rank(B)

| ≤

rank(A + B)

≤

rank(A) + rank(B).

One consequence of Fact 2.3 is that many different representations
of a matrix are more or less equivalent, when it comes to their rank.
For example, if M is a boolean matrix, one can deﬁne a matrix M0 of
1)Mi,j , replacing 1’s with
the same dimensions, with M0i,j = (
1 and
0’s with 1. Then we see that M0 = J
2M, where J is the all 1’s matrix,
and so

−
−

−

Fact 2.4.

rank(M0)

|

−

rank(M)

| ≤

rank(J) = 1.

Since taking linear combinations of the rows or columns cannot

increase the dimension of their span, we get:

Fact 2.5. rank(AB)

min

{

≤

rank(A), rank(B)

.

The tensor product of an m
nn0 matrix T = M

the mm0 ×
(i, i0), (j, j0), with T(i,i0),(j,j0) = Mi,j ·
the rank, a fact that is very useful for proving lower bounds:

Mi0,j0

}
n0 matrix M0 is
n matrix M and an m0 ×
M0 whose entries are indexed by tuples
. The tensor product multiplies

×
⊗

Fact 2.6. rank(M

M0) = rank(M)

rank(M0).

·
The matrices we are working with are boolean, so one can view

⊗

the entries of the matrix as real numbers, or rationals, or coming
from the ﬁeld of integers modulo 2: F
different notions of rank, but we have:

2. This potentially leads to 3

Lemma 2.7. The real rank of a boolean matrix is the same as its rational
rank. The real rank is always at least as large as the rank over F

2.

The proof of the ﬁrst fact follows from Gaussian elimination. If the
rank over the rationals is r, we can always apply a linear transforma-
tion to the rows using rational coefﬁcients to bring the matrix into
this form:

1 0 0
0 1 0
0 0 1
...
...
...
0 0 0
0 0 0
...
...
...

. . .
. . .
. . .
. . .
. . .
. . .
...

0 M1,r+1
0 M2,r+1
0 M3,r+1
...
1 Mr,r+1
0
...

0
...

. . . M1,n
. . . M2,n
. . . M2,n

. . . Mr,n
. . .
...

0
...

































This transformation does not affect the rank over the reals, and now
it is clear that the rank is exactly r. Now if any set of rows is linearly



<!-- pdf-page: 3 -->
rank 35

dependent over the rationals, then we can ﬁnd an integer linear
dependence between them, and so get a linear dependence over F
This proves that the rank over F
2 is at most the rank over the reals.

2.

Throughout the rest of the book, unless we explicitly state other-

wise, we shall always consider the rank over the reals. One conse-
quence of Lemma 2.7 is:

Lemma 2.8. A boolean matrix of rank r has at most 2r distinct rows, and at
most 2r distinct columns.

Proof. Since the rank over F
expressible as the linear combination of some r rows over F
2. There
are only 2r such linear combinations possible, so there can be at most
2r distinct rows.

2 is also at most r, every row must be

Lower bounds using Rank

Lemma 2.8 immediately gives some bound on the communication
in terms of the rank of the matrix. If the matrix has rank r, it has at
most 2r distinct rows. Alice only needs to communicate which one of
these rows her row corresponds to. This takes r bits of communica-
tion. Bob can then respond with the value of the function. We have
shown:

Theorem 2.9. If a matrix has rank r then its communication complexity is
at most r + 1.

The main reason that rank is useful in this context is that it can
be used to prove lower bounds on communication, via the following
theorem:

Theorem 2.9 is far from the last word on
the subject. By the end of this chapter,
we will prove that the communication is
bounded by a quantity closer to √r.

Lemma 2.10. If a boolean matrix can be partitioned into 2c monochromatic
rectangles, then its rank is at most 2c.

Lemma 2.10 follows easily from Fact 2.1. For every rectangle

×

B, deﬁne the matrix where Ri,j = 1 if (i, j)

R = A
R, and Ri,j = 0
otherwise. Then we see that R a matrix that has rank 1. Moreover, M
can be expressed as the sum of at most 2c such matrices, those that
correspond to 1-rectangles.

∈

Since every function with low communication gives rise to a par-
tition into monochromatic rectangles (Theorem 1.7), we immediately
get:

Theorem 2.11. If a matrix has rank r, then its communication complexity is
at least log r.

Theorem 2.11 allows us to prove lower bounds on many of the
examples we have already considered. So let us revisit some of them.

Lemma 2.10 applies even if the matrix
has +1,

1 entries.

−



<!-- pdf-page: 4 -->
36 communication complexity

Equality We start with the equality function, deﬁned in (1.1). The
matrix of the equality function is just the identity matrix. Since
the rows of this matrix are all linearly independent, the rank of
the matrix is 2n, proving that the communication complexity of
equality is at least n bits.

Greater-than Consider the greater than function, deﬁned in (1.3). The
matrix of this function is the upper-triangular matrix which is 1
above the diagonal and 0 on all other points. Once again we see
that rows are linearly independent, and so the matrix has full rank.
This proves that the communication complexity is at least log n.

Disjointness Consider the disjointness function, deﬁned in (1.2). Let
Dn be boolean matrix that represents disjointness. Let us order
the rows of the matrix in lexicographic order, so that the sets that
contain the element n correspond to the last row and last column.
If we partition the rows into two parts based on whether the row
corresponds to a set that contains n or not, and do the same for the
columns, we get that if the rows and columns come from the part
where n is included in both, then the matrix is 0. However, if n is
included in only the rows, or only the columns, we get a copy of
the matrix Dn

1. So Dn can be expressed as:

−

Dn =

Dn
Dn

"

−

−

1

1 Dn

1
−
0 #

rank(Dn
In other words Dn = D1 ⊗
−
by Fact 2.6. We conclude that rank(Dn) = 2n, proving that the
communication complexity of disjointness is at least n.

1, and so rank(Dn) = 2

Dn

·

1)

−

i ) ×

i=0 (n

[n], deﬁne the monomial x = ∏i

k-disjointness Consider the disjointness function restricted to sets of
i=0 (n
size at most k. In this case, the matrix is an ∑k
∑k
i )
matrix. Let us write Dn,k to represent the matrix for this problem.
For two sets X, Y
X yi, and the
n such that yi = 0 if and only if i
string y
Y. Then we see
that Disj(X, Y) = x(y). Now any non-zero linear combination of
the rows corresponds to a linear combination of the monomials we
have deﬁned, and so gives a non-zero polynomial f . To show that
the matrix has full rank, we need to prove that there is a set Y that
gives rise to an input y with f (y)

= 0.

∈ {

0, 1

⊆

∈

}

∈

To show this, let X be a set that corresponds to a monomial of

maximum degree in f . Let us restrict the values of all variables
outside X to be equal to 1. After doing this, f becomes a non-zero
polynomial that depends only on the variables of X. Since such
polynomials are in one to one correspondence with the boolean
functions on these variables, we get that there must be some

Alexander Razborov, 1987.

6


<!-- pdf-page: 5 -->
rank 37

setting of the variables of X giving an assignment y with f (y) = 1.
Moreover, this gives an assignment to y with at most k entries that
are 0.

Inner-product Our ﬁnal example the inner product function IP :

0, 1

{

n

}

× {

0, 1

n

}

→ {

0, 1

}

, deﬁned by

IP(x, y) =

x, y

i

h

mod 2.

(2.1)

The trivial protocol takes n bits, and one case use bounds on the

size of the largest rectangle to show that the communication is at
least Ω(n). Here it will be helpful to use Fact 2.4. If Pn represents
the matrix whose entries are , sorting the rows and columns
lexicographically, we see that

See Exercise 1.1

Pn =

Pn
Pn

−

−

"

Pn
1
−
Pn
1 −

−

1

=

1
1

"

1#

1
1# ⊗

−

Pn

1,

−

and so by Fact 2.6, rank(Pn) = 2rank(Pn
rank(Pn) = 2n, and so the communication complexity of IP is at
least n.

1). This proves that

−

Towards the Log-Rank Conjecture

Lovasz and Saks conjectured1 that Theorem 2.11 is closer to the
truth than Theorem 2.9:

Conjecture 2.12. There is a constant α such that the communication
complexity of a matrix M is at most logα rank(M).

Kushilevitz showed2 that α must be at least log3 6 for the conjec-
ture to hold, so we cannot expect the communication complexity of a
matrix to be exactly equal to its rank. Our main goal in this section is
to prove the following theorem3:

Theorem 2.13. If the rank of a matrix is r, its communication complexity is
at most O(√r log2 r).

The proof of Theorem 2.13 relies4 on a powerful theorem from

convex geometry called John’s theorem5. We use it to show:

Lemma 2.14. Any m
monochromatic rectangle of size at least mn

×

n boolean matrix of rank r > 1 must have a

2−

20√r log r.

·

Let us see how to use Lemma 2.14 to get a protocol. Let R be the
rectangle promised by the lemma. Then, rearranging the rows and

columns, we can write the matrix as:

R A
B C#

"

. Now we claim6 that

1 Lovász and Saks, 1988

2 Nisan and Wigderson, 1995

3 Lovett, 2014

Lovett actually proves that the commu-
nication is bounded by O(√r log r), but
we prove the weaker bound here for
ease of presentation.

4 Rothvoß, 2014

5 John, 1948



<!-- pdf-page: 6 -->
38 communication complexity

rank

R
B#!

 "

+ rank

R A

(cid:16)h

≤

i(cid:17)

rank

R A
B C#!

 "

+ 3.

Indeed, one can write

R A
B C#

"

=

0 A
B C#

"

+

R 0
0#
0

"

R A

=

0 A

+

R 0

h

i

R
B#

"

=

h

"

0
B#

i
+

"

h

R
0 #

,

i

So by Fact 2.3,

rank

R
B#!

 "

+ rank

R A

(cid:16)h

i(cid:17)

rank(A) + rank(B) + 2

rank

0 A
B C#!

 "

+ 2

rank

R A
B C#!

 "

+ 3.

(2.2)

≤

≤

≤

7 (t + 3)/2

≤

2t/3, when t

9.

≥

8 Fact: 1

x

−

≤

e−

x, for x

0.

≥

Input: Alice knows i, Bob knows j.
Output: Mi,j.

while rank(M) > 9 do

Find a monochromatic
rectangle R as promised by
Lemma 2.14;

Now suppose

R
B#

"

has the smaller rank. Then Bob sends the bit

0 if his input is consistent with R and 1 otherwise. If it is consistent,
then if rank(M) > 9, players have reduced7 the rank of the matrix by
a factor of at least 2
3 . If it is not consistent, the players have reduced
the size of the matrix by a factor of 1

20√r log r.

By Lemma 2.8, we can assume that any matrix of rank r has at
most 2r rows and columns. The number of 0 transmissions in this
protocol is at most 2r ln 2
sions, the number of entries in the matrix have been reduced to8

220√r log r, since after that many transmis-

·

2−

−

22r(1

−

2−

20√r log r)2r

·

220√r log r < 22re−
= 22re−

20√r log r2r ln 2

2−

220√r log r

·

2r ln 2 = 1.

The number of 1 transmissions is at most O(log3/2 r), since af-
ter that many transmissions, the rank of the matrix is reduced to
less than 6. Thus, the number of leaves in this protocol is at most
2O(√r log2 r). By Theorem 1.3, we can bal-

220√r log r

(2r ln 2

·

log3/2 r

) ≤

ance the protocol tree to obtain a protocol with communication
O(√r log2 r) that computes the same function.

It only remains to prove Lemma 2.14. To prove it, we need to

understand John’s theorem. A set K
x, y

Rr is called convex if whenever
⊆
K, then all the points on the line from x to y are also in K. The

∈

Write M =

R A
C
B

;

(cid:21)

(cid:20)

if
rank

(cid:18)(cid:20)

then

R
B

(cid:21)(cid:19)

> rank

R A

(cid:0)(cid:2)

(cid:3)(cid:1)

if i is consistent with R
then

Both parties replace
M with

R A

;

else

end

else

(cid:2)

(cid:3)

Both parties replace
M with

B C

;

(cid:2)

(cid:3)

if j is consistent with R
then

Both parties replace
R
B

M with

;

(cid:20)

(cid:21)

Both parties replace
A
C

M with

;

(cid:20)

(cid:21)

else

end

end

end
The parties exchange at most 9 bits
to compute Mi,j, using Theorem
2.9;

Figure 2.1: Protocol for Low Rank
Matrices with 2O(√r log2 r) leaves.



<!-- pdf-page: 7 -->
rank 39

set is called symmetric if whenever x
centered at 0 is a set of the form:

∈

K, then

x

−

∈

K. An ellipsoid

E =

x

(

∈

Rr :

r
∑
i=1 h

x, uii

2 /α2

i ≤

,

1

)

where u1, . . . , ur are a basis for Rr. John’s theorem shows9:

9 John, 1948

Rr be a symmetric convex body
Theorem 2.15 (John’s Theorem). Let K
such that the unit ball is the most voluminous of all ellipsoids contained in
K. Then every element of K is of length at most √r.

⊆

The most voluminous ellipsoid contained in K behaves nicely
when K is changed. Suppose the ellipsoid E above is the largest
ellipsoid in K. Suppose that for some i, we multiply every element
of K by a number e in the direction of ui: namely we consider the
convex body:

K0 =

x0 :

x

∃

∈




K,

x0, uj

=

(cid:10)

(cid:11)

e

x, uii

· h
x, uj




if j = i,
otherwise. 


(cid:10)

(cid:11)



Since scaling the space by β in any direction changes the volume of
all objects by exactly β, the largest ellipsoid in K0 is the scaled version
of the largest ellipsoid in K:





Fact 2.16. The largest ellipsoid in K0 is

E0 =

x

(

∈

Rr :

r
∑
j=1

x, uj

(cid:10)

(cid:11)

2

/β2

j ≤

,

1

)

where βj = αj if j

= i, and βi = eαi.

Lemma 2.14 is proved in two steps. In the ﬁrst step, we use
John’s theorem to show that the matrix must contain a large nearly
monochromatic rectangle. In the second step, we will show how
any such rectangle of low rank must contain a large monochromatic
rectangle itself.

Since the matrix has rank r, we know that M can be expressed as
n matrix. We

r matrix, and B is an r

M = AB, where A is an m
start by showing:

×

×

Lemma 2.17. Any boolean matrix M of rank r can be expressed as M = AB,
r matrix whose rows are vectors of length at most √r, and
where A is an m
B is an r

n matrix whose columns are vectors of length at most 1.

×

×

Proof. Start with M = AB for A, B not necessarily satisfying the
length constraints. Let v1, . . . , vm be the rows of A, and let w1, . . . , wn
be the columns of B. Let K be the convex hull of

.

v1, . . . ,

{±

vm}

±

The "√r" and "1" in the statement of
Lemma 2.17 can be replaced by any
numbers whose product is √r.

6


<!-- pdf-page: 8 -->
40 communication complexity

An ellipsoid centered at the origin in the space is speciﬁed by a
basis u1, . . . , ur for the space, and numbers α1, . . . , αr. The ellipsoid
determined by these parameters is the set

E =

x

(

∈

Rr :

r
∑
i=1 h

x, uii

2 /α2

i ≤

.

1

)

Our ﬁrst goal is to ensure that the ellipsoid of maximum volume
in K is the unit ball. This is the same as ensuring that α1 = α2 = . . . =
αr = 1. Suppose αi is not 1 for some i. Then we can scale every vector
vj by a factor of αi in the direction10 ui, and scale every vector wj by a
factor of 1/αi in the direction of ui. This preserves the inner products
of all pairs of vectors. By Fact 2.16, repeating this for each coordinate
i ensures that the ellipsoid of maximum volume in K is the unit ball.
Now, by John’s theorem, every vector vi must have length at most √r,
since every vector in K has length at most √r.

It only remains to argue that vectors w1, . . . , wn are of length at

most 1. This is where we use the fact that the matrix is boolean.
Consider any wi, and the unit vector in the same direction: ei =
wi/
in the unit ball, and so is contained in K, ei = ∑j µjvj + ∑j κj(
convex combination of the vj’s. Thus

. The length of wi can be expressed as

wi, eii

, but since ei is
vj) is a

wik

−

k

h

wi, eii

h

= ∑
j

µj

wi, vj

(cid:10)

(cid:11)

+ ∑
j

κj

wi,

vj

−

(cid:10)

(cid:11)

∑
j

µj + ∑
j

≤

κj = 1,

where the inequality follows from the fact that M is boolean.

For the rest of the proof, we assume that M has as least mn/2 0’s.
We can do this, because if M has more 1’s than 0’s, we can replace M
M, where J is the all 1’s matrix. This can increase the rank by
with J
at most 1, but now the role of 0’s and 1’s has been reversed.

−

Lemma 2.17 says something about the angles between the vectors

10 Formally, we write vj = ∑r
and wk = ∑r
i0 =1 βi0
γi with αiγi, and βi with βi/αi. This
.
preserves the inner product

i0 =1 γi0
and replace

ui0

vj, wk

ui0

,

(cid:10)

(cid:11)

we have found. Deﬁne θi,j = arccos

. Then observe that

when vi, wj are orthogonal, the angle is π/2. But when the inner
product is 1, the angle is at most arccos

1
√r

π
2 −

2π
7√r .

≤

So we get:

(cid:16)

(cid:17)

vi,wj
h
vikk
k

i
wjk (cid:19)

(cid:18)

= π
2
π
2 −

≤

θi,j 


2π
7√r

if Mi,j = 0,
if Mi,j = 1.

Consider the following random experiment. Sample t vectors of
length 1 uniformly at random z1, . . . , zt, and deﬁne the rectangle R
by:



R =

(i, j) :

{

k,

vi, zki

h

∀

> 0,

wj, zk

< 0

.

}

(cid:10)

(cid:11)



<!-- pdf-page: 9 -->
π
2

π
4

arccos(α)

π/2

−

2πα/7

0

0.5
α

1

For a ﬁxed (i, j) and k the probability that
wk, zki

< 0 is exactly 1

. So we get

4 −

−
2π

π/2

θi,j

h

vk, zki

h

> 0 and

[(i, j)

Pr
R

∈

R]

=




≤



t

1
4

(cid:17)
1
4 −

1
7√r

(cid:16)

(cid:16)

t

(cid:17)

if Mi,j = 0,

if Mi,j = 1.

Let R1 denote the number of 1’s in R and R0 denote the number of

0’s. Set t = 7√r log r. By what we have just argued,

Figure 2.2: arccos(α)
1.
0

α

≤

≤

rank 41

π/2

−

≤

2πα/7 for

vi

wj

Figure 2.3: The region where all zk’s
must fall to ensure that (i, j)
Mi,j = 0.

∈

R, when

vi

2p
7pr

 

wj

E [R0]

E [R1]

≥

=

≤

≤
=

mn/2
47√r log r
mn
2−
2 ·
mn/2
47√r log r
mn
2 ·
mn
2 ·

2−

2−

14√r log r,

4
7√r

1

−

(cid:18)

14√r log r

(cid:19)
4
7√r

e−

14√r log r

r−

4 log e.

·

·

Figure 2.4: The region where all zk’s
must fall to ensure that (i, j)
Mi,j = 1.

∈

R, when

7√r log r

7√r log r

Fact: 1

x

−

≤

e−

x for x

0.

≥

Now let Q = R0 −

r4R1. By linearity of expectation, we have

E [Q]

mn
2 ·

2−

14√r log r

2−

16√r log r.

mn

·

≥

≥

(1

·

−

1/r)

since r > 1.



<!-- pdf-page: 10 -->
42 communication complexity

Thus there must be some rectangle R realizing this value of Q. Only
1/r3 fraction of such a rectangle can correspond to 1 entries of the
matrix. We have shown:

Claim 2.18. If at least half of the matrix is 0’s, then there is a submatrix T of
16√r log r such that the fraction of 1’s in T is at most 1/r3.
size at least mn2−

Call a row of T good if it contains at most 2/r3 fraction 1’s. At
least half the rows of T must be good, or else T would have more
than 1/r3 fraction 1’s overall. Let T0 be the submatrix obtained by
restricting T0 to the good rows. Since rank(T0) = r, there are r rows
A1, . . . , A0r that span all the rows of T0. Since each row Ai can have
only 2/r3 fraction of 1’s, at most 2/r2
can contain a 1 in one of these r0 rows.

1/2 fraction of the columns

≤

Let T00 be the matrix obtained by restricting T0 to the columns that

do not have a 0 in the rows A1, . . . , Ar. Since every row of T00 must
be a linear combination of rows that only have 0’s in them, we have
found a monochromatic matrix of size at least mn2−
mn2−

18√r log r. This concludes the proof of Lemma 2.14.

16√r log r/4

≥

Open Problem 2.19. It would be very nice to ﬁnd a more direct geometric
argument to prove Lemma 2.14.

Non-negative Rank and Covers

Another way to measure the complexity of a matrix is by measur-
ing its non-negative rank. The non-negative rank of a m
matrix M is the smallest number r such that M = AB, where A, B are
matrices with non-negative entries, such that A is an m
and B is an r
non-negative rank 1 matrices that sum to M. Clearly, we have

r matrix
n matrix. Equivalently, it is the smallest number of

n boolean

×

×

×

Fact 2.20. rank(M)

rank+(M).

≤

0
1
1
0
1
0
0
0
0
1
1
1

2

6
6
6
6
6
6
6
6
6
6
6
6
6
6
6
6
6
6
4

1 1
1 0
1 0
0 0
0 0
1 0
0 0
0 0
0 0
1 0
1 0
1 1

0
1
0
0
0
0
0
0
0
0
0
0

0 1
1 0
0 0
1 1
0 0
0 1
0 0
0 0
0 0
0 0
0 0
0 1

1
0
0
0
1
0
1
1
1
1
0
0

1
0
0
0
0
0
0
0
0
0
0
0

0 1
0 1
0 0
0 0
0 0
0 1
0 1
1 1
0 1
0 1
0 0
1 1

3

7
7
7
7
7
7
7
7
7
7
7
7
7
7
7
7
7
7
5

T

0

T

A1, . . . , Ar0 T

00

Figure 2.5: Going from a nearly
monochromatic rectangle to a
monochromatic rectangle.

×

of size n, consider the
i + x2

{
n matrix where Mi,j = (xi −

In general, rank(M) and rank+(M) may be far apart. For example,
x1, . . . , xn}
xj)2 = x2

given a set of numbers X =
j + 2xixj. Since M is
n
the sum of three rank 1 matrices, rank(M) = 3. On the other hand,
we can show by induction on n that rank+(M)
log n. Indeed, if
rank+(M) = k, then there must be non-negative rank 1 matrices
R1, . . . , Rk such that M = R1 + . . . + Rk. Let the support of R1 be
the rectangle A
X
B
|
| ≤ |
Suppose A
to the numbers of X
log n

/2, and let M0 be the submatrix that corresponds
log(n/2) =

B. Then we must have that either
A

/2, or else there will be an element x

A. Then we get that rank+(M0)

A
X
|
B, but Mx,x = 0.

1, proving that k

1, and so k

≥
log n.

/2 or

| ≤ |

log n

|
∩

≤ |

\
1

≥

×

∈

X

|

|

−

−

≥

−

≥



<!-- pdf-page: 11 -->
rank 43

If M = R1 + . . . + Rr, where R1, . . . , Rr are rank 1 non-negative ma-

trices, then the support of each matrix Ri must be a monochromatic
rectangle in M with value 1. Thus, we get a 1-cover of the matrix:

Fact 2.21. M always has a 1-cover with rank+(M) rectangles.

Moreover, one can prove that if a matrix has both small rank and a

small cover, then there is a small communication protocot11:

11 Lovász, 1990

Theorem 2.22. If M has a 1-cover of size r, then there is a protocol comput-
ing M with O(log r

log rank(M)) bits of communication.

·

Proof. The protocol is similar to the one used to prove Theorem 1.8.
For every rectangle R in the cover, we can write

M =

R A
B C#

,

"

and by (2.2), either

or

rank

R A

(cid:16)h

≤

i(cid:17)

(rank(M)

3)/2,

−

rank

R
B#! ≤

 "

(rank(M)

3)/2.

−

(2.3)

(2.4)

So in each step of the protocol, if Alice sees an R that is consistent
with her input satisfying (2.3), she announces its name, or if Bob sees
a rectangle R in the cover consistent with his input and satisfying
(2.4), he announces its name. Both parties then restrict their attention
to the appropriate submatrix, which reduces the rank of M by a
factor of 2.

This can continue for at most O(log rank(M)) steps before the rank

of the matrix becomes 1. On the other hand, if neither party ﬁnds
such an R, then there must be be no such R that covers their input, so
they can safely output a 1.

Putting together Fact 2.21 and Theorem 2.22, we get

Corollary 2.23. The communication of M is at most

O(log(rank+ M)

log rank(M))

·

≤

O(log2 rank+(M)).

Exercise 2.1

Fix a function f

: X

Y

0, 1

with the property that in

×

→ {

}

every row and column of the communication matrix M f there are
))
exactly t ones. Cover the zeros of M f using O(t(log
monochromatic rectangles.

+ log

X

Y

|

|

|

|



<!-- pdf-page: 12 -->
44 communication complexity

Exercise 2.2

Show that Nisan-Widgerson protocol (i.e., the proof of Lemma
2.13) goes though even if we weaken Lemma 2.14 to only guarantee
a rectangle with rank at most r/8 (instead of rank at most one, or
monochromatic).

Exercise 2.3

Recall that for a simple, undirected graph G the chromatic number

χ(G) is the minimum number of colors needed to color the vertices
of G so that no two adjacent vertices have the same color. Show that
log χ(G) is at most the deterministic communication complexity of
G’s adjacency matrix.

Exercise 2.4

For any symmetric matrix M

entries, show that

0, 1

∈ {

n

×

n with ones in all diagonal

}

,

2c

≥

n2
M

|

|

where c is the deterministic communication complexity of M, and
M

is the number of ones in M.

|

|

Exercise 2.5

For any boolean matrix M, deﬁne rank2(M) to be the rank of M

over F
2, the ﬁeld with two elements. Exhibit an explicit family of ma-
rank2(M)/10, where c
trices M
is the deterministic communication complexity of M. Conclude that
this falsiﬁes the analogue of log-rank conjecture for rank2.

n with the property that c

∈ {

0, 1

≥

}

×

n

Exercise 2.6

Show that if f has fooling set of size s then rk(M f )

tensor product.

√s. Hint:

≥


