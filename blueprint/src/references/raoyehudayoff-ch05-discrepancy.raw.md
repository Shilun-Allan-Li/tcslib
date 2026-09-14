<!-- generated-by: proofmatch local extraction -->
<!-- source-pdf-sha256: 4c44440f2aaa0ac0f6a2e09591838c6865607cd9872cd966896a94edb2dc06bb -->
<!-- extractor: pdfminer.six v20260107 -->

<!-- pdf-page: 1 -->
5
Discrepancy

The discrepancy method is a powerful way to prove lower bounds
on communication complexity. We will use it here to prove optimal
lower bounds on randomized protocols, and tight lower bounds in
the number-on-forehead model.

One reason why our previous approaches were insufﬁcient to
prove lower bounds on randomized protocols is that the existence of
a randomized protocol only guarantees a partition of the space into
nearly monochromatic rectangles, rather than completely monochro-
matic rectangles. In order to work with nearly monochromatic rectan-
gles, we need to work with a quantity that is sensitive to the bias of a
rectangle. Let g be a boolean function, and let χS be the characteristic
function of the set S. Then we deﬁne the discrepancy of S with respect
to g to be

E

χS(x)

h

(

·

−

1)g(x)

,

i(cid:12)
(cid:12)
(cid:12)

(cid:12)
(cid:12)
(cid:12)

where the expectation is taken over a random input x. A large, nearly
monochromatic rectangle (or cylinder intersection) must have high
discrepancy:

Fact 5.1. If R is a (1
of density δ, then the discrepancy of R must be at least (1

e)-monochromatic rectangle (or cylinder intersection)

−

2e)δ.

−

Proof. Only points inside R contribute to its discrepancy. Since (1
e)
fraction of these points have the same value under g, the discrepancy
is at least δ(1

e) = δ(1

2e).

−

e

−

−

−

Let π(x, y) denote the output of a protocol π with c bits of commu-

nication and error e. Let R1, . . . , Rt be the rectangles induced by the



<!-- pdf-page: 2 -->
64 communication complexity

protocol. Then we have

1

−

2e = E
x,y

= E
x,y

h

h

(

(

−

−

1)π(x,y)+g(x,y)

1)π(x,y)

(

·

−

i
1)g(x.y)

i

E
x,y " 

≤

t
∑
i=1

χRi (x, y)

o(Ri)

·

(

−

! ·

1)g(x,y)

,

#

where here o(Ri) is
the protocol outputs O. We can continue to bound:

1 if the protocol outputs 1 in Ri, and it is 1 if

−

2e

1

−

≤

≤

E
x,y

t
∑
i=1 (cid:12)
h
(cid:12)
(cid:12)
2c
(cid:12)
max
R (cid:12)
(cid:12)
(cid:12)
(cid:12)

·

χRi (x, y)

(

·

−

1)g(x,y)

χR(x, y)

(

·

−

E
x,y

h

i(cid:12)
(cid:12)
(cid:12)
1)g(x,y)
(cid:12)

,

i(cid:12)
(cid:12)
(cid:12)
(cid:12)

where the maximum is taken over all choices of rectangles. Rearrang-
ing, we get

2c

≥

maxR

Ex,y

1

2e
−
χR(x, y)

.

1)g(x,y)

(

·

−

The same calculation also works in the case of cylinder intersections.
We have shown:

(cid:12)
(cid:12)

(cid:2)

(cid:3)(cid:12)
(cid:12)

Theorem 5.2. If the maximum discrepancy of every rectangle (or cylinder
intersection) is at most γ, then every protocol with error e computing the

function must have communication at least log

1

2e
−
γ

.

(cid:16)

(cid:17)

Some Examples Using Convexity in Combinatorics

To bound the discrepancy of communication protocols, we shall use
Jensen’s inequality. Before applying these ideas to bounding the
discrepancy of rectangles and cylinder intersections, we show how to
use them to prove some interesting results in combinatorics.

While there are dense graphs that have no 3-cycles (for example
the complete bipartite graph), there are no dense graphs that avoid
4-cycles:

Lemma 5.3. Every n-vertex graph with e (n
1)4/4 4-cycles.

2) edges has at least (en

−

Proof. Let 1x,y be 1 when there is an edge between the vertices x and
y, and 0 otherwise. Then if x, x0, y, y0 are chosen uniformly at random,

Figure 5.1: A dense graph with no
3-cycles.



<!-- pdf-page: 3 -->
we can count the number of 4-cycles by computing:

discrepancy

65

E

1

1x,y ·
E
y

x,x0 (cid:20)

h
= E

1

x0,y ·
1x,y ·

x,y0 ·
1

x0,y

h

1

x0,y0

2

i

i

(cid:21)
2

x0,y

i(cid:21)

≥

E
x,x0 (cid:20)

E
y

= E
y

(cid:20)

E
x,y

≥

E
x
(cid:2)
1x,y

1

2

1x,y ·

h
1x,y

2

(cid:21)

4

(cid:3)
.

(cid:2)
This last quantity is at least (e
edge as long as x and y are distinct. This gives (en
since each cycle is counted 4 times.

−

(cid:3)
1/n)4, since we are picking a random

1)4/4 cycles,

−

We can use similar ideas to prove that every dense bipartite graph

must contain a reasonably large bipartite clique. Next we show a
slightly different way to prove this:
Lemma 5.4. If G is a bipartite graph of edge density e, and bipartition
A, B, with
B
|
log n
2 log(e/e) ,
Q
|
connected by an edge.

⊆
√n, such that every pair of vertices q

= n, then there exists subsets Q

B with
Q, r

A, R

| ≥

| ≥

⊆

∈

∈

R

|

|

R is

Proof. Pick a random subset Q
the common neighbors of Q. Given any vertex b
d, the probability that b is included in R is exactly

A of size

⊆

∈

log n

2 log(e/e) , and let R be all
B that has degree

log n

( d
2 log(e/e))
( n
2 log(e/e)) ≥

log n

log n
2 log(e/e)

.

d
en

(cid:19)

(cid:18)

Fact: ( n

k )k

≤ (n

k) ≤

( en

k )k.

So if di is the degree of the i’th vertex, the expected size of the set R
is at least

log n
2 log(e/e)

n
∑
i=1 (cid:18)

di
en

(cid:19)

n

≥

·  

1
n

n
∑
i=1

di
en !

log n
2 log(e/e)

log n

2 log(e/e) = √n.

n

·

≥

e
e

(cid:16)

(cid:17)

So there must be some choice of Q, R that proves the Lemma.

By convexity.

Lower bounds for Inner-Product

n and want to compute
mod 2. We have seen that this requires n + 1 bits of communi-

Say Alice and Bob are given x, y
x, y
h
cation using a deterministic protocol. Here we show that it requires
n/2 bits of communication even using a randomized protocol.

∈ {

0, 1

}

i

≈



<!-- pdf-page: 4 -->
66 communication complexity

Lemma 5.5. For any rectangle R, the discrepancy of R with respect to the
inner product is at most 2−

n/2.

Proof. Since R is a rectangle, we can write its characteristic function
as the product of two functions A and B. Thus we can write:

χR(x, y)

1)h

x,y

i

(

·

−

E
x,y

h

= E
x,y

2

i

A(x)

B(y)

(

·

−

·

2

1)h

x,y

i

h
A(x) E
y

h
A(x)2 E
y

= E
x

E
x

≤

(cid:20)

(cid:20)

h

B(y)

1)h

(

·

−

B(y)

1)h

(

·

−

i
x,y

i

2

i(cid:21)
2
i

x,y

,

(cid:21)
i
Z2

where the inequality follows from the fact that E [Z]2
any real valued random variable Z. Now we can drop A(x) from this
expression to get:

for

≤

E

(cid:3)

(cid:2)

χR(x, y)

1)h

x,y

i

(

·

−

E
x,y

h

2

i

E
y

E
x

≤

(cid:20)
= E

B(y)

(

·

−

h
B(y)B(y0)

2

1)h

x,y

i

x,y,y0 h

= E

B(y)B(y0)

1)h

x,y+y0i

(cid:21)
x,y

i
1)h

+

x,y0i

h

i

−

i

(

(

·

·

−

x,y,y0 h
In this way, we have completely eliminated the set A! Moreover, we
can eliminate the set B too and write:

i

χR(x, y)

1)h

x,y

i

(

·

−

E
x,y

h

2

i

≤

≤

B(y)B(y0)

1)h

x,y+y0i

(

·

−

E
x,y,y0 h
E
E
x
y,y0 (cid:20)(cid:12)
(cid:12)
(cid:12)
(cid:12)

1)h

x,y+y0i

(

−

h

(cid:21)

i(cid:12)
(cid:12)
(cid:12)
(cid:12)

i

(5.1)

Now, whenever y + y0 is not 0 modulo 2, the expectation is 0. On the
n. So
other hand, the probability that y + y0 is 0 modulo 2 is exactly 2−
we can bound (5.1) by 2−

n.

Lemma 5.5 and Theorem 5.2 together imply:

Theorem 5.6. Any 2-party protocol that computes the inner-product with
error at most e over the uniform distribution must have communication at
least n/2

log(1/(1

2e)).

−

−

Similar ideas can be used to show that the communication com-
plexity of the generalized inner product must be large in the number-on-
forehead model1. Here each of the k players is given a binary string
i=1 xi,j mod 2
xi ∈ {
0, 1
We can show:

n. They want to compute GIP(x) = ∑n

j=1 ∏k

}

Lemma 5.7. For any cylinder intersection S, the discrepancy of S with
respect to the inner product is at most e−

n/4k

−

.

1

1 Babai et al., 1989

Each vector xi can be interpretted as
a subset of [n]. Then our protocol for
computing the set intersection size
gives a protocol for computing the
inner product with communication
O(k4n/2k).



<!-- pdf-page: 5 -->
Proof. Since S is a cylinder intersection, its characteristic function
can be expressed as the product of k boolean functions χS = ∏k
where χi does not depend on the i’th input. Thus we can write:

i=1 χi,

discrepancy

67

χS(x)

(

·

−

1)GIP(x)

E
x

h

= E

x "

k
∏
i=1

2

i

χi(x)

(

·

−

1)GIP(x)

2

#

= E
x1,...,xk

χk(x) E

xk "

1 "

−

k
1
−
∏
i=1

χi(x)

(

·

−

1)GIP(x)

E
x1,...,xk

≤

1 

−

χk(x)2 E

xk "

k
1
−
∏
i=1

χi(x)

(

·

−

1)GIP(x)

#

where the inequality follows from the fact that E [Z]2
for
any real valued random variable Z. Now we can drop χk(x) from
this expression to get:

Z2

≤

E

(cid:2)

(cid:3)



2

##
2

,





χS(x)

(

·

−

1)GIP(x)

E
x

h

2

i

E
x1,...,xk

≤

1 

−



=

E
x1,...,xk,x0k "

k
1
−
∏
i=1

E
xk "

χi(x)

(

·

−

1)GIP(x)

2



#

k
1
−
∏
i=1

χi(x)χi(x0)

(

·

−


j=1(xk+x0k) ∏k

1
i=1 xi,j
−

1)∑n

#

In this way, we have completely eliminated the function χk! Repeat-
ing this trick k

1 times gives the bound

−

χS(x)

(

·

−

E
x

h

1

2k

−

1)GIP(x)

≤

E
x2,x02,...,xk,x0k (cid:20)(cid:12)
(cid:12)
(cid:12)
(cid:12)

i
1

1)∑n

j=1 x1 ∏k

i=2(xi+x0i )

(

E
x1 (cid:20)

−

.

(cid:21)

(cid:21)(cid:12)
(cid:12)
(cid:12)
(cid:12)

Now, whenever ∏k
j, the expectation is 0. On the other hand, the probability that this
expression is 0 modulo 2 is exactly (1

i=2 (xi,j + xi0,j) is not 0 modulo 2, at any coordinate
−

k+1)n. So we get

2−

−

χS(x)

(

·

−

1)GIP(x)

E
x

h

1

2k

−

i

(1

−

≤

2−

k+1)n < e−

n/2k

1

−

.

This proves that

Fact: 1

−

x < e−

x for x > 0.

χS(x)

(

·

−

E
x

h

1)GIP(x)

< e−

n/4k

1

−

.

i

By Lemma 5.7 and Theorem 5.2:

Theorem 5.8. Any randomized protocol for computing the generalized inner
product in the number-on-forehead model with error e requires n/4k
log(1/(1

2e)) bits of communication.

−

−

1

−



<!-- pdf-page: 6 -->
68 communication complexity

Lower bounds for Disjointness in the Number-on-Forehead model

At first it may seem that the discrepancy method is not very useful
for proving lower bounds against functions like disjointness, which
do have large monochromatic rectangles.

Suppose Alice and Bob are given two sets X, Y

[n] and want to

compute disjointness. If we use a distribution on inputs that gives
intersecting sets with probability at most e, then there is a trivial
protocol with error at most e. On the other hand, if the probability of
intersection is at least e, then then there must be some ﬁxed coordi-
nate i such that an intersection occurs in coordinate i with probability
at least e/n. Setting R =

(X, Y) : i

, we get

X, i

Y

⊆

{
χR(X, Y)

(

∈

∈
1)Disj(X,Y)

E

}

e/n,

·

h

(cid:12)
(cid:12)
(cid:12)

≥

i(cid:12)
(cid:12)
(cid:12)

−
so we cannot hope to prove a lower bound better than Ω(log n) this
way. Nevertheless, we show that one can use discrepancy to give
a lower bound on the communication complexity of disjointness 2,
even when the protocol is allowed to be randomized, by studying a
different expression. In fact, this is the only known method to prove
lower bounds on the communication complexity of disjointness in the
number-on-forehead model.

Consider the following distribution on sets. Let the universe

consist of disjoint sets I1, . . . , Im. Alice gets m independently sampled
sets X1, . . . , Xm, where Xi is a random subset of Ii, and Bob gets m
random sets of size 1, Y1, . . . , Ym, where the i’th set is again drawn
from Ii. Let X =
Lemma 5.9. For any rectangle R,

m
i=1Yi. We prove:

m
i=1Xi, and Y =

∪

∪

E

χR(X, Y)

h

1)∑m

i=1 Disj(Xi,Yi)

(

·

−

1

≤ s

∏m

j=1 |

Ii|

i

.

Proof. As usual, we express χR(X, B) = A(X)
convexity argument. We get:

·

B(X) and carry out a

2 Sherstov, 2012; and Rao and Yehuday-
off, 2015

E

χR(X, Y)

(

·

−

1)∑m

i=1 Disj(Xi,Yi)

2

A(X)

B(Y)

(

·

−

·

i
i=1 Disj(Xi,Yi)

1)∑m

2

A(X)2 E

B(Y)

(

1)∑m

i=1 Disj(Xi,Yi)

i

2

h
B(Y)B(Y0)

·

(

−
1)∑m

·

−

(cid:21)
i=1 Disj(Xi,Yi)+∑m
i=1 Disj(Xi,Y0i )

i

1)∑m

i=1 Disj(Xi,Yi)+∑m

i=1 Disj(Xi,Y0i )

(

−

h

i

(cid:21)

i(cid:12)
(cid:12)
(cid:12)
(cid:12)

h
= E

h

E

≤

≤

≤

(cid:20)
E
X,Y,Y0 h
E
E
X
Y,Y0 (cid:20)(cid:12)
(cid:12)
(cid:12)
(cid:12)



<!-- pdf-page: 7 -->
For any ﬁxing of Y, Y0, the inner expectation is 0 as long as Y
. Thus we get

The probability that Y = Y0 is exactly 1/ ∏m
1)∑m

j=1 |
1/ ∏m

i=1 Disj(Xi,Yi)

, proving the

χR(X, Y)

(

2

Ii|
j=1 |

Ij|

·

−

that E
bound.
h

≤

i

discrepancy

69

= Y0.

Lemma 5.9 may not seem useful at ﬁrst, because under the given
m. However,

distribution, the probability that X, Y are disjoint is 2−
we can actually use it to give a linear lower bound on the communi-
cation of deterministic protocols. Suppose a deterministic protocol
for disjointness has communication c. Then there must be at most 2c
monochromatic 1-rectangles R1, . . . , Rt that cover all the 1’s. When-
ever X, Y are disjoint, we have that ∑m
other hand, the probability that X, Y are disjoint is exactly 2−
we get

j=1 Disj(Xi, Yi) = m. On the

m. Thus,

m

2−

≤

≤

≤

E

t
∑
i=1

"

χRi (X, Y)

(

·

−

1)∑m

j=1 Disj(Xi,Yi)

#

E

t
∑
i=1 (cid:12)
h
(cid:12)
(cid:12)
2c
(1/

·

χRi (X, Y)

(

·

−

1)∑m

j=1 Disj(Xi,Yi)

m
∏
j=1 q

).

Ij|

|

i(cid:12)
(cid:12)
(cid:12)

|

≥

Ii|

m, a linear lower bound

= 4, and rearranging gives c

Setting
on the communication complexity of disjointness. While we have
already seen several approaches to proving linear lower bounds on
disjointness, this approach has a unique advantage: it works even
in the number-on-forehead model. Consider the distribution where
for each j = 1, 2, . . . , m, X1,j ⊆
and X2,j, . . . , Xk,j ⊆
the constraint that their intersection contains exactly 1 element. Set
Xi =
forehead. Then we prove:

Ii is picked uniformly at random,
Ii are picked uniformly at random, subject to

m
j=1Xi,j. Suppose the i’th player has set Xi written on his

∪

Lemma 5.10. For any cylinder intersection S,

E

χS(X)

h

(

·

−

1)∑m

j=1 Disj(X1,j,...,Xk,j)

m
∏
j=1

≤

i

1

2k

−

1

.

−
Ij|

|

q

Proof. We prove the lemma by induction on k. When k = 2, the
statement was already proved in Lemma 5.9.

For ease of notation, we write Tj to denote the input in the j’th
interval, X1,j, . . . , Xk,j. Suppose χS(X) = ∏k
i=1 χi(X), where χi is
the indicator of the i’th cylinder. Then, as usual, we can apply a
convexity argument to bound:

6


<!-- pdf-page: 8 -->
70 communication complexity

E

χS(X)

(

·

−

1)∑m

j=1 Disj(X1,j,...,Xk,j)

2

h

E
X1,...,Xk

≤

E
X1,...,Xk

≤

1 

−



1 

−



χk(X)2

i
χi(X)

E
Xk "

·

k
1
−
∏
i=1

1)∑m

j=1 Disj(Tj)

(

·

−

k
1
−
∏
i=1

E
Xk "

χi(X)

(

·

−

1)∑m

j=1 Disj(Tj)

2



#

2

#





=

E
X1,...,Xk

−

1,Xk,X0k "

k
1
−
∏
i=1

χi(X)χi(X0)

(

·

−

1)∑m



j=1 Disj(Tj)+Disj(T0j )

(5.2)

,

#

−

where here X = X1, . . . , Xk, X0 = X1, . . . , Xk
X1,j, . . . , Xk
points of the last k

1 sets.

−

−

1,j, X0k,j. Let v, v0 denote the two common intersection

1, X0k, and T0j =

Now whenever v = v0, we have Disj(Tj) = Disj(T0j ), and so the
= v0,
X0k,j, and

j term of the sum is 0 modulo 2. On the other hand, when v
then any intersection in Tj must take place in the set Xk,j \
any intersection in T0j must take place in X0k,j \
the intersections of all the sets to Xk ∩
induction to bound the discrepancy.

Xj,k, so we can ﬁx
X0

X0k and the Xc

c
k and use

k ∩

Let Zj be the random variable deﬁned as:

Zj = 


Then we get:



1

|

q

2

−

(2k
Xk,j\

1)2
−
X0k,j||
X0k,j\

if v = v0,

otherwise.

Xk,j|

(5.2)

E

≤

m
∏
j=1

"

Zj

# ≤

m
∏
j=1

E

Zj

,

(cid:2)

(cid:3)

since the Zi’s are independent of each other. We need a technical
claim next:

Claim 5.11. Suppose a set Q
v

Ij is sampled by including a random element
Ij and adding every other element to Q independently with probability

⊆

∈
= 0. Then E

γ

1
Q

|

h

≤

|

i

1/(γ

).

Ij|

|

Proof.

E

1
Q

| (cid:21)

(cid:20)

|

= ∑
Q,v
1
Ij|

=

γ

|

(1/

)

Ij|

|

·

Q

γ|

1(1
|−
Q

|

|

γ)|

Ij|−|

Q

|

−

∑
=∅
Q

Q

γ|

|(1

−

γ)|

Ij|−|

Q

|

≤

γ

1
Ij|

|

(1

−

γ + γ)|

Ij| =

.

1
Ij|

|

γ

6
6
6


<!-- pdf-page: 9 -->
1,j is of size t, then the probability that v = v0 is

discrepancy

71

If X2,j ∩

. . .

Xk

−

∩

|

|

Q

exactly 1/t. Thus, the probability of this event is exactly the expected
, where Q is the intersection of the ﬁrst k
1 sets. After
size of 1/
picking the common intersection point, every other element of Ij is
included in Q independently with probability
. So by Claim
5.11, Pr[v = v0] = 2k

1
−
= v0, we can bound

. When v

−

2k

1
1

−

−

1

1

−
Ij|

|

Zj =

≤

2

−

(2k
−
X0k,j| · |
Xk,j \
1)2

2

−

|
q
(2k

−
2

·  

1)2
X0k,j \
1
Xk,j \

|

Xk,j|

+

1
X0k,j \

|

,

Xk,j| !

X0k,j|

By the Arithmetic mean - geometric
mean inequality: √ab

a+b
2 .

≤

Let Q = Xk \

X0k. Once again we see that Q is sampled by picking
the value of V uniformly, and then every other element is included
in Q independently with probability 2k
−
2(2k
−

1
1) . So by Claim 5.11,

2

−
1
−
. Combining these bounds, we get

E

1
Xk,j\

|

(cid:20)

X0k,j| (cid:21)

1

= 2(2k
(2k

−
2

−

−
1)

−

1)
Ij|

|

2

−

(2k
1)2
−
X0k,j| #
Xk,j \
|
−
−
−
(2k
Ij|
−

1)(2k
−
2
1)

−

|

2

1

1)2

E

Zj

(cid:2)

(cid:3)

≤

≤

=

Pr[v = v0] + E

"
2(2k

1

+

1

2k

−

−
Ij|

|
(2k
−

1

1)2

,

−
Ij|

as required.

|

Lemma 5.10 can be used to prove a linear lower bound on the
communication of deterministic protocols. Suppose a deterministic
protocol for disjointness has communication c. Then there must be
at most 2c monochromatic 1-cylinder intersections S1, . . . , St that
cover all the 1’s. Whenever X1, . . . , Xk are disjoint, we have that
∑m
that X1, . . . , Xk are disjoint is exactly 2−

j=1 Disj(X1,j, X2,j, . . . , Xk,j) = m. On the other hand, the probability

m. Thus, we get

m

2−

≤

≤

≤

E

t
∑
i=1

"

χSi (X1, . . . , Xk)

(

·

−

1)∑m

j=1 Disj(X1,i,...,Xk,j)

#

t
∑
i=1 (cid:12)
(cid:12)
(cid:12)

2c

E

χSi (X1, . . . , Xk)

h
m
∏
j=1

1

2k

−

|

q

1

−
Ij|

.





· 



1)∑m

j=1 Disj(X1,i,...,Xk,j)

(

·

−

i(cid:12)
(cid:12)
(cid:12)

Setting

= 16

Ij|

|

(2k

−

1

·

−

1)2, we get that c

m =

≥

16(2k

n
1

−

−

1)2 .

Setting

Ii|

= `, for all i, and rear-

−

n
`

=

≥

(2k

n/2

√`
1

1)
2
−
·
(cid:16)
, where a = (2

|
ranging gives c
(cid:17)
(`/a)1/`
(2k
−
1))2. The derivative of (`/a)1/`
is
(cid:0)
ln(`/a)
(`/a)1/`
`2
` = e
a slightly better bound: c

a. In this way, one can set ` to get
1)2 .

, which is 0 when

n log e
(2k
1

1

−

(cid:16)

(cid:17)

8e

−

(cid:1)

·

·

·

1

≥

·

−

−

6


<!-- pdf-page: 10 -->
72 communication complexity

Theorem 5.12. Any deterministic protocol for computing disjointness in the
number-on-forehead model requires

1)2 bits of communication.

16(2k

n
1

−

−


