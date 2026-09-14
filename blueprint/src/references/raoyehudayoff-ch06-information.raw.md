<!-- generated-by: proofmatch local extraction -->
<!-- source-pdf-sha256: 6d75772463348271496e345864f541b18ebe1d130191f210a3310d21cd274be7 -->
<!-- extractor: pdfminer.six v20260107 -->

<!-- pdf-page: 1 -->
6
Information

Shannon’s seminal work on information theory1 has had a big im-
pact on communication complexity. Shannon wanted to measure the
amount of information (or entropy) contained in a random variable
X. Shannon’s deﬁnition was motivated by the observation that the
amount of information contained in a message is not the same as the
length of the message. Suppose we are working in the distributional
setting, where the inputs are sampled from some distribution µ.

1 Shannon, 1948

• Consider a protocol where Alice’s ﬁrst message to Bob is a c-bit

The entropy of the message is 0.

string that is always 0c, no matter what her input is. This message
does not convey any information to Bob. We might as well run the
protocol imagining that this ﬁrst message has already been sent,
and so reduce the communication of the ﬁrst step to 0.

The entropy of the message is log

S

.

|

|

The entropy of the message is

en.

≈

• Consider a protocol where Alice’s ﬁrst message to Bob is a random
c, with

string from a set S
parties should use log
reducing the communication from c to log

2c.
In this case, the
}
bits to index the elements of the set,
S

0, 1
⊆ {
S
|

| (cid:28)

S

|

|

.

|

|

• Consider a protocol where Alice’s ﬁrst message to Bob is the

−

e, and is a uniformly random n bit

string 0n with probability 1
string with the remaining probability.
In this case one cannot
encode every message using fewer than n bits. However, Alice
can send the bit 0 to encode the string 0n, and the the string 1x
to encode the n bit string x. Although the ﬁrst message is still
quite long in the worst case, the expected length of the message is
1

e + e(n + 1) = 1 + en.

−

Shannon’s deﬁnition of entropy gives a general way to compute
the length of the smallest encoding of a message. Given a random
variable X with probability distribution p(x), deﬁne the entropy of X
to be



<!-- pdf-page: 2 -->
74 communication complexity

1

0.5

0

0

H (e)

0.5

e

1

Figure 6.1: The entropy of a bit with
p(1) = e.

H (X) = ∑
x

p(x) log(1/p(x)) = E

p(x) (cid:20)

log

1
p(x)

.

(cid:21)

The deﬁnition ensures that the entropy
is always non-negative.

Can you think of an example that
shows that the expected length needs to
be at least H (X) + 1?

The entropy of X characterizes the expected number of bits that need
to be transmitted to encode X.
Intuitively, if there is an encoding
of X that has expected length k, then X can be encoded by a string
of length 10k most of the time, so one would expect that X takes
on one of 2O(k) values most of the time, and so the expected value
of log(1/p(x)) should be O(k). Conversely, if the entropy of X is k,
then one can encode X using the positive integers, in such a way that
p(1)
j=1 p(i) > 1), so the expected
integer is at most 1/i (since otherwise ∑i
length of transmitting the number that encodes X should be bounded
by ∑i p(i) log i, which is at most the entropy. Formally, we can prove:

. . . . The probability that the sample for X is the i’th

p(2)

≥

≥

Theorem 6.1. X can be encoded using a message whose expected length is at
most H (X) + 1. Conversely, every encoding of X has expected length at least
H (X).

e

log(1/p(i))

p(i + 1). Let `i =

∑i p(i)(log(1/p(i)) + 1) = H (X) + 1. The encoding

Proof. Without loss of generality, suppose that X is an integer from
[n], with p(i)
. We shall encode i
d
≥
with a leaf at depth `i. Then the expected length of the message will
be ∑i p(i)`i ≤
is done greedily. In the ﬁrst step, we pick the ﬁrst vertex of the
complete binary tree at depth `1 and let that vertex represent 1. We
delete all of its descendants so that the vertex becomes a leaf. Next
we ﬁnd the ﬁrst vertex at depth `2 that has not been deleted, and use
it to represent 2. We continue in this way until every element of [n]
has been encoded. For i < j, the number of vertices at depth `j that
`i , so the number of vertices
are deleted in the i’th step is exactly 2

`j−



<!-- pdf-page: 3 -->
information 75

at depth j that are deleted before the j’th step is

j
1
−
∑
i=1

`j−

`i = 2

`j

2

j
1
−
∑
i=1

`i

2−

! ≤

`j

2

j
1
−
∑
i=1

p(i) < 2

`j ,

so some vertex will be available at the j’th step. This ensures that
every step of this process succeeds.

Conversely, suppose X can be encoded in such a way that i is
encoded using `i bits. Then the expected length of the encoding is:

E
p(i)

[`i] = E
p(i)

[log(1/p(i))]

−

E
p(i)

log(2−

`i /p(i))

H (X)

log

−

≥

2−

E
p(i)

h

h
`i /p(i)

i

!

i

By convexity of the log function,
log (E [Y]).
E [log Y]

≤

= H (X)

log

−

`i

2−

∑
i

.

!

If you pick a random path starting from the root in the protocol tree,
`i . The probability
you hit the leaf encoding i with probability 2−
that you hit one of the leaves encoding a number from [n] is thus
∑i 2−
most the expected length of the encoding.

is at most 0, and the entropy is at

1. Thus log

∑i 2−

≤

`i

`i

(cid:16)

(cid:17)

Entropy, Divergence and Mutual Information

The concepts of divergence and mutual information are
closely related to the concept of entropy. They provide a toolbox that
helps to understand the ﬂow of information in different situations.
The divergence between two distributions p(x) and q(x) is deﬁned to
be

p(x)

q(x)

= ∑
x

p(x) log

p(x)
q(x)

= E

p(x) (cid:20)

log

p(x)
q(x)

.

(cid:21)

The divergence is a measure of distance the two distributions.

p(x)

p(x)

= 0.

p(x)
q(x) ≥

0.

Clearly,

Fact 6.2.

Proof.

p(x)

q(x)

log

p(x)
q(x)

p(x) log

= E

p(x) (cid:20)
∑
x

−

=

(cid:21)
q(x)
p(x) ≥ −

log ∑
x

p(x)

q(x)
p(x)

= log 1 = 0.

The inequality follows from the convex-
ity of the log function.

 
 
 


<!-- pdf-page: 4 -->
76 communication complexity

0.8

γ

0.5

0.2

e log e

γ + (1 − e) log 1−e
1−γ

0.1

0.5
e

0.9

5

4.5

4

3.5

3

2.5

2

1.5

1

0.5

0

Figure 6.2: The divergence between two
bits.



<!-- pdf-page: 5 -->
information 77

However, the divergence is not symmetric:

p(x)

q(x)

=

q(x)

p(x)

in

general. Moreover, the divergence can be inﬁnite, for example if p is
supported on a point that has 0 probability under q. If X is an `-bit
string, we see that:

H (X) = E
p(x)

[log(1/p(x))] = `

−

E
p(x) (cid:20)

log

p(x)
`
2−

(cid:21)

= `

−

p(x)

q(x)

,

where q(x) is the uniform distribution on `-bit strings. So we see
that the entropy of a string is just a way to measure the divergence
from uniform. In particular, since the divergence is non-negative
(Fact 6.2), the uniform distribution has maximum entropy of all the
distributions on a set.

In our context, the divergence is most often measured between two
distributions that arise from the same probability space. For example,
if

is an event in a probability space containing x, we have

E

Fact 6.3.

p(x
)
|E
p(x) ≤

log 1
p(
E

) .

We can use divergence to quantify the dependence between two

random variables. If p(a, b) is a joint distribution, we deﬁne the
mutual information between a and b to be

I (A : B) = E

p(a,b) (cid:20)

log

p(a, b)
p(a)p(b)

= E

(cid:21)

p(a,b) (cid:20)

log

p(b
a)
|
p(b)

= E

p(a) "

(cid:21)

p(b
a)
|
p(b) #

.

H (AB). The mutual

We have that I (A : B) = H (A) + H (B)
information of any random variable with itself is the same as its en-
tropy I (A : A) = H (A). On the other hand, if A, B are independent,
I (A : B) = 0. In general, the mutual information is always a num-
H (A). The ﬁrst
ber between these two quantities: 0
inequality follows from Fact 6.2, and the second by observing:

I (A : B)

≤

≤

−

H (A)

−

I (A : B) = E

p(a,b) (cid:20)

= E

p(a,b) (cid:20)

log

log

1

p(a) −

log

p(a, b)
p(a)p(b)

(cid:21)

p(b)
p(a, b)

0.

≥

(cid:21)

Chain Rules

Chain rules allow one to relate bounds on the information of a
collection of random variables to the information associated with

Proof.

)

p(x
|E
p(x)

= E
p(x
|E

) (cid:20)

log

= E
p(x
|E

log

≤

log

) (cid:20)
1
p(

E

.

)

)

p(x
|E
p(x)

x)
)

p(
E |
p(
E

(cid:21)

(cid:21)

The entropy, mutual information and
divergence are all expectations over the
universe of various log-ratios.

6


<!-- pdf-page: 6 -->
78 communication complexity

each variable. Suppose p(a, b) and q(a, b) are two distributions. Then
we have

p(a, b)

q(a, b)

= E

p(a,b) (cid:20)

= E

p(a,b) (cid:20)
p(a)

q(a)

=

log

log

p(a)
q(a)

p(a)
q(a)

+ E

p(a) "

·
·

p(b
q(b

a)
|
a)
|
+ E

(cid:21)

p(a,b) (cid:20)
a)
|
a) #

.

(cid:21)
p(b

q(b

|

log

p(b
q(b

a)
|
a)
|

(cid:21)

In words, the total divergence is the sum of the divergence from the
ﬁrst variable, plus the expected divergence from the second variable.
Similar chain rules hold for the entropy and mutual informa-
tion. Suppose A, B are two random bits that are always equal. Then
H (AB) = 1
Nevertheless, a chain rule does exist for entropy. Denote

= H (A) + H (B), so the entropy does not add in general.

H (B

|

A) = E

p(a,b) (cid:20)

log

1
p(b

|

.

a)

(cid:21)

Then we have the chain rule2: H (AB) = H (A) + H (B

A).

|

Suppose A, B, C are three random bits that are all equal to each
other. Then I (AB : C) = 1 < 2 = I (A : C) + I (B : C). On the other
hand, if A, B, C are three random bits satisfying A + B + C = 0 mod 2,
we have I (AB : C) = 1 > 0 = I (A : C) + I (B : C). Nevertheless, a
chain rule does hold for mutual information, after we use the right
deﬁnition. Denote:

I (B : C

|

A) = E

p(a,b,c) (cid:20)

log

p(b, c

a)
|
a)p(c

p(b

|

.

a)

(cid:21)

|

Then we have the chain rule3: I (AB : C) = I (A : C) + I (B : C

A).

|

Subadditivity

Each of the deﬁnitions we have seen so far satisﬁes the property that
conditioning on variables can either only increase the quantity or
only decrease the quantity, a property that we loosely refer to as
subadditivity. We start with the divergence. Suppose p(a, b), q(a, b) are
two distributions. Then:

E
p(b) "

p(a
b)
|
q(a) #

= E

p(a,b) (cid:20)
p(a)

q(a)

=

log

p(a)
q(a)

+ log

b)
p(a
|
p(a)

+ I (A : B)

p(a)

q(a)

≥

(cid:21)

.

One consequence of this last inequality is:

log

2 H (AB) = E p(a,b)
log 1
E p(a,b)
A) .
H (B
h

h
p(a) + log

p(a)p(b
1
p(b

a)

|

|

i

1

=

a)

i

= H (A) +

|

3 I (AB : C) =
log p(a,c)
E p(a,b,c)
·
p(a)p(b
|
h
I (A : C) + E p(a,b,c)
I (A : C) + E p(a,b,c)
I (A : C) + I (B : C

=

p(b
a,c)
|
a)
p(c)
·
log p(b
a,c)
i
|
p(b
a)
|
log p(b,c
h
a)
p(b
·
A).

|

h
|

=

a

|

i

=

a)
i
|
p(c

6


<!-- pdf-page: 7 -->
Fact 6.4. If q(x1, . . . , xn) is a product distribution, then for any p,

p(x1, . . . , xn)
q(x1, . . . , xn ≥

n
∑
i=1

p(xi)
q(xi)

.

When it comes to entropy, we have:

H (AB) = H (A) + H (B)

I (A : B)

−

≤

H (A) + H (B) .

This last inequality also implies that

H (A)

≥

H (AB)

−

H (B) = H (A

B) .

|

We have already seen that conditioning on a random variable can
both decrease, or increase the mutual information. Nevertheless,
when A, B are independent, we can prove4:

I (AB : C)

≥

I (A : C) + I (B : C) .

Shearer’s Inequality

A useful consequence of subadditivity is Shearer’s inequality:

information 79

Proof of Fact 6.4.

p(x1, . . . , xn)
q(x1, . . . , xn

n
∑
i=1

n
∑
i=1

n
∑
i=1

=

=

≥

E
p(x<i "

E
p(x<i "

x<i)
x<i) #

p(xi|
q(xi|
p(xi|
q(xi)

x<i)

#

p(xi)
q(xi)

.

4 I (AB : C)
I (B : C
A)
|
H (B
AC)
|
since H (B
H (B

−
−
−
AC)
|

≤
A) = H (B).

I (B : C) =
A)

I (A : C)
−
I (B : C) = H (B
H (B) + H (B
C)
|
≥
C), and

H (B

|

|

−
0,

|

Lemma 6.5. Suppose X = X1, . . . , Xn is a random variable and S
set sampled independently of X. Then if p(i
e for every i
have H (XS |
Proof. Suppose S =

, with a < b < c. Then we can express

H (X).

a, b, c

[n] is a
[n], we

⊆
∈

S)

S)

≥

≥

∈

e

·

}

{
H (XS) = H (Xa) + H (Xb |
X<a) + H (Xb |
H (Xa |
by subadditivity. In general, we get that

≥

Xa) + H (Xc |

Xa, Xb)
X<b) + H (Xc |

X<c) ,

∑
S
i
∈

H (Xi |

X<i)

#

H (XS |

S)

≥

=

E
S "
n
∑
i=1

p(i

S)H (Xi |

∈

X<i)

e

·

≥

H (X) .

Pinsker’s Inequality

Pinsker’s inequality bounds the statistical distance between two
distributions in terms of the divergence between them.

Lemma 6.6.

p(x)
q(x) ≥

2
ln 2 · |

p

2.

q

|

−



<!-- pdf-page: 8 -->
80 communication complexity

0.8

γ

0.5

0.2

0.1

e log e

γ + (1 − e) log 1−e
1−γ

− 2

ln 2 (e − γ)2

0.6

0.5

0.4

0.3

0.2

0.1

0

0.5
e

0.9

Figure 6.3: Pinsker’s Inequality



<!-- pdf-page: 9 -->
Proof. Let T be the set that maximizes p(T)

q(T), and deﬁne

−

information 81

1 if x

T,

∈

0 otherwise.

xT =




q(T) = p(xT = 1)



−

q(xT = 1). We shall prove:

Then,

|

p

q

= p(T)

|

−
p(x)
q(x) ≥

−
p(xT)
q(xT)
2
ln 2 ·

(p(xT = 1)

q(xT = 1))2 =

−

2
ln 2 · |

p

2.

q

|

−

≥

f
g

0

0.67

1

e

Figure 6.4: f = e log e
e) log 1
1/3 , g = 2
−

ln 2 (e

2/3 + (1
2/3)2.

e

−

−

The ﬁrst inequality follows from the chain rule for divergence. It
only remains to prove the second inequality. Suppose p(xT = 1) =
e

q(xT = 1) = γ. Then we shall show that

≥

e log

e
γ

+ (1

−

e) log

e
γ −

2
ln 2 ·

(e

−

γ)2

1
1

−
−

(6.1)

is always non-negative. (6.1) is 0 when e = γ, and its derivative with
respect to γ is

e
−
γ ln 2
γ

=

(γ

=

+

(1
eγ

−
γ(1

−
ln 2

−
e)

1

e

−
γ) ln 2 −
−
e + eγ
−
γ) ln 2 −
1

e)

4(γ

−
ln 2

e)

4(γ

−
ln 2

γ(1

(cid:18)

−

γ) −

4

.

(cid:19)

1
γ(1

Since
γ) is always at most 4, the derivative is non-positive when
γ < e, and non-negative when γ > e. This proves that (6.1) is always
non-negative, as required.

−

Pinsker’s inequality implies that two variables that have low
information with each other cannot affect each other’s distributions
by much:

Corollary 6.7. If A, B are random variables then on average over b,

e
≈

p(a

b)

p(a), where e =

ln 2

I(A:B)
2

·

.

|
Another useful corollary is that conditioning on a low entropy
random variable cannot change the distribution of many other inde-
pendent random variables:

q

Corollary 6.8. Let A1, . . . , An be independent random variables, and B
[n] be uniformly random and independent
be jointly distributed. Let i
p(ai), where
of all other variables. Then on average over b, i, p(ai|
e
≤

H(B) ln 2
2n

e
≈

b)

∈

.

q



<!-- pdf-page: 10 -->
82 communication complexity

Proof. By subadditivity, we have:

H (B) /n

≥

≥

I (A1, . . . , An : B) /n

(1/n)

n
∑
j=1

I

Aj : B

.

(cid:0)

(cid:1)

Thus we get that for a uniformly random coordinate i,

E [I (Ai : B)]

H (B) /n.

≤

The bound then follows from Corollary 6.7.

Some Examples from Combinatorics

The entropy function has found many applications in combina-
torics, where it can be used to give simple proofs. Here we give a few
examples that illustrate its power.

On the Size of Projections

Let S be a set of n3 points in R3, and let Sxy, Syz, Sxz denote the pro-
jections of S onto the xy, yz, xz planes.

Claim 6.9. One of the three projections must have size at least n2.

Proof. Let X, Y, Z be the coordinates of a uniformly random point
from S. By Shearer’s inequality,

H (XY) + H (YZ) + H (XZ)
3

2
3 ·

≥

H (XYZ) = 2 log n,

so one of the ﬁrst three terms must be at least 2 log n, proving that
the projection must be of size at least n2.

Figure 6.5: A set in R3 projected to the
three planes.



<!-- pdf-page: 11 -->
On the Size of Triangle Intersecting Graphs

Suppose
intersect. Then we claim:

F

is a family of subsets of [n] such that any two sets from

Claim 6.10.

2n

1.

−

|F | ≤

information 83

F

Proof. For any set T
half of all the sets can be in

∈ F

, its complement cannot be in

. So only

F

.

F

G

Let

be a family of graphs on n vertices such that every two
graphs intersect in a triangle5. Such a family can be obtained by
choosing a ﬁxed triangle, which gives 2(n
2)/8 graphs. This bound is
known to be tight6, but here we give a simple argument that provides
a partial converse7:

Theorem 6.11.

|G| ≤

2(n

2)/4.

Proof. Let G be a uniformly random graph from the family. G can
be described by a binary vector of length (n
2), where each bit indi-
cates whether a particular edge is present or not. Let S be a random
subset of n/2 of the vertices, and let GS denote the graph obtained
by deleting all edges that go from S to the complement of S. Since
the probability that any particular edge is retained is exactly 1/2,
Shearer’s inequality gives ES [H (GS |

Now any two graphs G, G0 in the family intersect in a triangle, so
we must have that GS, G0S must share an edge in common, no matter
what S is, because at least one of the edges of the triangle will not be
thrown away in the above process. But this means that the number of
such projections is at most half of all possible projections, by Claim

H (G) /2.

S)]

≥

Figure 6.6: Two intersecting families of
sets on a universe of size 3.

5 A cycle of length 3

6 Ellis et al., 2010

7 Chung et al., 1986

6.10. Writing e(S) = (|
2 ) + (n
edges possible in the graph GS, this means that H (GS) + 1
expectation exactly half of the edges contribute to e(S), so we get:

2 ) for the total number of

− |

≤

S

S

|

|

e(S). In

1

2 · (n

2) = E

S

[e(S)]

E
S

[H (GS |

≥

S)] + 1

1
2 ·

≥

H (G) + 1,

Very similar ideas can be used to show
that any family of graphs that intersects
in an r-clique can be of size at most

2(n

2)/2r

1. See Exercise 6.4.

−

≤ (n

2) −

2, which implies that

|G| ≤

2(n

2) −

2

=

and so H (G)
2)/4.

2(n

An Isoperimetric Inequality in the Hypercube

n and the edges
The hypercube is the graph who vertex set is
connect two vertices that disagree in exactly one coordinate. The
hypercube contains 2n vertices and 2nn/2 edges. Here we give a tight
bound on the number of edges in any subset of the vertices8:

0, 1

{

}

8 Samorodnitsky. Ref?



<!-- pdf-page: 12 -->
84 communication complexity

Theorem 6.12. If S
log
most |
2

S

S

.

|

|

|

0, 1

}

⊆ {

n, the number of edges contained in S is at

Proof. Let e(S) denote the number of edges in S. Let X be a uni-
formly random element of S. Then for any vertex x
S and y such
that x, y is an edge of the hypercube where x, y disagree in the i’th
coordinate, we have

∈

H (Xi |

X

−

i = x

−

i) =

1 if (x, y) is an edge that is contained in S,




0 otherwise.

So ∑x
i = x

−
twice. By subadditivity,

[n] H (Xi |

X

S,i

∈

∈

i) = 2e(S), since each edge is counted

−

Here X
X1, X2, . . . , Xi

−

i denotes

1, Xi+1, . . . , Xn.

−

log

S

|

|

= H (X) =

n
∑
i=1

H (Xi |

X<i)

≥

n
∑
i=1

H (Xi |

X

−

i) =

proving that e(S)

S

|

|

log
2

S

|

|

.

≤

Lower bound for Indexing

2e(S)
S

|

|

,

We now have enough information theory tools to prove some lower
bounds in communication complexity. Suppose Alice has a random n
[n]. The goal of the
bit string x, and Bob is given a random index i
players is to compute the i’th bit, xi, but the protocol must start with
a message from Alice to Bob, and then Bob must output the answer.
We prove that Ω(n) bits of communication are necessary, even if the
parties are only looking for an average-case protocol.

∈

Suppose there is a protocol for this problem where Alice sends
a message M that is ` bits long. Then by Corollary 6.8, on average
p(xi),
over the choice of m and a random coordinate i, p(xi|
` ln 2
2n . Since p(xi) is uniform for each i, the probability
with e =
that Bob makes an error in the i’th coordinate must be at least 1/2
p(xi|
|
1/2
−
protocol has a small probability of error.

q
−
p(xi)
. So the probability that Bob makes an error is at least
−
` ln 2
2n , proving that at least Ω(n) bits must be transmitted if the

e
≈

m)

m)

|

q

Randomized Communication of Disjointness

One of the triumphs of information theory is its ability to prove
optimal lower bounds on the randomized communication complexity
of functions like disjointness9, which we do not know how to prove
any other way.

If Bob could tell Alice i in the ﬁrst step,
that would give a log n bit protocol.

Proving a deterministic lower bound
for this problem is easy: after Alice’s
message, Bob must know the entire
n-bit string. So Alice must send n bits.

The square-root dependence is tight: If
Alice sends the majority of all her bits,
that bit is equal to a random coordinate
with probability 1/2 + Ω(1/√n). See
Exercise 6.2.

9 Kalyanasundaram and Schnitger, 1992;
Razborov, 1992; Bar-Yossef et al., 2004;
and Braverman and Moitra, 2013

This result is especially impactful
because many other lower bounds
in other models (more in Part II) are
consequences of Theorem 6.13.



<!-- pdf-page: 13 -->
Theorem 6.13. Any randomized protocol that computes disjointness
function with error 1/2

e must have communication Ω(e2n).

−

Obstacles to Proving Theorem 6.13

The natural way to prove lower bounds on randomized protocols is
to ﬁnd a hard distribution on the inputs, such that any protocol with
low communication must make an error a signiﬁcant fraction of the
time. This is the approach we took when we proved lower bounds
on the inner-product function (Theorem 5.6), and the same distri-
bution works to understand the pointer-chasing problem (Theorem
6.16). In those cases, the uniform distribution on inputs is a hard
distribution. But the uniform distribution is not a hard distribution
for disjointness: two uniformly random sets A, B will intersect with
very high probability, so the protocol can output 0 without communi-
cating and still have very low error. In fact, it can be shown that any
distribution where A and B are independent cannot be used to prove
a strong lower bound. So we must use a hard distribution where
A, B are correlated.

A natural distribution to use, given these constraints, is a convex
combination of two uniformly random disjoint sets, and two sets that
intersect in exactly one element. Once we restrict our attention to
B
such a distribution, we have a second challenge: the events i
A
∩
= j. This makes arguments
and j
involving subadditivity much harder to carry out. The subtleties in
the proof arise from coming up with technical ideas that allow us to
circumvent these obstacles.

B are not independent for i

∈

∩

∈

A

Proving Theorem 6.13

Given a randomized protocol with error 1/2
error an arbitrarily small constant by repeating the protocol O(1/e2)
times and outputting the majority outcome. So to prove the lower
bound, it sufﬁces to show that any protocol with error < 1
32 must
have communication Ω(n).

e, one can make the

−

We start by deﬁning a hard distribution on inputs. View the

A.
[n] uniformly at random, and let AT, BT to be

sets A, B as n-bit strings, by setting Ai = 1 if and only if i
Pick an index T
∈
= T, sample (Ai, Bi) to be one
random and independent bits. For i
of (0, 0), (0, 1), (1, 0) with equal probability, and independent of all
other paris (Aj, Bj). A and B intersect in at most 1 element, and they
intersect with probability 1
4 .

∈

Let S denote the messages of a deterministic protocol of communi-
cation `. Let Q denote the random variable T, A<T, B>T. Observe that
conditioned on any ﬁxing of S, Q, A, B become independent:

information 85

By Theorem 3.3, Theorem 6.13 is
equivalent to the existence of such a
hard distribution.

Intuitively this is because if the enropy
H (A) << n then Alice can encode her
set with much less than n bits and send
it to Bob. On the other hand, if A, B are
independent and H (A) , H (B) are both
large, the sets will intersect with high
probability, and the parties need not
communicate to compute disjointness.

Note that the n coordinates
(A1, B1), (A2, B2), . . . , (An, Bn) are
not independent, a complication that
makes the proof subtle.

6
6


<!-- pdf-page: 14 -->
q) = p(a

Proof of Claim 6.14: After ﬁxing Q,
A, B become indepenent: for every q,
q). Since ﬁxing S
p(b
p(ab
restricts the inputs to a rectangle, A, B
remain independent after ﬁxing S: for
qs).
qs) = p(a
every q, s, p(ab

p(b

qs)

q)

|

|

·

|

|

|

·

|

Note that p(at|
uniform for any q.

q) and p(bt|

q) are both

86 communication complexity

Claim 6.14. For every q, s, p(ab

qs) = p(a

qs)

p(b

qs).

|
Suppose the error of the protocol on A, B is at most 1

|

·

|

qs) is ν1-close to uniform, and p(bt|

that for any q, s, if p(at|
close to uniform, then the probability that the protocol makes an
error conditioned on q, s is at least 1
that the sets will be disjoint is within ν1 + ν2 of 1
αqs =

ν2, since the probability
4 . Thus, denoting
p(bt|

and βqs =

p(at|

p(bt|

ν1 −

4 −

qs)

q)

q)

−

−

|

|

|

|

:

32 . Observe
qs) is ν2-

qs)

p(at|
1
32 ≥

1
4 −

E
p(q,s) (cid:20)

αqs −

βqs

(cid:21)

p(at = 0 = bt)

≥

·

p(q,s

E
at=0=bt) (cid:20)

|

1
4 −

αqs −

βqs

,

(cid:21)

which implies that

E
at=0=bt)

p(q,s

|

αqs + βqs

(cid:2)

(cid:3)

1
4 −

1
8

=

1
8

,

≥

and so one of the two terms in the expectation must be at least 1
16 .
Without loss of generality, say we have

E
at=0=bt)

p(q,s

|

αqs

(cid:2)

(cid:3)

1
16

,

≥

then we can write:

E
bt=0)

|

p(q,s

αqs

(cid:2)

(cid:3)

≥

≥

p(at = 0

bt = 0)

|

1
32

.

E
at=0=bt)

·

p(q,s

|

αqs

(cid:2)

(cid:3)

(6.2)

Intuitively, (6.2) says that the protocol learns a signiﬁcant amount of
information about at, even conditioned on the event that bt = 0. We
shall use the subadditivity of information to show that this can only
happen if many bits are communicated. We need a technical lemma:

Lemma 6.15. Let X = X1, . . . , Xn and Y = Y1, . . . , Yn be random variables
such that the n tuples (X1, Y1), . . . , (Xn, Yn) are mutually independent. Let
M be another random variable in the same space. Then

n
∑
i=1
n
∑
i=1

I (Xi : M

I (Yi : M

|

|

X<iY
≥

i)

≤

I (X : M

iY>i)

X

≤

≤

I (Y : M

Y) ,

X) .

|

|



<!-- pdf-page: 15 -->
information 87

Proof. Using the chain rule repeatedly:

n
∑
i=1

I (Xi : M

X<iY
≥

i)

|

n
∑
i=1
n
∑
i=1
n
∑
i=1

≤

=

=

I (Xi : MY<i |

X<iY
≥

i)

I (Xi : Y<i |

X<iY
≥

i) + I (Xi : M

X<iY)

|

I (Xi : M

|

X<iY) = I (X : M

Y) .

|

Since I (Xi : Y<i |

X<iY
≥

i) = 0.

The second bound is proved similarly.

Now we shall use Lemma 6.15 and Pinsker’s inequality to bound

the error ν of the protocol. Let
disjoint. Then we see that p(ab
Lemma 6.15. Moreover, conditioned on
)
p(abt

D
|D

p(t

D

). So Lemma 6.15 gives:

denote the event that A, B are
) satisﬁes the assumptions of

, T is independent of A, B:

|D

) = p(ab
`

|D

|D
·
I (AT : S

n ≥
Since p(bt = 0

3 , (6.3) implies that

TA<T B

≥

TD

|

) = I (AT : S

QBTD

)

|

(6.3)

) = 2
|D
`

n ≥
3`
2n ≥

⇒

p(bt = 0

)

·

|D

I (AT : S

|

Q, BT = 0,

)

D

I (AT : S

= I (AT : S

)

Q, BT = 0,

D
Q, BT = 0) ,

|

|

Since BT = 0 implies

.

D

By Pinsker’s inequality (Corollary 6.7) we get:

3` ln 2

4n ≥

p(qs

r

=

p(qs

E
bt=0)
|
E
bt=0)

|

[

[

|

|

p(at|
p(at|

qs, bt = 0)

p(at|
] =

−
p(at|

q)

|

q, bt = 0)

]

|

E
bt=0)

|

p(qs

qs)

−

Combining this with (6.2), we get that
`

Ω(n), as required.

≥

3` ln 2
4n ≥

q

(cid:2)
1
32 , proving that

(cid:3)

αqs

.

Recall Claim 6.14.

Lower bound for Number of Rounds

Are interactive protocols more powerful than protocols
that do not have much interaction?10 Here we show that a protocol
with more rounds can have signiﬁcantly less communication than a
protocol with fewer rounds.

In the k step pointer-chasing problem, Alice and Bob each have a

string x, y

∈

[n]n. Deﬁne 1 = z0, z1, z2, . . . using the rule

if i is odd,

if i is even.

zi =

xzi
yzi

1

−

1

−






10 Yao, 1983; Duris et al., 1987; Halsten-
berg and Reischuk, 1993; and Nisan and
Wigderson, 1993



<!-- pdf-page: 16 -->
88 communication complexity

The goal of the parties is to output whether or not zk > n/2.

k

1

−

≤

∈
−

10n/k.

[n]n be uniformly distributed, and let m
1 denote
1 messages of a protocol computing whether or not

There is an obvious deterministic protocol that takes k rounds
and k log n bits of communication: in each step one of the players
announces z1, z2, . . . , zk. There is a randomized protocol with k
−
rounds and O((k + n/k) log n) bits of communication. In the ﬁrst
step, Alice and Bob each announce the values of xi, yi, for i
Alice and Bob then continue to use the deterministic protocol, but
do not communicate if one of the values they need has already been
10 rounds11.
announced. In expectation, this protocol will have k + 1
We shall prove that any randomized or deterministic protocol with
1 rounds must have much more communication.
−
Let x, y
the ﬁrst k
zk > n/2, and the communication complexity of the protocol is `.
The key idea here is quite similar to the lower bound for the indexing
problem. We will try to argue by induction that zk remains random
even after conditioning on m<k. Suppose k is even. Then intuitively,
if Alice sends the message mk
that zk
is independent of zk after ﬁxing m<k
like a random coordinate of y
uniform. On the other hand, if Bob sends mk
close to uniform conditioned on m<k
is independent of y, mk
coordinate of y

1, but now mk
−
m<k) is distributed
−
1, which is likely to be close to
1, then zk
1 is again
1 by induction, and now zk
1
−
m<k) is distributed like a random

1 is close to random conditioned on m<k
1. So p(zk|

1, we will have shown by induction

m<k, which is again close to uniform.

1, so p(zk|

m<k

−

−

−

−

−

≤

−

−

−

−

|

1

k

|

Theorem 6.16. Any randomized k
−
pointer chasing problem that is correct with probability 1/2 + e requires

1 round protocol for the k-step

e2n

(k

−

1)2 −

k log n bits of communication.

Proof. The proof will proceed by induction. We shall show that
zk remains close to uniformly random, even conditioned on the
messages that have been sent in the ﬁrst k
uniform (when we do not condition on any of the messages).

1 rounds. Initially, z1 is

−

Let rk denote the random variable m1, . . . , mk, z1, . . . , zk. We shall

Since the information about the number
of rounds is lost once we move to
viewing a protocol as a partition into
rectangles, it seems hard to prove a
separation between a few rounds and
many rounds using the techniques
we have seen before. A protocol with
low communication will have a large
rectangle, so we cannot bound the
size of rectangles to get a separation
between interactive protocols and
non-interactiveprotocols.

11 It can be shown that this randomized
protocol will have < k rounds with
high probability. Indeed, the probability
that none of the announced values
help to save a round of communication
is exponentially small in k, as long
as Ω(k) of the values zi are distinct.
For a uniformly random input, most
of the zi’s will be distinct with high
probability.

Theorem 6.16 actually proves that
the communication is at least
Ω(n/k2) in the randomized set-
ting with k
1 rounds. This is
because when k < 3
n/ log n,

−

e2n

1)2 −

k log n = Ω(n/k2), and
p

4(k
−
when k
n/ log n, the communica-
tion must be at least k which is again
Ω(n/k2).

p

≥

3

prove by induction on k that on average over rk

close to uniform, with e
imply that `

e2n

(k

−

≤
k log n.

≥

(k

−

1)2 −

The case when k = 1 is trivial. Suppose k

`+log n
n

1)

q

1, p(zk|

rk

−

−

1) is e-

. Rearranging, this would

2, mk

1 contains at most ` + k log n bits of information,
Since rk
Corollary 6.8 implies that if i is a uniformly random coordinate
2, mk
independent of all other variables, then on average over i, rk

−

−

≥

1,

−

−

2 and k is even12.

12 The proof is exactly the same when k
is odd.

p(yi|

rk

−

2)

e0
≈

p(yi)

e0
≈

p(yi|

mk

−

1, rk

−

2),



<!-- pdf-page: 17 -->
where e0 =

`+k log n
n

. There are two cases to consider:

information 89

γ

Fact: If i, j, a are independent, and
p(j), we have p(ai)

p(i)
p(aj). See
the Conventions chapter of the book for
a proof.

≈

≈

γ

q
Bob sends the message mk

1 In this case, after ﬁxing rk

2, zk

1 is inde-

−
pendent of yi for every i. By induction, p(zk
uniform, with e = (k

1|
. So on average over rk

`+k log n
n

2)

rk

−

−

−
−
2) is e-close to

1, i,:

−

−

q

p(zk|

rk

−

1) = p(yzk

−

e
≈

−

−

2)

mk

mk

1, rk

p(yi|
1 |
1 In this case, p(yi|
rk
−
1, zk

−

2, yi is independent of mk

−

−

2)

1, rk

p(yi).

e0
≈
1) = p(yi|
1. So on average

rk

−

2), since

−

−

Alice sends the message mk

after ﬁxing rk
over rk

1, i:

−

−

p(zk|

rk

−

1) = p(yzk

2)

rk

−

1 |

−

e
≈

p(yi|

rk

−

2)

e0
≈

p(yi).

Both of these bounds imply that p(zk|
uniform, as required.

rk

−

1) is (k

1)

−

q

`+k log n
n

-close to

Very similar intuitions can be used to show that the deterministic
communication of the pointer-chasing problem is Ω(n) if fewer than
k rounds of communication are used.

Theorem 6.17. Any k
k-step pointer-chasing problem requires n

−

1 round deterministic protocol that computes the

k bits of communication.

16 −

1 round deterministic protocol with com-
1 denote the

Proof. Consider any k
−
munication complexity `
messages of the protocol. Let ri denote z0, z1, . . . , zi, m1, . . . , mi. Let p
denote the uniform distribution on inputs to the protocol. We shall
show by induction on i that there is a ﬁxed value of ri such that

k, and let m1, . . . , mk

n
16 −

≤

−

• z0, z1, . . . , zi are all distinct.

ri) is e-close to uniform, with e = 2

• p(zi+1|
• p(m
z

i|

≤

i)

≤

≥

2−|

m

i|−

≤

i.

`+k
n ≤

1/4.

q

−

−

−

rk

1 shows that the protocol cannot

1) cannot be close to uniform.

1 contains all the messages in the ﬁrst k rounds,

The ﬁrst property applied to i = k
be correct, since rk
and so p(zk|
When i = 0, the claims are trivially satisﬁed. Now suppose i > 0 is
even13, so zi+1 = xzi . By induction, there exists a setting of ri
1 that
satisﬁes the given conditions. We only need to show that there exists
a setting of values for zi, mi to append to ri
1 to obtain the setting of
ri that we want. There are two cases:

−

−

13 The proof is symmetric when i is odd.

Alice sends the i + 1’st message In this case, ﬁxing ri

1 leaves mi and zi

independent. Pick mi by greedily setting each bit of mi in such a

−



<!-- pdf-page: 18 -->
90 communication complexity

way that the probability of that bit is maximized conditioned on
ri

1 and all previous bits. This ensures that

−

p(mi|

ri

−

1)

≥

2−|

mi|.

To choose zi, deﬁne

B1 =

{

j :

z0, z1, . . . , zi
p(xj|

1}
−
mi, ri
p(xj)
p(Zi = j
ri
|
p(Zi = j
z

−

B2 =

(

B3 =

j :

(cid:26)

1)

> 4

` + k

·

n )

1)
1)

−
i

|

≤

−

< 1/2

(cid:27)

We shall prove:

Claim 6.18.

B1 ∪

|

B2 ∪

B3|

< n.

B3| ≤
|
p(Zi ∈

Proof. Obviously,

We have

k

−

1 < n/16

`

−

≤

n/16.

n/2, or else we would have

|
2en

B1| ≤
≤

i

z

−

≤

1)

B3|

p(Zi ∈
contradicting the fact that p(zi|
ri
B1| ≤
We shall prove that

B2 −

−

|

ri

B3|

−

1) > 2e

−

e = e,

1) is e-close to uniform.

−
n/4. Observe that:

B2 −

|

B1| ·

4

·

` + k

n ≤

∑
B2−

j

∈

B1

p(xj|

mi, ri
p(xj)

1)

−

= ∑
B2−
j
B1
∈
p(x[n]

p(xj|

i
≤
−
1)

−
1)

i, z
≤
z

i

≤

m
p(xj|
i, z
m
≤
z
B1 |

≤

i

i
≤
−
1)

−

1)

.

Since xj is independent of z
j /
∈

B1.

1 for all

i

≤

−

By Fact 6.4. Here x[n]
projected to the coordinates that are not
in B1.

denotes x

B1

−

−
p(x[n]

B1 |

−

≤

By the choice of mi, we have

p(m

z

i|

≤

i

≤

−

1) = p(mi|
ri
mi|
2−|
≥

·

1)

−
2−|

·
m

p(m

≤
1|−

i

≤

−

i

1|
−
i+1

z

1)
`

i

−
≤
2−

k,

−

≥

So we can apply Fact 6.3 to conclude that

p(x[n]

−
p(x[n]

m

i, z
≤
z
B1 |

≤

i

i
≤
−
1)

−

B1 |

−

1)

` + k,

≤

giving that
n/4 = n.

B2 −

|

B1| ≤

n/4. Thus

B1 ∪

|

B2 ∪

B3|

< n/16 + n/2 +



<!-- pdf-page: 19 -->
information 91

1)

−

1)

−

p(m

i

1|

−

≤

z

i

≤

−

1)

·

p(m

i
≤
−
p(m

=

=

p(zi|

z

1|
i

≤

≤

i)
1, zi|
z

−

p(zi|
m
p(zi|

≤

i
≤
−
1, z

i

−

≤

i
−
z

z
i
≤
1)

i
≤
1)

Set zi to be an arbitrary element outside of B1 ∪
completes the description of ri. Since zi /
∈
Since after ﬁxing mi, ri, x is independent of y, the distribution of
ri) is the same as the distribution of p(xzi |
1). Thus it is
p(xzi |
`+k
n -close to uniform by Pinsker’s inequality and the fact that
2
·
B3.
zi /
q
∈

B1, z0, . . . , zi are distinct.

B3. This

B2 ∪

miri

−

Finally, we have:

p(m

z

i|

≤

≤

ri

−

i) = p(mi|
mi|
2−|

≥

·

2−|

m

i

i|−

≤

·

≥

i)
1)

1)
·
p(zi|

z

≤

p(m
i
1|
−
≤
m
1, z
i
≤
1)
p(zi|
≤
(1/2) = 2−|

i
−
z

−

≤

m

i

−

(i+1)

i|−

≤

p(m

i

1|

−

≤

z

i

≤

−

1)

·

by the choice of mi, and the fact that zi /
∈

B2.

Bob sends the i + 1’st message In this case, we pick zi ﬁrst. Deﬁne the

sets:

B1 =

{

z0, z1, . . . , zi
p(xj|

j :

1}
−
1)

ri
−
p(xj)
p(Zi = j
ri
|
p(Zi = j
z

B2 =

(

B3 =

j :

(cid:26)

> 4

` + k

·

n )

1)
1)

−
i

|

≤

−

< 1/2

(cid:27)

Analogous to Claim 6.18, we have

Claim 6.19.

B2 ∪
B1 ∪
n/16 and

|
B1| ≤
We shall prove that

Proof.

|

< n.

B3|
B3| ≤
B1| ≤

|
B2 −
` + k

|

·

n ≤

B2 −

|

B1| ·

4

n/2, as proved in Claim 6.18.

n/4. Observe that:

∑
B2−

j

∈

B1

1)

p(xj|

ri
−
p(xj)

= ∑
B2−
j
B1
∈
p(x[n]

≤

B1 |
−
p(x[n]

1, z

p(xj|

i

≤

m
p(xj|
m

i

−
z

≤
1, z

−
z

≤
B1 |

−

i

−

≤

i

−

i
≤
1)

` + k,

≤
n/4. Thus

giving that
n/4 = n.

B2 −

|

B1| ≤

B1 ∪

|

B2 ∪

B3|

< n/16 + n/2 +

B3, and pick mi by
We let zi be an element that is not in B1 ∪
greedily setting each bit of mi in such a way that the probability of
that bit is maximized conditioned on ri

1, zi and all previous bits.

B2 ∪

−

i
≤
1)

1)

−

Since xj is independent of z
j /
∈

B1.

1 for all

i

≤

−

1)

−

By Fact 6.4.

Using p(m
Fact 6.3.

i

1|

−

≤

z

i

≤

−

1)

≥

`

2−

k, and

−



<!-- pdf-page: 20 -->
92 communication complexity

Clearly, z0, . . . , zi are all distinct. p(xzi |
1), which is 2
as p(xzi |
inequality and the fact that zi /
∈

B2.

q

ri

−

Finally, we have

ri) has the same distribution

`+k
n -close to uniform by Pinsker’s

p(m

z

i|

≤

≤

i)

≥

≥

≥

as required.

ri

−

p(mi|
mi|
2−|

·

m

2−|

≤

i|−

·

1, zi)
p(zi|
r
≤
p(zi|
z
(i+1),

≤

≤

p(m
1)
1) ·

−
i

i

−

z

i)

≤

i

−

1|
p(m

i

1|

−

≤

z

i

≤

−

1)

Lower bounds on Non-Negative Rank

Exercise 6.1

Show that for anys two joint distributions p(x, y), q(x, y) with same
support, we have

E
p(y) "

p(x
y)
p(x) # ≤

|

E
p(y) "

p(x
y)
|
q(x) #

.

Exercise 6.2

Suppose n is odd, and x

0, 1
from the set of strings that have more 1’s than 0’s. Use Pinsker’s
inequality to show that the expected number of 1’s in x is at most
n/2 + O(√n).

n is sampled uniformly at random

∈ {

}

Exercise 6.3

Let X be a random variable supported on [n] and g : [n]

function. Prove that

[n] be a

→

Pr[X

= g(X)]

H (X

g(X))
|
log n

1

.

−

≥

Use the fact that α log α
for α > 0.

≥

−

log e
e ≥ −

1,

Use this bound to show that if Alice has a uniformly random
[n]n, and Bob has uniformly random input i
[n],
vector y
and Alice sends Bob a message M with that contains ` bits, the
probability that Bob guesses yi is at most 1+`/n
log n .

∈

∈

Exercise 6.4

be a family of graphs on n vertices, such that every two

Let

G

vertices in the graph share a clique on r vertices. Show that the

number of graphs in the family is at most 2(n

2)/2r

1.

−

6

