<!-- generated-by: proofmatch local extraction -->
<!-- source-pdf-sha256: 50833afe740311645b86221ba7175d9c5dcecea394eb400cb4b9ccfcf341ce65 -->
<!-- extractor: pdfminer.six v20260107 -->

<!-- pdf-page: 1 -->
Chapter 8

Generalized domains

→

R. What about, say, f : {0, 1, 2}n

So far we have studied functions f : {0, 1}n
→
R? In fact, very little of what we’ve done so far depends on the domain be-
ing {0, 1}n; what it has mostly depended on is our viewing the domain as a
product probability distribution. Indeed, much of analysis of Boolean func-
R where the
tions carries over to the case of functions f : Ω1
Ωn
domain has a product probability distribution π1
πn. There are two
main exceptions: the “derivative” operator Di does not generalize to the case
when
2 (though the Laplacian operator Li does), and the important
notion of hypercontractivity (introduced in Chapter 9) depends strongly on
the probability distributions πi.

× · · · ×
⊗ · · · ⊗

Ωi

| >

→

|

In this chapter we focus on the case where all the Ωi’s are the same, as
are the πi’s. (This is just to save on notation; it will be clear that everything
we do holds in the more general setting.) Important classic cases include
functions on the p-biased hypercube (Section 8.4) and functions on abelian
groups (Section 8.5). For the issue of generalizing the range of functions – e.g.,
studying functions f : {0, 1, 2}n

{0, 1, 2} – see Exercise 8.33.

→

8.1. Fourier bases for product spaces

We will now begin to discuss functions on (ﬁnite) product probability spaces.

Deﬁnition 8.1. Let (Ω, π) be a ﬁnite probability space with
sume π has full support. For n
∈
product space of functions f : Ωn

N+ we write L2(Ωn, π⊗

R, with inner product

Ω

2 and as-
| ≥
n) for the (real) inner

|

→

Here π⊗

n denotes the product probability distribution on Ωn.

f , g

〈

〉 =

x

E
π⊗
∼

n

[ f (x)g(x)].

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.

207



<!-- pdf-page: 2 -->
208

8. Generalized domains

Example 8.2. A simple example to keep in mind is Ω
π(b)

1/3. Here a, b, and c are simply abstract set elements.

π(c)

=

{a, b, c} with π(a)

=

=

=

We can (and will) generalize to nondiscrete probability spaces, and to
complex inner product spaces. However, we will keep to the above deﬁnition
for now.

Notation 8.3. We will write π1/2 for the uniform probability distribution
1, 1}. Thus so far in this book we have been studying functions in
on {
−
1, 1}n, π⊗
L2({
−

1/2). For simplicity, we will write this as L2({
−

1, 1}n).

n

Notation 8.4. Much of the notation we used for L2({
−
to the case of L2(Ωn, π⊗
f (x)
|
notation from Chapter 3.3.

n): e.g.,

n [
|

Ex

π⊗

=

k

k

∼

f

p

1, 1}n) extends naturally
p]1/p, or the restriction

As we described in Chapter 1.4, the essence of Boolean Fourier analysis

is in deriving combinatorial properties of a Boolean function f : {
→
−
R from its coefﬁcients over a particular basis of L2({
1, 1}n), the basis of
parity functions. We would like to achieve the same thing more generally for
functions in L2(Ωn, π⊗
n). We begin by considering vector space bases more
generally.

−

1, 1}n

Deﬁnition 8.5. Let
| =
L2(Ω, π) is just the set of m indicator functions (1x)x

|

Ω

m. The indicator basis (or standard basis) for

Ω, where
∈

1x(y)

1 if y

= (

0 if y

x,

x.

=

6=

Fact 8.6. The indicator basis is indeed a basis for L2(Ω, π) since the functions
(1x)x

Ω are nonzero, spanning, and orthogonal. Hence dim(L2(Ω, π))
∈
N+.
We will usually ﬁx Ω and π and then consider L2(Ωn, π⊗
n) for n
Ωn for the mn-
Applying the above deﬁnition gives us an indicator basis (1x)x
∈
L2(Ω, π) in this
dimensional space L2(Ωn, π⊗
Ω f (x)1x. This is not very interesting; the coefﬁcients are
basis is just f
∈
just the values of f so they don’t tell us anything new about the function. We
would like a different basis that will generate useful “Fourier formulas” as in
Chapter 1.4.

n). The representation of f

m.

P

=

=

∈

∈

x

For inspiration, let’s look critically at the familiar case of L2({

Here we used the basis of all parity functions, χS(x)
helpful to think of the basis function χS : {
with its 0-1 indicator vector and write

1, 1}n

→

−

1, 1}n).
−
S xi. It will be
R as follows: Identify S

=

∈

i

Q

χS(x)

n

=

i
1
=
Y

φSi (xi),

where φ0

1, φ1

id.

=

≡

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 3 -->
8.1. Fourier bases for product spaces

209

(Here id is just the identity map id(b)
of this basis which we’d like to generalize.

=

b.) We will identify three properties

1, 1}n, the set {1, id} is a basis for the 2-dimensional space L2({

First, the parity basis is a product basis. We can break down its “prod-
[n] of the product domain
uct structure” as follows: For each coordinate i
1, 1}, π1/2).
{
−
We then get a basis for the 2n-dimensional product space L2({
1, 1}n) by tak-
ing all possible n-fold products. More generally, suppose we are given an
inner product space L2(Ω, π) with
1 be any basis for
−
m) forms a basis
this space. Then the set of all products φi1 φi2 · · ·
<
for the space L2(Ωn, π⊗
n).

m. Let φ0, . . . , φm
i j

φi n (0

| =

Ω

−

−

≤

∈

|

Second, it is convenient that the parity basis is orthonormal. We will later
1 for L2(Ω, π) is orthonormal, then so too is
−
n
n). This relies on the fact that π⊗
1, 1}n)
1, 1}, π1/2) is orthonormal:
0. Orthonormality is the property that makes
L2(Ω, π)

check that if a basis φ0, . . . , φm
the associated product basis for L2(Ωn, π⊗
is the product distribution. For example, the parity basis for L2({
is orthonormal because the basis {1, id} for L2({
E[12]
xi]
Parseval’s Theorem hold; in the general context, this means that if f
has the representation

E[x2
i ]

1, E[1

0 ciφi then E[ f 2]

0 c2
i .

m
i

m
i

=

−

=

=

−

∈

−

−

1

1

·

=

=

=

P

Finally, the parity basis contains the constant function 1. This fact leads
to several of our pleasant Fourier formulas. In particular, when you take
an orthonormal basis φ0, . . . , φm
φ0, φi
〉 =
〈
m
1
0 ciφi, then E[ f ]
f
−
i
=

=
≡
L2(Ω, π) has the expansion
∈
0 c2
i .
>

1 for L2(Ω, π) which has φ0
−
0. Hence if f

π[φi(x)] for all i
∼

c0 and Var[ f ]

1, then 0

Ex

P

=

>

=

=

i

P
We encapsulate the second and third properties with a deﬁnition:

P

Deﬁnition 8.7. A Fourier basis for an inner product space L2(Ω, π) is an
orthonormal basis φ0, . . . , φm

1.

1 with φ0
−

≡

Example 8.8. For each n
Fourier basis for L2({

1, 1}n, π⊗

∈

N+, the 2n parity functions (χS)S
n
1/2).

−

[n] form a
⊆

Remark 8.9. A Fourier basis for L2(Ω, π) always exists because you can ex-
tend the set {1} to a basis and then perform the Gram–Schmidt process. On the
other hand, Fourier bases are not unique. Even in the case of L2({
1, 1}, π1/2)
there are two possibilities: the basis {1, id} and the basis {1,

id}.

−

−

Example 8.10. In the case of Ω
possible Fourier basis (see Exercise 8.4) is

=

{a, b, c} with π(a)

π(b)

π(c)

=

=

=

1/3, one

φ0

1,

≡

φ1(a)
φ1(b)
φ1(c)

p2
p2/2
p2/2,

= +
= −
= −

φ2(a)
φ2(b)
φ2(c)

0

=
= +
= −

p6/2,
p6/2.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 4 -->
210

8. Generalized domains

As mentioned, given a Fourier basis for L2(Ω, π) you can construct a
n) by “taking all n-fold products”. To make

Fourier basis for any L2(Ωn, π⊗
this precise we need some notation.

Deﬁnition 8.11. An n-dimensional multi-index is a tuple α

Nn. We write

∈

supp(α)

{i : αi

=

6=

0}, #α

supp(α)
|

= |

,

α

| =

|

αi.

n

i
1
=
X

We may write α
1}.

Nn
<

∈

m when we want to emphasize that each αi

{0, 1, . . . , m

−

∈

Deﬁnition 8.12. Given functions φ0, . . . , φm
α

L2(Ωn, π⊗

n) by

m, we deﬁne φα ∈

Nn
<

∈

L2(Ω, π) and a multi-index

1

−

∈

φα(x)

n

=

i
1
=
Y

φαi (xi).

Now we can show that products of Fourier bases are Fourier bases.

Proposition 8.13. Let φ0, . . . , φm
collection (φα)α
Nn
∈
<
that α

1 be a Fourier basis for L2(Ω, π). Then the
−
is a Fourier basis for L2(Ωn, π⊗
n) (with the understanding
(0, 0, . . . , 0) indexes the constant function 1).

m

=

Proof. First we check orthonormality. For any multi-indices α, β
have

Nn
<

∈

m we

φα, φβ〉 =

〈

E
π⊗
∼

n

x

[φα(x)

φβ(x)]

·

n

n

φαi (xi)

φβi (xi)

i
1
=
Y
[φαi (xi)

·

i
1
=
Y
φβi (xi)]

·

n

x

E
π⊗
∼
n

h

E
xi
∼

π

i
1
=
Y
n

βi}

=

1{αi

i
1
=
Y
β}.
1{α
=

=

=

=

=

i
(since π⊗

n is a product distribution)

(since {φ0, . . . , φm

1} is orthonormal)
−

This conﬁrms that the collection (φα)α
is orthonormal, and consequently
∈
linearly independent. It is therefore also a basis because it has cardinality mn,
(cid:3)
which we know is the dimension of L2(Ωn, π⊗

n) (see Fact 8.6).

Nn
<

m

Given a product Fourier basis as in Proposition 8.13, we can express any
L2(Ωn, π⊗
f (α)

n) as a linear combination of basis functions. We will write

f
for the “Fourier coefﬁcient” on φα in this expression.

∈

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.

b



<!-- pdf-page: 5 -->
8.2. Generalized Fourier formulas

211

Deﬁnition 8.14. Having ﬁxed a Fourier basis φ0, . . . , φm
n) is uniquely expressible as
f

L2(Ωn, π⊗

∈

1 for L2(Ω, π), every
−

f (α)φα.

f

=

α

Nn
∈
X
<

m

b

This is the Fourier expansion of f with respect to the basis. The real number
f (α) is called the Fourier coefﬁcient of f on α and it satisﬁes

b

f (α)

f , φα〉

.

= 〈
Example 8.15. Fix the Fourier basis as in Example 8.10. Let f : {a, b, c}2
→
{0, 1} be the function which is 1 if and only if both inputs are c. Then you can
check (Exercise 8.5) that

b

f

1
9 −

=

p2
18 φ(1,0)

−

p6
18 φ(2,0)

−

p2
18 φ(0,1)

−

p6
18 φ(0,2)

+

1
18 φ(1,1)

+

p12
36 φ(2,1)

+

p12
36 φ(1,2)

+

1
6 φ(2,2).

The notation

f (α) may seem poorly chosen because it doesn’t show the de-
pendence on the basis. However, the Fourier formulas we develop in the next
section will have the property that they are the same for every product Fourier
basis. We will show a basis-independent way of developing the formulas in
Section 8.3.

b

8.2. Generalized Fourier formulas

In this section we will revisit a number of combinatorial/probabilistic no-
n), these notions have familiar
tions and show that for functions f
Fourier formulas that don’t depend on the Fourier basis.

L2(Ωn, π⊗

∈

The orthonormality of Fourier bases gives us some formulas almost imme-

diately:

Proposition 8.16. Let f , g
basis, the following formulas hold:

∈

L2(Ωn, π⊗

n). Then for any ﬁxed product Fourier

E[ f ]
E[ f 2]

Var[ f ]

=

=

=

f , g

〈

〉 =

f (0)

b
Nn
α
∈
X
<

b
f (α)2

0
α
6=
X

α

b
Nn
∈
X
<
b
f (α)

m

f (α)2

m

(Parseval)

f (α)

g(α)

(Plancherel)

Cov[ f , g]

=

b
g(α).

0
α
6=
X
Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.

b

b



<!-- pdf-page: 6 -->
212

8. Generalized domains

Proof. We verify Plancherel’s Theorem, from which the other identities follow
(Exercise 8.6):

f , g

〈

〉 =

Nn
α
D X
∈
<

m

f (α)φα,

g(β)φβ

β

m

Nn
∈
X
<
b
φα, φβ〉

g(β)
〈

b
f (α)

E

b
f (α)

b
g(α)

α,β

Nn
<

∈
X

m

=

=

α

Nn
∈
X
<
.
Nn
<

m

−

by orthonormality of (φα)α
∈

m

b

b

(cid:3)

We now give the key deﬁnition for developing basis-independent Fourier
1, 1}) this deﬁnition appeared already in

In the case of L2({

expansions.
Exercise 3.28.

Deﬁnition 8.17. Let J
⊆
projection of f on coordinates J is the function f ⊆

[n] and write J

[n] \ J. Given f
J

L2(Ωn, π⊗

=

∈

L2(Ωn, π⊗

n), the

n) deﬁned by

f ⊆

J(x)

=

E
x0∼
π⊗

[ f (xJ, x0)],

J

∈

∈

ΩJ denotes the values of x in the J-coordinates. In other words,
J(x) is the expectation of f when the J-coordinates of x are rerandomized.
J to have Ωn as its domain, even though it only depends

where xJ
f ⊆
Note that we take f ⊆
on the coordinates in J.

Forming f ⊆

J is indeed the application of a projection linear operator to f ,
namely the expectation over J operator, EJ. We take this as the deﬁnition of
the operator: EJ f

{i} is a singleton we write simply Ei.

J. When J

f ⊆

=

=

Remark 8.18. This deﬁnition of Ei is consistent with Deﬁnition 2.23. You
are asked to verify that EJ is indeed a projection, self-adjoint linear operator
in Exercise 8.7.

Proposition 8.19. Let J
Fourier basis,

⊆

[n] and f

∈

L2(Ωn, π⊗

n). Then for any ﬁxed product

J

f ⊆

=

α

Nn
∈
X
<
supp(α)

m

⊆

f (α) φα.

J b

Proof. Since EJ is a linear operator, it sufﬁces to verify for all α that

φα
J
φ⊆
α = (
0

if supp(α)

J,

⊆

otherwise.

⊆

If supp(α)
J
φ⊆
α =
we can write φα =

J, then φα does not depend on the coordinates J; hence indeed
J φαi (xi)
,
i
, where φαJ depends only on the coordinates in J,
¡Q
¢

φα. So suppose supp(α)

J. Since φα(x)

J φαi (xi)

φαJ ·

φαJ

¢¡Q

6⊆

=

∈

∈

i

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 7 -->
8.2. Generalized Fourier formulas

213

depends only on the coordinates in J, and E[φαJ

0 precisely because

]

=

φαJ
supp(α)

J. Thus for every x

Ωn,

6⊆
φ⊆

J
α (x)

=

E
x0∼
π⊗

J

∈
[φαJ (xJ)φαJ

as needed.

(x0)]

=

φαJ (xJ)

·

E
x0∼
π⊗

J

[φαJ

(x0)]

0

=

(cid:3)

L2(Ωn, π⊗
Corollary 8.20. Let f
depends only on the coordinates in J

∈

n) and ﬁx a product Fourier basis. If f
J.

0 whenever supp(α)

[n] then

f (α)

⊆

=

6⊆

Proof. This follows from Proposition 8.19 because f

b

f ⊆

J.

=

(cid:3)

Corollary 8.21. Let i
Fourier basis,

∈

[n] and f

∈

L2(Ωn, π⊗

n). Then for any ﬁxed product

f (α) φα.

Ei f

=

0

α:αi
=
X

b

=

Ω

L2(Ωn, π⊗

Let us now deﬁne inﬂuences for functions f
{
−

n). In the case of
1, 1}, our deﬁnition of Infi[ f ] from Chapter 2.2 was E[(Di f )2]. However,
the notion of a derivative operator does not make sense for more general
domains Ω. In fact, even in the case of Ω
1, 1} it isn’t a basis-invariant
notion: the choice of f (x(i
1))
7→
is inherently
arbitrary. Instead we can fall back on the Laplacian operators, and take the
identity Infi[ f ]

{
=
−
rather than f (x(i

from Proposition 2.26 as a deﬁnition.

f (x(i
−
2

f , Li f

1))
−
2

f (x(i

1))

1))

∈

7→−

7→−

7→

= 〈

〉
[n] and f

Deﬁnition 8.22. Let i
∈
operator Li is the self-adjoint, projection linear operator deﬁned by

∈

n). The ith coordinate Laplacian

L2(Ωn, π⊗

The inﬂuence of coordinate i on f is deﬁned to be

Li f

f

=

−

Ei f .

〉 = 〈
The total inﬂuence of f is deﬁned to be I[ f ]

= 〈

Infi[ f ]

f , Li f

Li f , Li f

.

〉
1 Infi[ f ].
=

n
i

=

You can think of Li f as “the part of f which depends on the ith coordinate”.

P

Proposition 8.23. Let i
Fourier basis,

∈

[n] and f

L2(Ωn, π⊗

n). Then for any ﬁxed product

f (α) φα,

Infi[ f ]

f (α)2,

I[ f ]

Li f

=

0

α:αi
6=
X

b

f (α)2,

#α

·

=

α
X

b

Proof. The ﬁrst formula is immediate from Corollary 8.21, the second from
(cid:3)
Plancherel, and the third from summing over i.

∈

=

0

α:αi
6=
X

b

Exercise 8.9 asks you to verify the following formulas (cf. Exercise 2.21),

which are often useful for computations:

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 8 -->
214

8. Generalized domains

Proposition 8.24. Let i

[n] and f

L2(Ωn, π⊗

n). Then

Infi[ f ]

=

x

∈
E
π⊗
∼

n

∈
[ f (x1, . . . , xi

[Var
x0i∼
π
1, 1}, then

If furthermore f ’s range is {

1, x0i, xi
−

1, . . . , xn)]].
+

Infi[ f ]

E[
|

=

Li f

]

|

=

[ f (x)

6=

f (x1, . . . , xi

1, x0i, xi
−

1, . . . , xn)].
+

n

−
2 Pr
x
π⊗
∼
x0i∼
π

Example 8.25. Let’s continue Example 8.15, in which {a, b, c} has the uniform
distribution and f : {a, b, c}2
{0, 1} is 1 if and only if both inputs are c. We
compute Inf1[ f ] two ways. Using Proposition 8.24 we have Var[ f (x1, a)]
=
2
1
Var[ f (x1, b)]
9 (because f (x1, c) is Bernoulli with
3 ·
2
parameter 1
27 . Alternatively, using the formula from
Proposition 8.23 as well as the Fourier expansion from Example 8.15, we can
( 1
18 )2
compute Inf1[ f ]

0 and Var[ f (x1, c)]
=
2
9 =

3 ); thus Inf1[ f ]

p6
18 )2

p2
18 )2

36 )2

36 )2

2
3 =

( 1
6 )2

( p12

( p12

2
27 .

1
3 ·

→

=

=

+

+

+

+

=

(
−

=

(
−

+

Next, we straightforwardly extend our deﬁnitions of the noise operator

and noise stability to general product spaces.

Deﬁnition 8.26. Fix a ﬁnite product probability space (Ωn, π⊗
and x
follows: For each i

Nρ(x) to denote that y

[n] independently,

Ωn we write y

[0, 1]
Ωn is randomly chosen as

n). For ρ

∼

∈

∈

∈

∈

yi = (

xi
drawn from π with probability 1

with probability ρ,

ρ.

−

n and y

π⊗

If x
(This deﬁnition is symmetric in x and y.)

∼

∼

Nρ(x), we say that (x, y) is a ρ-correlated pair under π⊗

n.

Deﬁnition 8.27. For a ﬁxed space L2(Ωn, π⊗
ator with parameter ρ is the linear operator Tρ on functions f
deﬁned by

n) and ρ

∈

[0, 1], the noise oper-
n)

L2(Ωn, π⊗

∈

The noise stability of f at ρ is

Tρ f (x)

[ f (y)].

E
Nρ(x)

=

y

∼

Stabρ[ f ]

f , Tρ f

= 〈

〉 =

E
(x,y) ρ-correlated
under π⊗

n

[ f (x) f (y)].

Proposition 8.28. Let ρ
product Fourier basis,

∈

[0, 1] and let f

∈

L2(Ωn, π⊗

n). Then for any ﬁxed

Tρ f

=

α

Nn
∈
X
<

m

b

ρ#α

f (α) φα,

Stabρ[ f ]

ρ#α

f (α)2.

=

α

Nn
∈
X
<

m

b

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 9 -->
8.2. Generalized Fourier formulas

215

Proof. Let J denote a ρ-random subset of [n]; i.e., J is formed by including
each i
EJ[ f ⊆

[n] independently with probability ρ. Then by deﬁnition Tρ f (x)

∈
J(x)], and so from Proposition 8.19 we get

=

Tρ f (x)

E
J

=

[ f ⊆

J(x)]

=

E
J

Nn
α
h X
∈
<
supp(α)

f (α) φα(x)

J b

=

i

α

Nn
∈
X
<

m

ρ#α

f (α) φα(x),

b

m

⊆

since for a ﬁxed α, the probability of supp(α)
Stabρ[ f ] now follows from Plancherel.

⊆

J is ρ#α. The formula for
(cid:3)

Remark 8.29. The ﬁrst formula in this proposition may be used to extend
the deﬁnition of Tρ f to values of ρ outside [0, 1].

We also deﬁne ρ-stable inﬂuences. The factor of ρ−

1 in our deﬁnition is

for consistency with the L2({

1, 1}n) case.

Deﬁnition 8.30. For f
ence of i on f is

∈

−
L2(Ωn, π⊗

n), ρ

∈

(0, 1], and i

∈

[n], the ρ-stable inﬂu-

Inf(ρ)
i

[ f ]

=

ρ−

1Stabρ[Li f ]

We also deﬁne I(ρ)[ f ]

=

1 Inf(ρ)

i

n
i

=

[ f ].

=

0

α:αi
6=
X

ρ#α
−

1

f (α)2.

b

P

Just as in the case of L2({

1, 1}n) we can use stable inﬂuences to deﬁne
the “notable” coordinates of a function, of which there is a bounded quantity.
A verbatim repetition of the proof of Proposition 2.54 yields the following
generalization:

−

Proposition 8.31. Suppose f
[n] : Inf(1
0
−
i

1, let J

{i

²

L2(Ωn, π⊗
∈
δ)
[ f ]

²}. Then

J

n) has Var[ f ]

1
δ² .

∈

≥

=

<

≤
We end this section by discussing the “degree” of functions on general
1, 1}n) the Fourier expansion is a real polynomial;
product spaces. For f
n)
this yields an obvious deﬁnition for degree. But for general f
the domain is just an abstract set so we need to look for a more intrinsic
deﬁnition. We take our cue from Exercise 1.10(b):

L2(Ωn, π⊗

L2({

| ≤

−

∈

∈

|

1. Given 0

δ

<

<

1,

≤

Deﬁnition 8.32. Let f
deg( f ), is the least k
on at most k coordinates).

∈

L2(Ωn, π⊗

n) be nonzero. The degree of f , written
N such that f is a sum of k-juntas (functions depending

∈

Proposition 8.33. Let f
Fourier basis we have deg( f )

=
Proof. The inequality deg( f )
Fourier expansion:

∈

L2(Ωn, π⊗

n) be nonzero. Then for any ﬁxed product

max{#α :

f (α)

0}.

max{#α :
b

≤

0} is immediate from the

6=

6=
f (α)

b
f (α) φα

f

=

α:

0

6=

f (α)
X
b

b

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 10 -->
216

8. Generalized domains

f (α) φα depends on at most #α coordinates. For the reverse
and each function
inequality, suppose f
gm where each g i depends on at most k
coordinates. By Corollary 8.20 each g i has its Fourier support on functions φα
(cid:3)
with #α

gm(α), so the same is true of f .

b
f (α)

k. But

+ · · · +

g1(α)

g1

=

≤

=

+ · · · +

b
c
8.3. Orthogonal decomposition

c

In this section we describe a basis-free kind of “Fourier expansion” for func-
tions on general product domains. We will refer to it as the orthogonal decom-
n), though it goes by several other names in the liter-
position of f
ature: e.g., Hoeffding decomposition, Efron–Stein decomposition, or ANOVA
decomposition. The general idea is to express

L2(Ωn, π⊗

∈

where each function f =
from coordinates S (but not from any subset of S)”.

∈

S

f

=

S

f =

(8.1)

[n]

S
⊆
X
L2(Ωn, π⊗
n) gives the “contribution to f coming

S

To make this more precise, let’s start with the familiar case of f : {

1, 1}n
→
R simply by
R. Here it is possible to deﬁne the functions f =
f =
f (S) χS. (Later we will give an equivalent deﬁnition that doesn’t in-
volve the Fourier basis.) This deﬁnition satisﬁes (8.1) as well as the following
b
two properties:

1, 1}n

S : {

→

−

−

=

S depends only on the coordinates in S.

(1) f =
(2) If T ( S and g is a function depending only on the coordinates in T,

then

f =

S, g

0.

〉 =

〈

S is
These properties describe what we mean precisely when we say that f =
the “contribution to f coming from coordinates S (but not from any subset
of S)”. Furthermore, decomposition (8.1) is orthogonal, meaning
0 whenever S

S, f =

〉 =

f =

T.

T

〈

To make this deﬁnition basis-free, recall the “projection of f onto coordi-
J

J, from Exercise 3.28 and Deﬁnition 8.17. You can think of f ⊆
nates J”, f ⊆
as the “contribution to f coming from coordinates J (collectively)”. It has a
probabilistic deﬁnition not depending on any basis, and with the deﬁnition
f =

f (S) χS we have from Exercise 3.28 or Proposition 8.19 that

S

6=

J

f ⊆

=

f =

S.

(8.2)

J
S
⊆
X
It is precisely by inverting (8.2) that we can give a basis-free deﬁnition of the
functions f =

S.

Let’s do this inversion for a general f

L2(Ωn, π⊗
n). The projection func-
n) can be deﬁned as in Deﬁnition 8.17. If we want (8.2)

∈

tions f ⊆

J

L2(Ωn, π⊗

∈

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.

=

b



<!-- pdf-page: 11 -->
8.3. Orthogonal decomposition

217

to hold for J

= ;

then we should deﬁne

=
(which is the constant function equal to E[ f ]). Given this, if we want (8.2) to
hold for singleton sets J

{ j}, then we need

f =;

f ⊆;

{ j}

f ⊆

=

In other words,

=
f =;

{ j}

f =

+

⇐⇒

{ j}

f =

{ j}

f ⊆

f ⊆;.

−

=

f =

{ j}(x)

=

x

[ f

E
π⊗
∼

n

|

x j

=

x j]

−

x

E
π⊗
∼

n

[ f (x)].

Notice this function only depends on the input value x j; it measures the
change in expectation of f if you know the value x j. Moving on to sets of
cardinality 2, if we want (8.2) to hold for J

{i, j}, then we need

{i, j}

f ⊆

f =;

f ⊆;

+

+

=

=

{i}

f =

{i}

( f ⊆

+

−

{ j}

f =

+
f ⊆;)

{ j}

( f ⊆

f ⊆;)

+

−

{i, j}

f =

+

=
f =

{i, j}

and hence

{i, j}

f =

{i, j}

f ⊆

{i}

f ⊆

{ j}

f ⊆

f ⊆;.

−

−

+

=

S by the
It’s clear that we can continue this and deﬁne all the functions f =
principle of inclusion-exclusion. To show this deﬁnition leads to an orthogonal
decomposition we will need the following lemma:

Lemma 8.34. Let f , g
coordinate outside I
J

[n]. Then

f , g

L2(Ωn, π⊗

n). Assume that f does not depend on any
∈
[n], and g does not depend on any coordinate outside
f ⊆

J, g⊆

∩

∩

J

.

I

I

⊆
〉 = 〈

〈

〉

Proof. We may assume without loss of generality that I
x

Ωn we can break it into the parts (xI

J, xI\J, xJ\I ). We then have

∪

=

J

[n]. Given any

⊆

∈

f , g

〈

〉 =

xI

∩

E

J ,xI\J ,xJ\I

[ f (xI

∩

g(xI

∩

·

J, xJ\I )],

∩
J, xI\J)

where we have abused notation slightly by writing f and g as functions just
of the coordinates on which they actually depend. Since xI\J and xJ\I are
independent, the above equals

E
xI
∩

∩

E
xI\J

E
xJ\I

·

[ f (xI

J, xI\J)]

[g(xI

J, xJ\I )]

.

J ·
J, xI\J)] is nothing more than f ⊆

¸
J(xI
J). Thus the above equals

J(xI

∩

I

I

∩

∩

J), and similarly

g⊆

I

J(xI

∩

J)]

∩

= 〈

f ⊆

I

J, g⊆

I

∩

∩

J

.

〉

(cid:3)

But now ExI\J [ f (xI
∩
J, xJ\I )]
ExJ\I [g(xI
=
I
[ f ⊆

∩

E
xI
∩

J

g⊆
∩
J(xI

∩

∩
J)

·

∩

We can now give the main theorem on orthogonal decomposition:

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 12 -->
218

8. Generalized domains

L2(Ωn, π⊗

n). Then f has a unique decomposition as

Theorem 8.35. Let f

∈

where the functions f =

S

∈

f

=

L2(Ωn, π⊗

S

f =

[n]

S
⊆
X

n) satisfy the following:

S depends only on the coordinates in S.
L2(Ωn, π⊗

(1) f =
(2) If T ( S and g
S, g

0.

f =

∈

〈

〉 =

n) depends only on the coordinates in T, then

This decomposition has the following additional properties:

(3) Condition (2) additionally holds whenever S

(4) The decomposition is orthogonal:
T .

(5)

S

T f =

S

f ⊆
[n], the mapping f

=
⊆
(6) For each S

P

f =

S, f =

T

〈

〉 =

6⊆

T.

0 for S

T.

6=

f =

S is a linear operator.

7→

⊆

⊆

Proof. We ﬁrst show the existence of a decomposition satisfying (1)–(6). We
then show uniqueness for decompositions satisfying (1) and (2). As suggested
above, for each S

[n] we deﬁne

S

f =

=

(
−

1)|

S

J

| f ⊆

J,

|−|

J

S
J
⊆
X
L2(Ωn, π⊗
n) are as in Deﬁnition 8.17. Since each f ⊆
where the functions f ⊆
depends only on the coordinates in J, condition (1) certainly holds. It is also
immediate that condition (5) holds by inclusion-exclusion; you are asked to
prove this explicitly in Exercise 8.14. Condition (6) also follows because each
f

J is a linear operator, as discussed after Deﬁnition 8.17.

∈

J

7→

f ⊆
We now verify (2). Assume T ( S and that g

L2(Ωn, π⊗

n) only depends

∈

on the coordinates in T. We have

f =

S, g

〈

〉 =

1)|

(
−

S

J

|−|

|

〈

f ⊆

J, g

.

〉

(8.3)

S
J
⊆
X

Take any i
∈
J0
and J00
∪

=

S \ T and pair up the summands in (8.3) as J0, J00, where J0
{i}. By Lemma 8.34 we have

i

63

f ⊆

J00, g

〈

〉 = 〈

f ⊆

J00

T , g⊆

T

∩

〉 = 〈

f ⊆

J0

T , g⊆

∩

T

,

S

J0

〉
| and (

the latter equality using i
T. But the signs (
| are
opposite, so the summands in (8.3) cancel in pairs. This shows the sum is 0,
conﬁrming (2).

1)|

1)|

|−|

|−|

−

−

6∈

S

J00

We complete the existence proof by noting that (2)

=⇒
f =
suming (1)). The ﬁrst implication is because
g depends only on the coordinates in T (Lemma 8.34), and S
S

T. The second implication is because S

∩
T implies either S

〉 = 〈

S, g

(3)
S, g⊆

=⇒
T
S
∩

(4) (as-
when
〉
T ( S when
S.

T or T

f =

〈

6=

6⊆

6⊆

6⊆

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 13 -->
8.3. Orthogonal decomposition

219

It remains to prove the uniqueness statement. Suppose f has two repre-
sentations satisfying (1) and (2). By subtracting them we get a decomposition
of the 0 function that satisﬁes (1) and (2); our goal is to show that each func-
tion in this decomposition is the 0 function. We can do this by showing that
any decomposition satisfying (1) and (2) also satisﬁes “Parseval’s Theorem”:
2
f , f
2. But this is an easy consequence of (4), which we just
〈
k
(cid:3)
noted is itself a consequence of (1) and (2).

[n] k
⊆

〉 =

f =

S

S

P

We can connect the orthogonal decomposition of f to its expansion under

Fourier bases as follows:

Proposition 8.36. Let f

L2(Ωn, π⊗

n) have orthogonal decomposition f

∈
S. Fix any Fourier basis φ0, . . . , φm

1 for L2(Ω, π). Then
−
f (α) φα.

=

(8.4)

S

[n] f =
⊆

P

S

f =

=

α

Nn
∈
X
<
supp(α)

m

S b

=

Proof. This follows easily from the uniqueness part of Theorem 8.35. If we
f
take (8.4) as the deﬁnition of functions f =
S depends only on the coordinates in S. Further, if g depends
and that f =
S and g have disjoint Fourier support by
only on coordinates T ( S, then f =
(cid:3)
Corollary 8.20; hence

0 by Plancherel (Proposition 8.16).

S, it is immediate that

S f =

S, g

P

=

S

f =

〈

〉 =

Example 8.37. Let’s compute the orthogonal decomposition of the function
f : {a, b, c}2
{0, 1} from Example 8.15. Recall that in this example {a, b, c}
c. First,
has the uniform distribution and f (x1, x2)

x2

→

=

=

Next, for i

=

1, 2 we have that f ⊆

c and 0 otherwise; hence

f =

{i}(x1, x2)

f =;

=

E[ f ]

=
{i}(x) is 1

1 if and only if x1
1
9 .
=
3 if xi
2
9
1
9
−
{1,2} as f

=
if xi
else.

= (

c,

+

=

{1}

f =;

f =

f =

−
x2

−
c,

−

=

=

if x1
if exactly one of x1, x2 is c,
if x1, x2

c.

6=

4
9
2
9
1
9

+

−



+


f =

{1,2}(x1, x2)

=

You can check (Exercise 8.20) that this is consistent with Proposition 8.36 and
the Fourier expansion from Example 8.15.

We can write all of the Fourier formulas from Section 8.2 in terms of the

orthogonal decomposition; e.g.,

f , g

〈

〉 =

f =

S, g=

S

,

Infi[ f ]

[n]〈
S
S
⊆
⊆
X
X
Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.

S
3
X

i k

=

=

〉

[n]

S

f =

2
2, Tρ f
k

S

| f =

S.

ρ|

Finally, it’s easiest to compute f =

{2}; this yields



<!-- pdf-page: 14 -->
220

8. Generalized domains

These formulas can be proved either by using the connection from Proposi-
tion 8.36 or by reasoning directly from the deﬁning Theorem 8.35; see Ex-
ercise 8.18. The orthogonal decomposition also gives us the natural way of
stratifying f by degree; we end this section by generalizing some more deﬁni-
tions from Chapter 1.4:

Deﬁnition 8.38. For f
k
k f =
of f to be f =
=
We also use notation like f ≤

n) and k

L2(Ωn, π⊗

∈
∈
S and the weight of f at degree k to be Wk[ f ]
S
S and W>
f =

N we deﬁne the degree k part
2
2.
k

k[ f ]

f =

k f =

|=

S

S

S

k

k

|

=

k k

|

|>

= k
2
2.
k

P

=

|

|≤

8.4. p-biased analysis

P

P

1, 1}n as having each bit independently equal to
−
(0, 1) and equal to 1 (False) with probability q

Perhaps the most common generalized domain in analysis of Boolean func-
tions is the case of the hypercube with “biased” bits. In this setting we think of
1 (True)
a random input in {
with probability p
p.
1
(We could also consider different parameters pi for each coordinate; see Ex-
ercise 8.24.) In the notation of the chapter this means L2(Ωn, π⊗
n
p ), where
1, 1} and πp is the distribution on Ω deﬁned by πp(
Ω
q.
This context is often referred to as p-biased Fourier analysis, though it would
be more consistent with our terminology if it were called “µ-biased”, where

p, πp(1)

{
−

−
∈

1)

=

−

=

−

=

=

µ

=

xi

E
∼

πp

[xi]

q

p

1

−

=

−

=

2p.

n

−

π⊗
p

→

1, 1}n

One of the more interesting features of the setting is that we can ﬁx a combi-
natorial Boolean function f : {
1, 1} and then consider its properties
{
−
for various p between 0 and 1; we will discuss this further later in this sec-
tion. We will also sometimes use the abbreviated notation Prπp [
] in place of
·
Prx

], and similarly Eπp [

∼
The p-biased hypercube is one of the generalized domains where it can
2 there is
pay to look at an explicit Fourier basis. In fact, since we have
a unique Fourier basis {φ0, φ1} (up to negating φ1). For notational simplicity
we’ll write φ instead of φ1 and use “set notation” rather than multi-index
notation:

| =

[
·

Ω

].

·

|

Deﬁnition 8.39. In the context of p-biased Fourier analysis we deﬁne the
basis function φ : {

R by

1, 1}

−

→

φ(xi)

xi

µ

,

−
σ

=

where

µ

=

xi

E
∼

πp

[xi]

q

p

1

−

=

−

=

2p, σ

=

stddev
∼

πp

xi

[xi]

=

4pq

=

2pp

1

p.

−

Note that σ2

1

µ2. We also have the formula φ(1)

p/q, φ(

−

=
Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.

=

−

p

q/p.

= −

p

p

p
1)



<!-- pdf-page: 15 -->
8.4. p-biased analysis

221

We will use the notation µ and σ throughout this section. It’s clear that
0 and

1, 1}, πp) because E[φ(xi)]

{1, φ} is indeed a Fourier basis for L2({
E[φ(xi)2]

1 by design.

−

=

=

Deﬁnition 8.40. In the context of L2({
Fourier basis functions (φS)S

−

1, 1}n, π⊗

n
p ) we deﬁne the product

[n] by
⊆
φS(x)

φ(xi).

=

S
i
∈
Y

f (S) for the associated Fourier coefﬁcient;

Given f
i.e.,

∈

L2({

1, 1}n, π⊗

n
p ) we write

−

Thus we have the biased Fourier expansion

b

f (S)

=

x

b
E
π⊗
p

∼

[ f (x) φS(x)].

n

Although the notation is very similar to that of the classic uniform-distribution

f (S) φS(x).

f (x)

=

[n]

S
⊆
X

b

Fourier analysis, we caution that in general,

L2({
Example 8.41. Let χi
xi, viewed under the p-biased distribution. We have

−

∈

φSφT

φS

T .

6=
n
1, 1}n, π⊗
p ) be the ith dictator function, χi(x)

4

=

φ(xi)

xi

µ

−
σ

=

=⇒

xi

µ

+

=

σφ(xi),

and the latter is evidently f ’s (biased) Fourier expansion. That is,

χi(

)
;

=

µ,

χi({i})

=

σ,

χi(S)

=

0 otherwise.

b

This example lets us see a link between a function’s “usual” Fourier expan-
sion and its biased Fourier expansion. (For more on this, see Exercise 8.25.)
Let’s abuse notation a little by writing simply φi instead of φ(xi). We have
the formulas

b

b

⇐⇒
and we can go from the usual Fourier expansion to the biased Fourier expan-
sion simply by plugging in the latter.

=

=

+

xi

µ

σφi,

(8.5)

φi

xi

µ

−
σ

Example 8.42. Recall the “selection function” Sel : {
Exercise 1.1(j); Sel(x1, x2, x3) outputs x2 if x1
The usual Fourier expansion of Sel is

= −

−

1, 1}3

1 and outputs x3 if x1

→

{
−

1, 1} from
1.

=

Sel(x1, x2, x3)

1
2 x2

+

1
2 x3

−

=

1
2 x1x2

+

1
2 x1x3.

Using the substitution from (8.5) we get

Sel(x1, x2, x3)

=

1
2 (µ
µ

1
σφ2)
2 (µ
+
1
2 µ)σ φ2

+
( 1
2 −

1
σφ3)
2 (µ
+
+
−
1
( 1
2 µ)σ φ3
2 +

σφ1)(µ
+
2 σ2 φ1φ2

1

σφ2)
1

1
2 (µ
+
+
2 σ2 φ1φ3.

+

=
Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.

+

−

+

σφ1)(µ

σφ3)

+
(8.6)



<!-- pdf-page: 16 -->
222

8. Generalized domains

Thus if we write Sel(p) for the selection function thought of as an element of
L2({

3
1, 1}3, π⊗
p ), we have

−

)
;

Sel(p)(

=
Sel(p)({1, 2})
ƒ

µ,

Sel(p)(2)

2 σ2,
1
ƒ

= −

=

( 1
2 −
Sel(p)({1, 3})

1
2 µ)σ,
1

Sel(p)(3)

( 1
2 +

1
2 µ)σ,

=
Sel(p)(S)

2 σ2,

ƒ

=

0 else.

=

ƒ

By the Fourier formulas of Section 8.2 we can deduce, e.g., that E[Sel(p)]
Inf1[Sel(p)]
2 σ4, etc.

( 1
2 σ2)2

ƒ
1

2 σ2)2

ƒ

1

µ,

=

(
−

=

+

=

Let’s codify a piece of notation from this example:

Notation 8.43. Let f : {
function when viewed as an element of L2({

→

−

1, 1}n

R and let p

∈
1, 1}n, π⊗

n
p ).

−

(0, 1). We write f (p) for the

We now discuss derivative operators. We would like to deﬁne an opera-
n
p ) that acts like differentiation on the biased Fourier

tor Di on L2({
expansion. For example, referring to (8.6) we would like to have

1, 1}n, π⊗

−

D3Sel(p)

In general we are seeking ∂
∂φi
ship (8.5), satisﬁes

( 1
2 +

1
2 µ)σ

1

2 σ2 φ1.

=
which, by basic calculus and the relation-

+

∂
∂φi =

∂xi
∂φi ·

∂
∂xi =

σ

·

∂
∂xi

.

Recognizing ∂
∂xi
lowing:

as the “usual” ith derivative operator, we are led to the fol-

Deﬁnition 8.44. For i
L2({

1, 1}n, π⊗

n
p ) is deﬁned by

∈

−

[n], the ith (discrete) derivative operator Di on

Di f (x)

σ

·

=

f (x(i

1))

7→

f (x(i

1))

7→−

.

−
2

Note that this deﬁnes a different operator for each value of p. We sometimes
write the above deﬁnition as

With respect to the biased Fourier expansion of f
ator Di satisﬁes

∈

Dφi =

σ

·

Dxi .

L2({

1, 1}n, π⊗

n
p ) the oper-

−

f (S) φS\{i}.

(8.7)

Di f

=

i
S
3
X

b

Given this deﬁnition we can derive some additional formulas for inﬂu-

ences, including a generalization of Proposition 2.21:

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 17 -->
8.4. p-biased analysis

223

Proposition 8.45. Suppose f
1, 1}). Then
range {

−

L2({

1, 1}n, π⊗

n
p ) is Boolean-valued (i.e., has

−

∈

for each i

[n], and

∈

Infi[ f ]

σ2 Pr
x
π⊗
p
∼

n

=

[ f (x)

6=

f (x⊕

i)]

I[ f ]

σ2 E
x
π⊗
p
∼

n

=

[sens f (x)].

If furthermore f is monotone, then Infi[ f ]

σ

f (i).

=

Proof. Using Deﬁnition 8.44’s notation we have
b
σ2 E
πp

[(Dφi f )2]

Infi[ f ]

E
πp

=

=

[(Dxi f )2].

Since (Dxi f )2 is the 0-1 indicator that i is pivotal for f , the ﬁrst formula
follows. The second formula follows by summing over i. Finally, when f is
monotone we furthermore have that (Dxi f )2
Infi[ f ]
σ E
πp

Dxi f and hence

=
[Dφi f ]

σ2 E
πp

[Dxi f ]

f (i),

σ

=

=

=

as claimed.

b

(cid:3)

The remainder of this section is devoted to the topic of threshold phenom-
ena in Boolean functions. Much of the motivation for this comes from theory
of random graphs, which we now brieﬂy introduce.

(v
2)

Deﬁnition 8.46. Given an undirected graph G on v
2 vertices, we identify
≥
it with the string in {True,False}(v
2) which indicates which edges are present
(True) and which are absent (False). We write G (v, p) for the distribution
; this is called the Erd˝os–Rényi random graph model. Note that if we
edges.
{True,False}
¡

π⊗
p
permute the v vertices of a graph, this induces a permutation on the
A (v-vertex) graph property is a Boolean function f : {True,False}(v
2)
that is invariant under all v! such permutations of its input; colloquially, this
means that f “does not depend on the names of the vertices”.

→

v
2

¢

Graph properties are always transitive-symmetric functions in the sense of
Deﬁnition 2.10.

Example 8.47. The following are all v-vertex graph properties:

Conn(G)

3Col(G)

Cliquek(G)
Majn(G)
χ[n](G)

=

=

=

=

=

True if G is connected;
True if G is 3-colorable;
True if G is contains a clique on at least k vertices;
True (assuming n
=
True if G has an odd number of edges.
¡

is odd) if G has at least

v
2

v
2

¢

¡

¢

/2 edges;

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 18 -->
224

8. Generalized domains

Note that each of these actually deﬁnes a family of Boolean functions, one
for each value of v; this is the typical situation in the study of graph proper-
ties. An example of a function f : {True,False}(v
2)
{True,False} that is not a
True if vertex #1 has at least one
graph property is the one deﬁned by f (G)
neighbor; this f is not invariant under permuting the vertices.

→

=

Graph properties which are monotone are particularly nice to study; these
are the ones for which adding edges can never make the property go from True
to False. The properties Conn, Cliquek, and Majn deﬁned above are all mono-
tone, as is
3Col. Now suppose we take a monotone graph property, say, Conn.
A typical question in random graph theory would be, “how many edges does a
graph need to have before it is likely to be connected?” Or more precisely, how
does PrG

True] vary as p increases from 0 to 1?

¬

G (v,p)[Conn(G)
∼

=

There’s no need to ask this question just for graph properties. Given any
{True,False} it is intuitively
monotone Boolean function f : {True,False}n
True] to in-
clear that when p increases from 0 to 1 this causes Prπp [ f (x)
crease from 0 to 1 (unless f is a constant function). As illustration, we show a
True] versus p for the dictator function, AND2, and Maj101.
plot of Prπp [ f (x)

→

=

=

Figure 8.1. Plot of Prπp [ f (x)
AND2 (dashed), and f
f

=

Maj101 (solid)

=

=

True] versus p for f a dictator (dotted),

The Margulis–Russo Formula quantiﬁes the rate at which Prπp [ f (x)
=
True] increases with p; speciﬁcally, it relates the slope of the curve at p to the
total inﬂuence of f under π⊗
1 notation.

n
p . To prove the formula we switch to

±

Margulis–Russo Formula. Let f : {
and the relation µ

2p, we have

1

−

=

−

1, 1}n

R. Recalling Notation 8.43

→

d
dµ

E[ f (p)]

1
σ ·

=

n

f (p)(i).

(8.8)

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.

i
1
=
X

d



<!-- pdf-page: 19 -->
225

(8.9)

8.4. p-biased analysis

In particular, if f : {

1, 1} is monotone, then

1, 1}n

−

{
−

→

d
d p

Pr
π⊗
p

∼

n

x

[ f (x)

1]

= −

=

d
dµ

E[ f (p)]

1
σ2 ·

=

I[ f (p)].

Proof. Treating f as a multilinear polynomial over x1, . . . , xn we have

E[ f (p)]

=

Tµ f (1, . . . , 1)

f (µ, . . . , µ)

=

(this also follows from Exercise 1.4). By basic calculus,

d
dµ

f (µ, . . . , µ)

n

=

i
1
=
X

Dxi f (µ, . . . , µ).

But

Dxi f (µ, . . . , µ)

E[Dxi f (p)]

E[Dφi f (p)]

=
completing the proof of (8.8). As for (8.9), the second equality follows immedi-
2p and
ately from Proposition 8.45. The ﬁrst equality holds because µ
(cid:3)
E[ f ]

1]; the two factors of

2 cancel.

2 Pr[ f

d

=

=

=

−

σ

σ

1

1

1

f (p)(i),

=

−

= −

1

−

Remark 8.48. If f : {True,False}n
function, the Margulis–Russo Formula implies that Prπp [ f (x)
=
strictly increasing function of p, because I[ f (p)] is always positive.

{True,False} is a nonconstant monotone
True] is a

→

Looking again at Figure 8.1 we see that the plot for Maj101 looks very
much like a step function, jumping from nearly 0 to nearly 1 around the
critical value p
1/2. For Majn, this “sharp threshold at p
1/2” becomes
more and more pronounced as n increases. This is clearly suggested by the
Margulis–Russo Formula: the derivative of the curve at p
1/2 is equal to
I[Majn] (the usual, uniform-distribution total inﬂuence), which has the very
large value Θ(pn) (Theorem 2.33). Such sharp thresholds exist for many
Boolean functions; we give some examples:

=

=

=

Example 8.49. In Exercise 8.23 you are asked to show that for every ²
there is a C such that

0

>

Pr

π1/2

C/pn

−

[Majn =

True]

²,

≤

Pr

π1/2
+

C/pn

[Majn =

True]

².

1

−

≥

Regarding the Erd˝os–Rényi graph model, the following facts are known:

Pr
G (v,p)
∼

G

[Cliquelog v(G)

[Conn(G)

Pr
G (v,p)
∼

G

True]

True]

=

=

0 if p

−−−−→v

→∞ (

1 if p

0 if p

−−−−→v

→∞ (

1 if p

1/4,

1/4.

ln v
v (1
ln v
v (1

−

+

log log v
log v ),
log log v
log v ).

<

>

<

>

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 20 -->
226

8. Generalized domains

In the above examples you can see that the “jump” occurs at various values
of p. To investigate this phenomenon, we ﬁrst single out the value for which
Prπp [ f (x)

True]

1/2:

=

=

Deﬁnition 8.50. Let f : {True,False}n
{True,False} be monotone and non-
constant. The critical probability for f , denoted pc, is the unique value
True]
pc,
in (0, 1) for which Prx
=
4pc qc.
µc

1/2. We also write qc

∼
2pc, and σc

[ f (x)

pc

qc

→

π⊗
p

−

=

=

1

1

n

=

−

=

−

=

p
In Exercise 8.27 you are asked to verify that pc is well deﬁned.

=

±

±

=

pc. Intuitively, we would expect Prπp [ f (x)

Looking at the connectivity property from Example 8.49 we see that not
True] jump from near 0 to near 1 in an interval of
only does Prπp [Conn
o(1), it actually makes the jump in an interval of the form
the form pc
o(1)). This latter phenomenon is (roughly speaking) what is meant
pc(1
by a “sharp threshold”. To investigate this further, suppose that f is a (non-
True] at
constant) monotone function and ∆ is the derivative of Prπp [ f (x)
True] to jump from near 0 to
p
near 1 in an interval of around pc of width about 1/∆. Thus a “sharp thresh-
old” should roughly correspond to the case that 1/∆ is small even compared
to min(pc, qc). The Margulis–Russo Formula says that ∆
I[ f (pc)], and
=
c it follows that 1/∆ is “small”
σ2
since min(pc, qc) is proportional to 4pc qc
compared to min(pc, qc) if and only if I[ f (pc)] is “large”. Thus we have a neat
criterion:
{True,False} be monotone.
Sharp threshold principle: Let f : {True,False}n
True] has a “sharp threshold” if and only
Then, roughly speaking, Prπp [ f (x)
if f has “large” (“superconstant”) total inﬂuence under its critical probability
distribution.

1
σ2
c

→

=

=

=

=

∈

−

L2({

1, 1}n, π⊗

Of course this should all be made a bit more precise; see Exercise 8.28
for details. In light of this principle, we may try to prove that a given f
has a sharp threshold by proving that I[ f (pc)] is not “small”. In turn, this
strongly motivates the problem of “characterizing” Boolean-valued functions
n
p ) for which I[ f ] is small. Friedgut’s Junta Theorem, men-
f
tioned at the end of Chapter 3.1 and proved in Chapter 9.6, tells us that in
1/2, the only way I[ f ] can be small is if f
the uniform distribution case p
is close to a junta. In particular, any monotone graph property with pc
1/2
must have a very large derivative d
pc: since the func-
d p Prπp [ f
tion is transitive-symmetric, all n coordinates are equally inﬂuential and it
can’t be close to a junta. These results also hold so long as p is bounded
away from 0 and 1; see Chapter 10.3. However, many interesting monotone
graph properties have pc very close to 0: e.g., connectivity, as we saw in Ex-
n
p ) with small I[ f ]
ample 8.49. Characterizing the functions f

True] at p

1, 1}n, π⊗

L2({

=

=

=

=

∈

−

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 21 -->
8.5. Abelian groups

227

when p
Hatami described in Chapter 10.5.

=

on(1) is a trickier task; see the work of Friedgut, Bourgain, and

8.5. Abelian groups

L2(Ωn, π⊗

n) with

The previous section covered the case of f
2; there,
| =
we saw it could be helpful to look at explicit Fourier bases. When
3
this is often not helpful, especially if the only “operation” on the domain is
equality. For example, if f : {Red,Green,Blue}n
R, then it’s best to just work
abstractly with the orthogonal decomposition. However, if there is a notion
of, say, “addition” in Ω, then there is a natural, canonical Fourier basis for
L2(Ω, π) when π is the uniform distribution.

| ≥

→

Ω

∈

|

|

Ω

+

More precisely, suppose the domain Ω is a ﬁnite abelian group G, with
and identity 0. We will consider the domain G under the uni-
operation
form probability distribution π; this is quite natural because π is translation-
invariant: π(X )
G. In this setting it is more
⊆
convenient to allow functions with range the complex numbers; thus we come
to the following deﬁnition:

X ) for any X

G, t

π(t

=

+

∈

Deﬁnition 8.51. Let G be a ﬁnite abelian group with operation
tity 0. For n
∈
functions f : G n

and iden-
N+ we write L2(G n) for the complex inner product space of

C, with inner product

+

→

E
G n
∼
Here and throughout this section x
uniform distribution on G n.

f , g

〉 =

∼

〈

x

[ f (x)g(x)].

G n denotes that x is drawn from the

Everything we have done in this chapter for the real inner product space
n) generalizes easily to the case of a complex inner product; the main

L2(Ωn, π⊗
difference is that Plancherel’s Theorem becomes

f , g

〈

〉 =

α

Nn
∈
X
<

f (α)

g(α)

m

b

b

=

[n]〈
S
⊆
X

f =

S, g=

S

.

〉

See Exercise 8.32 for more.

A natural Fourier basis for L2(G) comes from a natural family of functions
C, namely the characters. These are deﬁned to be the group homomor-
G
phisms from G to C×, where C× is the abelian group of nonzero complex
numbers under multiplication.

→

Deﬁnition 8.52. A character of the (ﬁnite) group G is a function χ : G
which is a homomorphism; i.e., satisﬁes χ(x
there is some m
1
of unity. In particular,

C×
χ(x)χ(y). Since G is ﬁnite
G. Thus
+· · ·+
χ(x)m, meaning the range of χ is in fact contained in the mth roots
G.

+
x (m times) for each x

N+ such that 0

1 for all x

χ(0)

→

χ(x)

y)

=

=

=

=

+

∈

∈

x

x

|

| =

∈

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 22 -->
228

8. Generalized domains

We have the following easy facts:

Fact 8.53. If χ and φ are characters of G, then so are χ and φ

χ.

Proposition 8.54. Let χ be a character of G. Then either χ

·
1 or E[χ]

0.

=

y is uniformly

≡
1. Since x

+

Proof. If χ
6≡
distributed on G when x

1, pick some y
∈
G,

G such that χ(y)

6=

∼
[χ(x

[χ(x)]

E
G
x
∼
1 it follow that E[χ(x)] must be 0.

E
G
x
∼

E
G
x
∼

y)]

=

=

+

[χ(x)χ(y)]

=

χ(y) E
G
∼

x

[χ(x)].

(cid:3)

Since χ(y)

6=

Proposition 8.55. The set of all characters of G is orthonormal. (As a conse-
quence, G has at most dim(L2(G))

= |
2]
Proof. First, if χ is a character, then
E[
χ
|
|
φ, χ
if φ is another character distinct from χ then
〈
character by Fact 8.53, and φ
we used χ

φ/χ
·
=
1. Thus

1 because
E[φ

1. Next,
χ is a
·
1 because φ and χ are distinct; here
(cid:3)

χ
|
| ≡
χ]. But φ

0 by Proposition 8.54.

1/χ because

characters.)

|
χ, χ

=
〉 =

6≡
φ, χ

〉 =

G

χ

χ

〈

·

=

〉 =
|
As we will see next, G in fact has exactly

| ≡

〈

characters. It thus follows
from Proposition 8.55 that the set of all characters (which includes the con-
stant 1 function) constitutes a Fourier basis for L2(G).

G
|

|

To check that each ﬁnite abelian group G has

distinct characters, we
begin with the case of a cyclic group, Zm for some m. In this case we know
that every character’s range will be contained in the mth roots of unity.

G
|

|

Deﬁnition 8.56. Fix an integer m
m, we deﬁne χ j : Zm
exp(2πi/m). For 0
j
<
see that these are distinct characters of Zm.

≤

≥

→

2 and write ω for the mth root of unity
ω jx. It is easy to

C by χ j(x)

=

Thus the functions χ0

1 form a Fourier basis for L2(Zm).
−
Furthermore, Proposition 8.13 tells us that we can get a Fourier basis for
L2(Zn

m) by taking all products of these functions.

1, χ1, . . . , χm

≡

Deﬁnition 8.57. Continuing Deﬁnition 8.56, let n
deﬁne χα : Zn

C by

m →

n

N+. For α

Nn
<

∈

m we

∈

j
1
=
Y
These functions are easily seen to be (all of the) characters of the group Zn
m,
and they constitute a Fourier basis of L2(Zn

m).

χα(x)

=

χα j (x j).

Most generally, by the Fundamental Theorem of Finitely Generated Abelian

Groups we know that any ﬁnite abelian G is a direct product of cyclic groups
of prime-power order. In Exercise 8.35 you are asked to check that you get all
of the characters of G – and hence a Fourier basis for L2(G) – by taking all

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 23 -->
8.6. Highlight: Randomized decision tree complexity

229

products of the associated cyclic groups’ characters. In the remainder of the
section we mostly stick to groups of the form Zn
Returning to the characters χ0, . . . , χm
1) that they satisfy χ j

1 from Deﬁnition 8.56, it is easy
−
to see (using ωm
χ j0 =
=
·
j (mod m). Thus the characters themselves form a group under mul-
χ j
tiplication, isomorphic to Zm. As in Chapter 3.2, we index them using the
Zm. More generally, indexing the Fourier basis/characters of L2(Zn
notation
m)
Zn
by

m instead of multi-indices, we have:

j0 (mod m) and also 1/χ j

m for simplicity.

χ j

=

=

χ

+

−

of Zn

m form a group under multiplication:

d

d

Fact 8.58. The characters (χα)α
∈
χα
χα =

χβ =
χα ·
1/χα =

β,
+
χ

α.
−

•

Zn
m

d

•
As mentioned, the salient feature of L2(G) distinguishing it from other
spaces L2(Ω, π) is that there is a notion of addition on the domain. This
means that convolution plays a major role in its analysis. We generalize the
deﬁnition from the setting of Fn
2 :

Deﬁnition 8.59. Let f , g
L2(G) deﬁned by

∈

L2(G). Their convolution is the function f

g

∈

∗

g)(x)

( f

∗

=

E
G
y
∼

[ f (y)g(x

y)]

−

=

E
G
y
∼

[ f (x

−

y)g(y)].

Exercise 8.36 asks you to check that convolution is associative and com-

mutative, and that the following generalization of Theorem 1.27 holds:

Theorem 8.60. Let f , g

L2(G). Then

f

∈

g(α)

∗

=

f (α)

g(α).

b

b

We conclude this section by mentioning vector space domains. When
(cid:129)
doing Fourier analysis over the group Zn
m, it is natural for subgroups to arise.
Things are simplest when the only subgroups of Zm are the trivial ones, {0}
and Zm; in this case, all subgroups will be isomorphic to Zn0
≤
n. Of course, this simple situation occurs if and only if m is equal to some
prime p. In that case, Zp can be thought of as a ﬁeld, Zn
p as an n-dimensional
vector space over this ﬁeld, and its subgroups as subspaces. We use the
Fn
notation Fn
p to index the Fourier basis/characters;
p in this setting and write
this generalizes the notation introduced for p
2 in Chapter 3.2. Indeed, all
c
of the notions from Chapters 3.2 and 3.3 regarding afﬁne subspaces and
restrictions thereto generalize easily to L2(Fn

m for some n0

=

p).

8.6. Highlight: Randomized decision tree complexity

A decision tree T for f : {
1, 1} can be thought of as a deterministic
algorithm which, given adaptive query access to the bits of an unknown string

{
−

→

−

1, 1}n

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 24 -->
230

8. Generalized domains

∈
=

1, 1}n, outputs f (x). For example, to describe a natural decision tree for
x
{
−
Maj3 in words: “Query x1, then x2. If they are equal, output their value;
f
otherwise, query and output x3.” For a worst-case input (one where x1
x2)
this algorithm has a cost of 3, meaning it makes 3 queries. The cost of the
worst-case input is the depth of the decision tree.

6=

As is often the case with algorithms it can be advantageous to allow ran-
domization. For example, consider using the following randomized query
algorithm for Maj3: “Choose two distinct input coordinates at random and
query them. If they are equal, output their value; otherwise, query and out-
put the third input coordinate.” Now for every input there is at least a 1/3
chance that the algorithm will ﬁnish after only 2 queries. Indeed, if we deﬁne
the cost of an input x to be the expected number of queries the algorithm
makes on it, it is easy to see that the worst-case inputs for this algorithm
have cost (1/3)

(2/3)

8/3

3.

3

2

<
Let’s formalize the notion of a randomized decision tree:

=

+

·

·

−

→

1, 1}n

R, a (zero-error) randomized decision
Deﬁnition 8.61. Given f : {
tree T computing f is formally deﬁned to be a probability distribution over
(deterministic) decision trees that compute f . The cost of T on input x
∈
1, 1}n is deﬁned to be the expected number of queries T makes on x when
{
−
T . The cost of T itself is deﬁned to be the maximum cost of any input.
T
Finally, the (zero-error) randomized decision tree complexity of f , denoted
RDT( f ), is the minimum cost of a randomized decision tree computing f .

∼

We can get further savings from randomization if we are willing to assume
1, 1}3 is uniformly
that the input x is chosen randomly. For example, if x
random then any of the deterministic decision trees for Maj3 will make 2
queries with probability 1/2 and 3 queries with probability 1/2, for an overall
expected 5/2

3 queries.

{
−

8/3

∼

<

<

Deﬁnition 8.62. Let T be a randomized decision tree. We deﬁne

δi(T )

=

x

∆(T )

=

1,1}n,
T

Pr
{
−
∼
T
∼
δi(T )

n

i
1
=
X
1, 1}n

[T queries xi],

=

x

E
1,1}n,
{
−
∼
T
T
∼

[# of coordinates queried by T on x].

(8.10)

Given f : {
randomized decision trees T computing f .

→

−

R, we deﬁne ∆( f ) to be the minimum of ∆(T ) over all

We can also generalize these deﬁnitions for functions f

n). A
deterministic decision tree over domain Ω is the natural generalization in
Ω
which each internal query node has
outgoing edges, labeled by the ele-
ments of Ω. We write δ(π)
(T ), ∆(π)(T ), ∆(π)( f ) for the generalizations to trees

L2(Ω, π⊗

∈

|

|

i

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 25 -->
8.6. Highlight: Randomized decision tree complexity

231

over Ω; in the case of L2({
(πp) for brevity.

−

1, 1}n, π⊗

n
p ) we use the superscript (p) instead of

It follows immediately from the deﬁnitions that for any f

∆(π)( f )

RDT( f )

DT( f ).

≤

≤

L2(Ωn, π⊗

n),

∈

Remark 8.63. In the deﬁnition of ∆(π)( f ) it is equivalent if we only allow
deterministic decision trees; this is because in (8.10) we can always choose
the “best” deterministic T in the support of T .

Example 8.64. It follows from our discussions that RDT(Maj3)
∆(Maj3)
≤
equalities.
majority of 3 function on n

8/3 and
5/2; indeed, it’s not hard to show that both of these bounds are
In Exercise 8.38 you are asked to generalize to the recursive
3d inputs; it satisﬁes DT(Maj⊗
d
3 )
d
3 )

RDT(Maj⊗
∆(Maj⊗

(8/3)d
(5/2)d

n.89,
n.83.

nlog3(5/2)

nlog3(8/3)

n, but

d
3 )

3d

≤

=

≈

=

≤

=

=

≤

=

≈

Incidentally, these bounds are not asymptotically sharp; estimating RDT(Maj⊗
in particular is a well-studied open problem.

d
3 )

Example 8.65. In Exercise 8.39 you are asked to show that for the logical OR
function, ∆(p)(ORn)
1/2 but is asymptotic
=
to n/(2 ln 2) at the critical probability pc.

, which is roughly 2 for p

(1
−
p

p)n

=

−

1

Example 8.64 illustrates a mildly surprising phenomenon: using random-
ness it’s possible to evaluate certain unbiased n-bit functions f while reading
only a 1/nΘ(1) fraction of the input bits. This is even more interesting when f
d
is transitive-symmetric like Maj⊗
3 . In that case it’s not hard to show (Exer-
cise 8.37) that any randomized decision tree T computing f can be converted
to one where ∆(T ) remains the same but all δi(T ) are equal to ∆( f )/n. Then f
can be evaluated despite the fact that each input bit is only queried with prob-
ability 1/nΘ(1).

In this section we explore the limits of this phenomenon. In particular,
a longstanding conjecture of Yao [Yao77] says that this is not possible for
monotone graph properties:

Yao’s Conjecture. Let f : {
−
vertex graph property, where n

{
−

→
. Then RDT( f )

1, 1} be a nonconstant monotone v-

Ω(n).

≥

1, 1}n
v
2

=

¡

¢

Toward this conjecture we will present a lower bound due to O’Donnell,
Saks, Schramm, and Servedio [OSSS05]. (Two other incomparable bounds
are discussed in the notes for this chapter.) It has the advantages that it
works for the more general class of transitive-symmetric functions and that
it even lower-bounds ∆(pc)( f ):

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 26 -->
232

8. Generalized domains

1, 1}n
Theorem 8.66. Let f : {
symmetric function with critical probability pc. Then

{
−

→

−

1, 1} be a nonconstant monotone transitive-

∆(pc)( f )

≥

(n/σc)2/3.

Theorem 8.66 is essentially sharp in several interesting cases. Whenever
Θ(1/pn) and The-
the critical probability pc is Θ(1/n) or 1
Θ(1/n) then σc
=
Ω(n). This occurs,
orem 8.66 gives the strongest possible bound, ∆(pc)( f )
e.g., for the ORn function (Example 8.65). Furthermore, Theorem 8.66 can
be tight up to a logarithmic factor when pc
1/2 as the following theorem of
Benjamini, Schramm, and Wilson shows:

=

≥

−

Theorem 8.67. [BSW05]. There exists an inﬁnite family of monotone transitive-
symmetric functions f n : {
∆( f )
O(n2/3 log n).

1, 1} with critical probability pc

1/2 and

1, 1}n

{
−

→

−

=

≤

Theorem 8.66 follows easily from two inequalities [OS06, OS07], [OSSS05],

which we now present:

OS Inequality. Let f

−
In particular, if f has range {

∈

L2({

1, 1}n, π⊗

n
p ). Then

2
k
1, 1} and is monotone, then I[ f ]

≤ k

=

f (i)

n
i

f

1

·

∆(p)( f ).

p
σ

∆(p)( f ).

P

−

b

≤

OSSS Inequality. Let f
randomized decision tree computing f . Then

L2(Ωn, π⊗

∈

n) have range {

−

p
1, 1} and let T be any

n

Var[ f ]

≤

δ(π)
i

(T )

·

Infi[ f ].

i
1
=
X
Remark 8.68. An interesting corollary of the OSSS Inequality is that

MaxInf[ f ]

Var[ f ]/∆(π)( f )

≥

the last inequality assuming Ω

Var[ f ]/DT( f )

≥
1, 1}. See Exercise 8.44.

≥

Var[ f ]/ deg( f )3,

{
−

=

These two inequalities can be thought of as strengthenings of basic Fourier
inequalities which take into account the decision tree complexity of f . The
OS Inequality essentially generalizes the result that majority functions maxi-
f (i); i.e., Theorem 2.33. The OSSS Inequality is a generalization
mizes
of the Poincaré Inequality, discounting the inﬂuences of coordinates that are
rarely read.

P

n
i

b

=

1

We will ﬁrst derive the query complexity lower bound Theorem 8.66 from
the OS and OSSS Inequalities. We will then prove the latter two inequalities.

Proof of Theorem 8.66. We consider f to be an element of L2({
).
Let T be a randomized decision tree achieving ∆(pc)( f ). In the OSSS Inequal-
I[ f ]/n
ity, we have Var[ f ]

1 since pc is the critical probability and Infi[ f ]

n
1, 1}n, π⊗
pc

−

=

=

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 27 -->
8.6. Highlight: Randomized decision tree complexity

233

for each i

∈

[n] since f is transitive-symmetric. Thus

δ

(pc)
i

(T )

I[ f ]
n

·

1

≤

i
1
=
X

∆(pc)( f )

n

≤

I[ f ]

·

≤

σ∆(pc)( f )3/2,

=⇒

where we used the OS Inequality. The theorem follows by rearranging.

(cid:3)

Now we prove the OS and OSSS Inequalities, starting with the latter. We

will need a simple lemma that uses the decomposition f

Ei f

=

+

Li f .

Lemma 8.69. Let f , g
ω
for the restriction of f in which the jth coordinate is ﬁxed to value ω, and
similarly for g. Then

[n]. Given ω

∈

∈

∈

|

n) and let j

L2(Ωn, π⊗

Ω, write f

Cov[ f , g]

=

E
ω,ω0

π

∼

independent

[Cov[ f

ω, g

ω

0]]

|

|

+ 〈

L j f , L j g

.

〉

Proof. Since the covariances and Laplacians are unchanged when constants
are added, we may assume without loss of generality that E[ f ]
0.
Then Cov[ f , g]

E[g]

and

f , g

=

=

= 〈

〉

E
ω,ω

0

[Cov[ f

ω, g

|

ω

|

0]]

f

[
〈
|
0
ω, g

E
ω,ω
f

[
〈

|

0

=
E
ω,ω

=

ω, g

ω

E[ f

ω] E[g

ω

0]]

|
]

|

0〉 −
E[ f ] E[g]

ω

|

0〉

−

|
E
ω,ω

=

ω, g

[

f

|

〈

0

]

ω

|

0〉

E j f , E j g

= 〈

.

〉

Thus the stated equality reduces to the basic (Exercise 8.8) identity

f , g

〈

E j f , E j g

〉 = 〈

L j f , L j g

.

〉

〉 + 〈

Proof of the OSSS Inequality. More generally we show that if g : {
{
−

1, 1} is also an element of L2(Ωn, π⊗

n), then

−

1, 1}n

(cid:3)

→

Cov[ f , g]

n

≤

i
1
=
X

δ(π)
i

(T )

·

Infi[g].

(8.11)

=

f . We may also assume that T

The result then follow by taking g
T is a
single deterministic tree computing f ; this is because (8.11) is linear in the
quantities δ(π)
(T ). We prove (8.11) by induction on the structure of T. If T is
depth-0, then f must be a constant function; hence Cov[ f , g]
0 and (8.11) is
trivial. Otherwise, let j
[n] be the coordinate queried at the root of T. For
Ω, write Tω for the subtree of T given by the ω-labeled child of the
each ω
root. By applying Lemma 8.69 and induction (noting that Tω computes the

=

=

∈

∈

i

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 28 -->
234

8. Generalized domains

restricted function f

ω), we get

|

E
ω,ω0

π

∼

independent

[Cov[ f

ω, g

ω

0]]

|

|

+ 〈

L j f , L j g

〉

Cov[ f , g]

=

≤

=

≤

=

E
ω,ω
π
0∼
δ(π)
i

j
i
hX
6=
(T)

j
i
6=
X

j
i
6=
X
n

i
1
=
X

δ(π)
i

(T)

δ(π)
i

(T)

δ(π)
i

(Tω)

·

Infi[gω

L j f , L j g

〉

0]
i

+ 〈

Infi[g]

f , L j g

〉

+ 〈

(in part since E[L j g]

0)

=

Infi[g]

E[

|

+

L j g

]

|

(since

f

|

| ≤

1)

Infi[g],

·

·

·

where the last step used δ(π)
j
inductive proof of (8.11).

(T)

1 and Proposition 8.24. This completes the
(cid:3)

=

Finally, we prove the OS Inequality. For this we require a deﬁnition.

Deﬁnition 8.70. Let (Ω, π) be a ﬁnite probability space and T a deterministic
decision tree over Ω. The decision tree process associated to T generates
a random string x distributed according to π (and some additional random
variables), as follows:

(1) Start at the root node of T; say it queries coordinate j1. Choose x j1 ∼

and follow the outgoing edge labeled by the outcome.

π

(2) Suppose the node of T which is reached queries coordinate j2. Choose
π and follow the outgoing edge labeled by the outcome.

x j2 ∼

(3) Repeat until a leaf node is reached. Then, deﬁne J

to be the set of coordinates queried.

{ j1, j2, j3, . . . }

[n]

⊆

=

(4) Draw the as-yet-unqueried coordinates, denoted xJ, from π⊗

J.

Despite the fact that the coordinates xi are drawn in a random, dependent
order, it’s not hard to see (Exercise 8.42) that the ﬁnal string x
(xJ, xJ) is
distributed according the product distribution π⊗

n.

=

Proof of the OS Inequality. We will prove the claim
the “in particular” statement follows immediately from Proposition 8.45. Fix
a deterministic decision tree T achieving ∆(p)( f ) (see Remark 8.63) and let
x
(xJ, xJ) be drawn from the associated decision tree process. Using the
notation φ from Deﬁnition 8.39 we have

f (i)

≤ k

2
k

p

P

=

b

=

f

1

·

n
i

∆(p)( f );

n

i
1
=
X

f (i)

E
J,xJ ,xJ

=

[ f (x)

φ(xi)]

E
J,xJ

[ f (xJ) E
xJ

[

=

φ(xi)]].

b
Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.

n

i
1
=
P

n

i
1
=
P



<!-- pdf-page: 29 -->
8.7. Exercises and notes

235

Here we abused notation slightly by writing f (xJ); in the decision tree process,
f ’s value is determined once xJ is. Since E[φ(xi)]
J we may
continue:

0 for each i

=

6∈

E
J,xJ

[ f (xJ) E
xJ

[

n

i
1
=
P

φ(xi)]]

E
J,xJ

=

[ f (xJ)

n

i
1
=
P

J}φ(xi)]

1{i

∈

≤

E
J,xJ

[ f (xJ)2]

E
J,xJ ·³
EJ,xJ [ f (xJ)2] is simply

s

r

n

i
1
=
P
f

J}φ(xi)

1{i

∈

2

,
¸

´

2 since T computes f .
k

k

by Cauchy–Schwarz. Now
To complete the proof it sufﬁces to show that

q

i
1
=
P
To see this, expand the square:

E
J,xJ ·³

n

J}φ(xi)

1{i

∈

∆(p)( f ).

2

=

¸

´

n

1{i

E
J,xJ ·³
i
1
=
P
Conditioned on i

∈

J}φ(xi)
´

2

n

=

¸

i
1
=
X

[1{i

E
J,xJ

∈

J}φ(xi)2]

+

E
J,xJ

[1{i,i0∈

J}φ(xi)φ(xi0)].

i0
i
6=
X

J the quantity E[φ(xi)2] is simply 1. Thus
n

∈
n

J}φ(xi)2]

[1{i

E
J,xJ

∈

i
1
=
X

∆(p)( f ).

=

Pr[i

J]

∈

=

i
1
=
X
J}φ(xi)φ(xi0)]

i0. Sup-
0 whenever i
It remains to show that EJ,xJ [1{i,i0∈
pose we condition on the event that i, i0
J and we further condition on i
being queried before i0 is queried. Certainly this may affect the conditional
distribution of xi, but the conditional distribution of xi0 remains πp; hence
E[φ(xi0)]
0 under this conditioning. Of course the same argument holds
when we condition on i0 being queried before i. From this it follows that
(cid:3)
EJ,xJ [1{i,i0∈

J}φ(xi)φ(xi0)] is indeed 0, completing the proof.

=

=

6=

∈

8.7. Exercises and notes

8.1 Explain how to generalize the deﬁnitions and results in Sections 8.1

and 8.2 to general ﬁnite product spaces L2(Ω1

Ωn, π1

πn).

× · · · ×

× · · · ×

8.2 Verify that Deﬁnition 8.1 indeed deﬁnes a real inner product space. (Where

is the fact that π has full support used?)

8.3 Verify the formula for

f (α) in Deﬁnition 8.14.

8.4 Verify that φ0, φ1, φ2 from Example 8.10 indeed constitute a Fourier basis

for Ω

=

{a, b, c} with the uniform distribution.

b

8.5 Verify the Fourier expansion in Example 8.15.

8.6 Complete the proof of Proposition 8.16.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 30 -->
236

8. Generalized domains

8.7 Prove that the expectation over I operator, EI , is a linear operator on
EI ), and
). Deduce that Tρ is also self-adjoint.

L2(Ωn, π⊗
self-adjoint (i.e.,

EI g), a projection (i.e., EI

EI f
+
EI f , g

n) (i.e., EI ( f

+
f , EI g

EI

g)

=

◦

〈
8.8 Show for any f , g
E j f , E j g

f , g

〈

〉 = 〈

∈
〉 + 〈

=
〉 = 〈
L2(Ωn, π⊗
L j f , L j g

〉

〉
n) and j
.

8.9 Prove Proposition 8.24. (Hint: Exercise 1.17.)

L2(Ωn, π⊗
8.10 Let f
∈
2
Li f
Li f
1
2 =
k
k
= k
k
(a) Show that
Li f
k
p
(b) In case 1
≤

n) have range {
Infi[ f ].
p
p ≤
k
2, show that in fact

2pInfi[ f ] for any p
≥
Li f
k
k

≤

−

general form of Hölder’s inequality to bound
and

Li f
k

k

2.)

[n] that f

E j f

=

+

∈

L j f and that

1, 1}. Proposition 8.24 tells us that

1.
p
Infi[ f ]. (Hint: Use the
p ≤
Li f
k

p in terms of

Li f
k

1
k

k

8.11 Generalize all of Exercise 2.35 to the setting of L2(Ωn, π⊗

1, 1] should refer only to ρ

n). Caution: the
[0, 1] in this

∈

two statements referring to ρ
more general setting.
Ω

[

∈

−

8.12 Assume
|
(a) For x

| =
Ωn and y

m and let π denote the uniform distribution on Ω.
Nρ(x), write a formula for Pr[yi =
(there are two cases depending on whether or not xi
=

∼

∈

ω] in terms of ρ
ω).

(b) Verify that your formula deﬁnes a valid probability distribution on Ω
0. We may therefore extend the deﬁnition of

even when
Nρ to this case. (Cf. the second half of Deﬁnition 2.40.)
n and y

Nρ(x), the distribution of (x, y) is

1 ≤
−

1
m

−

<

ρ

(c) Verify that for x

π⊗
symmetric in x and y.

∼

∼

(d) Show that when y

Ω \ {xi}.

N

−

∼

1
m

1

−

(x), each yi is uniformly distributed on

(e) Verify that the formula for Tρ from Proposition 8.28 continues to hold
[0, 1] and

0. (Hint: Use the fact that it holds for ρ

for
that the formula in part (a) is a polynomial in ρ.)

1 ≤
−

1
m

−

<

∈

ρ

8.13 Show that Deﬁnition 8.30 extends by continuity to

Inf(0)
i

[ f ]

=

f (α)2.

1
#α
=
X
0
αi
6=

b

Extend also Proposition 8.31 to the case of δ

1.

=

8.14 Prove explicitly that condition 5 holds in Theorem 8.35.

8.15 Prove that condition 6 must hold in Theorem 8.35 directly from the
uniqueness statement (i.e., without appealing to the explicit construc-
tion).

L2(Ωn, π⊗
8.16 Let f
∈
T is equal to f =
S)⊆

n). Prove directly from the deﬁning Theorem 8.35 that
T and is equal to 0 otherwise.

S if S

( f =

⊆

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 31 -->
8.7. Exercises and notes

237

8.17 Let f

∈

∼

π⊗

L2(Ωn, π⊗

n) and let x

n. In this exercise you should think
about how the (conditional) expectation of f changes as the random vari-
ables x1, . . . , xn are revealed one at a time.
(a) Recalling that f ⊆

[t](x) depends only on x1, . . . , xt, show that the se-
0...n is a martingale (where
=

quence of random variables ( f ⊆
f ⊆

[0] denotes f ;); i.e.,

[t](x))t

E[ f ⊆

[t](x)

|

f ⊆

[t
[0](x), . . . , f ⊆

1](x)]
−

[t

f ⊆

1](x)
−

=

[n].

t

∀

∈

(This is the Doob martingale for f .)
[n] deﬁne

(b) For each t

∈

dt f

=

[t]

f ⊆

−

[t

f ⊆

1]

−

=

f =

S.

[n]
S
⊆
X
max(S)

t

=
1](x)]
−

Show that E[dt f (x)
|
the martingale difference sequence for f .)

[t
[0](x), . . . , f ⊆

f ⊆

0. (Here (dt f )t

1...n is
=

=

8.18 For f , g

∈

L2(Ωn, π⊗

n), prove the following directly from Theorem 8.35:

f , g

〈

〉 =

Infi[ f ]

f =

S, g=

S

〉

[n]〈
S
⊆
X

=

n

S
3
X
k

S

f =

2
2

k

i k

Wk[ f ]

I[ f ]

Tρ( f =

S)

=

=

Stabρ[ f ]

=

·

k
0
=
X
(Tρ f )=
n

S

ρk

k
0
=
X

ρk f =

S

=
Wk[ f ].

·

8.19 Let f

L2(Ωn, π⊗

n) and let S

[n]. Show that

∈

⊆

S

f =

k

2|

S

|

f

.

k∞ ≤

k

k∞

8.20 Explicitly verify that Proposition 8.36 holds for the function in Exam-

ples 8.15 and 8.37.

8.21 Let f

L2(Ωn, π⊗

n) and let i

∈

S
its ith coordinate to have value ωi, forming the subfunction g
Show that g
2.

[n]. Suppose we take f =

S\{i}. In particular, E[g]
S
n) be a symmetric function. Show that if 1

0 assuming

| ≥

⊆

=

∈

|

S and restrict
( f =
ωi .

S)
|

=

S

n,

T

| ≤

| ≤ |

≤ |

g=
=
L2(Ωn, π⊗
S]
Var[ f ⊆

8.22 Let f

∈
then 1
S
|

|

1
T

|

|

≤

Var[ f ⊆

T ].

8.23 Prove the sharp threshold statement about the majority function made
in Example 8.49. (Hint: Chernoff bound.) In the social choice literature,
this fact is known as the Condorcet Jury Theorem.

8.24 Let p1, . . . , pn
tribution on {
Proposition 8.45 to the setting of L2({

(0, 1) and let π
∈
1, 1}n. Write µi
−

πp1 ⊗ · · ·
1
−

=
=

πpn be the associated product dis-
pi. Generalize
1

2ppi

2pi and σi

=
1, 1}n, π).

−

−

p

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 32 -->
238

8. Generalized domains

8.25 Let f : {

1, 1}n

R and consider the general product distribution setting

→
−
of Exercise 8.24.
(a) For S

{i1, . . . , i k}
=
Show that DφS =

show that

Q

DxS .
(b) Writing f (µ) for the function f viewed as an element of L2({

∈

·

[n], write DφS for Dφi1 ◦· · ·◦
S σi

⊆
i

Dφik

and similarly DxS .

1, 1}n, π),

−

f (p)(S)

=

σi

DxS f (µ1, . . . , µn).

·

(c) Show that ˆ
k

d
k∞ ≤
8.26 (a) Generalize Exercise 2.10 by showing that for f

f (p) ˆ

k∞

· k

∈

f

.

i

Q

S
i
∈
Y
S σi

L2({

1, 1}n, π⊗

n
p ) with

−

∈

range {

1, 1},

−

Pr
π⊗
p

x

∼
[n] and b

[i is b-pivotal for f on x]

n

πp(b)Infi[ f ]

=

∈

∈

{
−

for i

1, 1}.
(b) Generalize Proposition 4.7 by showing that if f : {
w, then I[ f (p)]
≤
4w.
4pw
≤
(0, 1). Let f : {True,False}n

DNFwidth( f )
then I[ f (p)]

4qw

≤

≤

≤

monotone function. Show that there exists p
True]

α. (Hint: Intermediate Value Theorem.)

∈

8.27 Fix any α

∈

=

8.28 Fix a small constant 0

1, 1}n

−

{
−

→

1, 1} has

4w, and if f has CNFwidth( f )

w,

≤

→

{True,False} be a nonconstant
(0, 1) such that Prπp [ f (x)

=

²

∈

−

−

=

=

<

<

→

²).

True]

c =
=

−
4pc(1
p1

(0, 1) such that Prπp [ f (x)

1/2. Let f : {True,False}n

p0 is the threshold width. Now let ( f n)n

{True,False}
be a nonconstant monotone function. Let p0 (respectively, pc, p1) be
the unique value of p
² (respec-
(This is a valid deﬁnition by Exercise 8.27.) Deﬁne
tively, 1/2, 1
also σ2
pc). The threshold interval for f is deﬁned to be [p0, p1],
and δ
N be a sequence
∈
of nonconstant monotone Boolean functions (usually “naturally related”,
with f n’s input length an increasing function of n). Deﬁne the sequences
p0(n), pc(n), p1(n), σ2
c(n), δ(n). We say that the family ( f n) has a sharp
threshold if δ(n)/σ2
; otherwise, we say it has a coarse
c(n)
→
threshold. (Note: If pc(n)
1/2 for all n, this is the same as saying that
0.) Show that if ( f n) has a coarse threshold, then there
δ(n)/pc(n)
→
n2
, an inﬁnite sequence n1
exists C
, and a sequence
< ∞
(p(ni))i
N such that:
∈
Prπp(ni )[ f ni (x)
²
<
I[ f (p(ni))
ni

C for all i.

² for all i;

True]

0 as n

→ ∞

< · · ·

n3

=

<

≤

<

<

−

1

•

]

•

≤

(Hint: Margulis–Russo and the Mean Value Theorem.)

1, 1}n

8.29 Let f : {
−
F : [0, 1]
→
Prπp [ f (x)
Assume that pc

= −

{
−

→

≤

1, 1} be a nonconstant monotone function and let

[0, 1] be the (strictly increasing) function deﬁned by F(p)
1]. Let pc be the critical probability such that F(pc)

=
1/2.
1/2. (This is without loss of generality since we can

=

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 33 -->
8.7. Exercises and notes

239

replace f by f †. We often think of pc
show a weak kind of threshold result: roughly speaking, F(p)
p
o(1) when p
=
(a) Using the Margulis–Russo Formula and the Poincaré Inequality show

1/2.) The goal of this exercise is to
o(1) when

o(pc) and F(p)

ω(pc).

¿

−

=

=

=

1

that for all 0

1,

p

<

<

F 0(p)

F(p)(1
p(1

≥

F(p))
p)

.

−
−

(b) Show that for all p

1
2p .

pc we have F 0(p)

≥

≤

F(p)

2p and hence d

d p ln F(p)

≥

(c) Deduce that for any 0

p0

≤

≤

pc we have F(p0)

1
2

≤

p0/pc; i.e., F(p0)

≤

p

² if p0

(2²)2 pc.

≤

constant τ
we used 1
proved bound 1

>
−

(d) Show that the factor (2²)2 can be improved to Θ(τ)²1
τ for any small
+
0. (Hint: The quadratic dependence on ² arose because
pc; but from part (c) we have the im-
F(p)

1/2 for p

≥
F(p)
(e) In the other direction, show that so long as p1

≤
τ once p

(2τ)2 pc.)

−

≥

−

≤

1

1

F(p1)
hold, show that we at least have F(1/2)

². (Hint: Work with ln(1

≥

−

−

1
(2²)2 pc
=
F(p)).) In case p1

1/2, we have
1/2 does not

≤
≤

1

≥

−

pc/2.

p

(f ) The bounds in part (e) are not very interesting when pc is close to 1/2.

1

−

≥

−

δ)

pδ/2 (even when pc

Show that we also have F(1

8.30 Consider the sequence of functions f n : {True,False}n

1/2).
{True,False} de-
ﬁned for odd n
Maj3(x1, x2, Majn
2(x3, . . . , xn)).
−
(a) Show that f n is monotone and has critical probability pc
=
(b) Sketch a plot of Prπp [ f n(x)
(c) Show that I[ f n]
(d) Show that the sequence f n has a coarse threshold as deﬁned in Exer-

True] versus p (assuming n very large).

3 as follows: f n(x1, . . . , xn)

Θ(pn).

1/2.

→

≥

=

=

=

=

cise 8.28 (assuming ²

1/4).

<

8.31 (a) Consider the following probability distributions on strings x

Fn
2 :

∈

∼

(1) First choose k

{0, 1, 2, . . . , n} uniformly. Then choose x uni-

formly from the set of all strings of Hamming weight k.

(2) First choose a uniformly random “path π from (0, 0, . . . , 0) up
to (1, 1, . . . , 1)”; i.e., let π be a uniformly random permutation
from Sn and let π≤
2 denote the string whose jth coordi-
{0, 1, 2, . . . , n}
nate is 1 if and only if π( j)
k.
uniformly and let x be the “kth string on the path”, namely π≤

i. Then choose k

Fn

≤

∼

∈

i

(3) First choose p

[0, 1]. Then choose x

∼

π⊗

n
p .

∼

Show that these are in fact the same distribution. (Hint: Imagine
choosing n
1 indistinguishable points uniformly from [0, 1] and then
randomly assigning them the labels “p”, 1, 2, . . . , n.)

+

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 34 -->
240

8. Generalized domains

(b) We denote by νn the distribution on F[n]
2

we use the notation νN for the distribution on FN
abstract set of cardinality n. Given a nonempty J
x
∈
xJ has the distribution νJ.

from part (a); more generally,
2 where N is an
[n], show that if
2 denotes the restriction of x to coordinates J, then

νn and xJ

FJ

∼

⊆

(c) Let f : Fn

R and ﬁx i

2 →

be

[n]. The ith Shapley value of f is deﬁned to

∈

[ f (x(i

1))

f (x(i

0))].

7→

=

Shapi[ f ]

E
νn
x
∼
n
1 Shapi[ f ]
Show that
i
=
(d) Suppose f : Fn
2 →

−
f (1, 1, . . . , 1)
{0, 1} is monotone. Show Shapi[ f ]

1
0 Infi[ f (p)] d p.
8.32 Explain how to generalize the deﬁnitions and results in Sections 8.1, 8.2
R
n). In particular,

to the case of the complex inner product space L2(Ωn, π⊗
verify the following formulas from Proposition 8.16:

f (0, 0, . . . , 0).

P

=

=

−

7→

4

E[ f ]
2]

f

|

E[
|

f (0)

f , f

E[
b
〈

]

〉

=

=

=

Var[ f ]

f

−

= 〈

E[ f ], f

−

α

〈

m

Nn
∈
X
<
E[ f ]

f (α),

f (α)

〉 =

b
〉 =

b
0 |
α
6=
X

2

f (α)
|

α

Nn
∈
X
<

f (α)

2

|

|

m

b

f , g

〈

〉 =

f (α),

g(α)

〈

α

m

Nn
∈
X
<
b
E[ f ], g
f

〉 =

α

Nn
∈
X
<

E[g]

b
−

〉 =

b
f (α)

g(α)

m

b
f (α)

b
g(α).

Cov[ f , g]

= 〈

−

0
α
6=
X

b

8.33 (a) As in Exercise 2.58, explain how to generalize the deﬁnitions and
V , where
→
V . Here the
is deﬁned
V ]. In particular, verify the formulas from

results in Sections 8.1, 8.2 to the case of functions f : Ωn
V is a real inner product space with inner product
f (α) will be elements of V , and
Fourier coefﬁcients
f (x), g(x)
to be Ex
〉
Proposition 8.16, including Placherel:

,
·〉
f , g

n [
〈

f , g

〈·
〈

f (α),

π⊗

b

b

∼

〉

g(α)
〉

V .

(b) For Σ a ﬁnite set we write

|

〈

0

∀

Σ

≥

P

4

| =

〉 =

b
m, we also identify
b
Rm : µ1

α〈
Σ for the set of all probability distributions
Σ with
µm

over Σ (cf. Exercise 7.22). Writing
the standard convex simplex in Rm, namely {µ
=
i} (where we assume some ﬁxed ordering of Σ). Finally,
1, µi
we identify the m elements of Σ with the constant distributions in
Σ; equivalently, the vertices of the form (0, . . . , 0, 1, 0, . . . , 0). Given a
Σ, often the most useful way to treat it analytically
Rm and then use the
Σ
→ 4
Rm. Using this idea, show that

4
function f : Ωn
is to interpret it as a function f : Ωn
setting described in part (a), with V
if f : Ωn

Σ and π is a distribution on Ω, then

4
+ · · · +

→

=

⊂

∈

→

Stabρ[ f ]

=

x

π⊗

∼

Pr
n,y
∼

[ f (x)

=

Nρ(x)

f (y)].

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 35 -->
8.7. Exercises and notes

241

(Here in Stabρ[ f ] we are interpreting f ’s range as
in the expression f (x)
set Σ.)

Rm, whereas
f (y) we are treating f ’s range as the abstract

4

=

⊂

Σ

8.34 We say a function f

expressible as f (x)
the sense of Deﬁnition 8.32).
(a) Given ω(

=

1)

L2(Ωn, π⊗

∈
sgn(`(x)), where ` : Ωn

n) is a linear threshold function if it is
R has degree at most 1 (in

→

−

∈
∈

Ωn and x
, . . . , ω(xn)
n )

{
−
Ωn. Show that if ω(
1, 1}n

1, 1}n, we introduce the notation ω(x)
1), ω(
+
∈
for the string (ω(x1)
n are
1)
−
1
1, 1}n is a ρ-correlated
drawn independently and (x, y)
{
−
∼
pair of binary strings, then (ω(x), ω(y)) is a ρ-correlated pair under
n.
π⊗
(b) Let f
ω(
∈
f (ω(x)). Show that gω(
“usual” sense.

Ωn, deﬁne gω(
1),ω(
=
+
1) is a linear threshold function in the
1),ω(
−
+

n) be a linear threshold function. Given a pair

L2(Ωn, π⊗
1)
−

1, 1} by gω(

∈
1), ω(
+

1), ω(
+

1)(x)
−

1, 1}n

1) : {
−

{
−

{
−

1),ω(
+

π⊗

→

×

∼

−

(c) Prove that Peres’s Theorem (from Chapter 5.5) applies to linear thresh-

old functions in L2(Ωn, π⊗

n), with the same bounds.

8.35 Let G be a ﬁnite abelian group. We know by the Fundamental Theorem
Zmn where each

of Finitely Generated Abelian Groups that G ∼=
m j is a prime power.
(a) Given α

G, deﬁne χα : G

C by

Zm1 × · · ·

∈

→
n

exp(2πiα j x j/m j).

χα(x)

=

j
1
=
Y

Show χα is a character of G and that the χα’s are distinct functions
for distinct α’s. Deduce that the set of all χα’s forms a Fourier basis
for L2(G).

(b) Show that this set of characters forms a group under multiplication
and that this group is isomorphic to G; i.e., generalize Fact 8.58. This
G. We also identify the
is called the dual group of G and it is written
characters in

G with their indices α.

8.36 Verify that the convolution operation on L2(G) is associative and commu-
g(α)
G. (See Exer-

g(α) for all α

f (α)

b

b

tative, and that it satisﬁes
cise 8.35 for the deﬁnition of

8.37 (a) Let f

∈

L2(Ωn, π⊗

n) be any transitive-symmetric function and let T
be a randomized decision tree computing f . Show that there exists
a randomized decision tree T 0 computing f with ∆(π)(T 0)
∆(π)(T )
and such that δ(π)
(T 0) is the same for all i
[n]. (Hint: Randomize
over the automorphism group Aut( f ) and use Exercise 2.47.)

=

∈

i

b

(b) Given a randomized decision tree T , let δ(π)(T )

(T )}.
n), deﬁne δ(π)( f ) to be the minimum value of

[n]{δ(π)
i
∈

maxi

=

Given f

∈

L2({

1, 1}n, π⊗

−

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.

f
∗
G.)
(cid:129)
b

=

b

∈

b



<!-- pdf-page: 36 -->
242

8. Generalized domains

δ(π)(T ) over all T which compute f ; this is called the revealment of f .
Show that if f is transitive-symmetric, then δ(π)( f )

∆(π)( f ).

8.38 (a) Show that DT(Maj⊗

d
3 )

3d, RDT(Maj⊗

d
3 )

≤

(5/2)d.

2
(b) Show that RDT(Maj⊗
3 )

bound?

=

<

(8/3)2. How small can you make your upper

1
n
(8/3)d, and ∆(Maj⊗

=

d
3 )

≤

8.39 (a) Show that for every deterministic decision tree T computing the logi-

cal OR function on n bits,

∆(p)(T)

p

1

·

+

(1

−

=

p)p

2

(1

·
p)n

+
2 p
−

(1

−

· · · +

p)2 p

3

·

+ · · ·

−

(n

·

−

1)

+

(1

−

p)n

1

−

n

·

=

1

−

(1
−
p

p)n

.

Deduce ∆(p)(ORn)
−
(b) Show that ∆(pc)(ORn)

=

1

(1
−
p

p)n

.

n/(2 ln 2) as n

critical probability for ORn.

∼

, where pc denotes the

→ ∞

8.40 Let NAND : {True,False}2

{True,False} be the function that outputs True

unless both its inputs are True.
(a) Show that for d even, NAND⊗

d

→

Tribes⊗

d/2
2,2 .

(Thus the recursive

=

NAND function is sometimes known as the AND-OR tree.)
2d.
2.

d)
(b) Show that DT(NAND⊗
(c) Show that RDT(NAND)
(d) For b

{True,False} and T a randomized decision tree computing
a function f , let RDTb(T ) denote the maximum cost of T among
b. Show that there is a randomized decision
inputs x with f (x)
tree T computing NAND with RDTFalse(T )

=
=

3/2.

=

∈

(e) Show that RDT(NAND⊗
3.
(f ) Show that there is a family of randomized decision trees (Td)d

≤

2)

with Td computing NAND⊗

d, satisfying the inequalities

+,

N

∈

=

RDTFalse(Td)
RDTTrue(Td)

≤

≤

2RDTTrue(Td
RDTFalse(Td

1)
−
1)
−

+

(1/2)RDTTrue(Td

1).
−

(g) Deduce RDT(NAND⊗

8.41 Let C

=

{monotone f : {

k}. Show that C is learn-
1, 1}
able from random examples with error ² in time nO(pk/²). (Hint: OS In-
equality and Corollary 3.32.)

DT( f )

→

−

≤

|

( 1
+

d)
≤
1, 1}n

p33
4
{
−

≈

)d

n.754, where n

2d.

=

8.42 Verify that the decision tree process described in Deﬁnition 8.70 indeed
n. (Hint: Induction on the

generates strings distributed according to π⊗
structure of the tree.)

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 37 -->
8.7. Exercises and notes

243

8.43 Let T be a deterministic decision tree of size s. Show that ∆(T)

log s.
(Hint: Let P be a random root-to-leaf path chosen as in the decision tree
process. How can you bound the entropy of the random variable P?)

≤

8.44 Let f

L2(Ωn, π⊗
(a) Show that MaxInf[ f ]

∈

n) be a nonconstant function with range {

1, 1}.

Var[ f ]/∆(π)( f ) (cf. the KKL Theorem from

−

≥

(b) In case Ω

Chapter 4.2).
{
−

=

1, 1} show that MaxInf[ f ]

Var[ f ]/ deg( f )3. (You should

use the result of Midrij ¯anis mentioned in the notes in Chapter 3.6.)

(c) Show that I[ f ]

Var[ f ]/δ(π)( f ), where δ(π)( f ) is the revealment of f ,

deﬁned in Exercise 8.37(b).

≥

≥

8.45 Let f

L2(Ωn, π⊗

n) have range {

1, 1}.

∈

(a) Let T be a randomized decision computing f and let i
(T ). (Hint: The decision tree process.)
(b) Suppose f is transitive-symmetric. Show that ∆(π)( f )

that Infi[ f ]

δ(π)
i

≤

−

(Hint: Exercise 8.37(b).) This result can be sharp up to an O(
factor even for an f : {
{
−

1, 1} with Var[ f ]

1, 1}n

→

=

−

p

[n]. Show

∈

≥

Var[ f ]

n.
·
log n)
1; see [BSW05].

p

=
L2(Ωn, π⊗

8.46 In this exercise you will give an alternate proof of the OSSS Inequality
1 and is weaker by only a factor of 2 when
1, 1}. Given a random-

that is sharp when Var[ f ]
Var[ f ] is small. Let f
ized decision tree T we write err(T )
(a) Let T be a depth-k deterministic decision tree (not necessarily com-
puting f ) whose root queries coordinate i. Let T be the distribution
over deterministic trees of depth at most k
1 given by following
a random outgoing edge from T’s root (according to π). Show that
err(T )

n) have range {
Prx

−
n [T (x)

err(T)

f (x)].

π⊗

6=

=

−

∈

∼

≤

1
2 Infi[ f ].

+

(b) Let T be a randomized decision tree of depth 0. Show that err(T )
1]}.

min{Pr[ f (x)

1], Pr[ f (x)

≥

(c) Prove by induction on depth that if T is any randomized decision tree,
err(T ).
−
1 and in

then 1
2
= −
Verify that this yields the OSSS Inequality when Var[ f ]
general yields the OSSS Inequality up to a factor of 2.

min{Pr[ f (x)

1], Pr[ f (x)

Infi[ f ]

(T )

1]}

P

n
i

≥

=

=

=

·

i

=
1 δ(π)

= −

8.47 Show that the OSSS Inequality fails for functions f : {

R. (Hint:
The simplest counterexample uses a decision tree with the shape in Fig-
ure 8.2.)

1, 1}n

→

−

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 38 -->
244

8. Generalized domains

Figure 8.2. The basis for a counterexample to the OSSS Inequality when
f : {

1, 1}n

R

−

→

Can you make the ratio of the left-hand side to the right-hand side

equal to 130
+
157

20p3

? Larger?

|

|

S

S

≤

≤

k

k

k

k

i k

S

2
2,

f ⊆

f =

<···<

n g(X i1, . . . , X i k ), where g : Rk

Notes. The origins of the orthogonal decomposition described in Section 8.3
date back to the work of Hoeffding [Hoe48] (see also von Mises [vM47]). Ho-
effding’s work introduced U-statistics, i.e., functions f of independent random
variables X 1, . . . , X n of the form avg1
i1
→
R is a symmetric function. Such functions are themselves symmetric. For
S (which, by symmetry, depends only
these functions, Hoeffding introduced f ⊆
) and proved certain inequalities (e.g., those in Exercise 8.22) relating
on
2
Var[ f ] to the quantities
2. Nonsymmetric functions f were
considered only rarely in the subsequent three decades of statistics research.
One notable exception comes in the work of Hájek [Háj68], who effectively
1, known as the Hájek projection of f . Also, a work of Bour-
introduced f ≤
k. The ﬁrst
gain [Bou79] essentially describes the decomposition f
work that mentions the general orthogonal decomposition for not-necessarily-
symmetric functions appears to be that of Efron and Stein [ES81] from the
late 1970s. Efron and Stein’s description is brief; the subsequent work of
Karlin and Rinott [KR82] gives a more thorough development. Efron and
I[ f ] for symmet-
Stein’s main result was a proof of the statement Var[ f ]
ric f ; in the statistics literature this is known as the Efron–Stein Inequality.
Steele [Ste86a] extended this to the case of nonsymmetric f by a simple proof
that used the Fourier basis approach to orthogonal decomposition. This ap-
proach via Fourier bases originated in the work of Rubin and Vitale [RV80];
see also Takemura [Tak83] and Vitale [Vit84]. The terminology “Fourier
basis” we use is not standard.

k f =

P

=

≤

The p-biased hypercube distribution is strongly motivated by the Erd˝os–
Rényi [ER59] theory of random graphs (see e.g., Bollobás and Riordan [BR08]
for history) and by percolation theory (introduced in Broadbent and Hammer-
sley [BH57]). Inﬂuences under the p-biased distribution – and their connec-
tion to threshold phenomena – were studied by Russo [Rus81, Rus82]. The
former work proved the Margulis–Russo formula independently of Margulis,

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 39 -->
8.7. Exercises and notes

245

who had proven it earlier [Mar74]. Fourier analysis under the p-biased distri-
bution seems to have been ﬁrst introduced to the theoretical computer science
literature by Furst, Jackson, and Smith [FJS91], who extended the LMN
learning algorithm for AC0 to this setting. Talagrand [Tal93, Tal94] devel-
oped p-biased Fourier for the study of threshold phenomena, strengthening
Margulis and Russo’s work and proving the KKL Theorem in the p-biased
setting. Similar results were obtained by Friedgut and Kalai [FK96] using
an earlier work of Bourgain, Kahn, Kalai, Linial, and Katznelson [BKK+92]
that proved a version of the KKL Theorem in the setting of general product
spaces. The statements about sharp thresholds for cliques and connectivity
in Example 8.49 are essentially due to Matula and to Erd˝os–Rényi, respec-
tively; see, e.g., Bollobás [Bol01]. Weak threshold results similar to the ones
in Exercise 8.29 were proved by Bollobás and Thomason [BT87], using the
Kruskal–Katona Theorem rather than the Poincaré Inequality.

Fourier analysis on ﬁnite abelian groups – and more generally, on locally
compact abelian groups – is an enormous subject upon which we have touched
only brieﬂy. We cannot survey it here but refer instead to the standard text-
book of Rudin [Rud62] and to the reader-friendly textbook of Terras [Ter99],
which focuses on ﬁnite groups.

1, 1}n

One of the earliest works on randomized decision tree complexity is that
of Saks and Wigderson [SW86]; they proved the contents of Exercise 8.40.
(We note that RDT( f ) is usually denoted R( f ) in the literature, and DT( f ) is
usually denoted D( f ).) One basic lower bound in the area is that RDT( f )

DT( f ) for any f : {

≥
1, 1}; in fact, this lower bound holds even
for “nondeterministic decision tree complexity”, as proved in [BI87, Tar89].
p
Yao’s Conjecture is also sometimes attributed to Richard Karp. Regarding
the recursive majority-of-3 function, Ravi Boppana was the ﬁrst to point out
3d. Saks and Wigderson
that RDT(Maj⊗
(8/3)d and also that it is not optimal. Fol-
noted the bound RDT(Maj⊗
lowing subsequent works [JKS03, She08] the best known upper bound is
O(2.65d) [MNSX11] and the best known lower bound is Ω(2.55d) [Leo12].

o(3d) even though DT(Maj⊗

d
3 )

d
3 )

d
3 )

{
−

→

−

=

=

≤

The proof of the OSSS Inequality we presented is essentially Lee’s [Lee10];
the alternate proof from Exercise 8.46 is due to Jain and Zhang [JZ11].
The Condorcet Jury Theorem (see Exercise 8.23) is from [dC85]. The Shap-
ley value described in Exercise 8.31 was introduced by the Nobelist Shap-
ley [Sha53]; for more, see Roth [Rot88]. Exercise 8.34 is from Blais, O’Donnell,
and Wimmer [BOW10]. Exercises 8.37(a) and 8.45 are from the work of
Benjamini, Schramm, and Wilson [BSW05]; the term “revealment” was intro-
duced by Schramm and Steif [SS10]. Exercise 8.47 is from [OSSS05]. Related
to this, it is extremely interesting to ask whether something like the result of

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 40 -->
246

8. Generalized domains

Exercise 8.44(b) holds for functions f : {
that the answer is yes:

−

1, 1}n

[

→

1, 1]. It has been suggested

−

Aaronson–Ambainis Conjecture. [Aar08, AA11] Let f : {
Then MaxInf[ f ]

poly(Var[ f ]/ deg( f )).

−

1, 1}n

[

→

1, 1].

−

≥

If true, this conjecture would have signiﬁcant consequences for the limitations
of efﬁcient quantum computation; see Aaronson and Ambainis [AA11]. The
best result in the direction of the conjecture, due to Dinur et al. [DFKO07], is
the lower bound MaxInf[ f ]

poly(Var[ f ]/2deg( f )).

≥

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.


