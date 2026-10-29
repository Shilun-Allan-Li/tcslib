<!-- generated-by: proofmatch local extraction -->
<!-- source-pdf-sha256: 8b2c50cf9621a397e8a43be5883167d7a1f33b2bb96f0683b7b0709539ec807f -->
<!-- extractor: pdfminer.six v20260107 -->

<!-- pdf-page: 1 -->
Chapter 11

Gaussian space and
Invariance Principles

The ﬁnal destination of this chapter is a proof of the following theorem due to
Mossel, O’Donnell, and Oleszkiewicz [MOO05b, MOO10], ﬁrst mentioned in
Chapter 5.2:

Majority Is Stablest Theorem. Fix ρ
E[ f ]
0. Then, assuming MaxInf[ f ]
(≤, ≤)-notable coordinates,



1, 1}n
(0, 1). Let f : {
1, 1] have

≤, or more generally that f has no
≤

→

−

−

[

Stabρ[ f ]

1

−

≤

2
π arccos ρ

o≤(1).

+

Majn, the volume- 1

2
π arccos ρ is achieved
This bound is tight; recalling Theorem 2.45, the bound 1
by taking f
. More
generally, in Section 11.7 we’ll prove the General-Volume Majority Is Stablest
Theorem, which shows that for any ﬁxed volume, “Hamming ball indicators
have maximal noise stability among small-inﬂuence functions”.

2 Hamming ball indicator, for n

→ ∞

−



There are two main ideas underlying this theorem. The ﬁrst is that “func-
tions on Gaussian space” are a special case of small-inﬂuence Boolean func-
tions. In other words, a Boolean function may always be a “Gaussian function
in disguise”. This motivates analysis of Gaussian functions, the topic intro-
duced in Sections 11.1 and 11.2. It also means that a prerequisite for proving
the (General-Volume) Majority Is Stablest Theorem is proving its Gaussian
special cases, namely, Borell’s Isoperimetric Theorem (Section 11.3) and the
Gaussian Isoperimetric Inequality (Section 11.4). In many ways, working
in the Gaussian setting is nicer because tools like rotational symmetry and
differentiation are available.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.

327



<!-- pdf-page: 2 -->
328

11. Gaussian space and Invariance Principles

The second idea is the converse to the ﬁrst: In Section 11.6 we prove the
Invariance Principle, a generalization of the Berry–Esseen Central Limit The-
orem, which shows that any low-degree (or uniformly noise-stable) Boolean
function with small inﬂuences is approximable by a Gaussian function. In
fact, the Invariance Principle roughly shows that given such a Boolean func-
tion, if you plug any independent mean-0, variance-1 random variables into
its Fourier expansion, the distribution doesn’t change much. In Section 11.7
we use the Invariance Principle to prove the Majority Is Stablest Theorem by
reducing to its Gaussian special case, Borell’s Isoperimetric Theorem.

11.1. Gaussian space and the Gaussian noise operator

We begin with a few deﬁnitions concerning Gaussian space.

1

1

−







Φ(

exp(

−
Φ(t)

Notation 11.1. Throughout this chapter we write ϕ for the pdf of a standard
1
2 z2). We also write Φ for its cdf,
Gaussian random variable, ϕ(z)
p2π
N(0, 1)n
and Φ for the complementary cdf Φ(t)
t). We write z

(z1, . . . , zn) is a random vector in n whose components zi
to denote that z
are independent Gaussians. Perhaps the most important property of this
distribution is that it’s rotationally symmetric; this follows because the pdf
2
2 of z.
at z is

z2
n)), which depends only on the length

‖
n, γ) for the space
Deﬁnition 11.2. For n
p
of Borel functions f :
p under the
Gaussian measure (the “γ” stands for Gaussian). Here for a function f on
Gaussian space we use the notation

that have ﬁnite pth moment

we write L p(

(2π)n/2 exp(

1 + · · · +

+ and 1

2 (z2

≤ ∞

→


n

≤

−

−

∼

p

‖

‖

‖

z

f

1

1

All functions f :
without further mention.

→

n

E
N(0,1)n

f

‖

‖p 

z

∼
and sets A

⊆

[

f (z)

p]1/p.

|

|
n are henceforth assumed to be Borel

Notation 11.3. When it’s clear from context that f is a function on Gaussian
space we’ll use shorthand notation like E[ f ]
1A is the
0-1 indicator of a subset A

Ez
n we’ll also write

N(0,1)n [ f (z)]. If f





∼

⊆

volγ(A)

E[1A]



Pr
N(0,1)n

[z



A]



z

∼

for the Gaussian volume of A.

Notation 11.4. For f , g
E[ f g], under which L2(

n, γ) we use the inner product notation

L2(

n, γ) is a separable Hilbert space.

〈

f , g

〉 

If you’re only interested in Boolean functions f : {

1, 1} you
might wonder why it’s necessary to study Gaussian space. As discussed at the
beginning of the chapter, the reason is that functions on Gaussian space are

→

−

−

{

1, 1}n

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 3 -->
11.1. Gaussian space and the Gaussian noise operator

329

special cases of Boolean functions. Conversely, even if you’re only interested
in studying functions of Gaussian random variables, sometimes the easiest
proof technique involves “simulating” the Gaussians using sums of random
bits. Let’s discuss this in a little more detail. Recall that the Central Limit
xM)
Theorem tells us that for x
. This is the sense in
approaches that of a standard Gaussian as M
→ ∞
which a standard Gaussian random variable z
N(0, 1) can be “simulated” by
random bits. If we want d independent Gaussians we can simulate them by
summing up M independent d-dimensional vectors of random bits.

1, 1}M, the distribution of

(x1 + · · · +

1
pM

{
−

∼

∼

Deﬁnition 11.5. The function BitsToGaussiansM : {
by

−

1, 1}M

→

is deﬁned

BitsToGaussiansM(x)

More generally, the function BitsToGaussiansd
an input x

1, 1}d, by
{

(x1 + · · · +
d is deﬁned on
M : {
−
M, thought of as a matrix of column vectors ~x1, . . . ,~xM 

1, 1}dM

1, 1}d

xM).

→

−



×

{

1
pM

BitsToGaussiansd

M(x)

1
pM



(~x1 + · · · +

~xM).

Although M needs to be large for this simulation to be accurate, many of

1, 1}M

−

→

1, 1}dM

the results we’ve developed in the analysis of Boolean functions f : {

→
are independent of M. A further key point is that this simulation preserves
polynomial degree: if p(z1, . . . , zd) is a degree-k polynomial applied to d inde-
pendent standard Gaussians, the “simulated version” p
M :
is a degree-k Boolean function. These facts allow us to transfer
{
−
many results from the analysis of Boolean functions to the analysis of Gauss-
ian functions. On the other hand, it also means that to fully understand
Boolean functions, we need to understand the “special case” of functions on
Gaussian space: a Boolean function may essentially be a function on Gaussian
space “in disguise”. For example, as we saw in Chapter 5.3, there is a sense in
; what it’s converging
which the majority function Majn “converges” as n
to is the sign function on 1-dimensional Gaussian space, sgn

BitsToGaussiansd

→ ∞

, γ).

L1(

◦

−

We’ll begin our study of Gaussian functions by developing the analogue
of the most important operator on Boolean functions, namely the noise oper-
ator Tρ. Suppose we take a pair of ρ-correlated M-bit strings (x, x′) and use
them to form approximate Gaussians,



y

BitsToGaussiansM(x),

y′

BitsToGaussiansM(x′).




1,
For each M it’s easy to compute that E[y]

ρ. As noted in Chapter 5.2, a multidimensional version of the
and E[yy′]
Central Limit Theorem (see, e.g., Exercises 5.33, 11.46) tells us that the joint
distribution of (y, y′) converges to a pair of Gaussian random variables with
the same properties. We call these ρ-correlated Gaussians.

0, Var[y]

Var[y′]

E[y′]









Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 4 -->
330

11. Gaussian space and Invariance Principles

Deﬁnition 11.6. For
1, we say that the random variables (z, z′) are
ρ-correlated (standard) Gaussians if they are jointly Gaussian and satisfy
E[z]

ρ. In other words, if

1, and E[zz′]

0, Var[z]

Var[z′]

E[z′]

≤

−

≤

1

ρ











(z, z′)

N

∼

0
0

[

,

]

1 ρ
ρ 1

[

.

]

Note that the deﬁnition is symmetric in z, z′ and that each is individually
distributed as N(0, 1).

N(0, 1)d and ~u,~v

Fact 11.7. An equivalent deﬁnition is to say that z
where ~g
In particular we may choose d
ρ g1 +
deﬁning z

2, ~u

ρ2 g2.

g1 and z′

(1, 0), and ~v


1

∼





−



~u,~g

and z′

 〈

〉

~v,~g

,
〉
 〈
~u,~v
ρ.
〈
ρ2), thereby

〉 

(ρ,



1

−



d are any two unit vectors satisfying



Remark 11.8. In Fact 11.7 it’s often convenient to write ρ
θ

and z′
~v

, in which case we may deﬁne the ρ-correlated Gaussians as z
for any unit vectors ~u,~v making an angle of θ; e.g., ~u

cos θ for some
~u,~g
〉
(1, 0),

(cos θ, sin θ).

 〈


~v,~g

 〈



〉



Deﬁnition 11.9. For a ﬁxed z
ρ-correlated to z, written z′
g
obtain a ρ-correlated pair of Gaussians (z, z′).

N(0, 1). By Fact 11.7, if we draw z

Nρ(z), if z′ is distributed as ρz

we say random variable z′ is a Gaussian
ρ2 g where
Nρ(z), we

1
N(0, 1) and then form z′

−
∼



∼

∼

+

∼



ρ

1

≤

≤

−

n-valued
Deﬁnition 11.10. For
1 and n
random variables (z, z′) are ρ-correlated n-dimensional Gaussian random
vectors if each component pair (z1, z′1), . . . , (zn, z′n) is a ρ-correlated pair of
Gaussians, and the n pairs are mutually independent. We also naturally
extend the deﬁnition of z′
ρ2 g for g
ρz

Nρ(z) to the case of z

n; this means z′

+ we say that the

∼
N(0, 1)n.







1

+

−

∼



Nρ(z) we obtain a ρ-
Remark 11.11. Thus, if z
correlated n-dimensional pair (z, z′). It follows from this that (z, z′) has the
same distribution as (Q z,Q z′) for any rotation Q on n.

N(0, 1)n and then z′

∼

∼

Now we can introduce the Gaussian analogue of the noise operator.

Deﬁnition 11.12. For ρ
operator deﬁned on the space of functions f

−



[

1, 1], the Gaussian noise operator Uρ is the linear

L1(

n, γ) by



Uρ f (z)



E
Nρ(z)

z′∼

[ f (z′)]



g

∼

E
N(0,1)n

[ f (ρz

ρ2 g)].

1

−

+



Fact 11.13. (Exercise 11.3.) If f
nomial, then Uρ f (z)

f (ρz).



L1(

n, γ) is an n-variate multilinear poly-



Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 5 -->
11.1. Gaussian space and the Gaussian noise operator

331

Remark 11.14. Our terminology is nonstandard. The Gaussian noise op-
erators are usually collectively referred to as the Ornstein–Uhlenbeck semi-
group (or sometimes as the Mehler transforms). They are typically deﬁned for
ρ

[0, 1] (i.e., for t

]) by

[0,

e−

t





Pt f (z)

[ f (e−

t z

1

e−

2t g)]

Ue−

t f (z).

g



+
The term “semigroup” refers to the fact that the operators satisfy Pt1Pt2 
1, 1]; see Exer-
Pt1+
cise 11.4).

Uρ1ρ2 (which holds for all ρ1, ρ2 

t2, i.e., Uρ1Uρ2 



−



−

∼

[



∞

E
N(0,1)n

Before going further let’s check that Uρ is a bounded operator on all of
1; in fact, it’s a contraction (cf. Exercise 2.33):

n, γ) for p

L p(

≥
Proposition 11.15. For each ρ
contraction on L p(

n, γ); i.e.,

[

Uρ f

1, 1] and 1
‖p.
f

−
‖p ≤ ‖

‖

p

≤

≤ ∞

the operator Uρ is a

Proof. The proof for p
inequality, using that t

 ∞
t
7→ |

|

is easy; otherwise, the result follows from Jensen’s
p is convex:

Uρ f

‖

p
p 

‖

z

∼

E
N(0,1)n

[

|

Uρ f (z)

p]

|

E
N(0,1)n



z

∼

E
N(0,1)n

≤

z

∼

z′∼

[∣
∣
∣
∣
z′∼
[

p

[ f (z′)]

E
Nρ(z)

[

E
Nρ(z)

|

f (z′)

]

∣
∣
∣
p]
∣

]

|

p
p.

f

‖

 ‖



As in the Boolean case, you should think of the Gaussian noise operator
as having a “smoothing” effect on functions. As ρ goes from 1 down to 0,
Uρ f involves averaging f ’s values over larger and larger neighborhoods. In
E[ f ], the constant
particular U1 is the identity operator, U1 f
function. In Exercises 11.5, 11.6 you are asked to verify the following facts,
which say that for any f , as ρ
1− we get a sequence of smooth (i.e., C ∞)
functions Uρ f that tend to f .

f , and U0 f

→





Proposition 11.16. Let f
smooth function.



L1(

n, γ) and let

1

−



ρ



1. Then Uρ f is a

Proposition 11.17. Let f

L1(

n, γ). As ρ



1− we have

Uρ f

‖

f

−

‖1 →

0.

→

Having deﬁned the Gaussian noise operator, we can also make the natural
deﬁnition of Gaussian noise stability (for which we’ll use the same notation
as in the Boolean case):

Deﬁnition 11.18. For f

ity of f at ρ is deﬁned to be

L2(

n, γ) and ρ

[

−



1, 1], the Gaussian noise stabil-

Stabρ[ f ]



E
(z,z′) n-dimensional
ρ-correlated Gaussians

[ f (z) f (z′)]

f , Uρ f

Uρ f , f

.

〉

〉  〈

 〈

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 6 -->
332

11. Gaussian space and Invariance Principles

(Here we used that (z′, z) has the same distribution as (z, z′) and hence Uρ is
self-adjoint.)

Example 11.19. Let f :
,0]. Then
1(
halﬂine: f



−∞

Stabρ[ f ]



E
(z,z′) ρ-correlated
standard Gaussians

{0, 1} be the 0-1 indicator of the nonpositive

→

[ f (z) f (z′)]

Pr[z

0, z′

0]

≤



≤



1
2 −

1
2

arccos ρ
π

,

(11.1)
with the last equality being Sheppard’s Formula, which we stated in Sec-
tion 5.2 and now prove.

Proof of Sheppard’s Formula. Since (
as (z, z′), proving (11.1) is equivalent to proving

z,

−

−

z′) has the same distribution

Pr[z

0, z′

≤

≤

0 or z

0, z′

0]

1

−







arccos ρ
π

.

The complement of the above event is the event that f (z)
sure 0); thus it’s further equivalent to prove

6

f (z′) (up to mea-

Pr
(z,z′)
cos θ-correlated

[ f (z)

6

f (z′)]

θ
π



(11.2)

[0, π]. As in Remark 11.8, this suggests deﬁning z

~v,~g
,
〉
2 is some ﬁxed pair of unit vectors making an angle of θ, and

~u,~g

, z′

 〈

 〈

〉

for all θ

where ~u,~v
~g

∼



N(0, 1)2. Thus we want to show

Pr
N(0,1)2

[

~u,~g
〈

〉 ≤

0 &

~v,~g
〈

〉 

0 or vice versa]

θ
π .



~g

∼

But this last identity is easy: If we look at the diameter of the unit circle that
is perpendicular to ~g, then the event above is equivalent (up to measure 0)
to the event that this diameter “splits” ~u and ~v. By the rotational symmetry
of ~g, the probability is evidently θ (the angle between ~u,~v) divided by π (the
range of angles for the diameter).


Corollary 11.20. Let H
hyperplane containing the origin. Let h

n be any halfspace (open or closed) with boundary
2
π arccos ρ.
1H. Then Stabρ[h]

⊂

1

 ±



−

Proof. We may assume H is open (since its boundary has measure 0). By
the rotational symmetry of correlated Gaussians (Remark 11.11), we may
n : z1 
0}. Then it’s clear that the noise
rotate H to the form H
stability of h
1. Thus
,0] as in Example 11.19. Now if (z, z′) denote
sgn
h
−∞
ρ-correlated standard Gaussians, it follows from (11.1) that

1H doesn’t depend on n, i.e., we may assume n

 ±
2 f , where f

1(

{z







−







1

Stabρ[h]



E[h(z)h(z′)]





1

−

E[(1

2 f (z))(1

2 f (z′))]

−
4 E[ f ]

−
4Stabρ[ f ]

+

1

−



2
π arccos ρ.



Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 7 -->
11.1. Gaussian space and the Gaussian noise operator

333

2
π arccos ρ is also precisely the
Remark 11.21. The quantity Stabρ[sgn]
limiting noise stability of Majn, as stated in Theorem 2.45 and justiﬁed in
Chapter 5.2.

−



1

We’ve deﬁned the key Gaussian noise operator Uρ and seen (Proposi-
n, γ). Is it also hypercontractive?
tion 11.15) that it’s a contraction on all L p(
1
In fact, we’ll now show that the Hypercontractivity Theorem for uniform
bits holds identically in the Gaussian setting. The proof is simply a reduction
to the Boolean case, and it will use the following standard fact (see Jan-
son [Jan97, Theorem 2.6] or Teuwen [Teu12, Section 1.3] for the proof in
case of L2; to extend to other L p you can use Exercise 11.1):

±

Theorem 11.22. For each n
n, γ) for all 1
in L p(


.
 ∞
Gaussian Hypercontractivity Theorem. Let f , g
and assume 0

1. Then

prs

≤

p

ρ

+, the set of multivariate polynomials is dense

L1(

n, γ), let r, s

0,

≥



≤

≤
Uρ f , g

≤

f , Uρ g

〈

〉  〈

〉 

E
(z,z′) ρ-correlated
n-dimensional Gaussians

[ f (z)g(z′)]

f

‖1

+

r‖

g

‖1

+

s.

≤ ‖

+





r(

L1

L2(

n, γ) and g

Proof. (We give a sketch; you are asked to ﬁll in the details in Exercise 11.2.)
L1
n, γ). We may also assume
We may assume that f

n, γ) by a truncation and monotone convergence argument; thus the
f , g
left-hand side is ﬁnite by Cauchy–Schwarz. Finally, we may assume that f
and g are multivariate polynomials, using Theorem 11.22. For ﬁxed M
+ we consider “simulating” (z, z′) using bits. More speciﬁcally, let (x, x′)
1, 1}nM
−
n-valued random variables y, y′ by



1, 1}nM be a pair ρ-correlated random strings and deﬁne the joint

s(

×

−

+

{

{

BitsToGaussiansn

M(x),

y



BitsToGaussiansn

M(x′).

y′



By a multidimensional Central Limit Theorem we have that

E[ f (y)g(y′)]

M
→∞
−−−−→

E
(z,z′)
ρ-correlated

[ f (z)g(z′)].

(Since f and g are polynomials, we can even reduce to a Central Limit Theo-
rem for bivariate monomials.) We further have

f (y)

E[

|

|

1

r]1/(1

+

+

r) M

→∞
−−−−→

E
N(0,1)n

[

|

f (z)

|

z

∼

1

r]1/(1

+

+

r)

and similarly for g. (This can also be proven by the multidimensional Central
Limit Theorem, or by the one-dimensional Central Limit Theorem together
with some tricks.) Thus it sufﬁces to show

E[ f (y)g(y′)]

E[

|

≤

f (y)

|

1

r]1/(1

+

r) E[

+

1

s]1/(1

+

+

s)

g(y′)

|

|

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 8 -->
334

11. Gaussian space and Invariance Principles

for any ﬁxed M. But we can express f (y)
F,G : {
→
Hypercontractivity Theorem (for

G(x′) for some
and so the above inequality holds by the Two-Function


F(x) and g(y′)

1, 1}nM

1 bits).

−





±

An immediate corollary, using the proof of Proposition 10.4, is the stan-

dard one-function form of hypercontractivity:

Theorem 11.23. Let 1

for 0

ρ

≤

≤

p
q

1
1 .
−
−



q

p

≤

≤

≤ ∞

and let f



L p(

n, γ). Then

Uρ f

‖

‖q ≤ ‖

f

‖p

We conclude this section by discussing the Gaussian space analogue of
the discrete Laplacian operator. Taking our cue from Exercise 2.18 we make
the following deﬁnition:

Deﬁnition 11.24. The Ornstein–Uhlenbeck operator L (also called the in-
ﬁnitesimal generator of the Ornstein–Uhlenbeck semigroup, or the number
operator) is the linear operator acting on functions f

n, γ) by

L2(



L f



(provided L f exists in L2(
L.
this as the deﬁnition of

−

d
dρ

Uρ f

d
dt

Ue−

t f

t

0

ρ

1  −




∣
∣
n, γ)). Notational warning: It is common to see
∣

∣
∣
∣

Remark 11.25. We will not be completely careful about the domain of the
operator L in this section; for precise details, see Exercise 11.18.

L2(
Proposition 11.26. Let f
assume for simplicity that f is C 3. Then we have the formula

n, γ) be in the domain of L, and further



L f (x)

x



· 

f (x)

−

∆ f (x),

where ∆ denotes the usual Laplacian differential operator,
product, and

denotes the gradient.



denotes the dot

·

Proof. We give the proof in the case n
cise 11.7. We have



1, leaving the general case to Exer-

L f (x)

 −

lim
0+
t
→

N(0,1)[ f (e−

t x

Ez

∼

+

p1
t

−

e−

2t z)]

f (x)

.

−

(11.3)

Applying Taylor’s theorem to f we have

f (e−

t x

+

e−

2t z)

1

−

≈

f (e−

t x)

+

f ′(e−

t x)

e−

2t z

1

−

+

1
2 f ′′(e−

t x)(1

−

e−

2t)z2,

denotes that the two quantities differ by at most C(1
where the
|
in absolute value, for some constant C depending on f and x. Substituting

e−

−

z

|

2t)3/2

3


≈



Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 9 -->
11.1. Gaussian space and the Gaussian noise operator

335

this into (11.3) and using E[z]
constant, we get



0, E[z2]

L f (x)

 −

0+ 

lim
t
→
2t)3/2

using the fact that (1
claimed.

−

e−
t

1, and that E[

z

|

|

3] is an absolute

1
2 f ′′(e−

e−

2t)

t x)(1
t

−

,





+

f (e−

t x)
t

−

f (x)

0. But this is easily seen to be x f ′(x)

→

−

f ′′(x), as


An easy consequence of the semigroup property is the following:

Proposition 11.27. The following equivalent identities hold:

d
dρ
d
dt

Uρ f



ρ−

1LUρ f



ρ−

1UρL f ,

Ue−

t f

 −

LUe−

t f

 −

Ue−

t L f .

Proof. This follows from

Ue−

t

−

Ue−

t f (x)

d
dt

Ue−

t f (x)





lim
δ
0
→

lim
δ
0
→

δ f (x)
−
δ
t f (x)
δ

Ue−

δUe−

Ue−

t f (x)

−

Ue−

t Ue−

δ f (x)
δ

−

Ue−

t f (x)

. 



lim
δ
0
→

We also have the following formula:

Proposition 11.28. Let f , g
assume for simplicity that they are C 3. Then



L2(

n, γ) be in the domain of L, and further

f , Lg

〈

〉  〈

L f , g

〉  〈

f ,

g

.

〉



(11.4)

Proof. It sufﬁces to prove the inequality on the right of (11.4). We again
1, leaving the general case to Exercise 11.8. Using
treat only the case of n
Proposition 11.26,



L f , g

〈

〉 







∫

∫

∫

∫

(x f ′(x)

−

f ′′(x))g(x)ϕ(x) dx

x f ′(x)g(x)ϕ(x) dx

x f ′(x)g(x)ϕ(x) dx

+

∫

+

∫

f ′(x)g′(x)ϕ(x) dx,

f ′(x)(gϕ)′(x) dx

(integration by parts)

f ′(x)(g′(x)ϕ(x)

g(x)ϕ′(x)) dx

+

using the fact that ϕ′(x)

xϕ(x).

 −



Finally, by differentiating the Gaussian Hypercontractivity Inequality we
obtain the Gaussian Log-Sobolev Inequality (see Exercise 10.23; the proof is
the same as in the Boolean case):

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 10 -->
336

11. Gaussian space and Invariance Principles

Gaussian Log-Sobolev Inequality. Let f
Then



L2(

n, γ) be in the domain of L.

1

2 Ent[ f 2]

E[

f

‖

‖

≤

2].

It’s tempting to use the notation I[ f ] for E[
be careful because this quantity is not equal to
multilinear polynomial. See Exercise 11.13.

2]; however, you have to
f
‖
1 E[Varzi [ f ]] unless f is a

‖
n
i





11.2. Hermite polynomials

Having deﬁned the basic operators of importance for functions on Gaussian
space, it’s useful to also develop the analogue of the Fourier expansion. To
do this we’ll proceed as in Chapter 8.1, looking for a complete orthonormal
, γ), which we can extend to L2(
“Fourier basis” for L2(
n, γ) by taking prod-
ucts. It’s natural to start with polynomials; by Theorem 11.22 we know that
the collection ( j) j
, γ). To get an
orthonormal (“Fourier”) basis we can simply perform the Gram–Schmidt pro-
(with “h” standing for “Hermite”), we
cess. Calling the resulting basis (h j) j
get

z j is a complete basis for L2(

,  j(z)







h0(z)



1, h1(z)



z, h2(z)

1

z2
−
p2



, h3(z)



z3

3z

−
p6

,

. . .

(11.5)

Here, e.g., we obtained h3(z) in two steps. First, we made 3(z)
nal to h0, . . . , h2 as



z3 orthogo-

z3

z3, 1

1

〉 ·

− 〈

z3, z

z

〉 ·

− 〈

z3, z2

1
−
p2 〉 ·

z2
1
−
p2 

z3

−

− 〈

3z,

where z

∼

N(0, 1) and we used the fact that z3 and z3

z2
1
−
p2

·

and hence have Gaussian expectation 0. Then we deﬁned h3(z)
determining that E[(z3

3z)2]

6.

are odd functions
z3

3z

after

−
p6



−



Let’s develop a more explicit deﬁnition of these Hermite polynomials. The
computations involved in the Gram–Schmidt process require knowledge of
the moments of a Gaussian random variable z
N(0, 1). It’s most convenient
to understand these moments through the moment generating function of z,
namely

∼

E[exp(tz)]

1
p2π



∫

etz e−

1

2 z2

dz

e

1

2 t2 1
p2π



∫

1
2 (z

−

t)2

e−

dz

exp( 1

2 t2).



(11.6)

In light of our interest in the Uρ operators, and the fact that orthonormality
involves pairs of basis functions, we’ll in fact study the moment generating
function of a pair (z, z′) of ρ-correlated standard Gaussians. To compute it,

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 11 -->
11.2. Hermite polynomials

337

assume (z, z′) are generated as in Fact 11.7 with ~u,~v unit vectors in 2. Then

E
(z,z′)
ρ-correlated

[exp(sz

tz′)]

+











E
N(0,1)
g1,g2∼
independent

[exp(s(u1 g1 +

u2 g2)

t(v1 g1 +

+

v2 g2))]

E
N(0,1)

[exp((su1 +

tv1)g1)]

[exp((su2 +

tv2)g2)]

tv1)2) exp( 1

g1∼
exp( 1
2 (su1 +
2s2
2
exp( 1
~u
2 ‖
+ 〈
‖
2 (s2
exp( 1
2ρst

+

~u,~v

st
〉
t2)),

+

E
N(0,1)
tv2)2)
2t2)
2

g2∼
2 (su2 +
1
~v
2 ‖

‖

+

where the third equality used (11.6). Dividing by exp( 1

2 (s2

t2)) it follows that

+

E
(z,z′)
ρ-correlated

[exp(sz

1

2 s2) exp(tz′

1

2 t2)]



−

−

exp(ρst)

ρ j
j!

∞

0
j

∑



s j t j.

(11.7)

2 t2)
Inside the expectation above we essentially have the expression exp(tz
appearing twice. It’s easy to see that if we take the power series in t for
this expression, the coefﬁcient on t j will be a polynomial in z with leading
term 1

j! z j. Let’s therefore write

−

1

exp(tz

1

2 t2)



−

H j(z)t j,

1
j!

∞

0
j

∑

(11.8)

where H j(z) is a monic polynomial of degree j. Now substituting this into (11.7)
yields

1
j!k!

∞

0

j,k

∑

E
(z,z′)
ρ-correlated

[H j(z)Hk(z′)]s j tk

ρ j
j!

∞

0
j

∑



s j t j.

Equating coefﬁcients, it follows that we must have

[H j(z)Hk(z′)]

E
(z,z′)
ρ-correlated

j!ρ j
0

 

if j

if j

k,

k.



6

In particular (taking ρ

1),



j!

if j

k,



〈

0

if j

H j, Hk〉  
are orthogonal. Furthermore, since H j is monic
i.e., the polynomials (H j) j
and of degree j, it follows that the H j’s are precisely the polynomials that
arise in the Gram–Schmidt orthogonalization of {1, z, z2, . . . }. We also see
from (11.9) that the orthonormalized polynomials (h j) j
are obtained by
setting h j 

(11.9)

1
p j!

H j.

k;

6





Let’s summarize and introduce the terminology for what we’ve deduced.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 12 -->
338

11. Gaussian space and Invariance Principles

Deﬁnition 11.29. The probabilists’ Hermite polynomials (H j) j
are the uni-
variate polynomials deﬁned by the identity (11.8). An equivalent deﬁnition
(Exercise 11.9) is



H j(z)



1) j
(
−
ϕ(z) ·

d j
dz j

ϕ(z).

(11.10)

The normalized Hermite polynomials (h j) j

are deﬁned by h j 



1
p j!

H j; the

ﬁrst four are given explicitly in (11.5). For brevity we’ll simply refer to the
h j’s as the “Hermite polynomials”, though this is not standard terminology.

Proposition 11.30. The Hermite polynomials (h j) j
thonormal basis for L2(



, γ). They are also a “Fourier basis”, since h0 

1.

form a complete or-

Proposition 11.31. For any ρ

1, 1] we have

[

−



E
(z,z′)
ρ-correlated

[h j(z)hk(z′)]

h j, Uρ hk〉  〈

 〈

Uρ h j, hk〉  

ρ j

0

if j

if j

k,

k.



6

From this “Fourier basis” for L2(

, γ) we can construct a “Fourier basis”

for L2(

n, γ) just by taking products, as in Proposition 8.13.

Deﬁnition 11.32. For a multi-index α
variate) Hermite polynomial hα :

n

→
n



n we deﬁne the (normalized multi-
by

hα j (z j).

hα(z)



1
j

∏

α
Note that the total degree of hα is
|
with its indicator α deﬁned by α j 
Proposition 11.33. The Hermite polynomials (hα)α
thonormal (Fourier) basis for L2(

| 
1 j

n, γ). Further, for any ρ

S; thus hS(z) denotes zS






[

j α j. We also identify a subset S

[n]

⊆
S z j.



j




n form a complete or-


α
ρ|

1, 1] we have

−

|

if α

if α

β,

β.



6

E
(z,z′)
ρ-correlated

[hα(z)hβ(z′)]

hα, Uρ hβ〉  〈

 〈

Uρ hα, hβ〉  

0

We can now deﬁne the “Hermite expansion” of Gaussian functions.

Deﬁnition 11.34. Every f



L2(

n, γ) is uniquely expressible as

where the real numbers
convergence is in L2(

n, γ); i.e.,

f (α) are called the Hermite coefﬁcients of f and the

f



f (α)hα,

n

α

∑





f

−

∥
∥
∥
This is called the Hermite expansion of f .
∥
∥

∥
∥
∥
∥
∥
Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.

α
k
|≤
∑|



2

f (α)hα

0 as k

.

→ ∞

→



<!-- pdf-page: 13 -->
11.2. Hermite polynomials

339

Remark 11.35. If f :
Hermite expansion”:

n

→

is a multilinear polynomial, then it “is its own

f (S)zS

f (z)



[n]

S
⊆
∑





[n]

S
⊆
∑



f (S)hS(z)



1

α1,...,αn≤
∑
L2(

f (α)hα(z).



n, γ) satisfy the for-

Proposition 11.36. The Hermite coefﬁcients of f
mula



and for f , g

L2(



 〈
n, γ) we have the Plancherel formula

f (α)

f , hα〉

,


f , g

〈

〉 

f (α)

g(α).

n

α

∑





From this we may deduce:

Proposition 11.37. For f
sion



L2(

n, γ), the function Uρ f has Hermite expan-

and hence

Uρ f



n

α

∑

Stabρ[ f ]



α

ρ|

f (α)hα

|


α
ρ|

|

f (α)2.

n

α

∑
Proof. Both statements follow from Proposition 11.36, with the ﬁrst using
f (β)hβ, hα〉 


we also used Proposition 11.33 and the fact that Uρ is a contraction in L2(

Uρ hβ, hα〉 

Uρ f , hα〉  〈

Uρ f (α)

f (α);

f (β)

Å

β


β


Uρ

 〈

ρ|







〈

α

|

n, γ).


Remark 11.38. When f :
for Uρ f agrees with the formula f (ρz) given in Fact 11.13.

→

is a multilinear polynomial, this formula

n

Remark 11.39. In a sense it’s not very important to know the explicit for-
mulas for the Hermite polynomials, (11.5), (11.8); it’s usually enough just to
know that the formula for Uρ f from Proposition 11.37 holds.

Finally, by differentiating the formula in Proposition 11.37 at ρ

1 we de-
duce the following formula for the Ornstein–Uhlenbeck operator (explaining
why it’s sometimes called the number operator):



Proposition 11.40. For f



L2(

n, γ) in the domain of L we have

L f



α

∑

f (α)hα.

α

|

n |



(Actually, Exercise 11.18 asks you to formally justify this and the fact that
.) For additional facts
f is in the domain of L if and only if
 ∞
about Hermite polynomials, see Exercises 11.9–11.14.

f (α)2

α |

α

2

|


Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.





<!-- pdf-page: 14 -->
340

11. Gaussian space and Invariance Principles

11.3. Borell’s Isoperimetric Theorem

If we believe that the Majority Is Stablest Theorem should be true, then
we also have to believe in its “Gaussian special case”. Let’s see what this
n
1, 1] is a “nice” function (smooth,
Gaussian special case is. Suppose f :
0. You’re encouraged to
say, with all derivatives bounded) having E[ f ]
think of f as (a smooth approximation to) the indicator
1A of some set
1
2 . Now consider the Boolean function
A
⊆
g : {

n of Gaussian volume volγ(A)
1, 1}nM

1, 1} deﬁned by

→

−



±



[

{

−

→

−

g

f

◦



BitsToGaussiansn
M.

Using the multidimensional Central Limit Theorem, for any ρ
should have



(0, 1) we

Stabρ[g]

M
→∞
−−−−→
where on the left we have Boolean noise stability and on the right we have
Gaussian noise stability. Using E[g]
0, the Majority Is Stablest
Theorem would tell us that

Stabρ[ f ],

E[ f ]

→



Stabρ[g]

1

2
π arccos ρ

o≤(1),

+

−

≤
≤(M)

where ≤
MaxInf[g]. But ≤
have the Gaussian noise stability bound

→





0 as M

. Thus we should simply

→ ∞

Stabρ[ f ]

1

2
π arccos ρ.

(11.11)

−

1, 1] with E[ f ]

≤
(By a standard approximation argument this extends from “nice” f :
[
−
that the upper bound (11.11) is achieved when f is the
halfspace through the origin; see Corollary 11.20. (Note also that if n
f

→
0.) Note

1-indicator of any
1 and

sgn, then the function g is simply MajM.)
The “isoperimetric inequality” (11.11) is indeed true, and is a special case

0 to any measurable f :

1, 1] with E[ f ]

→

±





−



n

n

[

of a theorem ﬁrst proved by Borell [Bor85].

Borell’s Isoperimetric Theorem (volume- 1
any f

n, γ) with range [

1, 1] and E[ f ]

L2(



2 case). Fix ρ
0,

2
π arccos ρ,

−
Stabρ[ f ]

1

−

≤

(0, 1). Then for



with equality if f is the

±

1-indicator of any halfspace through the origin.

Remark 11.41. In Borell’s Isoperimetric Theorem, nothing is lost by restrict-
ing attention to functions with range {
1A
1, 1] follows straightforwardly
for A
‖2 is a
from the case of range {
convex functional of f ; see Exercise 11.25.

n. This is because the case of range [

1, 1}, i.e., by considering only f

1, 1}, essentially because

Stabρ[ f ]

Upρ f

 ±

 ‖

⊆

−

−

−



Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 15 -->
11.3. Borell’s Isoperimetric Theorem

341

More generally, Borell showed that for any ﬁxed volume α

[0, 1], the
maximum Gaussian noise stability of a set of volume α is no greater than that
of a halfspace of volume α. We state here the more general theorem, using
1, 1} for future notational convenience (and
range {0, 1} rather than range {
with Remark 11.41 applying equally):

−



Borell’s Isoperimetric Theorem. Fix ρ
with range [0, 1] and E[ f ]

α,



(0, 1). Then for any f



L2(

n, γ)



Stabρ[ f ]

Λρ(α).

≤

Here Λρ(α) is the Gaussian quadrant probability function, discussed in Exer-
n
cises 5.32 and 11.19, and equal to Stabρ[1H] for any (every) halfspace H
α.
having Gaussian volume volγ(H)

⊆



We’ve seen that the volume- 1

2 case of Borell’s Isoperimetric Theorem is a
special case of the Majority Is Stablest Theorem, and similarly, the general
version of Borell’s theorem is a special case of the General-Volume Majority
Is Stablest Theorem mentioned at the beginning of the chapter. As a conse-
quence, proving Borell’s Isoperimetric Theorem is a prerequisite for proving
the General-Volume Majority Is Stablest Theorem. In fact, our proof in Sec-
tion 11.7 of the latter will be a reduction to the former.

The proof of Borell’s Isoperimetric Theorem itself is not too hard; one of
ﬁve known proofs, the one due to Mossel and Neeman [MN12], is outlined in
Exercises 11.26–11.29. If our main goal is just to prove the basic Majority Is
Stablest Theorem, then we only need the volume- 1
2 case of Borell’s Isoperi-
metric Inequality. Luckily, there’s a very simple proof of this volume- 1
2 case
for “many” values of ρ, as we will now explain.

Let’s ﬁrst slightly rephrase the statement of Borell’s Isoperimetric Theo-
rem in the volume- 1
2 case. By Remark 11.41 we can restrict attention to sets;
then the theorem asserts that among sets of Gaussian volume 1
2 , halfspaces
through the origin have maximal noise stability, for each positive value of ρ.
Equivalently, halfspaces through the origin have minimal noise sensitivity
under correlation cos θ, for θ
2 ). The formula for this minimal noise sen-
sitivity was given as (11.2) in our proof of Sheppard’s Formula. Thus we have:

(0, π



Equivalent statement of the volume- 1
Fix θ

2 ). Then for any A

(0, π

n with volγ(A)

⊂



1
2 ,



2 Borell Isoperimetric Theorem.

Pr
(z,z′)
cos θ-correlated

[1A(z)

6

1A(z′)]

θ
π ,

≥

with equality if A is any halfspace through the origin.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 16 -->
342

11. Gaussian space and Invariance Principles

In the remainder of this section we’ll show how to prove this formulation
π
2` , where ` is a positive integer. This gives
of the theorem whenever θ
the volume- 1
2 case of Borell’s Isoperimetric Inequality for all ρ of the form
arccos π
+; in particular, for an inﬁnite sequence of ρ’s tending to 1. To
prove the theorem for these values of θ, it’s convenient to introduce notation
for the following noise sensitivity variant:

2` , `





Deﬁnition 11.42. For A
for the rotation sensitivity of A at δ, deﬁned by

⊆



n and δ

(usually δ

[0, π]) we write RSA(δ)



RSA(δ)



Pr
(z,z′)
cos δ-correlated

[1A(z)

6

1A(z′)].

The key property of this deﬁnition is the following:

Theorem 11.43. For any A

⊆
RSA(δ1 + · · · +

n the function RSA(δ) is subadditive; i.e.,

δ`)

≤

RSA(δ1)

+ · · · +

RSA(δ`).

In particular, for any δ



and `


RSA(δ)

+,

`

·

≤

RSA(δ/`).

∼

N(0, 1)n be drawn independently and deﬁne z(θ)

(cos θ)g
Proof. Let g, g′
+
(sin θ)g′. Geometrically, as θ goes from 0 to π
2 the random vectors z(θ) trace
from g to g′ along the origin-centered ellipse passing through these two points.
The random vectors z(θ) are jointly normal, with each individually distributed
as N(0, 1)n. Further, for each ﬁxed θ, θ′
the pair (z(θ), z(θ′)) constitute ρ-
correlated Gaussians with





cos θ cos θ′

ρ



+

sin θ sin θ′

cos(θ′

θ).

−



Now consider the sequence θ0, . . . , θ` deﬁned by the partial sums of the δi’s,
δi. We get that z(θ0) and z(θ`) are cos(δ1 + · · · +
i.e., θ j 
δ`)-correlated,
1

1) and z(θ j) are cos δ j-correlated for each j
and that z(θ j

[`]. Thus

j
i



Pr[1A(z(θ0))
`

6

1A(z(θ`))]

Pr[1A(z(θ j))

1A(z(θ j

1))]

−



6

δ`)



≤

1
j

∑

RSA(δ j),

(11.12)

`

1
j

∑



where the inequality is the union bound.

−


RSA(δ1 + · · · +

With this subadditivity result in hand, it’s indeed easy to prove the equiv-

alent statement of the volume- 1
{ π
4 , π

give an excellent UG-hardness result for the Max-Cut CSP.

10 , . . . }. As we’ll see in Section 11.7, the case of θ

8 , π

6 , π

2 Borell Isoperimetric Theorem for any θ


π
4 can be used to

Corollary 11.44. The equivalent statement of the volume- 1
ric Theorem holds whenever θ

+.

π
2` for `





2 Borell Isoperimet-

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 17 -->
11.4. Gaussian surface area and Bobkov’s Inequality

343

Proof. The exact statement we need to show is RSA( π
2` )
π
by taking δ
2 in Theorem 11.43 because



RSA( π
2 )



Pr
(z,z′)
0-correlated

[1A(z)

6

1A(z′)]

1
2 ,



1
2` . This follows

≥



using that 0-correlated Gaussians are independent and that volγ(A)

1
2 . 
Remark 11.45. Although Sheppard’s Formula already tells us that equality
holds in this corollary when A is a halfspace through the origin, it’s also
not hard to derive this directly from the proof. The only inequality in the
proof, (11.12), is an equality when A is a halfspace through the origin, because
the elliptical arc can only cross such a halfspace 0 or 1 times.
n not only has volume 1

2 , it has the prop-
Remark 11.46. Suppose that A
erty that x
1-indicator of A is an
odd function. (In both statements, we allow a set of measure 0 to be ignored.)
An example set with this property is any halfspace through the origin. Then
RSA(π)
1, and hence we can establish Corollary 11.44 more generally for

2 , π
1 , π
{ π
any θ

⊆
A; in other words, the

5 , . . . } by taking δ

A if and only if

π in the proof.

4 , π

3 , π

−

±



6

x





11.4. Gaussian surface area and Bobkov’s Inequality

This section is devoted to studying the Gaussian Isoperimetric Inequality.
This inequality is a special case of the Borell Isoperimetric Inequality (and
hence also a special case of the General-Volume Majority Is Stablest Theorem);
in particular, it’s the special case arising from the limit ρ

1−.

→

Restating Borell’s theorem using rotation sensitivity we have that for any
n is a halfspace with the same Gaussian volume as A then

n, if H

A
⊆
for all ≤,

⊆

Since RSA(0)

RSH(0)





RSA(≤)
0, it follows that

≥

RSH(≤).

RS′A(0+)

RS′H(0+).

≥
(Here we are considering the one-sided derivatives at 0, which can be shown
; see the notes at the end of this
to exist, though RS′A(0+) may equal
chapter.) As will be explained shortly, RS′A(0+) is precisely p2/π
surfγ(A),
where surfγ(A) denotes the “Gaussian surface area” of A. Therefore the above
inequality is equivalent to the following:

+∞

·

Gaussian Isoperimetric Inequality. Let A
n be any halfspace with volγ(H)
H

⊆
α. Then surfγ(A)



surfγ(H).

⊆


Remark 11.47. As shown in Proposition 11.49 below, the right-hand side
in this inequality is equal to U (α), where U is the Gaussian isoperimetric
function, encountered earlier in Deﬁnition 5.26 and deﬁned by U

Φ−

1.

≥

ϕ

n have volγ(A)

α and let



◦

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 18 -->
344

11. Gaussian space and Invariance Principles

Let’s now discuss the somewhat technical question of how to properly
deﬁne surfγ(A), the Gaussian surface area of a set A. Perhaps the most
natural deﬁnition would be to equate it with the Gaussian Minkowski content
of the boundary ∂A of A,

γ+(∂A)



lim inf
≤
→

0+

volγ({z : dist(z, ∂A)

≤

≤/2})



.

(11.13)

(Relatedly, one might also consider the surface integral over ∂A of the Gauss-
ian pdf ϕ.) Under the “ofﬁcial” deﬁnition of surfγ(A) we give below in Deﬁni-
γ+(∂A) whenever A is sufﬁciently nice
tion 11.48, we’ll indeed have surfγ(A)

– say, a disjoint union of closed, full-dimensional, convex sets. However, the
Minkowski content deﬁnition is not a good one in general because it’s possible
to have γ+(∂A1)
γ+(∂A2) for some sets A1 and A2 that are equivalent up to
measure 0. (For more information, see Exercise 11.15 and the notes at the
end of this chapter.)

6

pπ/2

·



As mentioned above, one “correct” deﬁnition is surfγ(A)

RS′A(0+).
This deﬁnition has the advantage of being insensitive to measure-0 changes
to A. To connect this unusual-looking deﬁnition with Minkowski content,
let’s heuristically interpret RS′A(0+). We start by thinking of it as RSA(≤)
for
“inﬁnitesimal ≤”. Now RSA(≤) can be thought of as the probability that the line
segment ` joining two cos ≤-correlated Gaussians crosses ∂A. Since sin ≤
≤,
1 up to O(≤2), we can think of these correlated Gaussians as g and
cos ≤
N(0, 1)n. When g lands near ∂A, the length
g
of ` in the direction perpendicular to ∂A will, in expectation, be ≤ E[
p2/π≤. Thus RSA(≤) should essentially be 1
we have heuristically justiﬁed

≈
≤g′ for independent g, g′

N(0, 1)

p2/π≤}) and

2 volγ({z : dist(z, ∂A)

+

∼

≈



]

|

|

≤

pπ/2

RS′A(0+)

·



pπ/2

RSA(≤)
≤

?


lim
≤
0+
→

·

γ+(∂A).

(11.14)

‖

L1(

1A‖

One more standard idea for the deﬁnition of surfγ(A) is “E[

]”. This
n, γ) is not actually differentiable.
doesn’t quite make sense since 1A 
However, we might consider replacing it with the limit of E[
] for a
sequence ( f m) of smooth functions approximating 1A. To see why this notion
should agree with the Gaussian Minkowski content γ+(∂A) for nice enough A,
let’s suppose we have a smooth approximator f to 1A that agrees with 1A on
{z : dist(z, ∂A)

will be 0 on the former set and (essentially) constantly 1/≤
≤/2}. Then
on the latter (since it must climb from 0 to 1 over a distance of ≤). Thus we
indeed have

≤/2} and is (essentially) a linear function on {z : dist(z, ∂A)

f m‖

≥
f
‖

‖

‖

E[

f

]

‖

≈

‖

volγ({z : dist(z, ∂A)

≤

≤/2})



γ+(∂A),

≈

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 19 -->
11.4. Gaussian surface area and Bobkov’s Inequality

345

as desired. We summarize the above technical discussion with the following
deﬁnition/theorem, which is discussed further in the notes at the end of this
chapter:

Deﬁnition 11.48. For any A

⊆

surfγ(A)



An equivalent deﬁnition is

n, we deﬁne its Gaussian surface area to be

pπ/2

RS′A(0+)

[0,

].

∞



·

surfγ(A)

inf



lim inf
m
→∞

{

z

∼

E
N(0,1)n

[

‖

f m(z)

]

,

‖

[0, 1]
where the inﬁmum is over all sequences ( f m)m
→
with ﬁrst partial derivatives in L2(
0. Further-
f m −
‖
Uρm f for any sequence
more, this inﬁmum is actually achieved by taking f m 
γ+(∂A) with Gaussian Minkowski
ρm →
content holds if A is a disjoint union of closed, full-dimensional, convex sets.

1−. Finally, the equality surfγ(A)

n, γ) such that





}
of smooth f m :
1A‖1 →

n

To get further acquainted with this deﬁnition, let’s describe the Gaussian
surface area of some basic sets. We start with halfspaces, which as men-
tioned in Remark 11.47 have Gaussian surface area given by the Gaussian
isoperimetric function.

Proposition 11.49. Let H
α
(0, 1). Then surfγ(H)
boundary contains the origin – then surfγ(H)

⊆
U (α)

ϕ(Φ−







n be any halfspace (open or closed) with volγ(H)
1/2 – i.e., H’s



1(α)). In particular, if α
1
.
p2π





Proof. Just as in the proof of Corollary 11.20, by rotational symmetry we
α, we
may assume H is a 1-dimensional halﬂine, H
have t

1(α). Then surfγ(H) is equal to

, t]. Since volγ(H)

−∞

Φ−





(



γ+(∂H)



lim
≤
0+
→

volγ({z



: dist(z, ∂H)

≤

≤
2 })





t
t
0+ 

lim
≤
→

≤/2
≤/2 ϕ(s) ds
+
−

≤

ϕ(t)





U (α).



Here are some more Gaussian surface area bounds:

Example 11.50. In Exercise 11.16 you are asked to generalize the above
is the union of disjoint nondegenerate in-
computation and show that if A
2m
1 ϕ(ti). Perhaps the
tervals [t1, t2], [t3, t4], . . . , [t2m
i

n is an origin-centered ball; Ball [Bal93]
next easiest example is when A
gave an explicit formula for surfγ(A) in terms of the dimension and radius,

1, t2m] then surfγ(A)



⊆



⊆

−

2
π (see Exercise 11.17). This upper bound
one which is always less than
was extended to non-origin-centered balls in Klivans et al. [KOS08]. Ball also

O(n1/4); Nazarov
showed that every convex set A
[Naz03] showed that this bound is tight up to the constant, using a construc-
tion highly reminiscent of Talagrand’s Exercise 4.18. As noted in Klivans

n satisﬁes surfγ(A)

⊆

≤

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 20 -->
346

11. Gaussian space and Invariance Principles

et al. [KOS08], Nazarov’s work also immediately implies that an intersection
of k halfspaces has Gaussian surface area at most O(
log k) (tight for appro-
priately sized cubes in k), and that any cone in n with apex at the origin
has Gaussian surface area at most 1. Finally, by proving the “Gaussian spe-
cial case” of the Gotsman–Linial Conjecture, Kane [Kan11] established that
if A
0}
{z : p(z)

for p an n-variate degree-k polynomial – then surfγ(A)
. This is tight
1).
for every k (even when n

n is a degree-k “polynomial threshold function” – i.e., A

k
p2π



⊆



≤



Though we’ve shown that the Gaussian Isoperimetric Inequality follows
from Borell’s Isoperimetric Theorem, we now discuss some alternative proofs.
In the special case of sets of Gaussian volume 1
2 , we can again get a very
simple proof using the subadditivity property of Gaussian rotation sensitivity,
Theorem 11.43. That result easily yields the following kind of “concavity
property” concerning Gaussian surface area:

Theorem 11.51. Let A

n. Then for any δ

0,



⊆

pπ/2

RSA(δ)
δ

·

≤

surfγ(A).

Proof. For δ

0 and ≤

δ/`, `







+, Theorem 11.43 is equivalent to

RSA(δ)
δ

≤

RSA(≤)
≤

.

Taking `
surfγ(A).

→ ∞

hence ≤

→

0+, the right-hand side becomes RS′A(0+)



p2/π
·


If we take δ


p2/π

π/2 in this theorem, the left-hand side becomes

Pr
N(0,1)n
z,z′
∼
independent

[1A(z)

6

1A(z′)]



2p2/π

·

volγ(A)(1

volγ(A)).

−

Thus we obtain a simple proof of the following result, which includes the
Gaussian Isoperimetric Inequality in the volume- 1

2 case:

Theorem 11.52. Let A

⊆
2p2/π

n. Then

volγ(A)(1

volγ(A))

−

≤

·

surfγ(A).

In particular, if volγ(A)
Inequality statement surfγ(A)



1
p2π 

≥

U ( 1

2 ).

1
2 , then we get the tight Gaussian Isoperimetric

As for the full Gaussian Isoperimetric Inequality, it’s a pleasing fact that
it can be derived by pure analysis of Boolean functions. This was shown
by Bobkov [Bob97], who proved the following very interesting isoperimetric
inequality about Boolean functions:

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 21 -->
11.4. Gaussian surface area and Bobkov’s Inequality

347

Bobkov’s Inequality. Let f : {

1, 1}n

−

[0, 1]. Then

→
(U ( f (x)),

U (E[ f ])

E
1,1}n
−
f is the discrete gradient (as in Deﬁnition 2.34) and

f (x))

] .

≤



‖

‖

∼

[

x

{

1). Thus to restate the inequality,

+

Here
Euclidean norm (in n



(11.15)

is the usual

‖ · ‖

U (E[ f ])

≤

x

E
1,1}n 
−

{

∼

U ( f (x))2

+

Di f (x)2

.



n

1
i



In particular, suppose f
since U (0)

U (1)







1A is the 0-1 indicator of a subset A

0 we obtain U (E[1A])

E[

].

1A‖

‖

≤

1, 1}n. Then

{

−

⊆

As Bobkov noted, by the usual Central Limit Theorem argument one can
straightforwardly obtain inequality (11.15) in the setting of functions f

L2(
n, γ) with range [0, 1], provided f is sufﬁciently smooth (for example, if f
n, by taking a
is in the domain of L; see Exercise 11.18). Then given A
sequence of smooth approximations to 1A as in Deﬁnition 11.48, the Gaussian
Isoperimetric Inequality U (E[1A])
{

≤
1, 1}n we can write the quantity E[

surfγ(A) is recovered.

] appearing in

Given A

⊆

1A‖

‖

Bobkov’s Inequality as

⊆

−

using the fact that for 1A : {

Di1A(x)2

1
4 ·



E[

‖

1A‖

]

1
2 ·

1, 1}n

sensA(x)

x

{

E
1,1}n
∼
−

{0, 1} we have

,



(11.16)

→

−
1[coordinate i is pivotal for 1A on x].

The quantity in (11.16) – (half of) the expected square-root of the number of
pivotal coordinates – is an interesting possible notion of “Boolean surface area”
1, 1}n. It was ﬁrst essentially proposed by Talagrand [Tal93].
for sets A
By Cauchy–Schwarz it’s upper-bounded by (half of) the square-root of our
usual notion of boundary size, average sensitivity:

⊆

−

{

E[

]

1A‖

E[

2]

1A‖

I[1A].

≤





‖

‖
(Note that I[1A] here is actually one quarter of the average sensitivity of A,
because we’re using 0-1 indicators as opposed to
1). But the inequality
in (11.17) is often far from sharp. For example, while the majority function has
average sensitivity Θ(pn), the expected square-root of its sensitivity is Θ(1)
because a Θ(1/pn)-fraction of strings have sensitivity
and the remainder
have sensitivity 0.

n/2



±

e

d

(11.17)

Let’s turn to the proof of Bobkov’s Inequality. As you are asked to show
in Exercise 11.20, the general-n case of Bobkov’s Inequality follows from the
1 case by a straightforward “induction by restrictions”. Thus just as in
n
the proof of the Hypercontractivity Theorem, it sufﬁces to prove the n
1
“two-point inequality”, an elementary inequality about two real numbers:





Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 22 -->
348

11. Gaussian space and Invariance Principles

Bobkov’s Two-Point Inequality. Let f : {

1, 1}

U (E[ f ])

E[

‖

≤

−
(U ( f ),

[0, 1]. Then

→
].

‖

f )



Writing f (x)

a

+



bx, this is equivalent to saying that provided a

b



±

[0, 1],

U (a)

1
2 ‖

≤

(U (a

b), b)

1
2 ‖

‖ +

(U (a

b), b)

.

‖

−

+

Remark 11.53. The only property of U used in proving this inequality is
that it satisﬁes (Exercise 5.43) the differential equation U U ′′
1 on (0, 1).

 −

Bobkov’s proof of the two-point inequality was elementary but somewhat
long and hard to motivate. In contrast, Barthe and Maurey [BM00] gave
a fairly short proof of the inequality, but it used methods from stochastic
calculus, namely Itô’s Formula. We present here an elementary discretization
of the Barthe–Maurey proof.

1

b

b

a

a

−

≤

+



−

≤

0. Let τ

δ for some δ

Proof of Bobkov’s Two-Point Inequality. By symmetry and continuity we
may assume δ
0 be a small
quantity to be chosen later such that b/τ is an integer. Let y0, y1, y2, . . . be
a, takes independent
a random walk within [a
equally likely steps of
b. Finally, for
, deﬁne zt  ‖
t
Claim 11.54. Assuming τ

with respect to (yt)t, i.e., E[zt

b] that starts at y0 
τ, and is absorbed at the endpoints a

±
. The key claim for the proof is:

0 is small enough, (zt)t is a submartingale

±
(U (yt), τpt)


y0, . . . , yt]

‖
τ(δ)

E[zt

τ(δ)

b, a

yt]

zt.

−







+



1 |

+



1 |

+

≥

Let’s complete the proof given the claim. Let T be the stopping time at
b. By the Optional Stopping Theorem we have

which yt ﬁrst reaches a
E[zT ]; i.e.,
E[z0]

±

≤

U (a)

E[

‖

≤

(U (zT ), τpT)

].

‖

(11.18)

In the expectation above we can condition on whether the walk stopped at
b. By symmetry, both events occur with probability 1/2 and neither
a
changes the conditional distribution of T. Thus we get

b or a

+

−

(U (a

U (a)

≤

≤

1
2 E[
1
2 ‖

‖
(U (a

+

b), τpT)

]

‖
E[τ2T])

+
b),

1
2 E[
1
2 ‖

+

‖ +

(U (a

‖
(U (a

−
b),

−

b), τpT)

]

‖

E[τ2T])

,

‖

with the second inequality using concavity of v
known fact (following immediately from Exercise 11.22) that E[T]
Substituting this into the above completes the proof.

v. But it’s a well-
(b/τ)2.

7→




pu2
+



It remains to verify Claim 11.54. Actually, although the claim is true
as stated (see Exercise 11.23) it will be more natural to prove the following
slightly weaker claim:

≥
Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.

+

E[zt

yt]

1 |

zt −

Cδτ3

(11.19)



<!-- pdf-page: 23 -->
11.4. Gaussian surface area and Bobkov’s Inequality

349

for some constant Cδ depending only on δ. This is still enough to com-
plete the proof: Applying the Optional Stopping Theorem to the submartin-
gale (zt +

Cδb2τ. Then continuing with the above we deduce Bobkov’s Inequality up
to Cδb2τ, and we can make τ arbitrarily small.

Cδτ3t)t we get that (11.18) holds up to an additive Cδτ3 E[T]

Even though we only need to prove (11.19), let’s begin a proof of the
+ and condition on yt 
original Claim 11.54 anyway. Fix t
b,
±
τ with
then the walk is stopped and the claim is clear. Otherwise, yt
equal probability, and we want to verify the following inequality (assuming
τ

0 is sufﬁciently small as a function of δ, independent of y):

y. If y is a
1 is y

±



+



(U (y), τpt)

‖

‖ ≤

(U (y

+

τ), τpt

1
2 ‖

(U (y

−

τ), τpt

1)

(11.20)

‖

1)

+
‖ +
τ2, τpt

U (y

τ)2

+

+

1
2 ‖
1
2

∥
∥



+
τ)2

1
2

+

U (y

−



∥
∥

τ2, τpt

.

+

∥
∥


By the triangle inequality, it’s sufﬁcient to show

U (y)

1
2

U (y

τ)2

τ2

U (y

τ)2

τ2,

+

≤



−

0 case of (11.20). (In fact,
and this is actually necessary too, being the t
this is identical to Bobkov’s Two-Point Inequality itself, except now we may
assume τ is sufﬁciently small.) Finally, since we actually only need the weak-
ened submartingale statement (11.19), we’ll instead establish

+

+

+



∥
∥

1
2

U (y)

Cδτ3

1
2

≤

−

U (y

τ)2

τ2

1
2

+

+

+

U (y

τ)2

τ2

+

−

(11.21)





δ
for some constant Cδ depending only on δ and for every τ
2 . We do this
using Taylor’s theorem. Write Vy(τ) for the function of τ on the right-hand
b] the function Vy is smooth on [0, δ
side of (11.21). For any y
2 ]
because U is a smooth, positive function on [ δ

b, a

[a

≤

−

+



Vy(τ)

Vy(0)

V ′y(0)τ



+
for some ξ between 0 and τ. The magnitude of V ′′′y (ξ) is indeed bounded by
some Cδ depending only on δ, using the fact that U is smooth and positive on
[ δ
2 , 1

U (y), and it’s straightforward to calculate that

δ
2 ]. But Vy(0)

+

+

−

the last identity used the key property U ′′
Thus we conclude Vy(τ)
proof.

U (y)

≥

−

V ′′y (0)

U ′′(y)

1/U (y)

0,





+
1/U mentioned in Remark 11.53.
Cδτ3, verifying (11.21) and completing the


 −


V ′y(0)

0,



2 , 1
2 V ′′y (0)τ2

1

−

δ
2 ]. Thus
6 V ′′′y (ξ)τ3
1

As a matter of fact, by a minor adjustment (Exercise 11.24) to this ran-
dom walk argument we can establish the following generalization of Bobkov’s
Inequality:

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 24 -->
350

11. Gaussian space and Invariance Principles

Theorem 11.55. Let f : {
increasing function of ρ
ρ

0, 1.





1, 1}n

] is an
[0, 1]. We recover Bobkov’s Inequality by considering

[0, 1]. Then E[

(U (Tρ f ),

Tρ f )

→

−



‖

‖

We end this section by remarking that De, Mossel, and Neeman [DMN13]
have given a “Bobkov-style” Boolean inductive proof that yields both Borell’s
Isoperimetric Theorem and also the Majority Is Stablest Theorem (albeit with
some aspects of the Invariance Principle-based proof appearing in the latter
case); see Exercise 11.30 and the notes at the end of this chapter.

11.5. The Berry–Esseen Theorem

Now that we’ve built up some results concerning Gaussian space, we’re mo-
tivated to try reducing problems involving Boolean functions to problems
involving Gaussian functions. The key tool for this is the Invariance Princi-
ple, discussed at the beginning of the chapter. As a warmup, this section is
devoted to proving (a form of) the Berry–Esseen Theorem. As discussed in
Chapter 5.2, the Berry–Esseen Theorem is a quantitative form of the Central
Limit Theorem for ﬁnite sums of independent random variables. We restate
it here:

Berry–Esseen Theorem. Let X 1, . . . , X n be independent random variables
with E[X i]
1 X i
and let Z

i 

N(0, 1) be a standard Gaussian. Then for all u

1. Let S
,

i , and assume

0 and Var[X i]

1 σ2

σ2

n
i

n
i















∼

Pr[S

|

u]

−

≤

Pr[Z

u]

| ≤

≤

cγ,

where

n

3
3

X i‖

γ



1 ‖

i

∑

and c is a universal constant. (For deﬁniteness, c

.56 is acceptable.)



In this traditional statement of Berry–Esseen, the error term γ is a little
opaque. To say that γ is small is to simultaneously say two things: the random
variables X i are all “reasonable” (as in Chapter 9.1); and, none is too domi-
nant in terms of variance. In Chapter 9.1 we discussed several related notions
of “reasonableness” for a random variable X . It was convenient there to use
4
2. For the Berry–Esseen
the deﬁnition that
Theorem it’s more convenient (and slightly stronger) to use the analogous
condition for the 3rd moment. (For the Invariance Principle it will be more
convenient to use (2, 3, ρ)- or (2, 4, ρ)-hypercontractivity.) The implication for
Berry–Esseen is the following:

4
4 is not much larger than

X

X

‖

‖

‖

‖

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 25 -->
11.5. The Berry–Esseen Theorem

351

Remark 11.56. In the Berry–Esseen Theorem, if all of the X i’s are “reason-
3
able” in the sense that
2 
max
i

i , then we can use the bound

X i‖
B

(11.22)

X i‖

3
3 ≤

Bσ3

{σi},

B

≤

γ

‖

‖

·

as this is a consequence of

γ



n

1 ‖

i

∑

n

1
i

∑

X i‖

3
3 ≤

B

σ3

i ≤

B

max
i

·

{σi}

·

σ2

i 

B

max
i

·

{σi}.

n

1
i

∑





(Cf. Remark 5.15.) Note that some “reasonableness” condition must hold if
i X i is to behave like a Gaussian. For example, if each X i is the “unrea-
S
2n2 each and 0 other-
sonable” random variable which is
wise, then S
n – quite unlike a Gaussian.
Further, even assuming reasonableness we still need a condition like (11.22)
ensuring that no X i is too dominant (“inﬂuential”) in terms of variance. For
example, if X 1 ∼
0, then
S

1, 1} is a uniformly random bit and X 2, . . . , X n ≡

X 1, which is again quite unlike a Gaussian.

0 except with probability at most 1

pn with probability 1

±



−

{

≡

There are several known ways to prove the Berry–Esseen Theorem; for ex-
ample, using characteristic functions (i.e., “real” Fourier analysis), or Stein’s
Method. We’ll use the “Replacement Method” (also known as the Lindeberg
Method, and similar to the “Hybrid Method” in theoretical cryptography). Al-
though it doesn’t always give the sharpest results, it’s a very ﬂexible technique
which generalizes easily to higher-degree polynomials of random variables (as
in the Invariance Principle) and random vectors. The Replacement Method
suggests itself as soon as the Berry–Esseen Theorem is written in a slightly
different form: Instead of trying to show

where Z

∼

N(0, 1), we’ll instead try to show the equivalent statement

X 1 +

X 2 + · · · +

X n ≈

Z,

(11.23)

Z1 +

X 1 +

X n ≈

X 2 + · · · +
i ). The state-
where the Z i’s are independent Gaussians with Z i ∼
ments (11.23) and (11.24) really are identical, since the sum of independent
Gaussians is Gaussian, with the variances adding. The Replacement Method
proves (11.24) by replacing the X i’s with Z i’s one by one. Roughly speaking,
we introduce the “hybrid” random variables

Z2 + · · · +

N(0, σ2

(11.24)

Z n,

show that H t

−

1 ≈

Z1 + · · · +

H t 
H t for each t



Z t +

X t

1 + · · · +

+

X n,

[n], and then simply add up the n errors.

As a matter of fact, the Replacement Method doesn’t really have anything

to do with Gaussian random variables. It actually seeks to show that

X 1 +

X 2 + · · · +

X n ≈

Y 1 +

Y 2 + · · · +

Y n

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 26 -->
352

11. Gaussian space and Invariance Principles



whenever X 1, . . . , X n, Y 1, . . . , Y n are independent random variables with “match-
E[Y i] and E[X 2
E[Y 2
ing ﬁrst and second moments”, meaning E[X i]
i ]
i ] for


3
3
each i
[n]. (The error will be proportional to
3).) Another
i(
Y i‖
xn is in-
way of putting it (roughly speaking) is that the linear form x1 + · · · +
variant to what independent random variables you substitute in for x1, . . . , xn,
so long as you always use the same ﬁrst and second moments. The fact that
N(E[X i], Var[X i])) and then
we can take the Y i’s to be Gaussians (with Y i ∼
in the end use the fact that the sum of Gaussians is Gaussian to derive the
simpler-looking

X i‖

+ ‖



‖

S



n

1
i

∑

X i ≈

N(E[S], Var[S])

is just a pleasant bonus (and one that we’ll no longer get once we look at
nonlinear polynomials of random variables in Section 11.6). Indeed, the re-
mainder of this section will be devoted to showing that

S X 

X 1 + · · · +

X n

is “close” to SY 

Y 1 + · · · +

Y n

whenever the X i’s and Y i’s are independent, “reasonable” random variables
with matching ﬁrst and second moments.

To do this, we’ll ﬁrst have to discuss in more detail what it means for two
random variables to be “close”. A traditional measure of closeness between
two random variables S X and SY is the “cdf-distance” used in the Berry–
. But there are
Pr[SY ≤
Esseen Theorem: Pr[S X ≤
other natural measures of closeness too. We might want to know that the
absolute moments of S X and SY are close; for example, that
SY ‖1.
S X ‖1 ≈ ‖
Or, we might like to know that S X and SY stray from the interval [
1, 1]
−
by about the same amount: E[dist[
1,1](SY )]. Here we are
using:

u] for every u

1,1](S X )]

E[dist[

u]

≈

≈



‖

−

−

Deﬁnition 11.57. For any interval
deﬁned to measure the distance of a point from I; i.e., distI (s)

I ( the function distI :

 6

infu



→
I {



s

|

≥

0 is
}.
u

−

|

All of the closeness measures just described can be put in a common frame-
E[(SY )] for various “test functions” (or

work: they are requiring E[(S X )]
“distinguishers”)  :

.

≈

→

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 27 -->
11.5. The Berry–Esseen Theorem

353

Figure 11.1. The test functions  used for judging Pr[S X ≤
u],

Pr[SY ≤
u]
1,1](SY )], respectively

1,1](S X )]

E[dist[

≈

S X ‖1 ≈ ‖

SY ‖1, and E[dist[

≈

‖

−

−

It would be nice to prove a version of the Berry–Esseen Theorem that
showed closeness for all the test functions  depicted in Figure 11.1, and
more. What class of tests might we able to handle? On one hand, we can’t be
N(0, 1), and
too ambitious. For example, suppose each X i ∼
(s)
1 because S X is supported on the integers, but
1s



E[(SY )]
N(0, n) is a continuous random variable. On the
other hand, there are some simple kinds of tests  for which we have exact
E[(SY )]; this is by the
equality. For example, if (s)
assumption of matching ﬁrst moments, E[X i]
E[Y i] for all i. Similarly, if
(s)

. Then E[(S X )]
0 because SY ∼

1, 1}, each Y i ∼

s, then E[(S X )]

s2, then





−





{



E[(S X )]

E



2

X i

i
∑
E[X 2
i ]



+



i
∑

j
i
6
∑





E[X 2
i ]

+

i
j
i
6
∑
∑
E[X i] E[X j]

E[X i X j]

(11.25)

(using independence of the X i’s); and also

E[(SY )]



E[Y 2
i ]

+

E[Y i] E[Y j].

(11.26)

j
i
6
∑
The quantities (11.25) and (11.26) are equal because of the matching ﬁrst and
second moment conditions.

i
∑

a

+



+



As a consequence of these observations we have E[(S X )]

E[(SY )] for
cs2. This suggests that to handle
any quadratic polynomial (s)
bs
a general test  we try to approximate it by a quadratic polynomial up to
some error; in other words, consider its 2nd-order Taylor expansion. For this
to make sense the function  must have a continuous 3rd derivative, and
the error we incur will involve the magnitude of this derivative. Indeed, we
will now prove a variant of the Berry–Esseen Theorem for the class of C 3
test functions  with ′′′ uniformly bounded. You might be concerned that
this class doesn’t contain any of the interesting test functions depicted in
Figure 11.1. But we’ll be able to handle even those test functions with some
loss in the parameters by using a simple “hack” – approximating them by
smooth functions, as suggested in Figure 11.2.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 28 -->
354

11. Gaussian space and Invariance Principles

Figure 11.2. The step function (s)
interval [u
O(1/η3). Similarly, we can smooth out (s)
satisfying

η] so that the resulting function
dist[

u can be smoothed out on the
η satisﬁes
′′′η ‖∞ ≤
η
1,1](s) to a function



O(1/η2).

η and

η, u

1s







−

+



≤

−

‖

‖

−

‖∞ ≤

′′′η ‖∞ ≤

‖







Invariance Principle for Sums of Random Variables. Let X 1, . . . , X n,
Y 1, . . . , Y n be independent random variables with matching 1st and 2nd mo-
ments; i.e., E[X k
i ]
i X i and SY 

{1, 2}. Write S X 

i ] for i

E[Y k

[n], k







i Y i. Then for any  :

→

with continuous third derivative,


E[(SY )]

E[(S X )]


where γX Y 
Y i‖
Proof. The proof is by the Replacement Method. For 0
“hybrid” random variable

3
3 + ‖

∣
X i‖
∣

−
3
3).

‖∞ ·

′′′

γX Y ,



i(

≤

∣
∣

‖

1
6 ‖

t

≤

≤

n, deﬁne the

so S X 

H0 and SY 
E[(S X )]

Y 1 + · · · +

H t 
H n. Thus by the triangle inequality,

1 + · · · +

Y t +

X t

X n,

+

E[(SY )]

−

≤

1)]

−

−

E[(H t)]

.

n

E[(H t

1
t

∑
Given the deﬁnition of γX Y , we can complete the proof by showing that for
each t

[n],

∣
∣

∣
∣

∣
∣

∣
∣


′′′

1
6 ‖

(E[

X t|

|

‖∞ ·

3]

E[

Y t|

|

+

3])

≥





E[(H t

1)]

−

E[(H t
1)
E[(U t +

−

−
X t)

E[(H t)]

−
(H t)]

(U t +
∣
∣

−

∣
∣
Y t)]

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.

∣
∣
∣
∣
∣
∣

(11.27)

,

∣
∣



<!-- pdf-page: 29 -->
11.5. The Berry–Esseen Theorem

355

where

Y t

U t 

Y 1 + · · · +

1 +
−
Note that U t is independent of X t and Y t. We are now comparing ’s values
at U t +
Y t, with the presumption that X t and Y t are rather small
compared to U t. This clearly suggests the use of Taylor’s theorem: For all
u, δ

X t and U t +

1 + · · · +

+

,

X t

X n.



(u

δ)

+



(u)

+

′(u)δ

+

1

2 ′′(u)δ2

+

1

6 ′′′(u∗)δ3,

u∗(u, δ) between u and u

δ. Applying this pointwise with

+

for some u∗
U t, δ
u





X t, Y t yields


(U t +
(U t +

X t)

Y t)

(U t)

(U t)

′(U t)X t +
′(U t)Y t +

+

+





1

2 ′′(U t)X 2
2 ′′(U t)Y 2

1

t +

t +

1

6 ′′′(U ∗t )X 3
t
)Y 3
1
6 ′′′(U ∗∗t
t

. Referring back to our goal of (11.27),
for some random variables U ∗t ,U ∗∗t
what happens when we subtract these two identities and take expectations?
The (U t) terms cancel. The next difference is

E[′(U t)(X t −

Y t)]

E[′(U t)]

E[X t −

Y t]



·
where the ﬁrst equality used that U t is independent of X t and Y t, and the
second equality used the matching 1st moments of X t and Y t. An identical
argument, using matching 2nd moments, shows that the shows that the dif-
ference of the quadratic terms disappears in expectation. Thus we’re left only
with the “error term”:





·

E[′(U t)]

0

0,

E[(U t +

X t)

(U t +

−

Y t)]

∣
∣



≤

∣
∣

1
6
1
∣
∣
6 ‖

E[′′′(U ∗t )X 3
′′′(U ∗∗t
t −
3]
′′′
Y t|
X t|

‖∞ ·

(E[

E[

+

)Y 3
t ]
3]),

|

|

∣
∣

where the last step used the triangle inequality. This conﬁrms (11.27) and
completes the proof.


We can now give a Berry–Esseen-type corollary by taking the Y i’s to be

Gaussians:

Variant Berry–Esseen Theorem. In the setting of the Berry–Esseen Theo-
rem, for all C 3 functions  :

,

→

E[(S)]

−

E[(Z)]

1
6 (1

2

+

≤

2
π )

‖

′′′

γ

≤

.433

′′′

‖

‖∞ ·

γ.

‖∞ ·



∣
∣

∣
∣

Proof. Applying the preceding theorem with Y i ∼
N(0, 1)), it sufﬁces to show that

N(0, σ2

i ) (and hence SY ∼

γX Y 

n

(

1
i

∑

X i‖

‖

3
3 + ‖

Y i‖

3
3)

≤

(1

+

2

2
π )

γ

·



(1

+

2

2
π )


Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



·

1 ‖

i

∑

X i‖

n

3
3.

(11.28)



<!-- pdf-page: 30 -->
356

11. Gaussian space and Invariance Principles

3
In particular, we just need to show that
3 for each i. This
holds because Gaussians are extremely reasonable; by explicitly computing
3rd absolute moments we indeed obtain

Y i‖

X i‖

3
3 ≤



2
π ‖

2

‖

Y i‖

‖

3
3 

σ3
i ‖

N(0, 1)

3
3 

‖

2



2

π σ3

i 

2
π ‖

X i‖

3
2 ≤

2

2





2
π ‖

X i‖

3
3.



This version of the Berry–Esseen Theorem is incomparable with the stan-
dard version. Sometimes it can be stronger; for example, if for some reason
we wanted to show E[cos S]
E[cos Z] then the Variant Berry–Esseen Theo-
rem gives this with error .433γ, whereas it can’t be directly deduced from the
standard Berry–Esseen at all. On the other hand, as we’ll see shortly, we can
only obtain the standard Berry–Esseen conclusion from the Variant version
with an error bound of O(γ1/4) rather than O(γ).

≈

We end this section by describing the “hacks” which let us extend the
Variant Berry–Esseen Theorem to cover certain non-C 3 tests . As mentioned
the idea is to smooth them out, or “mollify” them:

Proposition 11.58. Let  :
exists
satisfying

η :
k
+. Here Ck is a constant depending only on k, and

derivative of

η‖∞ ≤

cη and

η.

→









‖

be c-Lipschitz. Then for any η
0 there

(k)
1 for each
Ck c/ηk
−
η denotes the kth

η ‖∞ ≤

(k)

‖

→
−


η(s)

E
N(0,1)

[(s

+



g

∼



The proof of this proposition is straightforward, taking



ηg)]; see Exercise 11.38.

As η

also a larger and larger value of

0 this gives a better and better smooth approximation to , but
. Trading these off gives the following:

→

′′′η ‖∞

‖

Corollary 11.59. In the setting of the Invariance Principle for Sums of Ran-
dom Variables, if we merely have that  :

is c-Lipschitz, then



→

E[(S X )]

E[(SY )]

−

O(c)

≤

γ1/3
X Y .

·

Proof. Applying the Invariance Principle for Sums of Random Variables with
the test

η from Proposition 11.58 we get

∣
∣

∣
∣

E[

η(S X )]

E[

η(SY )]

−


η −

‖



But



∣
∣

cη implies

η(S X )]

‖∞ ≤
E[


E[(S X )]

−

O(c/η2)

γX Y .

·

≤

∣
∣

E[

|

≤

η(S X )

(S X )

cη

]

|

≤

−

and similarly for SY . Thus we get


∣
∣

∣
∣

E[(S X )]

E[(SY )]

−

≤


O(c)

which yields the desired bound by taking η

∣
∣

∣
∣



(η

·
+
γ1/3
X Y .

γX Y /η2)



Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 31 -->
11.6. The Invariance Principle

357

Remark 11.60. It’s obvious that the dependence on c in this theorem should
be linear in c; in fact, since we can always divide  by c it would have sufﬁced
to prove the theorem assuming c

1.



|

s



 |

−
1s

dist[

and (s)

This corollary covers all Lipschitz tests, which sufﬁces for the functions
(s)
1,1](s) from Figure 11.1. However, it still isn’t
enough for the test (s)
u – i.e., for establishing cdf-closeness as in the
usual Berry–Esseen Theorem. Of course, we can’t hope for a smooth approxi-
η for all s because of the discontinuity at u.
mator
u| ≤
η]
However, as suggested in Figure 11.2, if we’re willing to exclude s
we can get an approximator with third derivative bound O(1/η3), and thereby
obtain (Exercises 11.41, 11.42):

η satisfying

η(s)

η, u

1s

[u



−

−

+







≤

≤

|

Corollary 11.61. In the setting of the Invariance Principle for Sums of Ran-
dom Variables, for all u

we have



for ≤

O(γ1/4

u

Pr[SY ≤

Pr[S X ≤
+
X Y ); i.e., S X and SY have Lévy distance dL(S X , SY )

Pr[SY ≤

u]

−

−

≤

≤

+

u

≤]

≤]

≤

≤

≤

O(γ1/4

X Y ).


Finally, in the Berry–Esseen setting where SY ∼

the “anticoncentration” of Gaussians:

N(0, 1), we can appeal to

Pr[N(0, 1)

u

≤]

Pr[N(0, 1)

u]

Pr[u

N(0, 1)

u

≤]



≤

+
+
≤]. This lets us convert the Lévy distance
and similarly for Pr[N(0, 1)
bound into a cdf-distance bound. Recalling (11.28), we immediately deduce
the following weaker version of the classical Berry–Esseen Theorem:

≤
u

≤

−



≤

+

≤

≤

+

Pr[N(0, 1)

u]

≤
p2π

,

Corollary 11.62. In the setting of the Berry–Esseen Theorem, for all u

Pr[S

u]

Pr[Z

≤
) hides a universal constant.

≤

−

|

O(γ1/4),

u

| ≤

where the O(

·

,



Although the error bound here is weaker than necessary by a power of 1/4,
this weakness will be more than made up for by the ease with which the
Replacement Method generalizes to other settings. In the next section we’ll
see it applied to nonlinear polynomials of independent random variables. Ex-
ercise 11.46 outlines how to use it to give a Berry–Esseen theorem for sums
of independent random vectors; as you’ll see, other than replacing Taylor’s
theorem with its multivariate form, hardly a symbol in the proof changes.

11.6. The Invariance Principle

Let’s summarize the Variant Berry–Esseen Theorem and proof from the pre-
ceding section, using slightly different notation. (Speciﬁcally, we’ll rewrite
X i 

σi.) We showed that if x1, . . . , xn, y1, . . . , yn

ai xi where Var[xi]

1, so ai  ±



Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 32 -->
358

11. Gaussian space and Invariance Principles

are independent mean-0, variance-1 random variables, reasonable in the
sense of having third absolute moment at most B, and if a1, . . . , an are real
constants assumed for normalization to satisfy

1, then

i a2

i 
an yn,
an xn ≈
with error bound proportional to B max{

a1x1 + · · · +

a1 y1 + · · · +


}.

|

ai|
an xn is (roughly)
We think of this as saying that the linear form a1x1 + · · · +
invariant to what independent mean-0, variance-1, reasonable random vari-
ables are substituted for the xi’s, so long as all
’s are “small” (compared to
the overall variance). In this section we generalize this statement to degree-
k aS xS. The appropriate generaliza-
k multilinear polynomial forms,
tion of the condition that “all
’s are small” is the condition that all “in-
ai|

i a2
S are small. We refer to these nonlinear generalizations of
ﬂuences”
Berry–Esseen as Invariance Principles.

ai|

|≤

S

S

3

|

|

|



In this section we’ll develop the most basic Invariance Principle, which
involves replacing bits by Gaussians for a single Boolean function f . We’ll
show that this doesn’t change the distribution of f much provided f has small
inﬂuences and provided that f is of “constant degree” – or at least, provided f
is uniformly noise-stable so that it’s “close to having constant degree”. In-
variance Principles in much more general settings are possible – for example
Exercises 11.48 and 11.49 describe variants which handle several functions
applied to correlated inputs, and functions on general product spaces. Here
we’ll just focus on the simplest possible Invariance Principle, which is already
sufﬁcient for the proof of the Majority Is Stablest Theorem in Section 11.7.

Let’s begin with some notation.

Deﬁnition 11.63. Let F be a formal multilinear polynomial over the se-
quence of indeterminates x

(x1, . . . , xn):


F(x)

F(S)

xi,



[n]

S
⊆
∑



S
i

∏

where the coefﬁcients

F(S) are real numbers. We introduce the notation

Var[F]




S
6
∑

F(S)2,

Infi[F]

F(S)2.



i
S
3
∑



Remark 11.64. To justify this notation, we remark that we’ll always con-
sider F applied to a sequence z
(z1, . . . , zn) independent random variables
1. Under these circumstances the collection of
satisfying E[zi]

monomial random variables
S zi is orthonormal and so it’s easy to see
(cf. Chapter 8.2) that

0, E[z2
i ]







i

E[F(z)]

F(





), E[F(z)2]



F(S)2, Var[F(z)]

Var[F]





F(S)2.





We also have E[Varzi [F(z)]]



F(S)2, though we won’t use this.



S

i


Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



3





[n]

S
⊆
∑

Infi[F]

S
6
∑



<!-- pdf-page: 33 -->
11.6. The Invariance Principle

359

As in the Berry–Esseen Theorem, to get good error bounds we’ll need our
random variables zi to be “reasonable”. Sacriﬁcing generality for simplicity
in this section, we’ll take the bounded 4th-moment notion from Deﬁnition 9.1
which will allow us to use the basic Bonami Lemma (more precisely, Corol-
lary 9.6):

Hypothesis 11.65. The random variable zi satisﬁes E[zi]
E[z3
i ]

0, E[z2
i ]
0, and is “9-reasonable” in the sense of Deﬁnition 9.1; i.e., E[z4
i ]



1,


9.



≤

The main examples we have in mind are that each zi is either a uniform
1
random bit or a standard Gaussian. (There are other possibilities, though;
e.g., zi could be uniform on the interval [

p3, p3].)

±

−

We can now prove the most basic Invariance Principle, for low-degree

multilinear polynomials of random variables:

Basic Invariance Principle. Let F be a formal n-variate multilinear poly-
nomial of degree at most k

,


F(x)



S

[n],
S
|
∑

⊆

k

|≤

F(S)

xi.

S
i

∏





(x1, . . . , xn) and y

Let x
variables, each satisfying Hypothesis 11.65. Assume  :
′′′′

(y1, . . . , yn) be sequences of independent random
is C 4 with

C. Then

→



‖

‖∞ ≤

E[(F(x))]

E[(F(y))]

−

9k

C
12 ·

·

≤

∣
∣

∣
∣

Inft[F]2.

(11.29)

n

1
t

∑

Remark 11.66. The proof will be very similar to the one we used for Berry–
Esseen except that we’ll take a 3rd-order Taylor expansion rather than a
2nd-order one (so that we can use the easy Bonami Lemma). As you are asked
to show in Exercise 11.47, had we only required that  be C 3 and that the
xi’s and yi’s be (2, 3, ρ)-hypercontractive with 2nd moment equal to 1, then
we could obtain

E[(F(x))]

E[(F(y))]

−

‖

′′′
3

‖∞

·

≤

(1/ρ)3k

·

1
t

∑
Proof. The proof uses the Replacement Method. For 0

∣
∣

∣
∣

n

Inft[F]3/2.

n we deﬁne

t

≤

≤

F(y1, . . . , yt, xt

H t 
H n. We will show that

+

1, . . . , xn),

so F(x)



H0 and F(y)


E[(H t

1)

−

−

(H t)]

9k

C
12 ·

·

≤

Inft[F]2;

(11.30)

∣
as in our proof of the Berry–Esseen Theorem, this will complete the proof
∣
after summing over t and using the triangle inequality. To analyze (11.30)

∣
∣

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 34 -->
360

11. Gaussian space and Invariance Principles

we separate out the part of F(x) that depends on xt; i.e., we write F(x)
EtF(x)


xtDtF(x), where the formal polynomials EtF and DtF are deﬁned by

+

EtF(x)



F(S)

xi,

DtF(x)

t
S
63
∑



S
i

∏



t
S
3
∑

F(S)

i



S\{t}

∏

xi.

Note that neither EtF nor DtF depends on the indeterminate xt; thus we can
deﬁne

U t 
∆∆∆t 

so that

EtF(y1, . . . , yt
−
DtF(y1, . . . , yt

1,
1,

−

·

·

, xt
+
, xt

1, . . . , xn),
1, . . . , xn),

+

∆∆∆t xt,

∆∆∆t yt.

1

1

1

1

1

−

+



+



1)

H t

t +

t +

t +

t +

1 

(H t

(U t)

(U t)

U t +

H t 

t x4
24 ′′′′(U ∗t )∆∆∆4
t
t y4
)∆∆∆4
1
24 ′′′′(U ∗∗t
t

t x2
t y2

−
(H t)

2 ′′(U t)∆∆∆2
2 ′′(U t)∆∆∆2

′(U t)∆∆∆t xt +
′(U t)∆∆∆t yt +

U t +
We now use a 3rd-order Taylor expansion to bound (11.30):
6 ′′′(U t)∆∆∆3
6 ′′′(U t)∆∆∆3

t x3
t y3
for some random variables U ∗t and U ∗∗t
. As in the proof of the Berry–Esseen
Theorem, when we subtract these and take the expectation there are signiﬁ-
cant simpliﬁcations. The 0th-order terms cancel. As for the 1st-order terms,
E[′(U t)∆∆∆t xt−
The second equality here crucially uses the fact that xt, yt are independent of
U t, ∆∆∆t. The ﬁnal equality only uses the fact that xt and yt have matching 1st
moments (and not the stronger assumption that both of these 1st moments
are 0). The 2nd- and 3rd-order terms will similarly cancel, using the fact that
xt and yt have matching 2nd and 3rd moments. Finally, for the “error” term
we’ll just use
C and the triangle inequality; we thus
obtain

E[′(U t)∆∆∆t·

′(U t)∆∆∆t yt]

E(′(U t)∆∆∆t]

′′′′(U ∗∗t

′′′′(U ∗t )

E[xt−

(xt−

yt)]

yt]

| ≤

0.







)

,

·

|

|

|

E[(H t

1)

−

−

(H t)]

C
24 ·

≤

(E[(∆∆∆t xt)4]

E[(∆∆∆t yt)4]).

+

To complete the proof of (11.30) we now just need to bound

∣
∣

∣
∣

E[(∆∆∆t xt)4], E[(∆∆∆t yt)4]

9k

·

≤

Inft[F]2,

which we’ll do using the Bonami Lemma. We’ll give the proof for E[(∆∆∆t xt)4],
the case of E[(∆∆∆t yt)4] being identical. We have
∆∆∆t xt 

LtF(y1, . . . , yt

1, . . . , xn),

1, xt, xt

+

−

where

LtF(x)



xtDtF(x)



F(S)

xi.

t
S
3
∑

S
i

∏

Since LtF has degree at most k we can apply the Bonami Lemma (more
precisely, Corollary 9.6) to obtain
E[(∆∆∆t xt)4]

9k E[LtF(y1, . . . , yt

1, . . . , xn)2]2.

1, xt, xt



≤

−

+

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 35 -->
11.6. The Invariance Principle

361

1, xt, . . . , xn are independent with mean 0 and 2nd mo-

But since y1, . . . , yt
ment 1, we have (see Remark 11.64)
1, . . . , xn)2]

E[LtF(y1, . . . , yt

1, xt, xt

−

−

+

Thus we indeed have E[(∆∆∆t xt)4]

9k

·

≤



LtF(S)2



F(S)2

Inft[F].



[n]

S
⊆
∑

t
S
3
∑
Inft[F]2, and the proof is complete. 

̂



∣
∣

′′′′η ‖∞ ≤

‖
E[(F(x))]



−

Corollary 11.67. In the setting of the preceding theorem, if we furthermore
have Var[F]

1 and Inft[F]

≤ for all t

[n], then

≤

≤
E[(F(x))]



E[(F(y))]

−

C
12 ·

≤

k9k

≤.

·
F(S)2

Proof. We have

∣
t Inft[F]2
∣

≤

≤

t Inft[F]

∣
≤
∣

≤

S

|

S |

≤k Var[F].

≤



Corollary 11.68. In the setting of the preceding corollary, if we merely have
that  :


is c-Lipschitz (rather than C 4), then







→

E[(F(x))]

E[(F(y))]

−

O(c)

·

≤

2k≤1/4.

Proof. Just as in the proof of Corollary 11.59, by using
tion 11.58 (which has

O(c/η3)) we obtain

η from Proposi-

∣
∣

The proof is completed by taking η

∣
∣



4

E[(F(y))]

O(c)

(η

≤
∣
k9k≤
∣

≤

·

+
2k≤1/4.




k9k≤/η3).



Let’s connect this last corollary back to the study of Boolean functions.
1, 1}n
has ≤-small inﬂuences (in the sense of Deﬁnition 6.9)
Suppose f : {
and degree at most k. Letting g
(g1, . . . , gn) be a sequence of independent
standard Gaussians, Corollary 11.68 tells us that for any Lipschitz  we have

→

−



E
1,1}n
{
−

x

∼

[( f (x))]

E
N(0,1)n

−

g

∼

[( f (g))]

O(2k≤1/4).

≤

(11.31)

Here the expression “ f (g)” is an abuse of notation indicating that the real
numbers g1, . . . , gn are substituted into f ’s Fourier expansion (multilinear
polynomial representation).

∣
∣
∣
∣

∣
∣
∣
∣

At ﬁrst it may seem peculiar to substitute arbitrary real numbers into the
Fourier expansion of a Boolean function. Actually, if all the numbers being
1, 1] then there’s a natural interpretation: as
substituted are in the range [
you were asked to show in Exercise 1.4, if µ
E[ f (y)]
µi.
where y
On the other hand, there doesn’t seem to be any obvious meaning when real
numbers outside the range [
1, 1] are substituted into f ’s Fourier expansion,
as may certainly occur when we consider f (g).

1, 1}n is drawn from the product distribution in which E[yi]

1, 1]n, then f (µ)

∼

−

−

−



−





[

{

Nevertheless, (11.31) says that when f is a low-degree, small-inﬂuence
function, the distribution of the random variable f (g) will be close to that
1, 1} is Boolean-valued and unbiased.
of f (x). Now suppose f : {

1, 1}n

{

−
Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.

→

−



<!-- pdf-page: 36 -->
362

11. Gaussian space and Invariance Principles

−

Then (11.31) might seem impossible; how could the continuous random vari-
able f (g) essentially be
1 with probability 1/2?
1 with probability 1/2 and
The solution to this mystery is that there are no low-degree, small-inﬂuence,
unbiased Boolean-valued functions. This is a consequence of the OSSS In-
equality – more precisely, Exercise 8.44(b) – which shows that in this setting
1/k3 in (11.31), rendering the bound very weak. If the
we will always have ≤
Aaronson–Ambainis Conjecture holds (see the notes in Chapter 8.7), a similar
statement is true even for functions with range [

1, 1].

≥

+

−

The reason (11.31) is still useful is that we can apply it to small-inﬂuence,
low-degree functions which are almost {
1, 1]-valued. Such
functions can arise from truncating a very noise-stable Boolean-valued func-
tion to a large but constant degree. For example, we might proﬁtably ap-
k
n and then deduce some consequences for Majn(x) using
Maj≤
ply (11.31) to f
k
O(1/pk) (Corollary 5.23).
the fact that E[(Maj≤
n (x)
Let’s consider this sort of idea more generally:

1, 1}-valued, or [

Majn(x))2]

k[Majn]

W

−

−



−



≤

Corollary 11.69. Let f : {
f ≤

1, 1}n
k has ≤-small inﬂuences. Then for any c-Lipschitz  :

have Var[ f ]

→

−

≤

1. Let k

→

≥

0 and suppose
we have

E
1,1}n
{
−

x

∼

[( f (x))]

E
N(0,1)n

−

g

∼

[( f (g))]

In particular, suppose h : {
coordinates (we assume ≤

−
1, δ

1, 1}n

≤

≤

→
1
20 ). Then

∣
∣
∣
∣

O(c)

·

≤

∣
∣
∣
has Var[h]
∣



2k≤1/4

k

f 

.

‖2

+ ‖

(11.32)


1 and no (≤, δ)-notable

≤

E
1,1}n
{
−

x

∼

[(T1

−

δh(x))]

−

g

∼

E
N(0,1)n

[(T1

−

δh(g))]

≤δ/3.

O(c)

·

≤

∣
∣
∣
∣

∣
∣
∣
∣


Proof. For the ﬁrst statement we simply decompose f
left-hand side of (11.32) can be written as

k

f ≤

+

f 

k. Then the

E[( f ≤

k(x)

f 

k(x))]

+

E[( f ≤

k(g)

f 

k(g))]

−
k(x))]

+
k(g))]
E[( f ≤

∣
∣
c E[
∣

E[( f ≤

∣
∣
∣

≤

|
2k≤1/4,
using the fact that  is c-Lipschitz. The ﬁrst quantity is at most O(c)
by Corollary 11.68 (even if k is not an integer). As for the other two quantities,
Cauchy–Schwarz implies

∣
∣
∣

∣
∣
∣

−

+

+

|

|

|

·

f 

k(x)

]

c E[

f 

k(g)

],

E[

f 

k(x)

|

]

|

≤

E[ f 

k(x)2]



f (S)2

k

f 

‖2,

 ‖

and the same bound also holds for E[

S
∑|
|
k(g)
]; this uses the fact that E[ f 
f (S)2 just as in Remark 11.64. This completes the proof of (11.32).

f 







k

|

|

|
As for the second statement of the corollary, let f


tions on h imply that Var[ f ]



δh. The assump-
−
k has ≤-small inﬂuences for any k;

T1



S

|

k

k(g)2]



1 and that f ≤

≤

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 37 -->
11.6. The Invariance Principle

363

the latter is true because

Infi[ f ≤

k]



(1

i

−

δ)2

|

S

h(S)2

|

≤

i
S
3
∑

k,S
S
|≤
∑|

3


since h has no (≤, δ)-notable coordinate. Furthermore,



(1

−

δ)|

S

1

h(S)2

|−

Inf(1
i

−

δ)

[h]

≤

≤



k

f 

‖

‖

2
2 

(1

−

δ)2

|

S

h(S)2

|

(1

−

≤

δ)2k Var[h]

δ)2k

(1

−

≤

exp(

−

≤

2kδ)

k

f 

‖

‖2 ≤


exp(

−

kδ). So applying the ﬁrst part of the corollary

k

S
|
∑|
1; i.e.,

for any k
gives

≥

E[( f (x))]

−

E[( f (g))]

O(c)

·

≤

2k≤1/4

exp(

kδ)

−

+

(11.33)

for any k

∣
∣
≥

0. Choosing k



1
3 ln(1/≤), the right-hand side of (11.33) becomes





∣
∣

O(c)

≤−

(1/3) ln 2≤1/4

≤δ/3

O(c)

≤δ/3,

≤
20 (numerically, 1
1
where the inequality uses the assumption δ
4 −
This completes the proof of the second statement of the corollary.

≤

+





·

·

1
3 ln 2

≈

1
53 ).


Finally, if we think of the Basic Invariance Principle as the nonlinear
analogue of our Variant Berry–Esseen Theorem, it’s natural to ask for the
nonlinear analogue of the Berry–Esseen Theorem itself, i.e., a statement
showing cdf-closeness of F(x) and F(g). It’s straightforward to obtain a Lévy
distance bound just as in the degree-1 case, Corollary 11.61; Exercise 11.44
asks you to show the following:

Corollary 11.70. In the setting of Corollary 11.67 we have the Lévy distance
O(2k≤1/5). In the setting of Remark 11.66 we have the
bound dL(F(x), F(y))
(1/ρ)O(k)≤1/8.
bound dL(F(x), F(y))

≤
≤

Suppose we now want actual cdf-closeness in the case that y

N(0, 1)n.
In the degree-1 (Berry–Esseen) case we used the fact that degree-1 polyno-
mials of independent Gaussians have good anticoncentration. The analogous
statement for higher-degree polynomials of Gaussians is not so easy to prove;
however, Carbery and Wright [CW01, Theorem 8] have obtained the following
essentially optimal result:

∼

Carbery–Wright Theorem. Let p :
multilinear) of degree at most k, let g
Then for all ≤

0,

n

be a polynomial (not necessarily
1.

→
N(0, 1)n, and assume E[p(g)2]
∼





Pr[

p(g)

≤]

O(k≤1/k),

≤
) hides a universal constant.

| ≤

|

where the O(

·

Using this theorem it’s not hard (see Exercise 11.45) to obtain:

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 38 -->
364

11. Gaussian space and Invariance Principles

Theorem 11.71. Let f : {
inﬂuences and Var[ f ]

−

1, 1}n

→

1. Then for all u

be of degree at most k, with ≤-small


Pr[ f (x)

u]

Pr[ f (g)

|

≤
) hides a universal constant.

≤

−


u]

,

O(k)

·

| ≤

≤1/(4k

1),

+

where the O(

·

11.7. Highlight: Majority Is Stablest Theorem

{

The Majority Is Stablest Theorem (to be proved at the end of this section) was
originally conjectured in 2004 [KKMO04, KKMO07]. The motivation came
from studying the approximability of the Max-Cut CSP. Recall that Max-Cut
is perhaps the simplest possible constraint satisfaction problem: the domain
of the variables is Ω
1, 1} and the only constraint allowed is the binary

{0, 1}. As we mentioned brieﬂy in Chap-
: {
non-equality predicate,
ter 7.3, Goemans and Williamson [GW95] gave a very sophisticated efﬁcient
algorithm using “semideﬁnite programming” which (cGWβ, β)-approximates
Max-Cut for every β, where cGW ≈
.8786 is a certain trigonometric constant.

1, 1}2

−
6

→

−

δ, β

Turning to hardness of approximation, we know from Theorem 7.40 (devel-
oped in [KKMO04]) that to prove UG-hardness of (α
δ)-approximating
Max-Cut, it sufﬁces to construct an (α, β)-Dictator-vs.-No-Notables test which
uses the predicate
. As we’ll see in this section, the quality of the most nat-
ural such test can be easily inferred from the Majority Is Stablest Theorem.
Assuming that theorem (as Khot et al. [KKMO04] did), we get a surprising
conclusion: It’s UG-hard to approximate the Max-Cut CSP any better than the
Goemans–Williamson Algorithm does. In other words, the peculiar approxi-
mation guarantee of Goemans and Williamson on the very simple Max-Cut
problem is optimal (assuming the Unique Games Conjecture).

+

−

6

Let’s demystify this somewhat, starting with a description of the Goemans–
(V , E) be an n-vertex input graph for the algo-
E to denote that (v, w) is a uniformly random edge
-constraint) in the graph. The ﬁrst step of the Goemans–Williamson

Williamson Algorithm. Let G
rithm; we’ll write (v, w)
(i.e.,
Algorithm is to solve following optimization problem:

6

∼



maximize

E
(v,w)
∼
subject to ~U : V

E



→

~U(v), ~U(w)

1
2 −
Sn

−

1
2 〈
1.

〉



(SDP)

−

1 denotes the set of all unit vectors in

Here Sn
n. Somewhat surprisingly,
since this optimization problem is a “semideﬁnite program” it can be solved
in polynomial time using the Ellipsoid Algorithm. (Technically, it can only be
solved up to any desired additive tolerance ≤
0, but we’ll ignore this point.)
Let’s write SDPOpt(G) for the optimum value of (SDP), and Opt(G) for the



Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 39 -->
11.7. Highlight: Majority Is Stablest Theorem

365

optimum Max-Cut value for G. We claim that (SDP) is a relaxation of the
Max-Cut CSP on input G, and therefore

SDPOpt(G)

Opt(G).

≥

To see this, simply note that if F ∗ : V
(“cut”) for G then we can deﬁne ~U(v)
and achieve the optimal cut value ValG(F ∗) in (SDP).

→
(F ∗(v), 0, . . . , 0)

{
−





1, 1} is an optimal assignment
V

1 for each v

Sn

−



The second step of the Goemans–Williamson Algorithm might look famil-
iar from Fact 11.7 and Remark 11.8. Let ~U ∗ : V
1 be the optimal solu-
tion for (SDP), achieving SDPOpt(G); abusing notation we’ll write ~U ∗(v)
~v.
N(0, 1)n at random and outputs the assign-
The algorithm now chooses ~g
ment (cut) F : V
). Let’s analyze the
(expected) quality of this assignment. The probability the algorithm’s assign-
ment F cuts a particular edge (v, w)

1, 1} deﬁned by F(v)

~v,~g
〈

sgn(

E is

Sn

→

→

∼



−



−

〉

{

Pr
N(0,1)n

~g

[sgn(

)

〉

6

sgn(

~w,~g

)].

〈

〉


~v,~g
〈

∼
sgn(z′) when (z, z′) is a pair
This is precisely the probability that sgn(z)
[0, π] for the
of
angle between the unit vectors ~v, ~w, we conclude from Sheppard’s Formula
(see (11.2)) that

-correlated 1-dimensional Gaussians. Writing ∠(~v, ~w)

~v, ~w
〈

6



〉

[F cuts edge (v, w)]

Pr
~g

∠(~v, ~w)
π

.



By linearity of expectation we can compute the expected value of the algo-
rithm’s assignment F:

[ValG(F)]

E
~g



E
(v,w)

∠(~v, ~w)/π

.

E

∼


On the other hand, by deﬁnition we have



SDPOpt(G)



E
(v,w)

∼

E

1
2 −

1
2 cos∠(~v, ~w)

.





It remains to compare (11.34) and (11.35). Deﬁne

θ/π
1
2 cos θ  ≈
Then from (11.34) and (11.35) we immediately get

min
θ


cGW 

1
2 −

[0,π] 

.8786.

(11.34)

(11.35)

(11.36)

E
~g

[ValG(F)]

cGW ·

≥

SDPOpt(G)

cGW ·

≥

Opt(G);

i.e., in expectation the Goemans–Williamson Algorithm delivers a cut of
In other words, it’s a (cGWβ, β)-
value at least cGW times the Max-Cut.
approximation algorithm, as claimed. By being a little bit more careful about
this analysis (Exercise 11.33) you can show following additional result:

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 40 -->
366

11. Gaussian space and Invariance Principles

[θ∗, π], where θ∗

.74π is the minimizing θ
Theorem 11.72. [GW95]. Let θ
θ). Then on any
in (11.36) (also deﬁnable as the positive solution of tan(θ/2)
1
1
2 cos θ, the Goemans–Williamson Algorithm
graph G with SDPOpt(G)
2 −
produces a cut of (expected) value at least θ/π. In particular, the algorithm is
a (θ/π, 1

1
2 cos θ)-approximation algorithm for Max-Cut.

≥

≈





2 −

Example 11.73. Consider the Max-Cut problem on the 5-vertex cycle graph 5.
4
5 .
The best bipartition of this graph cuts 4 out of the 5 edges; hence Opt( 5)
Exercise 11.32 asks you to show that taking
5 , sin 4πv
5 ),

(cos 4πv

~U(v)



v

 5,



1

≥

1
2 −

2 cos 4π
5 .
in the semideﬁnite program (SDP) establishes that SDPOpt( 5)
(These are actually unit vectors in 2 rather than in 5 as (SDP) requires,
but we can pad out the last three coordinates with zeroes.) This exam-
ple shows that the Goemans–Williamson analysis in Theorem 11.72 lower-
bounding Opt(G) in terms of SDPOpt(G) cannot be improved (at least when
4
5 ). This is termed an optimal integrality gap. In fact, Theo-
SDPOpt(G)
rem 11.72 also implies that SDPOpt( 5) must equal 1
5 , for if it were
2 −
4
5 . Note that the
greater, the theorem would falsely imply that Opt( 5)
Goemans–Williamson Algorithm actually ﬁnds the maximum cut when run
on the cycle graph 5. For a related example, see Exercise 11.35.

2 cos 4π




1

Now we explain the result of Khot et al. [KKMO04], that the Majority Is
Stablest Theorem implies it’s UG-hard to approximate Max-Cut better than
the Goemans–Williamson Algorithm does:

Theorem 11.74. [KKMO04]. Let θ
to (θ/π

1
2 cos θ)-approximate Max-Cut.

δ, 1



+

2 −

( π
2 , π). Then for any δ

0 it’s UG-hard



Proof. It follows from Theorem 7.40 that we just need to construct a (θ/π, 1
2 −
1
2 cos θ)-Dictator-vs.-No-Notables test using the predicate
. (See Exercise 11.36
for an extremely minor technical point.) It’s very natural to try the following,
with β

6

1
2 −



1
2 cos θ



( 1
2 , 1):

β-Noise Sensitivity Test. Given query access to f : {

1, 1}n

−

{
−

→

1, 1}:

{

Choose x
∼
with probability β

cos θ-correlated strings. (Note that cos θ

1, 1}n and form x′ by reversing each bit of x independently
1
2 cos θ. In other words let (x, x′) be a pair of

1
2 −

−

0.)



Query f at x, x′.

Accept if f (x)

f (x′).

6

•

•

•

By design,

Pr[the test accepts f ]

NSβ[ f ]



1
2 −



1
2 Stabcos θ[ f ].

(11.37)

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 41 -->
11.7. Highlight: Majority Is Stablest Theorem

367

(We might also express this as “RS f (θ)”.) In particular, if f is a dictator,
1
it’s accepted with probability exactly β
2 cos θ. To complete the proof
1
that this is a (θ/π, 1
2 cos θ)-Dictator-vs.-No-Notables test, let’s suppose f :
1, 1}n
1, 1] has no (≤, ≤)-notable coordinates and show that (11.37) is at
[
{
−
−
most θ/π
o≤(1). (Regarding f having range [

1, 1], recall Remark 7.38.)

1
2 −

2 −



→
+

−

At ﬁrst it might look like we can immediately apply the Majority Is Sta-
blest Theorem; however, the theorem’s inequality goes the “wrong way” and
the correlation parameter ρ
cos θ is negative. These two difﬁculties actually
cancel each other out. Note that



Pr[the test accepts f ]

1
2 −
1
2 −

1
2 +

1
2 +





≤



n

0
k

∑

1
2

1
2

1
2 Stabcos θ[ f ]

(cos θ)kWk[ f ]

(

cos θ)kWk[ f ]

−
cos θ[ f odd],

k odd
∑
1
2 Stab

−

(since cos θ

0)



(11.38)

1, 1] is the odd part of f (see Exercise 1.8) deﬁned by

where f odd : {

−

1, 1}n

[
−
→
f odd(x)

1
2 ( f (x)



x))

f (

−



−

f (S) xS.

odd

S
|
∑|



Now we’re really in a position to apply the Majority Is Stablest Theorem
0, and f odd has no (≤, ≤)-notable coor-
to f odd, because

dinates (since it’s formed from f by just dropping some terms in the Fourier
expansion). Using

θ), the result is that

(0, 1), E[ f odd]

cos(π

cos θ

cos θ

−



Stab

−

cos θ[ f odd]

1

−

≤

−



−
2
π arccos(cos(π

θ))

−

+

o≤(1)

2θ/π

1

+

−



o≤(1).

Putting this into (11.38) yields

Pr[the test accepts f ]

1
2 +

≤

1
2 (2θ/π

1

+

−

o≤(1))

θ/π

+



o≤(1),

as needed.



Remark 11.75. There’s actually still a mismatch between the algorithmic
guarantee of Theorem 11.72 and the UG-hardness result Theorem 11.74, con-
β / .8446
cerning the case of θ
– neither result is sharp; see O’Donnell and Wu [OW08].

( π
2 , θ∗). In fact, for these values of θ – i.e., 1

2 ≤



1
Remark 11.76. If we want to prove UG-hardness of (θ′/π
2 cos θ′)-
approximating Max-Cut, we don’t need the full version of Borell’s Isoperi-
metric Theorem; we only need the volume- 1
θ′.
−
3
Corollary 11.44 gave a simple proof of this result for θ
4 π.

This yields UG-hardness of ( 3
1
)-approximating Max-Cut. The ratio
2p2
between α and β here is approximately .8787, very close to the Goemans–
Williamson constant cGW ≈

2 case with parameter θ


π
4 , hence θ′

.8786.

δ, 1

δ, 1

2 −

4 +

2 +

+



π

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 42 -->
368

11. Gaussian space and Invariance Principles

Finally, we will prove the General-Volume Majority Is Stablest Theorem,
by using the Invariance Principle to reduce it to Borell’s Isoperimetric Theo-
rem.

General-Volume Majority Is Stablest Theorem. Let f : {
≤, or more generally, that f has no (≤,
Suppose that MaxInf[ f ]
≤
coordinates. Then for any 0

1,

ρ

1, 1}n
[0, 1].
−
→
1
log(1/≤) )-notable

Stabρ[ f ]

≤


Λρ(E[ f ])

≤
) bound has no dependence on ρ.)

+



O

log log(1/≤)
log(1/≤)

ρ .

1

−

1

·



(11.39)

(Here the O(

·

Proof. The proof involves using the Basic Invariance Principle twice (in the
form of Corollary 11.69). To facilitate this we introduce f ′
δ f , where
(with foresight) we choose

T1



−

δ

3 log log(1/≤)

log(1/≤) ≥



1
log(1/≤) .

(We may assume ≤ is sufﬁciently small so that 0
E[ f ] and that

δ



≤

1
20 .) Note that E[ f ′]



Stabρ[ f ′]



[n]

S
⊆
∑

But

Stabρ(1

δ)2[ f ]

−

−

Stabρ[ f ]

S

ρ|

|(1

−

δ)2

|

S

|

f (S)2

Stabρ(1

δ)2[ f ].

−





(ρ

−

≤

ρ(1

−

δ)2)

1

−

1

·

ρ ·

Var[ f ]

2δ

1

−

ρ

1

·

≤

(11.40)

∣
∣

by Exercise 2.46, and with our choice of δ this can be absorbed into the error
of (11.39). Thus it sufﬁces to prove (11.39) with f ′ in place of f .

∣
∣

Let Sq :

be the continuous function which agrees with t

→


[0, 1] and is constant outside [0, 1]. Note that Sq is 2-Lipschitz. We will apply
the second part of Corollary 11.69 with “h” set to Tpρ f (and thus T1
Tpρ f ′). This is valid since the variance and (1
only smaller than those of f . Thus


δ)-stable inﬂuences of h are

δh

7→

−

−

t2 for t

E
1,1}n
{
−

x

∼

∣
∣
∣
∣

[Sq(Tpρ f ′(x))]

−

g

E
N(0,1)n

[Sq(Tpρ f ′(g))]

O(≤δ/3)

O



1
log(1/≤)

,

≤

∼

(11.41)
using our choice of δ. (In fact, it’s trading off this error with (11.40) that led
to our choice of δ.) Now Tpρ f ′(x)
δ)pρ f (x) is always bounded in [0, 1], so

T(1





∣
∣
∣
∣



−

Sq(Tpρ f ′(x))

(Tpρ f ′(x))2



⇒

E
1,1}n
−

{

x

∼

[Sq(Tpρ f ′(x))]

Stabρ[ f ′].



Furthermore, Tpρ f ′(g) is the same as Upρ f ′(g) because f ′ is a multilinear
polynomial. (Both are equal to f ′(ρ g); see Fact 11.13.) Thus in light of (11.41),
to complete the proof of (11.39) it sufﬁces to show

E
N(0,1)n

g

∼

[Sq(Upρ f ′(g))]

Λρ(E[ f ′])

≤

O

+

1
log(1/≤)

.

(11.42)





Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 43 -->
11.7. Highlight: Majority Is Stablest Theorem

369

Deﬁne the function F :

n

→

[0, 1] by

F(g)



trunc[0,1]( f ′(g))

0

if f ′(g)

f ′(g)

if f ′(g)

1

if f ′(g)






0,

[0, 1],

1.








We will establish the following two inequalities, which together imply (11.42):

g

∼

∣
∣
∣
∣

E
N(0,1)n

[Sq(Upρ f ′(g))]

E
N(0,1)n

−

g

∼

[Sq(Upρ F(g))]

E
N(0,1)n

g

∼

[Sq(Upρ F(g))]

Λρ(E[ f ′])

≤

∣
∣
∣
O
∣

+

O

≤

1
log(1/≤)

,


1
log(1/≤)

.







(11.43)

(11.44)

Both of these inequalities will in turn follow from

E
N(0,1)n

[

|

f ′(g)

F(g)

]

|

−

E
N(0,1)n



g

∼

g

∼

[dist[0,1]( f ′(g))]

O

≤

1
log(1/≤)

.

(11.45)

Let’s show how (11.43) and (11.44) follow from (11.45), leaving the proof
of (11.45) to the end. For (11.43),





E[Sq(Upρ f ′(g))]

E[Sq(Upρ F(g))]

−

2 E[

2 E[

|

|

≤

≤

∣
∣
∣

∣
∣
∣

Upρ f ′(g)

Upρ F(g)

]

−
F(g)

f ′(g)

−

O

]

|

≤

|
1
log(1/≤)

,



where the ﬁrst inequality used that Sq is 2-Lipschitz, the second inequality
used the fact that Upρ is a contraction on L1(
n, γ), and the third inequality
was (11.45). As for (11.44), Upρ F is bounded in [0, 1] since F is. Thus
E[(Upρ F(g))2]

E[Sq(Upρ F(g))]

Λρ(E[F(g)]),

Stabρ[F]





≤
where we used Borell’s Isoperimetric Theorem. But
O
This establishes (11.44).

1
log(1/≤)



|





by (11.45), and Λρ is easily shown to be 2-Lipschitz (Exercise 11.19(e)).

E[F(g)]

E[ f ′(g)]

−

| ≤

It therefore remains to show (11.45), which we do by applying the Invari-
ance Principle one more time. Taking  to be the 1-Lipschitz function dist[0,1]
in Corollary 11.69 we deduce

E
N(0,1)n

g

∼

[dist[0,1]( f ′(g))]

−

x

E
1,1}n
−

{

∼

[dist[0,1]( f ′(x))]

But E[dist[0,1] f ′(x)]

lishes (11.45) and completes the proof.

0 since f ′(x)



T1

−

δ f (x)



∣
∣
∣
∣

O(≤δ/3)

O



1
log(1/≤)

.

≤

∣
∣
∣
∣





[0, 1] always. This estab-


We conclude with one more application of the Majority Is Stablest Theo-
rem. Recall Kalai’s version of Arrow’s Theorem from Chapter 2.5, i.e., Theo-
rem 2.56. It states that in a 3-candidate Condorcet election using the voting
1, 1}, the probability of having a Condorcet winner – often
rule f : {
called a rational outcome – is precisely 3
3
1/3[ f ]. As we saw in the
4 Stab
proof of Theorem 11.74 near (11.38), this is in turn at most 3
4 Stab1/3[ f odd],
with equality if f is already odd. It follows from the Majority Is Stablest

1, 1}n

4 −

4 +

→

−

−

−

{

3

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 44 -->
370

11. Gaussian space and Invariance Principles

Theorem that among all voting rules with ≤-small inﬂuences (a condition all
reasonable voting rules should satisfy), majority rule is the “most rational”.
Thus we see that the principle of representative democracy can be derived
using analysis of Boolean functions.

11.8. Exercises and notes

11.1 Let A be the set of all functions f :

n

nations of indicator functions of boxes. Prove that A is dense in L1(

→

which are ﬁnite linear combi-
n, γ).

11.2 Fill in proof details for the Gaussian Hypercontractivity Theorem.

11.3 Prove Fact 11.13. (Cf. Exercise 2.25.)
11.4 Show that Uρ1Uρ2 
11.5 Prove Proposition 11.16. (Hint: For ρ

Uρ1ρ2 for all ρ1, ρ2 
6

Uρ f (z) and show
that g(z/ρ) is a smooth function using the relationship between convolu-
tion and derivatives.)



[

1, 1]. (Cf. Exercise 2.32.)

−
0, write g(z)

11.6 (a) Prove Proposition 11.17. (Hint: First prove it for bounded continu-

ous f ; then make an approximation and use Proposition 11.15.)

(b) Deduce more generally that for f

L1(

n, γ) the map ρ

“strongly continuous” on [0, 1], meaning that for any ρ

Uρ f is
[0, 1] we have

7→



Uρ′ f

‖

−

Uρ f

‖1 →

0 as ρ′

→


ρ. (Hint: Use Exercise 11.4.)

11.7 Complete the proof of Proposition 11.26 by establishing the case of gen-

eral n.

11.8 Complete the proof of Proposition 11.28 by establishing the case of gen-

eral n.

11.9 (a) Establish the alternative formula (11.10) for the probabilists’ Hermite
polynomials H j(z) given in Deﬁnition 11.29; equivalently, establish
the formula

H j(z)

(



−

1) j exp( 1

2 z2)

·

j

exp(

1

2 z2).

−

d
dz 


(Hint: Complete the square on the left-hand side of (11.8); then differ-
entiate j times with respect to t and evaluate at 0.)

(b) Establish the recursion

H j(z)

(z

−



d
dz )H j

1(z)

−

⇐⇒

h j(z)

1
p j ·



d
dz )h j

1(z)

−

(z

−
dz ) j1.

d

for j



+, and hence the formula H j(z)

(z



−

(c) Show that h j(z) is an odd function of z if j is odd and an even function

of z if j is even.

11.10 (a) Establish the derivative formula for Hermite polynomials:

H′j(z)

j

H j

1(z)

⇐⇒
Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.







−

−

·

·

h′j(z)

j

h j

1(z).


