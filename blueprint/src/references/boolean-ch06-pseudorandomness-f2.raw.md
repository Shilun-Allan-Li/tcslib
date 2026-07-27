<!-- generated-by: proofmatch local extraction -->
<!-- source-pdf-sha256: 6c10bfcc80801303a586f415265bdc336a4336277b45067f4b9b852d23df2f63 -->
<!-- extractor: pdfminer.six v20260107 -->

<!-- pdf-page: 1 -->
Chapter 6

Pseudorandomness and
F2-polynomials

In this chapter we discuss various notions of pseudorandomness for Boolean
functions; by this we mean properties of a ﬁxed Boolean function that are
in some way characteristic of randomly chosen functions. We will see some
deterministic constructions of pseudorandom probability density functions
with small support; these have algorithmic application in the ﬁeld of deran-
domization. Finally, several of the results in the chapter will involve interplay
between the representation of f : {0, 1}n
{0, 1} as a polynomial over the reals
and its representation as a polynomial over F2.

→

6.1. Notions of pseudorandomness

→
1, 1} is that all of its Fourier coefﬁcients are very small (as we saw in Exer-
1, 1}n
) will not

The most obvious spectral property of a truly random function f : {
{
−
cise 5.8). Let’s switch notation to f : {
be very small but rather very close to 1/2. Generalizing:

{0, 1}; in this case f (

→

;

−

−

1, 1}n

Proposition 6.1. Let n
function; i.e., each f (x) is 1 with probability p and 0 with probability 1
1, 1}n. Then except with probability at most 2−
independently for all x
of the following hold:

{0, 1} be a p-biased random
p,
−
n, all

1 and let f : {

{
−

→

>

−

∈

1, 1}n

f (

)
;

|

−

p

| ≤

2pn2−

n/2,

S

∀

6= ; |

f (S)

| ≤

2pn2−

n/2.

b

Proof. We have
independent. If S
b

f (S)

x

1

b
2n xS f (x), where the random variables f (x) are
=
, then the coefﬁcients 1
2n xS sum to 1 and the mean
= ;

P

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.

143



<!-- pdf-page: 2 -->
144

6. Pseudorandomness and F2-polynomials

f (S) is p; otherwise the coefﬁcients sum to 0 and the mean of

of
Either way we may apply the Hoeffding bound to conclude that

f (S) is 0.

b

f (S)

Pr[
|

E[

−

f (S)]

t]

2 exp(

t2
−
| ≥
n/2, the above bound is 2 exp(

1)
−

2n

≤

·

b

for any t
=
The result follows by taking a union bound over all S

0. Selecting t

2pn2−
b

>

b

2n)

−

4−

n.
(cid:3)

≤

[n].

⊆

This proposition motivates the following basic notion of “pseudorandom-

ness”:

Deﬁnition 6.2. A function f : {
f (S)
²-uniform) if

1, 1}n
−
.
6= ;
Remark 6.3. By Exercise 3.9, every function f is ²-regular for ²
b
1, 1}n
are often concerned with f : {

² for all S

| ≤

→

[

|

1, 1], in which case we focus on ²

R is ²-regular (sometimes called

= k

f

1. We
k
1.

≤

−

→

−

Example 6.4. Proposition 6.1 states that a random p-biased function is
n/2)-regular with very high probability. A function is 0-regular if and
(2pn2−
only if it is constant (even though you might not think of a constant func-
tion as very “random”). If A
2 is an afﬁne subspace of codimension k
k-regular (Proposition 3.12). For n even the inner product
then 1A is 2−
mod 2 function and the complete quadratic function, IPn, CQn : Fn
{0, 1},
n/2
1-regular (Exercise 1.1). On the other hand, the parity functions
are 2−
−
1, 1}n
χS : {
). By
→
Exercise 5.21, Majn is 1
pn

1, 1} are not ²-regular for any ²

1 (except for S

-regular.

2 →

{
−

= ;

Fn

⊆

−

<

The notion of regularity can be particularly useful for probability density

functions; in this case it is traditional to use an alternate name:

|

∈

c

| ≤

Ex

Fn

R≥

2 →

² for all γ

ϕ[χγ(x)]
∼

Deﬁnition 6.5. If ϕ : Fn
0 is a probability density which is ²-regular,
we call it an ²-biased density. Equivalently, ϕ is an ²-biased density if and
only if
2 \ {0}; thus one can think of “²-biased” as
meaning “at most ²-biased on subspaces”. Note that the marginal of such a
distribution on any set of coordinates J
1A/ E[1A] for some A

2 we call A an ²-biased set.
1, so every
Example 6.6. For ϕ a probability density we have
density is 1-biased. The density corresponding to the uniform distribution
on Fn
1, is the only 0-biased density. Densities corresponding to
the uniform distribution on smaller afﬁne subspaces are “maximally biased”:
Fn
2 is an afﬁne subspace of dimension less than n, then ϕA is not ²-
if A
1 (Proposition 3.12 again). If E
{(0, . . . , 0), (1, . . . , 1)}, then
biased for any ²
E is a 1/2-biased set (an easy computation, see also Exercise 1.1(h)).

[n] is also ²-biased. If ϕ is ϕA

2 , namely ϕ

ϕ
1
k
k

E[ϕ]

Fn

≡

⊆

=

⊆

=

=

⊆

<

=

There is a “combinatorial” property of functions f that is roughly equiv-
4
4 has an equivalent

alent to ²-regularity. Recall from Exercise 1.29 that ˆ
k

f ˆ
k

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 3 -->
6.1. Notions of pseudorandomness

145

non-Fourier formula: Ex,y,z[ f (x) f (y) f (z) f (x
z)]. We show (roughly speak-
ing) that f is regular if and only if this expectation is not much bigger than
E[ f ]4

Ex,y,z,w[ f (x) f (y) f (z) f (w)]:

+

+

y

=

Proposition 6.7. Let f : Fn

R. Then

2 →
4
(1) If f is ²-regular, then ˆ
f ˆ
E[ f ]4
4 −
k
k
4
f ˆ
(2) If f is not ²-regular, then ˆ
4 −
k
k

²2
≤
E[ f ]4

·

Var[ f ].
²4.

≥

Proof. If f is ²-regular, then

ˆ
k

4
f ˆ
4 −
k

E[ f ]4

=

S
6=;
X

f (S)4

≤

max
{
S
6=;

f (S)2}

·

On the other hand, if f is not ²-regular, then
4
f ˆ
ˆ
4 is at least
k
k

E[ f ]4

f (T)4

²4.

)4

f (

;

+

≥

+

|

b

b

S
6=;
X
f (T)

b

f (S)2

²2

·

≤

Var[ f ].

b
| ≥

² for some T

6= ;

; hence
(cid:3)

b

b

The condition of ²-regularity – that all non-empty-set coefﬁcients are
small – is quite strong. As we saw when investigating the 2
π Theorem in
Chapter 5.4 it’s also interesting to consider f that merely have
² for
|
| ≤
² for i. This
all i
suggests two weaker possible notions of pseudorandomness: having all low-
degree Fourier coefﬁcients small, and having all inﬂuences small. We will
consider both possibilities, starting with the second.

[n]; for monotone f this is the same as saying Infi[ f ]

f (i)

≤

∈

b

Now a randomly chosen f : {

1, 1} will not have all of its inﬂu-
ences small; in fact as we saw in Exercise 2.12, each Infi[ f ] is 1/2 in expec-
δ)-stable inﬂuences
tation. However, for any δ
exponentially small (recall Deﬁnition 2.52). In Exercise 6.2 you will show:

0 it will have all of its (1

{
−

→

>

−

−

1, 1}n

Fact 6.8. Fix δ
function. Then for any i

[0, 1] and let f : {
[n],

∈

−

1, 1}n

1, 1} be a randomly chosen

{
−

→

∈
E[Inf(1
−
i

δ)

(1

[ f ]]

=

−
2

δ/2)n
δ

.

−

This motivates a very important notion of pseudorandomness in the anal-
ysis of Boolean functions: having all stable-inﬂuences small. Recalling the
discussion surrounding Proposition 2.54, we can also describe this as having
no “notable” coordinates.

1, 1}n
Deﬁnition 6.9. We say that f : {
→
or no (², δ)-notable coordinates, if Inf(1
δ)
[ f ]
i
gets stronger as ² and δ decrease: when δ
we simply say f has ²-small inﬂuences.

−

−

≤
=

R has (², δ)-small stable inﬂuences,
[n]. This condition
² for all i,

² for each i
0, meaning Infi[ f ]

∈

≤

Example 6.10. Besides random functions, important examples of Boolean-
valued functions with no notable coordinates are constants, majority, and

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 4 -->
146

6. Pseudorandomness and F2-polynomials

|

|

δ)

S

6= ;

large parities. Constant functions are the ultimate in this regard: they have
(0, 0)-small stable inﬂuences. (Indeed, constant functions are the only ones
with 0-small inﬂuences.) The Majn function has 1
-small inﬂuences. To see
pn
the distinction between inﬂuences and stable inﬂuences, consider the parity
functions χS. Any parity function χS (with S
) has at least one coordinate
is “large” then all of its stable inﬂuences
with maximal inﬂuence, 1. But if
will be small: We have Inf(1
1 when i
S and equal
−
i
1, δ)-small stable inﬂuences. In particular,
to 0 otherwise; i.e., χS has ((1
χS has (², δ)-small stable inﬂuences whenever
.
|
The prototypical example of a function f : {

1, 1} that does not
have small stable inﬂuences is an unbiased k-junta. Such a function has
Var[ f ]
δ)-stable inﬂuences is
1. Thus Inf(1
1/k for at least one i; hence f
at least (1
−
−
−
i
does not have ((1
(0, 1). A some-
∈
x0Majn(x1, . . . , xn), which has
what different example is the function f (x)
Inf(1
−
0

(1
δ)k/k, δ)-small stable inﬂuences for any δ

1 and hence from Fact 2.53 the sum of its (1

[χS] equal to (1
δ)|

pδ; see Exercise 6.5(d).

| ≥
1, 1}n

ln(e/²)
δ

{
−

δ)k

δ)k

[ f ]

[ f ]

δ)|

→

−

−

−

=

−

−

≥

−

−

=

S

∈

|−

|−

1

δ)

δ)

S

S

≥

−

Let’s return to considering the interesting condition that
² for all
[n]. We will call this condition (², 1)-regularity. It is equivalent to saying
1 is ²-regular, or that f has at most ² “correlation” with every dictator:
² for all i. Our third notion of pseudorandomness extends this

i
that f ≤
f ,
χi

f (i)

| ≤

∈

b

|

±

|〈
condition to higher degrees:

〉| ≤

S

< |

| ≤

1, 1}n

f (S)
Deﬁnition 6.11. A function f : {
² for all
|
k; equivalently, if f ≤
), this condition
0
coincides with ²-regularity. When ϕ : Fn
0 is an (², k)-regular probability
b
density, it is more usual to call ϕ (and the associated probability distribution)
(², k)-wise independent.

k is ²-regular. For k

n (or k

R is (², k)-regular if

2 →

R≥

= ∞

| ≤

→

−

=

Below we give two alternate characterizations of (², k)-regularity; how-
ever, they are fairly “rough” in the sense that they have exponential losses
on k. This can be acceptable if k is thought of as a constant. The ﬁrst char-
acterization is that f is (², k)-regular if and only if ﬁxing k input coordinates
changes f ’s mean by at most O(²). The second characterization is the condi-
tion that f has O(²) covariance with every k-junta.

Proposition 6.12. Let f : {

1, 1}n

R and let ²

0, k

N.

∈

≥

→

−

(1) If f is (², k)-regular then any restriction of at most k coordinates changes f ’s

mean by at most 2k².

(2) If f is not (², k)-regular then some restriction to at most k coordinates

changes f ’s mean by more than ².

Proposition 6.13. Let f : {

1, 1}n

R and let ²

0, k

N.

∈

≥

→

−

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 5 -->
6.1. Notions of pseudorandomness

147

(1) If f is (², k)-regular, then Cov[ f , h]
k. In particular, Cov[ f , h]

hˆ
ˆ
1, 1}n
k1² for any h : {
k
−
2k/2² for any k-junta h : {

R with
1, 1}n

→

→
−

≤
≤

(2) If f is not (², k)-regular, then Cov[ f , h]

² for some k-junta h : {

>

1, 1}n

−

→

deg(h)
1, 1}.
{
−

≤

1, 1}.

{
−

We will prove Proposition 6.12, leaving the proof of Proposition 6.13 to the
exercises.

Proof of Proposition 6.12. For the ﬁrst statement, suppose f is (², k)-regular
and let J

k. Then the statement holds because

1, 1}J, where

[n], z

J

⊆

{
−

∈

E[ f J

z]

|

=

|
f (

| ≤
)
;

+

f (T) zT

J

T
⊆
X;6=

b
(Exercise 1.15) and each of the at most 2k terms

b

f (T) zT

a given restriction z

For the second statement, suppose that
{
−

| >
b
1, 1}J changes f ’s mean by

∈

|

|
f (J)

f (T)

is at most ².

| = |

|
J

², where 0
b

< |

k. Then

| ≤

b
f (T) zT .

h(z)

=

J

T
⊆
X;6=

b
², and this follows from

We need to show that

k

h

k∞ >
hχJ

h

k

k∞ = k

E[hχJ]

h(J)

| = |

f (J)

| >

².

| = |

(cid:3)

k∞ ≥ |

Taking ²

=

0 in the above two propositions we obtain:

b

b

Corollary 6.14. For f : {

1, 1}n

R, the following are equivalent:

→

−

(1) f is (0, k)-regular.

(2) Every restriction of at most k coordinates leaves f ’s mean unchanged.

(3) Cov[ f , h]

=

0 for every k-junta h : {

1, 1}n

−

1, 1}.

{
−

→

If f is a probability density, condition (3) is equivalent to Ex
every k-junta h : {

1, 1}n

1, 1}.

f [h(x)]

∼

=

E[h] for

−

{
−

→

For such functions, additional terminology is used:

1, 1}n

1, 1} is (0, k)-regular, it is also called kth-
Deﬁnition 6.15. If f : {
order correlation immune. If f is in addition unbiased, then it is called k-
resilient. Finally, if ϕ : Fn
0 is a (0, k)-regular probability density, then
we call ϕ (and the associated probability distribution) k-wise independent.

→
R≥

2 →

{
−

−

S
k
1
Example 6.16. Any parity function χS : {
| =
is k-resilient. More generally, so is χS
1, 1} that
does not depend on the coordinates in S. For a good example of a correlation
immune function that is not resilient, consider h : {
1, 1} deﬁned
1,...,3m}. This h is not unbiased, being True on only a
by h
+

1, 1}n
{
−
g for any g : {
−

1, 1} with
|
1, 1}n
{
−

χ{1,...,2m}

1, 1}3m

{
−

χ{m

→

→

→

−

−

+

·

=

∧

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 6 -->
148

6. Pseudorandomness and F2-polynomials

1/4-fraction of inputs. However, its bias does not change unless at least 2m
input bits are ﬁxed; hence h is (2m

1)th-order correlation immune.

−

We conclude this section with Figure 6.1, indicating how our various no-

tions of pseudorandomness compare:

Figure 6.1. Comparing notions of pseudorandomness: arrows go from
stronger notions to (strictly) weaker ones

For precise quantitative statements, counterexamples showing that no other
relationships are possible, and explanations for why these notions essentially
coincide for monotone functions, see Exercise 6.5.

6.2. F2-polynomials

We began our study of Boolean functions in Chapter 1.2 by considering their
polynomial representations over the real ﬁeld.
In this section we take a
brief look at their polynomial representations over the ﬁeld F2, with False,
True being represented by 0, 1
F2 as usual. Note that in the ﬁeld F2, the
∈
arithmetic operations
correspond to logical XOR and logical AND,
and
respectively.

+

·

R; then χ[n] : {
x1x2

Example 6.17. Consider the logical parity (XOR) function on n bits, χ[n].
To represent it over the reals (as we have done so far) we encode False,True
1, 1} has the polynomial representation
by
1
±
∈
F2; then
χ[n](x)
=
χ[n] : Fn
xn.
2 →
Notice this polynomial has degree 1, whereas the representation over the
reals has degree n.

{
−
F2 has the polynomial representation χ[n](x)

xn. Suppose instead we encode False,True by 0, 1

1, 1}n

+ · · · +

∈
x2

x1

· · ·

→

−

=

+

In general, let f : Fn

F2 be any Boolean function. Just as in Chapter 1.2
we can ﬁnd a (multilinear) polynomial representation for it by interpolation.
F2 for a
The indicator function 1{a} : Fn

2 →

Fn

2 →

1{a}(x)

xi

=

1

i:ai
=
Y

i:ai
=
Y

∈

2 can be written as
(1
0

xi),

−

(6.1)

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 7 -->
6.2. F2-polynomials

149

xi rather than
xi since these are the same in F2.) Hence f has the multilinear polynomial

a degree-n multilinear polynomial. (We could have written 1
1
expression

−

+

f (a)1{a}(x).

f (x)

=

Fn
a
2
∈
X

After simpliﬁcation, this may be put in the form
cS xS,

f (x)

=

[n]

S
⊆
X

(6.2)

(6.3)

where xS
the F2-polynomial representation of f . As an example, if f
function on 3 bits, its interpolation is

S xi as usual, and each coefﬁcient cS is in F2. We call (6.3)
χ[3] is the parity

Q

=

=

∈

i

χ[3](x)

=

=

(1

x1
x1

x1)(1
x2
x2

+

−
x3
x3

+

−

+

+

=

x2)x3

(1

+
2(x1x2

x1)x2(1
−
x1x3

−
x2x3)

x3)

x1(1
+
−
4x1x2x3

+

+

+

−

x2)(1

x3)

+

−

x1x2x3

(6.4)

as expected. We also have uniqueness of the F2-polynomial representation;
the quickest way to see this is to note that there are 22n
F2
and also 22n

possible choices for the coefﬁcients cS. Summarizing:

functions Fn

2 →

Proposition 6.18. Every f : Fn
tation as in (6.3).

2 →

F2 has a unique F2-polynomial represen-

Example 6.19. The logical AND function ANDn : Fn
expansion ANDn(x)
=
degree-2 expansion IP2n(x1, . . . , xn, y1, . . . , yn)

F2 has the simple
xn. The inner product mod 2 function has the

x1 y1

x2 y2

x1x2

2 →

· · ·

=

+

xn yn.

+ · · · +

Since the F2-polynomial representation is unique we may deﬁne F2-

degree:

Deﬁnition 6.20. The F2-degree of a Boolean function f : {False,True}n
→
{False,True}, denoted degF2
( f ), is the degree of its F2-polynomial representa-
tion. We reserve the notation deg( f ) for the degree of f ’s Fourier expansion.

We can also give a formula for the coefﬁcients of the F2-polynomial repre-

sentation:

Proposition 6.21. Suppose f : Fn
2 →
[n] cS xS. Then cS
f (x)
supp(x)
⊆
Corollary 6.22. Let f : {False,True}n
only if f (x)

P
True for an odd number of inputs x.

F2 has F2-polynomial representation
S f (x).
{False,True}. Then degF2

n if and

( f )

→

P

=

=

=

⊆

S

=

The proof of Proposition 6.21 is left for Exercise 6.10; Corollary 6.22 is just the
x f (x) by observing what
case S
happens with the monomial x1x2

[n]. You can also directly see that c[n]

xn in the interpolation (6.1), (6.2).

=

=

· · ·

P

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 8 -->
150

6. Pseudorandomness and F2-polynomials

→

Given a generic Boolean function f : {False,True}n

{False,True} it’s nat-
ural to ask about the relationship between its Fourier expansion (i.e., poly-
nomial representation over R) and its F2-polynomial representation. In fact
you can easily derive the F2-representation from the R-representation. Sup-
pose p(x) is the Fourier expansion of f ; i.e., f ’s R-multilinear representa-
tion when we interpret False, True as
=
2xn) is the unique R-multilinear representation for f
1
2 −
when we interpret False, True as 0, 1
R. But we can also obtain q(x) by car-
∈
rying out the interpolation in (6.1), (6.2) over Z. Thus the F2 representation
of f is obtained simply by reducing q(x)’s (integer) coefﬁcients modulo 2.

R. From Exercise 1.9, q(x)

2x1, . . . , 1

1
2 p(1

−

±

−

∈

1

We saw an example of this derivation above with χ[3]. The

1-representation

is x1x2x3. The representation over {0, 1}
−
2x3), which when expanded equals (6.4) and has integer coefﬁcients. Finally,
we obtain the F2 representation x1
x3 by reducing the coefﬁcients of (6.4)
modulo 2.

2x2)(1

2 −

x2

⊆

−

−

+

+

∈

Z

R is 1

1
2 (1

±
2x1)(1

One thing to note about this transformation from Fourier expansion to F2-
representation is that it can only decrease degree. As noted in Exercise 1.11,
the ﬁrst step, forming q(x)
2xn), does not change the
2x1, . . . , 1
−
0). And the second step, reducing q’s
degree at all (except if p(x)
coefﬁcients modulo 2, cannot increase the degree. We conclude:

1
1
2 p(1
2 −
1, q(x)

=
≡

−

≡

Proposition 6.23. Let f : {

1, 1}n

−

1, 1}. Then degF2

{
−

( f )

≤

deg( f ).

→

Here is an interesting consequence of this proposition. Suppose that f :
f ;
n. Let g
S
|
1. From Proposition 6.23

f (S)
1, 1} is k-resilient; i.e.,
f ([n] \ S) and hence deg(g)
k

0 for all
n
−
1. But if we interpret f , g : Fn
(g)

=
( f ) (unless f is parity or its negation).

=
·
F2, then g

−
≤
b
f and hence degF2

b
degF2

{
−
=

=
≤

2 →

χ[n]

(g)

| ≤

1, 1}n

{
→
−
g(S)
thus
we deduce degF2
x1
xn
Thus:

b
+· · ·+

+

=

<

−

−

n

k

k

Proposition 6.24. Let f : {
k
degF2

( f )

1.

n

−

≤

−

−

1, 1}n

1, 1} be k-resilient, k

{
−

n

−

<

1. Then

→

This proposition was shown by Siegenthaler, a cryptographer who was
studying stream ciphers; his motivation is discussed further in the notes in
Section 6.6. More generally, Siegenthaler proved the following result (the
proof does not require Fourier analysis):

Siegenthaler’s Theorem. Proposition 6.24 holds. Further, if f is merely
kth-order correlation immune, then we still have degF2

k (for k

( f )

n).

n

≤

−

<

Proof. Pick any monomial xJ of maximal degree d
polynomial representation; we may assume d

( f ) in f ’s F2-
1 else we are done. Make

degF2

=

>

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 9 -->
6.3. Constructions of various pseudorandom functions

151

an arbitrary restriction to the n
tion g : FJ
sentation; thus by Corollary 6.22, g is 1 for an odd number of inputs.

d coordinates outside of J, forming func-
F2. The monomial xJ still appears in g’s F2-polynomial repre-

2 →

−

Let us ﬁrst show Proposition 6.24. Assuming f is k-resilient, it is unbi-
ased. But g is 1 for an odd number of inputs so it cannot be unbiased (since
2d
1 is even for d
1). Thus the restriction changed f ’s bias, and we must
−
d
have n

k, hence d

1.

>

n

k

−

>

≤

−

−

Suppose now f is merely kth-order correlation immune. Pick an arbi-
trary input coordinate for g and suppose its two possible restrictions give
subfunctions g0 and g1. Since g has an odd number of 1’s, one of g0 has
an odd number of 1’s and the other has an even number. In particular, g0
and g1 have different biases. One of these biases must differ from f ’s. Thus
(cid:3)
n

k, hence d

k.

d

n

1

−

+

>

≤

−

We end this section by mentioning another bound related to correlation

immunity:

Theorem 6.25. Suppose f : {
but not k-resilient (i.e., E[ f ]

1, 1}n
{
−
0). Then k

→

−
6=

1

+

≤

2
3 n.

1, 1} is kth-order correlation immune

The proof of this theorem (left to Exercise 6.14) uses the Fourier expan-
sion rather than the F2-representation. The bounds in both Siegenthaler’s
Theorem and Theorem 6.25 can be sharp in many cases; see Exercise 6.15.

6.3. Constructions of various pseudorandom functions

In this section we give some constructions of Boolean functions with strong
pseudorandomness properties. We begin by discussing bent functions:

Deﬁnition 6.26. A function f : Fn
f (γ)

n/2 for all γ

2−

Fn
2 .

|

| =

∈

2 →

1, 1} (with n even) is called bent if

{
−

c
Bent functions are 2−
f (0)

n/2-regular. If the deﬁnition of ²-regularity were
b
needed to be at most ², then bent functions would
changed so that even
|
1 for any f :
be the most regular possible functions. This is because
Fn
n/2. In particular,
f (γ)
bent functions are those that are maximally distant from the class of afﬁne
functions, {

must be at least 2−
b

1, 1} and hence at least one

f (γ)2

2 →

{
−

Fn

P

=

b

b

γ

|

|

|

χγ : γ

±

∈

2 }.

We have encountered some bent functions already. The canonical example
χ(x1xn/2
xn/2xn).
+
2 this is just the AND2 function
1
2 x1x2, which is bent by inspection. For general n, the bentness

c
is the inner product mod 2 function, IPn(x)
1)b.) For n
(Recall the notation χ(b)
1
2 +
is a consequence of the following fact (proved in Exercise 6.16):

x2xn/2

+· · ·+

1
2 x1

1
2 x2

=
=

(
−

−

=

+

+

+

2

1

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 10 -->
152

6. Pseudorandomness and F2-polynomials

Proposition 6.27. Let f : Fn
f
{
−

{
2 →
−
1, 1} deﬁned by ( f
⊕

n0
+
2 →

g : Fn

⊕

1, 1} and g : Fn0
g)(x, x0)

{
−
f (x)g(x0) is also bent.

2 →

1, 1} be bent. Then

=

Another example of a bent function is the complete quadratic function
n xi x j) from Exercise 1.1. Actually, in some sense it is the

χ(

i

CQn(x)
j
≤
“same” example, as we now explain.

=

≤

<

1

P

Proposition 6.28. Let f : Fn
γ

Fn

2 , as is f

2 →

{
−

∈

◦

M for any invertible linear transformation M : Fn

χγ ·
±

f is bent for any
Fn
2 .

2 →

1, 1} be bent. Then

c

M
Proof. Multiplying by
have the same Fourier coefﬁcients as f up to a permutation (see Exercise 3.1).
(cid:3)

1 does not change bentness, and both χγ ·
−

f and f

◦

We claim that CQn arises from f
4 xi x j
≤

4, this is because

≤

<

1

i

j

=
=

IPn as in Proposition 6.28. In the
x3
(x1
(x1

x3)(x2

x3)x4

x3)

x2

+

+

+

+

+

+

case n
=
over F2; thus

P

1 0 1 0
1 1 1 0
0 1 1 0
0 0 0 1















CQ4(x)

=

IP4(Mx)

·

χ(0,0,1,0)(x), where M

=

is invertible.

The general case is left to Exercise 6.20. In fact, every bent f with degF2
2
arises by applying Proposition 6.28 to the inner product mod 2 function; see
Exercise 6.19. There are other large families of bent functions; however,
the problem of classifying all bent functions is open and seems difﬁcult. We
content ourselves by describing one more family:

( f )

≤

Proposition 6.29. Let f : F2n
1, 1}n
where g : {

2 →

{
−

−

{
−

→

1, 1} is arbitrary. Then f is bent.

1, 1} be deﬁned by f (x, y)

IP2n(x, y)g(y)

=

Proof. We will think of y

F2n

γ

∈

2 as (γ1, γ2). Then indeed
c

Fn

2 , so IP2n(x, y)

∈

χy(x). We’ll also write a generic

=

d
f (γ)

=

E
x,y

b

[χy(x)g(y)χ(γ1,γ2)(x, y)]

E
y

=

h
[g(y)χγ2(y)1{y
+

E
y

=

g(y)χγ2(y) E
γ1(x)]
[χy
x
+
i
n g(γ1)χγ2(γ1)

2−

γ1

0}]
=

=

n. (cid:3)

2−

= ±

We next discuss explicit constructions of small ²-biased sets, which are of
considerable use in the ﬁeld of algorithmic derandomization. The most basic
step in a randomized algorithm is drawing a string x
2 from the uniform
distribution; however, this has the “cost” of generating n independent, random
bits. But sometimes it’s not necessary that x precisely have the uniform
distribution; it may sufﬁce that x be drawn from an ²-biased density. If we
can deterministically ﬁnd an ²-biased (multi-)set A of cardinality, say, 2`, then

Fn

∼

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 11 -->
6.3. Constructions of various pseudorandom functions

153

we can generate x
ϕA using just ` independent random bits. We will see
some example derandomizations of this nature in Section 6.4; for now we
discuss constructions.

∼

∈

Fix `

N+ and recall that there exists a ﬁnite ﬁeld F

2` with exactly 2`
elements. It is easy to ﬁnd an explicit representation for F
2` – a complete
addition and multiplication table, say – in time 2O(`). (In fact, one can compute
F
within F
2` even in deterministic poly(`) time.) The ﬁeld elements x
2` are
naturally encoded by distinct `-bit vectors; we will write enc : F
F`
2 for
2`
this encoding. The encoding is linear; i.e., it satisﬁes enc(0)
(0, . . . , 0) and
enc(x

enc(y) for all x, y

enc(x)

∈
→

F

y)

=

+

=

+

2`.

∈

Theorem 6.30. There is a deterministic algorithm that, given n
²
≤
most 16(n/²)2 with the property that ϕA is an ²-biased density.

1/2, runs in poly(n/²) time and outputs a multiset A

Fn

⊆

1 and 0

<
2 of cardinality at

≥

=

=

2−

Proof. It sufﬁces to obtain cardinality (n/²)2 under the assumption that
t are integer powers of 2. We will describe a probabil-
t and n
2`
²
−
ity density ϕ on Fn
2 by giving a procedure for drawing a string y
ϕ which
∼
(n/²)2 possi-
uses 2` independent random bits. A will be the multiset of 22`
ble outcomes for y. It will be clear that A can be generated in deterministic
polynomial time. The goal will be to show that ϕ is 2−

t-biased.

=

To draw y

ϕ, ﬁrst choose r, s

2` independently and uniformly. This

∼
uses 2` independent random bits. Then deﬁne the ith coordinate of y by

∼

F

where the inner product
argue that

E[χγ(y)]

| ≤

,

enc(r i), enc(s)

yi = 〈
,
〈·
·〉
t. Now over F`
2,
2−

takes place in F`

〉

[n],

i

∈

2. Fixing γ

Fn

2 \ {0}, we need to

∈

|

n

i
1
=
X

γ, y

〈

〉 =

γi

〈

enc(r i), enc(s)

〉 =

D

i
1
=
X

where the last step used linearity of enc. Thus

n

γienc(r i), enc(s)

c

n

enc(

= 〈

E

i
1
=
P

γi r i), enc(s)
〉

,

E[χγ(y)]

E[(

1)〈

γ,y

〉]

=

−

E
r

E
s

[(

−

=

1)〈

enc(pγ(r)),enc(s)

〉]

,

(6.5)

2`

F

→

h
2` is the polynomial a

where pγ : F
γ2a2
nomial is of degree at most n, and is nonzero since γ
most n roots (zeroes) over the ﬁeld F
enc(pγ(r))
a root of pγ we have enc(pγ(r))
using Fact 1.7 here.) We deduce that

i
γnan. This poly-
0. Hence it has at
2`. Whenever r is one of these roots,
0 and the inner expectation in (6.5) is 1. But whenever r is not
0 and so the inner expectation is 0. (We are

+ · · · +

γ1a

7→

=

+

6=

6=

0

E[χγ(y)]

Pr[r is a root of pγ]

≤
which is stronger than what we need.

≤

n
2` =

≤

2−

t,

(cid:3)

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 12 -->
154

6. Pseudorandomness and F2-polynomials

The bound of O(n/²)2 in this theorem is fairly close to being optimally

small; see Exercise 6.24 and the notes for this chapter.

Another useful tool in derandomization is that of k-wise independent dis-
tributions. Sometimes a randomized algorithm using n independent random
bits will still work assuming only that every subset of k of the bits is indepen-
dent. Thus as with ²-biased sets, it’s worthwhile to come up with deterministic
constructions of small sets A
2 such that the density function ϕA is k-wise
independent (i.e., (0, k)-regular). The best known examples have the addi-
tional pleasant feature that A is a linear subspace of Fn
2 ; in this case, k-wise
independence is easy to characterize:

Fn

⊂

2 be the
Proposition 6.31. Let H be an m
span of H’s rows. Then ϕA is k-wise independent if and only if any sum of at
most k columns of H is nonzero in Fm

2 . (We exclude the “empty” sum.)

n matrix over F2 and let A

Fn

×

≤

Proof. Since ϕA
and only if

γ

A⊥

=

γ
∈
k for every γ

χγ (Proposition 3.11), ϕA is k-wise independent if
0. (cid:3)

A⊥ if and only if Hγ

A⊥ \ {0}. But γ

|

| >

P

∈

∈

=

Here is a simple construction of such a matrix with m

k log n:

∼

Theorem 6.32. Let k, `
there is a matrix H
nonzero in Fm
2 .

∈

∈
Fm
2

N+ and assume n
n
×

1,
such that any sum of at most k columns of H is

k. Then for m

1)`

2`

(k

=

≥

=

−

+

Proof. Write α1, . . . , αn for the elements of the ﬁnite ﬁeld Fn, and consider
the following matrix H0

×

n

:

Fk
n

∈

H0

=

1
α1
α2
1
...
αk
1

−

1











1
α2
α2
2
...
αk
2

−

1

1
αn
α2
n
...
αk
n

−

1

· · ·
· · ·
· · ·
. . .

· · ·

.











Any submatrix of H0 formed by choosing k columns is a Vandermonde matrix
and is therefore nonsingular. Hence any subset of k columns of H0 is linearly
independent in Fk
n. In particular, any sum of at most k columns of H0 is
nonzero in Fk
0)
with enc(αi
2. Since enc is a linear map we
2 . (cid:3)
may conclude that any sum of at most k columns of H is nonzero in Fm

∈
j), thought of as a column vector in F`

from H0 by replacing each entry αi

n. Now form H

Fm
2

j (i

>

×

n

Corollary 6.33. There is a deterministic algorithm that, given integers 1
k
most 2knk

n, runs in poly(nk) time and outputs a subspace A
1 such that ϕA is k-wise independent.
−

≤
2 of cardinality at

Fn

≤

≤

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 13 -->
6.4. Applications in learning and testing

155

1

−

2(k

2` is a power of 2 and then obtain cardinality
Proof. It sufﬁces to assume n
2nk
1. In this case, the algorithm constructs H as in Theorem 6.32
+
and takes A to be the span of its rows. The fact that ϕA is k-wise independent
(cid:3)
is immediate from Proposition 6.31.

1)`

=

=

−

For constant k this upper bound of O(nk

k/2

c), but there is a lower bound of Ω(nb

1) is close to optimal. It can be
−
c) for constant k;

k/2

improved to O(nb
see Exercises 6.27, 6.28.

We conclude this section by noting that taking an ²-biased density within

a k-wise independent subspace yields an (², k)-wise independent density:

Lemma 6.34. Suppose H
of H is nonzero in Fm
ϕ and setting z
y
∼
dent.

=

∈

n

Fm
2

×

∈

2 . Let ϕ be an ²-biased density on Fm

is such that any sum of at most k columns
2 . Consider drawing
2 . Then the density of z is (², k)-wise indepen-

y>H

Fn

Proof. Suppose γ
and hence

∈
E[χγ(z)]

|

Fn

2 has 0
ϕ[(
Ey
∼

−

| = |
c

γ

< |
| ≤
1)y>Hγ]

k. Then Hγ is nonzero by assumption
(cid:3)

² since ϕ is ²-biased.

| ≤

As a consequence, combining the constructions of Theorem 6.30 and The-
orem 6.32 gives an (², k)-wise independent distribution that can be sampled
from using only O(log k

log(1/²)) independent random bits:

+
k
Theorem 6.35. There is a deterministic algorithm that, given integers 1
≤
≤
Fn
n and also 0
2 of
cardinality O(k log(n)/²)2 (a power of 2) such that ϕA is (², k)-wise independent.

1/2, runs in time poly(n/²) and outputs a multiset A

log log(n)

+

<

≤

⊆

²

6.4. Applications in learning and testing

In this section we describe some applications of our study of pseudorandom-
ness.

|

=

≤

F2

2 →

{ f : Fn

We begin with a notorious open problem from learning theory, that of
learning juntas. Let C
f is a k-junta}; we will always assume
O(log n). In the query access model, it is quite easy to learn C exactly
that k
(i.e., with error 0) in poly(n) time (Exercise 3.37(a)). However, in the model of
random examples, it’s not obvious how to learn C more efﬁciently than in the
nk
poly(n) time required by the Low-Degree Algorithm (see Theorem 3.36).
Unfortunately, this is superpolynomial as soon as k
ω(1). The state of
affairs is the same in the case of depth-k decision trees (a superclass of C ),
and is similar in the case of poly(n)-size DNFs and CNFs. Thus if we wish to
learn, say, poly(n)-size decision trees or DNFs from random examples only, a
necessary prerequisite is doing the same for O(log n)-juntas.

>

·

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 14 -->
156

6. Pseudorandomness and F2-polynomials

Whether or not ω(1)-juntas can be learned from random examples in poly-
nomial time is a longstanding open problem. Here we will show a modest
improvement on the nk-time algorithm:

F2
Theorem 6.36. For k
can be exactly learned from random examples in time n(3/4)k

O(log n), the class C

{ f : Fn

2 →

≤

=

f is a k-junta}

|
poly(n).

·

(The 3/4 in this theorem can in fact be replaced by ω/(ω
number such that n

n matrices can be multiplied in time O(nω).)

+

1), where ω is any

The ﬁrst observation we will use to prove Theorem 6.36 is that to learn k-
juntas, it sufﬁces to be able to identify a single coordinate that is relevant (see
Deﬁnition 2.18). The proof of this is fairly simple and is left for Exercise 6.31:

×

Lemma 6.37. Theorem 6.36 follows from the existence of a learning algorithm
F2, ﬁnds
that, given random examples from a nonconstant k-junta f : Fn
at least one relevant coordinate for f (with probability at least 1
δ) in time
n(3/4)k

2 →
−

poly(n)

log(1/δ).

·

·

≤ |

| ≤

2 →

f (S) for all 1

Assume then that we have random example access to a (nonconstant)
k-junta f : Fn
F2. As in the Low-Degree Algorithm we will estimate the
k is a parameter to
d, where d
S
Fourier coefﬁcients
be chosen later. Using Proposition 3.30 we can ensure that all estimates
k, except with probability most δ/2, in time
are accurate to within (1/3)2−
nd
log(1/δ). (Recall that 2k
poly(n).) Since f is a k-junta, all of
k in magnitude; hence we
its Fourier coefﬁcients are either 0 or at least 2−
0. For any such S, all of the
can exactly identify the sets S for which
coordinates i
0 for all
log(1/δ)
1
(except with probability at most δ/2).

d, we can ﬁnd a relevant coordinate for f in time nd

S are relevant for f (Exercise 2.11). So unless

f (S)
=
poly(n)

poly(n)

f (S)

| ≤

≤ |

≤

≤

6=

S

∈

b

b

b

·

·

·

·

S

=

≤ |

| ≤

0 for all 1

To complete the proof of Theorem 6.36 it remains to handle the case that
f (S)
d; i.e., f is dth-order correlation immune. In this case,
k
( f )
by Siegenthaler’s Theorem we know that degF2
b
since f is not constant.) But there is a learning algorithm running in time
log(1/δ) that exactly learns any F2-polynomial of degree at most `
O(n)3`
(except with probability at most δ/2). Roughly speaking, the algorithm draws
O(n)` random examples and then solves an F2-linear system to determine the
coefﬁcients of the unknown polynomial; see Exercise 6.30 for details. Thus in
time n3(k
log(1/δ) this algorithm will exactly determine f , and in
particular ﬁnd a relevant coordinate.

d. (Note that d

poly(n)

≤

−

<

d)

k

−

·

·

·

3
4 k

=

By choosing d

we balance the running time of the two algorithms.
Regardless of whether f is dth-order correlation immune, at least one of the
two algorithms will ﬁnd a relevant coordinate for f (except with probability
poly(n)
log(1/δ). This completes the proof
δ/2
at most δ/2
of Theorem 6.36.

δ) in time n(3/4)k

+

=

§

¨

·

·

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 15 -->
6.4. Applications in learning and testing

157

Our next application of pseudorandomness involves using ²-biased dis-
tributions to give a deterministic version of the Goldreich–Levin Algorithm
(and hence the Kushilevitz–Mansour learning algorithm) for functions f with
small ˆ
f ˆ
k1. We begin with a basic lemma showing that you can get a good
k
estimate for the mean of such functions using an ²-biased distribution:

Lemma 6.38. If f : {
then

−

1, 1}n

→

R and ϕ : {

1, 1}n

−

R is an ²-biased density,

→

[ f (x)]

E
x
ϕ
∼

E[ f ]

−

ˆ
k

f ˆ
k1².

≤

¯
¯
¯
¯

¯
¯
¯
¯

¯
¯
¯
¯

¯
¯
¯
¯

This lemma follows from Proposition 6.13.(1), but we provide a separate proof:

Proof. By Plancherel,

[ f (x)]

E
x
ϕ
∼

ϕ, f

= 〈

f (

)
;

+

〉 =

ϕ(S)

f (S),

S
6=;
X

and the difference of this from E[ f ]

=

b
f (

;

) is, in absolute value, at most

b

b

ϕ(S)

f (S)

|

| · |

²
b
·

| ≤

f (S)

|

ˆ
k

f ˆ
k1².

| ≤

S
6=;
X
2
f ˆ
1 (Exercise 3.6), we also have the following immediate
k

S
6=;
X

b

b

b

(cid:3)

Since ˆ
k

corollary:

f 2 ˆ

k1 ≤

ˆ
k

Corollary 6.39. If f : {
then

−

1, 1}n

→

R and ϕ : {

1, 1}n

−

R is an ²-biased density,

→

[ f (x)2]
E
x
ϕ
∼

−

E[ f 2]

ˆ
k

2
f ˆ
1².
k

≤

We can use the ﬁrst lemma to get a deterministic version of Proposi-
tion 3.30, the learning algorithm that estimates a speciﬁed Fourier coefﬁcient.

Proposition 6.40. There is a deterministic algorithm that, given query access
to a function f : {
1, outputs
an estimate

R as well as U

f (U) satisfying

1/2, and s

f (U) for

1, 1}n

[n], 0

→

−

⊆

<

≤

≥

²

provided ˆ
k

e
f ˆ
k1 ≤

b

f (U)

f (U)

²,

| ≤

−

|

s. The running time is poly(n, s, 1/²).

e

b

= ;

because for general U, the algo-

χU with poly(n) overhead, and

Proof. It sufﬁces to handle the case U
rithm can simulate query access to f
=
f (U). The algorithm will use Theorem 6.30 to construct an (²/s)-biased den-
sity ϕ that is uniform over a (multi-)set of cardinality O(n2s2/²2). By enumer-
b
ating over this set and using queries to f , it can deterministically output the
ϕ[ f (x)] in time poly(n, s, 1/²). The error bound now follows
Ex
estimate
∼
(cid:3)
from Lemma 6.38.
e

ƒ

)
;

)
;

χU (

f (

=

f

·

·

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 16 -->
158

6. Pseudorandomness and F2-polynomials

The other key ingredient needed for the Goldreich–Levin Algorithm was

Proposition 3.40, which let us estimate

WS

|

J[ f ]

=

J
T
X
⊆

T)2

f (S

∪

=

z

E
1,1}J

{
−
∼

[

f J

|

z(S)2]

(6.6)

J

⊆

⊆

b
[n]. Observe that for any z

for any S
tion 6.40 to deterministically estimate
is that we can simulate query access to the restricted function
(²/s)-biased density ϕ remains (²/s)-biased on {
ˆ
f ˆ
ˆ
k1 ≤
k
k
tically estimate (6.6):

d
1, 1}J we can use Proposi-
². The reason
f J
z, the
1, 1}J, and most importantly
−
s by Exercise 3.7. It is not much more difﬁcult to determinis-

z(S) to accuracy

z ˆ
k1 ≤

{
−

d

d

f J

f J

±

∈

|

|

|

Proposition 6.41. There is a deterministic algorithm that, given query access
to a function f : {
1,
{
−
outputs an estimate β for WS

1, 1} as well as S
⊆
J[ f ] that satisﬁes

1/2, and s

1, 1}n

[n], 0

→

−

⊆

<

≤

≥

J

²

|

provided ˆ
k

f ˆ
k1 ≤

s. The running time is poly(n, s, 1/²).

WS

|

J[ f ]

|

β

| ≤

−

²,

Proof. Recall the notation FS
rithm’s task is to estimate Ez
²
4s2 -biased density, Corollary 6.39 tells us that

J f from Deﬁnition 3.20; by (6.6), the algo-
0 is an
1,1}J [(FS
{
−
∼

J f )2(z)]. If ϕ : {
−

1, 1}J

R≥

→

|

|

[(FS
E
z
ϕ
∼

|

J f )2(z)]

E
1,1}J

−

z

{
−
∼

[(FS

J f )2(z)]

|

ˆ
FS
k

|

2
J f ˆ
1 ·
k

≤

²
4s2 ≤

ˆ
k

2
f ˆ
1 ·
k

²
4s2 ≤

²
4 , (6.7)

¯
¯
where the second inequality is immediate from Proposition 3.21. We now
¯
J f )2(z)]. For each
show the algorithm can approximately compute Ez

¯
¯
¯

|

·

s

z

±

²
4s2 ≤

1, 1}J, the algorithm can use ϕ to deterministically estimate (FS
{
−
z(S) to within

∈
f J
the text following (6.6). Since
d
within, say, 3²
4 of (FS
algorithm can in deterministic poly(n, s, 1/²) time estimate Ez
to within
±
quantity Ez

=
²
4 in poly(n, s, 1/²) time, just as was described in
1, the square of this estimate is
J f )2(z). Hence by enumerating over the support of ϕ, the
J f )2(z)]
ϕ[(FS
∼
|
² of the desired
(cid:3)

3²
4 , which by (6.7) gives an estimate to within

J f )2(z)].

J f )(z)

z(S)

d

| ≤

f J

±

|

|

|

|

ϕ[(FS
∼

|

1,1}J [(FS
{
−
∼

|

Propositions 6.40 and 6.41 are the only two ingredients needed for a de-
randomization of the Goldreich–Levin Algorithm. We can therefore state a
derandomized version of its corollary Theorem 3.38 on learning functions with
small Fourier 1-norm:

1, 1}n
Theorem 6.42. Let C
istically learnable from queries with error ² in time poly(n, s, 1/²).

f ˆ
k1 ≤

{ f : {

1, 1}

{
−

→

ˆ
k

=

−

|

s}. Then C is determin-

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 17 -->
6.4. Applications in learning and testing

159

Since any f : {

1, 1}n

1, 1} with sparsity(

−
may also deduce from Exercise 3.37(c):

→

{
−

f )

s also has ˆ
k

f ˆ
k1 ≤

≤

s, we

Theorem 6.43. Let C
→
deterministically learnable exactly (0 error) from queries in time poly(n, 2k).

2O(k)}. Then C is

1, 1}n

{ f : {

1, 1}

{
−

f )

=

−

≤

|

b
sparsity(

Example functions that fall into the concept classes of these theorems are deci-
sion trees of size at most s, and decision trees of depth at most k, respectively.

b

We conclude this section by discussing a derandomized version of the

Blum–Luby–Rubinfeld linearity test from Chapter 1.6:

Derandomized BLR Test. Given query access to f : Fn

F2:

2 →

ϕ, where ϕ is an ²-biased density.

(1) Choose x

∼
∼
(2) Query f at x, y, and x

Fn

2 and y

y.

+

(3) “Accept” if f (x)

f (y)

+

=

f (x

y).

+

Whereas the original BLR Test required exactly 2n independent random
O(log(n/²)). This is very
bits, the above derandomized version needs only n
close to minimum possible; a test using only, say, .99n random bits would only
be able to inspect a 2−

.01n fraction of f ’s values.

+

If f is F2-linear then it is still accepted by the Derandomized BLR Test
with probability 1. As for the approximate converse, we’ll have to make a
slight concession: We’ll show that any function accepted with probability
close to 1 must be close to an afﬁne function, i.e., satisfy degF2
1. This
F2 might be 1 everywhere
concession is necessary: the function f : Fn
except on the (tiny) support of ϕ. In that case the acceptance criterion f (x)
f (y)
linear function. It is, however, very close to the afﬁne function 1.

+
1; yet f is very far from every

y) will almost always be 1

2 →

f (x

( f )

=

≤

+

+

=

0

Theorem 6.44. Suppose the Derandomized BLR Test accepts f : Fn
with probability 1
afﬁne g : Fn

1
2 θ. Then f has correlation at least pθ2
pθ2

F2; i.e., dist( f , g)

F2
2 →
² with some

2 +

².

−

1
2 −

1
2

≤

−

Remark 6.45. The bound in this theorem works well both when θ is close to 0
2δ we get that if f is accepted with
and when θ is close to 1; e.g., for θ
1
δ.
probability 1

δ, then f is nearly δ-close to an afﬁne function, provided ²

=

−

2 →

−

¿

Proof. As in the analysis of the BLR Test (Theorem 1.30) we encode f ’s
R. Using the ﬁrst few lines of that analysis we see that our
outputs by
1
hypothesis is equivalent to

±

∈

θ

≤

E
Fn
x
2
∼
y
ϕ
∼

[ f (x) f (y) f (x

y)]

=

+

[ f (y)

E
y
ϕ
∼

( f

·

∗

f )(y)].

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 18 -->
[ f (y)

E
y
ϕ
∼
and hence
θ2

160

6. Pseudorandomness and F2-polynomials

By Cauchy–Schwarz,

( f

·

∗

f )(y)]

[ f (y)2]
E
y
ϕ
∼

[( f

E
y
ϕ
∼

∗

r

≤

r

f )2(y)]

[( f

E
y
ϕ
∼

∗

=

r

f )2(y)],

[( f

E
y
ϕ
∼

≤

∗

f )2(y)]

E[( f

≤

f )2]

f

ˆ
k

+

f ˆ
k1²

=

∗

∗

f (γ)4

²,

+

Fn
Xγ
2
∈
f
c
∗

b
f (γ)

f (γ)2. The
where the inequality is Corollary 6.39 and we used
conclusion of the proof is as in the original analysis (cf. Proposition 6.7, Exer-
cise 1.29):

(cid:129)

=

b

θ2

²

−

≤

f (γ)4

≤

max
{
Fn
γ
2

∈

f (γ)2}

·

f (γ)2

f (γ)2},

=

max
{
Fn
γ
2

∈

c
and hence there exists γ∗ such that

Fn
Xγ
2
∈
c

b

Fn
Xγ
2
∈
b
pθ2
c

b
f (γ∗)

|

| ≥

b

c

².

−

(cid:3)

6.5. Highlight: Fooling F2-polynomials

b

Recall that a density ϕ is said to be ²-biased if its correlation with every F2-
linear function f is at most ² in magnitude. In the lingo of pseudorandomness,
one says that ϕ fools the class of F2-linear functions:
Deﬁnition 6.46. Let ϕ : Fn
of functions Fn

R≥
R. We say that ϕ ²-fools C if

0 be a density function and let C be a class

2 →

2 →

for all f

C .

∈

[ f (y)]

E
y
ϕ
∼

−

x

E
Fn
2
∼

²

≤

[ f (x)]

¯
¯
¯

¯
¯
¯

( f )

Theorem 6.30 implies that using just O(log(n/²)) independent random
bits, one can generate a density that ²-fools the class of f : Fn
1, 1} with
1. A natural problem in the ﬁeld of derandomization is: How
degF2
many independent random bits are needed to generate a density which ²-fools
all functions of F2-degree at most d? A naive hope might be that ²-biased
densities automatically fool functions of F2-degree d
1. The next example
shows that this hope fails badly, even for d

2 →

{
−

2:

≤

>

=

Example 6.47. Recall the inner product mod 2 function, IPn : Fn
{0, 1},
which has F2-degree 2. Let ϕ : Fn
R≥
0 be the density of the uniform dis-
tribution on the support of IPn. Now IPn is an extremely regular function
n/2-biased density (see Exer-
(see Example 6.4), and indeed ϕ is a roughly 2−
cise 6.7). But ϕ is very bad at fooling at least one function of F2-degree 2,
namely IPn itself:

2 →

2 →

E
Fn
2
∼

x

[IPn(x)]

1/2,

≈

[IPn(y)]
E
y
ϕ
∼

=

1.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 19 -->
6.5. Highlight: Fooling F2-polynomials

161

d log(n/d)

2 and O(log n)

The problem of using few random bits to fool n-bit, F2-degree-d functions
was ﬁrst taken up by Luby, Veliˇckovi´c, and Wigderson [LVW93]. They showed
how to generate a fooling distribution using exp(O(
log(1/²))) in-
dependent random bits. There was no improvement on this for 14 years, at
which point Bogdanov and Viola [BV07] achieved O(log(n/²)) random bits for
d
exp(poly(1/²)) random bits for d
3. In general, they
suggested that F2-degree-d functions might be fooled by the sum of d inde-
pendent draws from a small-bias distribution. Soon thereafter Lovett [Lov08]
showed that a sum of 2d independent draws from a small-bias distribu-
tion sufﬁces, implying that F2-degree-d functions can be fooled using just
log(n/²) random bits. More precisely, if ϕ is any ²-biased density on Fn
2O(d)
2 ,
Lovett showed that

p

=

=

+

+

·

E

y(1),...,y(2d )

[ f (y(1)
ϕ

+ · · · +

y(2d))]

[ f (x)]

−

x

E
Fn
2
∼

O(²1/4d

).

≤

∼
In other words, the 2d-fold convolution ϕ∗
degree d.

2d

¯
¯
¯

density fools functions of F2-

The current state of the art for this problem is Viola’s Theorem [Vio09b],
which shows that the original idea of Bogdanov and Viola [BV07] works:
Summing d independent draws from an ²-biased distribution fools F2-degree-
d polynomials.

Viola’s Theorem. Let ϕ be any ²-biased density on Fn
and deﬁne ²d
is ²d-fooled by the d-fold convolution ϕ∗

. Then the class of all f : Fn

9²1/2d

d; i.e.,

2 →

{
−

=

−

1

²

1. Let d

2 , 0
≤
1, 1} with degF2

≤

∈
( f )

N+
d

≤

E

y(1),...,y(d)

[ f (y(1)
ϕ

∼

+ · · · +

y(d))]

[ f (x)]

−

x

E
Fn
2
∼

9²1/2d

1

−

.

≤

¯
¯
¯

In light of Theorem 6.30, Viola’s Theorem implies that one can ²-fool n-bit
O(d2d log(1/²)) independent

functions of F2-degree d using only O(d log n)
random bits.

+

The proof of Viola’s Theorem is an induction on d. To reduce the case
1 to degree d, Viola makes use of a simple concept: directional

of degree d
derivatives.

+

Deﬁnition 6.48. Let f : Fn
F2 is deﬁned by
∆y f : Fn

2 →

2 →

F2 and let y

∈

Fn

2 . The directional derivative

y)
Over F2 we may equivalently write ∆y f (x)

f (x

=

+

∆y f (x)

f (x).

−

f (x

y)

+

+

f (x).

=

As expected, taking a derivative reduces degree by 1:

Fact 6.49. For any f : Fn

F2 and y

Fn

2 we have degF2

(∆y f )

∈
Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.

≤

2 →

degF2

( f )

1.

−

¯
¯
¯

¯
¯
¯



<!-- pdf-page: 20 -->
162

6. Pseudorandomness and F2-polynomials

In fact, we’ll prove a slightly stronger statement:

Proposition 6.50. Let f : Fn
2 →
g : Fn
F2 by g(x)
y)
−

2 →

f (x

=

+

F2 have degF2
f (x

=
y0). Then degF2

( f )

+

d and ﬁx y, y0
d
(g)

1.

≤

−

Fn

2 . Deﬁne

∈

Proof. In passing from the F2-polynomial representation of f (x) to that
of g(x), each monomial xS of maximal degree d is replaced by (x
y0)S.
Upon expansion the monomials xS cancel, leaving a polynomial of degree at
(cid:3)
most d

y)S

(x

1.

+

−

+

−

We are now ready to give the proof of Viola’s Theorem.

Proof of Viola’s Theorem. The proof is by induction on d. The d
1 case is
immediate (even without the factor of 9) because ϕ is ²-biased. Assume that
the theorem holds for general d
d
+
small.

≤
1. We split into two cases, depending on whether the bias of f is large or

1, 1} have degF2

1 and let f : Fn

2 →

{
−

( f )

≥

=

Case 1: E[ f ]2

>
p²d

²d. In this case,

E
(d
ϕ∗

[ f (z)]

1)

+

−

x

E
Fn
2
∼

[ f (x)]

E
(d
ϕ∗

∼

z

1)

+

[ f (z)]

−

x

E
Fn
2
∼

¯
¯
¯

[ f (x)]

[ f (x0) f (z)]

1)

+

−

E
x0,x
∼

Fn
2

(d

ϕ∗

[ f (z

+

1)

+

y) f (z)]

−

(d

ϕ∗

y,x

·

z

∼

¯
¯
E[ f ]
¯
| ·

Fn

x0∼

Fn

y

∼

¯
¯
E
¯
2 ,z

∼
E
2 ,z

∼
E
2 ,z

< |

=

=

¯
¯
¯

¯
¯
¯

¯
¯
[ f (x0) f (x)]
¯

¯
¯
¯
y) f (x)]

+

¯
¯
¯

Fn
2

[ f (x

E
∼
[∆y f (x)]
¯
¯
¯
.

=

y

Fn

ϕ∗

(d

1)

+

[∆y f (z)]

−

y,x

Fn
2

E
∼

∼

≤

¯
¯
¯
y

E
(d
ϕ∗

[∆y f (z)]

∼
E
Fn
z
2 h¯
∼
∼
y the directional derivative ∆y f has F2-degree at most d
¯
For each outcome y
¯
=
d ²d-fools any such polynomial, and
(Fact 6.49). By induction we know that ϕ∗
1) does too. Thus each quantity in the
it follows from Exercise 6.29 that ϕ∗
+
expectation over y is at most ²d, and we conclude

[∆y f (x)
¯
¯
¯

E
Fn
2
∼

−

(d

i

x

1)

+

E
(d
ϕ∗

1)

+

z

[ f (z)]

−

x

E
Fn
2
∼

[ f (x)]

∼

¯
¯
Case 2: E[ f ]2
¯

¯
¯
¯
≤
nearly as small. By Cauchy–Schwarz,

²d. In this case we want to show that Ew

1)[ f (w)]2 is

+

(d

ϕ∗

∼

²d
p²d =

p²d

1
3 ²d

1

+

≤

²d

1.
+

=

≤

[ f (w)]2

E
(d
ϕ∗

∼

w

1)

+

E
y
ϕ
∼

h
[ f (z

=

z

E
ϕ∗

d

∼
E
y,y0∼
ϕ

[ f (z

y)]

+

y) f (z

+

+

2

≤

i
y0)]
i

E
ϕ∗

d

z

∼

E
y
ϕ
∼

h
E
y,y0∼
ϕ
h

=

[ f (z

y)]2

+

[ f (z

E
ϕ∗

∼

d

z

+

i
y) f (z

+

.

y0)]
i

=

z

E
ϕ∗

∼

d

h

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 21 -->
6.6. Exercises and notes

163

y0) is of F2-degree
For each outcome of y
at most d in the variables z, by Proposition 6.50. Hence by induction we have

y0, the function f (z

y) f (z

y, y0

=

=

+

+

y) f (x

y0)]

+

²d

+

i

E
y,y0∼
ϕ
h

z

E
ϕ∗

∼

d

[ f (z

+

y) f (z

+

y0)]
i

≤

=

=

≤

[ f (x

+
f )(x)2]

x

E
E
Fn
y,y0∼
ϕ
2
∼
h
[(ϕ
E
Fn
2
∼

∗
ϕ(γ)2

x

f (γ)2

²d

+

²d

+

Fn
Xγ
2
∈
b
f (0)2
c
+

b
2²d

²2,

b

²2

f (γ)2

²d

+

0
γ
6=
X

b

≤
where the last step used the hypothesis of Case 2. We have thus shown

+

E
(d
ϕ∗

1)

+

w

[ f (w)]2

2²d

²2

+

≤

≤

3²d

4²d,

≤

∼
2p²d. Since we are in Case 2,

E[ f (w)]

| ≤

and hence

|

as needed.

E
(d
ϕ∗

∼

w

1)

+

[ f (w)]

E[ f ]

−

3p²d

=

≤

¯
¯
¯

¯
¯
¯

1,
+

(cid:3)

E[ f ]

p²d, and so

| ≤

|
²d

We end this section by discussing the tightness of parameters in Viola’s
Theorem. First, if we ignore the error parameter, then the result is sharp: a
counting argument (see [BV07]) shows that the d-fold convolution of ²-biased
densities cannot in general fool functions of F2-degree d
1. More explicitly,
for any d
2n -biased
density on F(`
1
2
for which

N+, `
2d
≥
1)n
and an explicit function f : F(`
+
2

1, Lovett and Tzur [LT09] gave an explicit `

1, 1} of degree d

{
−

→

1)n

+

+

+

∈

+

E
ϕ∗

∼

w

¯
¯
¯

[ f (w)]

d

−

E[ f ]

1

−

≥

2d
2n .

¯
¯
¯

1

−

Regarding the error parameter in Viola’s Theorem, it is not known whether
the quantity ²1/2d
can be improved, even in the case d
2. However, ob-
taining even a modest improvement to ²1/1.99d
(for d as large as log n) would
constitute a major advance since it would imply progress on the notorious
problem of “correlation bounds for polynomials”; see Viola [Vio09a].

=

6.6. Exercises and notes

6.1 Let f be chosen as in Proposition 6.1. Compute Var[

f (S)] for each S

[n].

⊆

6.2 Prove Fact 6.8.
6.3 Show that any nonconstant k-junta has Inf(1
−
i

least one coordinate i.

δ)

[ f ]

b
(1/2

≥

−

δ/2)k

1/k for at
−

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 22 -->
164

6. Pseudorandomness and F2-polynomials

6.4 Let ϕ : Fn

2 →
d-fold convolution ϕ∗

0 be an ²-biased density. For each d
d is an ²d-biased density.

R≥

N+ show that the

∈

6.5 (a) Show that if f : {
regular.

−

1, 1}n

R has ²-small inﬂuences, then it is p²-

→

(b) Show that for all even n there exists f : {

1, 1}n

−

{
−

→

1, 1} that is 2−

n/2-

regular but does not have ²-small inﬂuences for any ²

1/2.

(c) Show that there is a function f : {

1, 1}n

−

{
−

→

1, 1} with ((1

δ)n

1, δ)-
−

−

small stable inﬂuences that is not ²-regular for any ²

1.

δ)

(d) Verify that the function f (x)
Stab1

x0Majn(x1, . . . , xn) from Example 6.10
=
satisﬁes Inf(1
δ[Majn] for δ
(0, 1), and thus does not
−
0
=
∈
−
have (², δ)-small stable inﬂuences unless ²
1
≥
1, 1} from part (d) is 1
{
pn
−

(e) Show that the function f : {

1, 1}n

pδ.

[ f ]

→

−

−

+

1

-

<

<

regular.
(f ) Suppose f : {

1, 1}n

R has (², δ)-small stable inﬂuences. Show that

→
f is (η, k)-regular for η

−

δ)k
(g) Show that f has (², 1)-small stable inﬂuences if and only if f is (p², 1)-

1.
−

²/(1

=

−

p

regular.
(h) Let f : {

1, 1}n

−

{
−

→

then f is ²-regular and has ²-small inﬂuences.

1, 1} be monotone. Show that if f is (², 1)-regular

6.6 (a) Let f : {

→

R. Let (J, J) be a partition of [n] and let z
1, 1}n
1, 1}J uniformly random, give a formula for Varz[E[ f J

1, 1}J.
For z
z]]
in terms of f ’s Fourier coefﬁcients. (Hint: Direct application of Corol-
lary 3.22.)

−
{
−

{
−

∼

∈

|

(b) Using the above formula and the probabilistic method, give an alter-

nate proof of the second statement of Proposition 6.12.

6.7 Let ϕ : Fn

R≥

2 →

on the support of IPn : Fn
2−

2 →
n/2), but not for smaller ².

0 be the density corresponding to the uniform distribution
{0, 1}. Show that ϕ is ²-biased for ²

n/2/(1

2−

=

−

6.8 Prove Proposition 6.13.
6.9 Compute the F2-polynomial representation of the equality function Equn :

{0, 1}n

6.10 (a) Let f : {0, 1}n

→

{0, 1}, deﬁned by Equn(x)
R and let q(x)

1 if and only if x1

x2
[n] cS xS be the (unique) multilin-
⊆

= · · · =

xn.

=

S

=

=

ear polynomial representation of f over R. Show that

→

P

R

S

|−|

| f (R),

1)|

(
−

cS

=

S
R
⊆
X

where we identify R
is sometimes called Möbius inversion.

⊆

[n] with its 0-1 indicator string. This formula

(b) Prove Proposition 6.21.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 23 -->
6.6. Exercises and notes

165

6.11 (Cf. Lemma 3.5.) Let f : Fn
2−

Show that Pr[ f (x)
induction on n.)

0]

6=

≥

F2 be nonzero and suppose degF2

k.
2 →
k. (Hint: As in the similar Exercise 3.4, use

( f )

≤

6.12 Let f : {

1, 1}n
{0, 1}.
(a) Show that degF2

→

−

( f )

(b) Suppose

≤
cise 3.7, Corollary 6.22, and Exercise 1.3.)
k-granular. Show that degF2

b
result than part (a), by Exercise 3.32.)

f is 2−

log(sparsity(

f )).

(Hint: You will need Exer-

( f )

≤

k. (This is a stronger

6.13 Let f : {

b
1, 1}n
that the upper bound n/2

{
−

→

−

1, 1} be bent, n

( f )
1 follows from Exercise 6.12(b).)

2. Show that degF2

>

n/2. (Note

≤

+

6.14 In this exercise you will prove Theorem 6.25.
c0

(a) Suppose p(x)

cS xS
0,

=

r(x) is a real multilinear polynomial over
+
2
3 n for all monomials
x1, . . . , xn with c0, cS
S
xT appearing in r(x). Show that after expansion and multilinear
reduction (meaning x2
(b) Deduce Theorem 6.25.

1), p(x)2 contains the term 2c0 cS xS.

2
3 n, and

i 7→

+
|

| >

| >

6=

T

|

6.15 In this exercise you will explore the sharpness of Siegenthaler’s Theorem

and Theorem 6.25.
(a) For all n and k
has degF2
(b) For all n

( f )

=

n

1, ﬁnd an f : {0, 1}n

<
n

−
k

1.

−
3, ﬁnd an f : {0, 1}n

−

≥
immune and has degF2

( f )

n

=

−

(c) For all n divisible by 3, ﬁnd a biased f : {0, 1}n

order correlation immune.

{0, 1} that is k-resilient and

→

{0, 1} that is 1st-order correlation

→
1.

{0, 1} that is ( 2

3 n

1)th-

−

→

6.16 Prove Proposition 6.27.
6.17 Bent functions come in pairs: Show that if f : Fn
f is also a bent function (with domain

2n/2

Fn

2 →

1, 1} is bent, then

{
−

6.18 Extend Proposition 6.29 to show that if π is any permutation on Fn

2 ).

c

b
f (x, y)

=

IP2n(x, π(y))g(y) is bent.

6.19 Dickson’s Theorem says the following: Any polynomial p : Fn

degree at most 2 can be expressed as

k

p(x)

`0(x)

=

+

` j(x)`0j(x),

j
1
=
X
where `0 is an afﬁne function and `1, `01, . . . , `k, `0k are linearly indepen-
dent linear functions. Here k depends only on p and is called the “rank” of
p. Show that for n even, g : Fn
χ(p(x)) is bent if
1, 1} deﬁned by g(x)
n/2, if and only if g arises from IPn as in Proposition 6.28.
and only if k

2 →

{
−

=

=

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.

2 →

2 , then

F2 of

(6.8)



<!-- pdf-page: 24 -->
166

6. Pseudorandomness and F2-polynomials

6.20 Without appealing to Dickson’s Theorem, prove that the complete qua-
dratic x
n/2
. (Hint:
c
Induction on n, with different steps depending on the parity of n.)

n xi x j can be expressed as in (6.8), with k

= b

7→

≤

≤

<

1

i

j

6.21 Deﬁne mod3 : {

1, 1}n
{0, 1} by mod3(x)
ible by 3. Derive the Fourier expansion

→

−

1 if and only if

=

n
j

1 xi is divis-
=

P

mod3(x)

1
3 +

2
3 (

=

1/2)n

−

1)(

(
−

S

|

|

mod 4)/2p3|

[n]
S
⊆
X
S
even
|

|

P
|xS

S

2 , with yi j = 〈
t-biased.
Fn

N. Let A

and conclude that mod3 is 2
p
3
2 )x j.)
−

3 ( p3

2 )n-regular.

(Hint: Consider

n
j

1(
=

−

1
2 +

Q

6.22 In Theorem 6.30, show that given r, s any ﬁxed bit yi can be obtained in

deterministic poly(`) time.

2−
1.)
(b) Since F

t
6.23 (a) Slightly modify the construction in Theorem 6.30 to obtain a (2−
`)-biased density. (Hint: Arrange for pγ to have degree at most n

−
−
2` is a dimension-` vector space over F2, it has some basis
v1, . . . , v`. Suppose we modify the construction in Theorem 6.30 so that
ϕ is a density on Fn`
[`].
Show that ϕ remains 2−

enc(v j r i), enc(s)
〉

[n], j

for i

∈

∈

(0, 1) and n
Cn/²2

2 be a randomly chosen multiset in
6.24 Fix ²
which
elements are included, independently and uniformly. Show
that if C is a large enough constant, then A is ²-biased except with proba-
bility at most 2−

∈
d

n.

⊆

∈

e

n

×

Fn
2

6.25 Consider the problem of computing the matrix multiplication C

AB,
where A, B
. There is an algorithm [LG14] for solving this problem
∈
in time O(nω), where ω
2.373; however, the algorithm is very compli-
cated. Suppose you are given A, B, and the outcome C0 of running this
algorithm; you want to test that indeed C0
(a) Give an algorithm using n random bits and time O(n2) with the fol-
AB, then the algorithm “accepts” with prob-
AB, then the algorithm “accepts” with probability at

lowing property: If C0
ability 1; if C0
most 1/2. (Hint: Compute C0x and ABx for a random x

AB.

=

<

=

6=

=

Fn

2 .)

∈

(b) Show how to reduce the number of random bits used to O(log n) at the
expense of making the false acceptance probability 2/3, while keeping
the running time O(n2). (You may use the fact that in Theorem 6.30,
the time required to compute y given r and s is n

polylog(`).)

6.26 Simplify the exposition and analysis of Theorem 6.32 and Corollary 6.33
2, and show that you can take m to be one less (i.e.,

·

in the case of k
m

`).

=

=

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 25 -->
6.6. Exercises and notes

167

Fk
n

n

6.27 Consider the matrix H0

×

∈

constructed in Theorem 6.32, and suppose
we delete all rows corresponding to even (nonzero) powers of the α j’s.
Show that H0 retains the property that any sum of at most k columns
of H0 is nonzero in Fk
j for any
n. (Hint: Prove and use that (
Fn.) Deduce that the cardinality of A in Corollary 6.33
sequence of β j
can be decreased to 2(2n)b

j β j)2

j β2

k/2

P

P

c.

=

∈

6.28 Let A

⊆

k/2

| ≥

{
−

c) (for k constant).

1, 1}n be a multiset and suppose that the probability density φA
is k-wise independent. In this exercise you will prove the lower bound
Ω(nb
A
|
(a) Suppose F
for all S, T
∈
real vector with entries indexed by A whose ath entry is aS
Show that the set of vectors { 1
p
A
|

2[n] is a collection of subsets of [n] such that
k
T
S
|
⊆
R|
A
F deﬁne χA
F . For each S
| to be the
∈
S ai.
F } is orthonormal and hence

χA
S : S

1, 1}|

{
−

S ∈

| ≤

Q

∪

=

⊆

∈

A

∈

i

|

|

A

|

| ≥ |

F

.

|

(b) Show that we can ﬁnd F satisfying

if k is odd.

F

|

| ≥

n
j

k/2
j
0

=

P

¡

¢

if k is even and

|

n
j

F

(k
j

| ≥

1)/2
−
0
=
6.29 Let C be a class of functions Fn
C whenever f

C and z

1
−
1)/2
−

n
(k

P

+

¢

¡

¡

¢

z

R that is closed under translation; i.e.,
f +
2 (recall Deﬁnition 3.24). An example is
the class of functions of F2-degree at most d. Show that if ψ is a density
that ²-fools C , then ψ

ϕ also ²-fools C for any density ϕ.

2 →
Fn
∈

∈

∈

∗

6.30 Fix an integer `

1. In this exercise you will generalize Exercise 3.43 by

·

δ

≤

<

+

≤

2 →

Fn
2

2`(n`

showing how to exactly learn F2-polynomials of degree at most `.
(a) Fix p : Fn
(p)

` and suppose that x(1), . . . , x(m)

≥
F2 with degF2

∼
2 . Assume that m

log(1/δ)) for 0

(b) Show that the concept class of all polynomials Fn

` that satisﬁes q(x(i))

are drawn uniformly and independently from Fn
C
Show that except with probability at most δ, the only q : Fn
with degF2
(Hint: Exercise 6.11 with q

≥
1/2 and C a sufﬁciently large constant.
F2
p.

∈
F2 of degree
at most ` can be learned from random examples only, with error 0,
in time O(n)3`. (Remark: As in Exercise 3.43, since the key step is
solving a linear system, the learning algorithm can also be done in
O(n)ω` time, assuming matrix multiplication can be done in O(nω)
time.)

2 →
[m] is q
=

p(x(i)) for all i

2 →

(q)

p.)

−

≤

=

(c) Extend this learning algorithm so that in running time O(n)3`

log(1/δ)
δ. (Hint: Similar to Exer-

·

it achieves success probability at least 1
cise 3.40.)

−

6.31 In this exercise you will prove Lemma 6.37.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 26 -->
168

6. Pseudorandomness and F2-polynomials

(a) Give a poly(n, 2k)

examples from a k-junta Fn
ity at most δ) if f is a constant function, and if so, which one.

log(1/δ)-time learning algorithm that, given random
F2, determines (except with probabil-

2 →

·

(b) Given access to random examples from a k-junta f : Fn

[n] be a set of relevant coordinates for f and let z

P
how to obtain M independent random examples from the (k
junta fP
M
most δ).

F2, let
2 . Show
)-
|
log(1/δ) (except with probability at

z in time poly(n, 2k)

2 →
FP
∈

− |

⊆

P

·

·

|

(c) Complete the proof of Lemma 6.37. (Hint: Build a depth-k decision

tree for f .)

6.32 (a) Improve the bound in Lemma 6.38 to ˆ
k

Corollary 6.39 to ˆ
k

2
f ˆ
1²
k
(b) Improve the bound in Theorem 6.44 to pθ2

f ˆ
k1²

2
2².

− k

k

f

f (

)
|
;

² and the bound in

− |

b
²/p1

².

−

−

6.33 Improve on Theorem 6.44 by a factor of roughly 2 in the case of acceptance
probability near 1. Speciﬁcally, show that if f passes the Derandomized
BLR Test with probability 1
p1

δ, then there exists γ∗

2 with

f (γ∗)

Fn

| ≥

²/p1

2δ

².

−

∈

|

−
6.34 Fix an integer k

−

−

N+. Let ( f s)s

∈

{0,1}k be a collection of functions indexed
∈
R. Deﬁne the kth Gowers

c

b

by length-k binary sequences, each f s : Fn
“inner product”
〉U k

R by

( f s)s

∈

〈

2 →

( f s)s

〈

〉U k

=

E
x,y1,...,yk "
s

f s(x

+

yi)

,

#

1

i:si
=
P

{0,1}k
Y

∈

where the k
distributed on Fn
by

+

1 random vectors x, y1, . . . , yk are independent and uniformly
R
2 . Deﬁne the kth Gowers norm of a function f : Fn

2 →

f

k

kU k

= 〈

( f , f , . . . , f )

1/2k
U k ,
〉

where ( f , f , . . . , f ) denotes that all 2k functions in the collection equal f .
(You will later verify that
(a) Check that
〉U 1
(b) Check that

〉U k is always nonnegative.)
k

( f , f , . . . , f )
E[ f0] E[ f1] and therefore

2
U 1 =
k

E[ f ]2.

f0, f1

〈
=

〈

f

f00, f10, f01, f11

〈

〉U 2

=

f00(γ)

f10(γ)

f01(γ)

f11(γ)

Fn
Xγ
2
∈
c
4
f ˆ
c
4. (Cf. Exercise 1.29(b).)
k

c

c

c

and therefore

(c) Show that

f

4
U 2 =
k

ˆ
k

k

( f s)s

〉U k

=

E
y1,...,yk

〈

E
x "

1 "
−

0

s:sk
=
Y

f s(x

+

yi)

# ·

1

i:si
=
P

E
x0 "

1

s:sk
=
Y

f s(x0

+

1

i:si
=
P

,

yi)

##

(6.9)

where x0 is independent of x, y1, . . . , yk

1 and uniformly distributed.
−

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 27 -->
6.6. Exercises and notes

169

(d) Show that
(e) Using (6.9) and Cauchy–Schwarz, show that

〉U k is always nonnegative, as promised.

( f , f , . . . , f )

〈

( f s)s

〈

〉U k

≤

(f ) Show that

( f(s1,...,sk

1,0))S

−

〉U k

〈
q

〈

q

( f(s1,...,sk

1,1))s

−

〉U k .

f s

kU k .

(6.10)

( f s)s

〉U k

s

〈

≤

{0,1}k k
Y
∈
R, show that
f if sk

f

(g) Fixing f : Fn

( f s)s
+
(h) Show that

{0,1}k

∈

2 →

≤ k
1 deﬁned by f s
0 and f s
k · kU k satisﬁes the triangle inequality and is therefore a

k
1

1.
+
1 if sk

(Hint: Consider
1.)

kU k
=

kU k
=

=

=

+

+

1

f

seminorm. (Hint: First show that

f0

k

+

f1

2k
U k =
k

( f1[s

S])s

∈

{0,1}k

∈

〉U k

S

{0,1}k〈
X
⊆

and then use (6.10).)

(i) Show that

k·kU k is in fact a norm for all k

≥

2; i.e.,

f

k

kU k

=

0

=⇒

0.

f

=

Notes. The F2-polynomial representation of a Boolean function f is often
called its algebraic normal form. It seems to have ﬁrst been explicitly intro-
duced by Zhegalkin in 1927 [Zhe27].

→

For functions f : Zn

R, the idea of ²-regularity as a pseudorandomness
notion dates back to Chung and Graham [CG92], as does the equivalent com-
binatorial condition Proposition 6.7. (In the context of quasirandom graphs,
the ideas date further back to Thomason [Tho87] and to Chung, Graham,
and Wilson [CGW89].) The idea of treating functions with small (stable) in-
ﬂuences as being “generic” has its origins in the work of Kahn, Kalai, and
Linial [KKL88]. The notion was brought to the fore in work on hardness of ap-
proximation – implicitly, by Håstad [Hås96, Hås99], and later more explicitly
by Khot, Kindler, Mossel, and O’Donnell [KKMO07].

The notion of ²-biased sets (and also (², k)-wise independent distributions)
was introduced by Naor and Naor [NN93] (see also the independent work of
Peralta [Per90]). The construction in Theorem 6.30 is due to Alon, Goldre-
ich, Håstad, and Peralta [AGHP92] (as is Exercise 6.23). As noted by Naor
and Naor [NN93], ²-biased sets are closely related to error-correcting codes
over F2; indeed, they are equivalent to linear error-correcting in which all
1
pairs of codewords have relative distance in [ 1
2 ²]. In particular, the
construction in Theorem 6.30 is the concatenation of the well-known Reed–
Solomon and Hadamard codes (see, e.g., MacWilliams and Sloane [MS77]
for deﬁnitions). The nonconstructive upper bound in Exercise 6.24 is essen-
tially the Gilbert–Varshamov bound and is close to known lower bound of
Ω(n)), which follows from the work of McEliece,
Ω(

2 ², 1

2 −

2 +

n

1

²2 log(1/²) ) (assuming ²

2−

≥

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 28 -->
170

6. Pseudorandomness and F2-polynomials

Rodemich, Rumsey, and Welch [MRRW77] (see [MS77]). Additionally, con-
structive upper bounds of O( n
²5/2 ) are known using tools from coding
theory; see the work of Ben-Aroya and Ta-Shma [BT09] and Matthews and
Peachey [MP11].

²3 ) and O( n5/4

The probabilistic notion of correlation immunity – i.e., condition (2) of
Corollary 6.14 – was ﬁrst introduced by Siegenthaler [Sie84]; we further dis-
cuss his work below. Independently and shortly thereafter, Chor, Friedman,
Goldreich, Håstad, Rudich, and Smolensky [CFG+85] introduced the deﬁni-
tion of resilience and also connected it to (0, k)-regularity of the Fourier spec-
trum; i.e., they proved Corollary 6.14. (In the cryptography literature, Corol-
lary 6.14 is called the Xiao–Massey Theorem [XM88].) The work [CFG+85]
also essentially contains Theorem 6.25 and the relevant function from Exam-
ple 6.16; cf. the work of Mossel et al. [MOS04].

The problem of constructing explicit k-wise distributions of small support
arose in different guises in different areas – in the study of orthogonal arrays
(in statistics), error-correcting codes, and algorithmic derandomization. Alon,
Babai, and Itai [ABI85] gave the construction in Theorem 6.32 – in fact, the
stronger one from Exercise 6.27 – based on the analysis of dual BCH codes
in MacWilliams and Sloane [MS77]. The lower bound from Exercise 6.28
is essentially due to Rao [Rao47]; see also independent proofs [CFG+85,
ABI85].

Siegenthaler’s Theorem dates from 1984 [Sie84]. His motivation was the
study of cryptographic stream ciphers in cryptography. In this application, a
short random sequence of bits (“secret key”) is transformed via some scheme
into a very long sequence of pseudorandom bits (“keystream”), which can then
be used as a one-time pad for encryption. A basic component of most schemes
is a linear feedback shift register (LFSR), which can efﬁciently generate long,
fairly statistically-uniform sequences. However, due to its F2-linearity, it
suffers from some simple cryptanalytic attacks. An early idea for combating
this is to take n independent LFSR streams and combine them via some
function f : Fn
F2. Effective attacks are possible in such a scheme if f is
correlated with any of its input bits – or indeed (as Siegenthaler pointed out)
any input pair, triple, etc. This led Siegenthaler to deﬁne the probabilistic
notion of correlation-immunity. Although χ[n] is the maximally correlation-
immune function, it is not suitable as a LFSR combining function precisely
because of its F2-linearity; the same is true of any function of low F2-degree.
Siegenthaler precisely captured this tradeoff between correlation-immunity
and F2-degree in his theorem.

2 →

Bent functions were named and ﬁrst studied by Rothaus around 1966;
he didn’t publish the notion until 1976, however [Rot76], at which point

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 29 -->
6.6. Exercises and notes

171

there were already several works on subject, see, e.g., [Dil72]. Bent func-
tions have application in cryptography and coding theory; see, e.g., Carlet’s
survey [Car10]. The basic constructions presented in Section 6.3 are due
to Rothaus; the class of bent functions described in Exercise 6.18 is called
the Maiorana–McFarland family. Dickson’s Theorem is from a 1901 publica-
tion [Dic01, Theorem 199]; see also MacWilliams and Sloane [MS77, Theo-
rem 15.4].

Theorem 6.36 is from Mossel et al. [MOS04]; there is an improved al-
gorithm for learning k-juntas that runs in time roughly n.6024kpoly(n), due
to Gregory Valiant [Val12]. Avrim Blum offers a prize of $1,000 for solv-
log log n in poly(n) time [Blu03]. Theorem 6.42 is due to
ing the case of k
Kushilevitz and Mansour [KM93]. The Derandomized BLR Test and The-
orem 6.44 (and Exercise 6.32) are due to Ben-Sasson, Sudan, Vadhan, and
Wigderson [BSSVW03].

=

The result of Exercise 6.11 is due to Muller [Mul54a, Theorem 6]; deriving
Exercise 6.30 from it and from Blumer et al. [BEHW87] is folklore. The result
of Exercise 6.12(a) is due to Bernasconi and Codenotti [BC99]; Exercise 6.13
is from MacWilliams and Sloane [MS77]. In Exercise 6.25, part (a) is due
to Freivalds [Fre79] and part (b) to Naor and Naor [NN93]. The Gowers
norm and results of Exercise 6.34 are from Gowers [Gow01]. Our proof of the
second statement in Proposition 6.12 was suggested by Noam Lifshitz.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 30 -->

