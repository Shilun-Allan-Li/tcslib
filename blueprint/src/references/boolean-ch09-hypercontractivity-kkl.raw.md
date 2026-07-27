<!-- generated-by: proofmatch local extraction -->
<!-- source-pdf-sha256: 4ba63c9394e55298c5325a5d491092ceed68cf23063051ca11508391b4990d8f -->
<!-- extractor: pdfminer.six v20260107 -->

<!-- pdf-page: 1 -->
Chapter 9

Basics of
hypercontractivity

In 1970, Bonami proved the following central result:

The Hypercontractivity Theorem. Let f : {

Then

Tρ f
k

q

k

f

k

≤ k

p for 0

ρ

≤

≤

p
q

1
1 .
−
−

q

1, 1}n

R and let 1

→

p

q

.
≤ ∞

≤

≤

−

As stated, this theorem may look somewhat opaque. In this chapter we
consider some special cases of it that are easier to understand, easier to prove,
and that encompass almost all of the theorem’s uses. The proof of the full
theorem is deferred to Chapter 10. The special cases in this chapter are the
following:

k

p3

f

2.

f

4
k

k
1, 1}n and f : {

≤

k
k
1, 1}n

Bonami Lemma. Let f : {

1, 1}n

R have degree k. Then

−

→

The fundamental idea of this statement is that if x
→
R has low degree then the random variable f (x) is quite “reasonable”; e.g.,
it is “nicely” distributed around its mean. The Bonami Lemma has a very
easy inductive proof and is already powerful enough to obtain many of the
well-known applications of “hypercontractivity”, including the KKL Theorem
(proven at the end of this chapter) and the Invariance Principle.

{
−

∼

−

(2, q)-Hypercontractivity Theorem. Let f : {
Then
f

1, 1}n
.
≤ ∞
2. As a consequence, if f has degree at most k then

R and let 2

→

−

≤

q

q

T1/pq
k
q

1 f
−
k
1

k
f

k

≤ k
2.

f

q

k

k

k

≤

−

p

k
This theorem quantiﬁes the extent to which Tρ is a “smoothing” operator;
equivalently, it gives even more control over the “reasonableness” of low-
degree polynomials. Its consequences include a generalization of the Level-1

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.

247



<!-- pdf-page: 2 -->
248

9. Basics of hypercontractivity

Inequality (from Chapter 5.4) to “Level-k Inequalities”, as well as a Chernoff-
like tail bound for low-degree polynomials of random bits.

(p, 2)-Hypercontractivity Theorem. Let f : {
−
p. Equivalently, Stabρ[ f ]
Then
≤ k

Tpp
k

≤ k

2
k

k

f

1 f
−

R and let 1
1, 1}n
≤
→
2
1.
ρ for 0
f
1
k
+

≤

≤

ρ

2.

p

≤

This theorem is actually “equivalent” to the (2, q)-Hypercontractivity Theorem
by virtue of Hölder’s inequality. When specialized to the case of f : {
→
{0, 1} it gives a precise quantiﬁcation of the fact that the “noisy hypercube
1, 1}n
graph” is a “small-set expander”. Qualitatively, this means that if A
Nρ(x), then y is very unlikely to be in A.
is “small”, x

A, and y

1, 1}n

{
−

−

⊆

∼

∼

9.1. Low-degree polynomials are reasonable

As anyone who has worked in probability knows, a random variable can some-
times behave in rather “unreasonable” ways. It may be never close to its
expectation. It might exceed its expectation almost always, or almost never.
It might have ﬁnite 1st, 2nd, and 3rd moments, but an inﬁnite 4th moment.
All of this poor behavior can cause a lot of trouble – wouldn’t it be nice to have
a class of “reasonable” random variables?

A very simple condition on a random variable that guarantees some good
behavior is that its 4th moment is not too large compared to its 2nd moment.

Deﬁnition 9.1. For a real number B
X is B-reasonable if E[X 4]

B E[X 2]2. (Equivalently, if

1, we say that the real random variable
X

B1/4

X

≥

k

4

k

≤

2.)
k

k

≤

The smaller B is, the more “reasonable” X is. This deﬁnition is scale-
invariant (i.e., cX is B-reasonable if and only if X is, for c
0) but not
translation-invariant (c
X and X may not be equally reasonable). The latter
fact can sometimes be awkward, a point we’ll address further in Section 9.3.
Indeed, we’ll later encounter a few alternative conditions that also capture
“reasonableness”. For example, in Chapter 11 we’ll consider the analogous
B E[X 2]3/2. Strictly speaking, the 4th mo-
3rd moment condition, E[
|
ment condition is stronger: if X is B-reasonable, then

3]

X

+

6=

≤

|

3]

X

E[
|

|

E[

X

|

| ·

=

X 2]

≤

E[X 2]

E[X 4]

pB E[X 2]3/2;

≤

q

q

on the other hand, there exist random variables with ﬁnite 3rd moment and
inﬁnite 4th moment. However, such unusual random variables almost never
arise for us, and morally speaking the 4th and 3rd moment conditions are
about equally good proxies for reasonableness.

Example 9.2. If x
g
u

N(0, 1) is a standard Gaussian, then E[g4]
[
−

1, 1} is uniformly random then x is 1-reasonable. If
3, so g is 3-reasonable. If
5 -reasonable. In all

1, 1] is uniform, then you can calculate that it is 9

{
−

∼
∼

∼

=

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 3 -->
9.1. Low-degree polynomials are reasonable

249

of these examples B is a “small” constant, and we think of these random
variables simply as “reasonable”. An example of an “unreasonable” random
variable would be highly biased Bernoulli random variable; say, Pr[y
2−
B

=
n, where n is large. This y is not B-reasonable unless

n, Pr[y
2n.

2−

0]

1]

=

−

=

=

1

≥

Let’s give a few illustrations of why reasonable random variables are nice
to work with. First, they have slightly better tail bounds than what you would
get out of the Chebyshev inequality:

Proposition 9.3. Let X
all t

0.

>

0 be B-reasonable. Then Pr[

6≡

X

|

| ≥

X

t

k

k

2]

≤

B/t4 for

Proof. This is immediate from Markov’s inequality:

X

Pr[
|

| ≥

X

t

k

k

2]

=

Pr[X 4

t4

X

4
2]
k

k

≤

≥

E[X 4]
t4 E[X 2]2 ≤

B
t4

.

(cid:3)

More interestingly, they also satisfy anticoncentration bounds; e.g., you

can upper-bound the probability that they are near 0.

Proposition 9.4. Let X
t2)2/B for all t

[0, 1].

∈

0 be B-reasonable. Then Pr[
|

X

6≡

| >

X

t

k

2]
k

≥

(1

−

Proof. Applying the Paley–Zygmund inequality (also called the “second mo-
ment method”) to X 2, we get

X

Pr[
|

| ≥

X

t

k

2]
k

=

Pr[X 2

≥

t2 E[X 2]]

(1

−

≥

t2)2 E[X 2]2

E[X 4] ≥

(1

t2)2
−
B

.

(cid:3)

For a generalization of this proposition, see Exercise 9.12.

For a discrete random variable X , a simple condition that guarantees
reasonableness is that X takes on each of its values with nonnegligible prob-
ability:

Proposition 9.5. Let X be a discrete random variable with probability mass
function π. Write

min(π)

λ

=

Then X is (1/λ)-reasonable.

=

x

min
range(X )

∈

{Pr[X

x]}.

=

Proof. Let M

X

= k

On the other hand,

. Since Pr[
|
λM2

k∞
E[X 2]

≥

X

| =

M]

=⇒

≥
M2

λ we get

E[X 2]/λ.

≤

and thus E[X 4]

≤

E[X 4]

E[X 2

X 2]

≤
=
(1/λ) E[X 2]2 as required.

·

E[X 2],

M2

·

(cid:3)

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 4 -->
250

9. Basics of hypercontractivity

x1

1
pn

The converse to Proposition 9.5 is certainly not true. For example, if
1, 1}n, then X is very close to a standard
X
Gaussian random variable (for n large) and is, unsurprisingly, 3-reasonable.
On the other hand, the “λ” for this X is tiny, 2−

xn where x

+ · · · +

1
pn

{
−

n.

=

∼

This discussion raises the issue of how you might try to construct an
unreasonable random variable out of independent uniform
1 bits. By Propo-
sition 9.5, at the very least you must use a lot of them. Furthermore, it also
seems that they must be combined in a high-degree way. For example, to
construct the unreasonable random variable y from Example 9.2 requires
xn)/2n.
degree n: y

x1)(1

x2)

(1

(1

±

=

+

+

· · ·

+

Indeed, the idea that high degree is required for unreasonableness is

correct, as the following crucial result shows:

1, 1}n
The Bonami Lemma. For each k, if f : {
and x1, . . . , xn are independent, uniformly random
variable f (x) is 9k-reasonable, i.e.,

−

→
±

R has degree at most k
1 bits, then the random

E[ f 4]

≤

9k E[ f 2]2

f

4
k

≤

k

p3

f

2.
k

k

⇐⇒ k

In other words, low-degree polynomials of independent uniform

1 bits are
reasonable. As we will explain later, the Bonami Lemma is a special case of
more general results in the theory of “hypercontractivity”. However, many key
theorems using hypercontractivity – e.g., the KKL Theorem, the Invariance
Principle – really need only the simple Bonami Lemma. (We should also note
that the name “Bonami Lemma” is not standard; however, the result was ﬁrst
proved by Bonami and it’s often used as a lemma, so the name ﬁts. See the
discussion in the notes in Section 9.7.)

±

One pleasant thing about the Bonami Lemma is that once you decide
to prove it by induction on n, the proof practically writes itself. The only
“non-automatic” step is an application of Cauchy–Schwarz.

≥

=

Proof of the Bonami Lemma. We assume k
1 as otherwise f must be
constant and the claim is trivial. The proof is by induction on n. Again,
0, then f must be constant and the claim is trivial. For n
if n
1 we
En f (x) (Proposition 2.24), where
xnDn f (x)
can use the decomposition f (x)
k, and the polynomials Dn f (x) and En f (x) don’t
deg(Dn f )
depend on xn. For brevity we write f
En f (x). Now
e)4]
E[ f 4]
4 E[x3

Dn f (x), and e

1, deg(En f )

f (x), d

4 E[xnde3]

≤

=

≥

+

=

≤

−

=

=

=

k

nd3 e]

6 E[x2
+
n] E[d3 e]

nd2 e2]
+
n] E[d2 e2]
6 E[x2

E[e4]
+
4 E[xn] E[de3]

E[(xnd
+
nd4]
E[x4
+
n] E[d4]
E[x4

=

=

+
In the last step we used the fact that xn is independent of d and e, since Dn f
and En f do not depend on xn. We now use E[xn]

0 and E[x2
n]

E[x3
n]

+

+

+

4 E[x3

E[e4].

=

=

=

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 5 -->
9.1. Low-degree polynomials are reasonable

E[x4
n]

=

1 to deduce

E[ f 4]

E[d4]

+

=

6 E[d2 e2]

E[e4].

+

A similar (and simpler) sequence of steps shows that

E[ f 2]

E[d2]

+

=

E[e2].

251

(9.1)

(9.2)

To upper-bound (9.1), recall that d
polynomial of degree at most k
1 depending on n
can apply the induction hypothesis to deduce E[d4]
E[e4]
Schwarz, getting
have

Dn f (x) where Dn f is a multilinear
1 variables. Thus we
1 E[d2]2. Similarly,
9k
−
k. To bound E[d2 e2] we apply Cauchy–
E[e4] and letting us use induction again. Thus we

9k E[e2]2 since deg(En f )

E[d4]

−
≤

=

−

≤

≤

p

p

E[ f 4]

≤

9k

1 E[d2]2
−

9k

E[d2]2

≤

+
1 E[d2]2
−

³
where we used 9k
proof.

9k E[e2]2

9k E[e2]2

6

9k

1 E[d2]2
−

+
2 E[d2] E[e2]

q

p
E[e2]2

+

9k

=

+
E[d2]

2

,

+

E[e2]
´

³
9k E[d2]2. In light of (9.2), this completes the
(cid:3)

´

≤

Some aspects of the sharpness of the Bonami Lemma are explored in
Exercises 9.2, 9.3, 9.37, and 9.38. Here we make one more observation. At
the end of the proof we used the wasteful-looking inequality 9k
≤
9k E[d2]2. Tracing back through the proof, it’s easy to see that it would still
be valid even if we just had E[x4
1. For example,
i ]
the Bonami Lemma holds not just if the xi’s are random bits, but if they are
standard Gaussians, or are uniform on [
1, 1], or there are some of each. We
leave the following as Exercise 9.4.

9 rather than E[x4
i ]

1 E[d2]2
−

−

≤

=

Corollary 9.6. Let x1, . . . , xn be independent, not necessarily identically dis-
tributed, random variables satisfying E[xi]
0. (This holds if, e.g.,
xi has the same distribution as xi.) Assume also that each xi is B-
each
reasonable. Let f
F(x1, . . . , xn), where F is a multilinear polynomial of degree
at most k. Then f is max(B, 9)k-reasonable.

E[x3
i ]

−

=

=

=

As a ﬁrst application of the Bonami Lemma, let us combine it with Propo-
sition 9.4 to show that a low-degree function is not too concentrated around
its mean:

Theorem 9.7. Let f : {
most k; write µ

E[ f ] and σ

−

=

→

Var[ f ]. Then

1, 1}n

R be a nonconstant function of degree at

=
[
1,1}

|

Pr
{
−
∼

x

p
f (x)

µ

−

| >

1
2 σ]

≥

1

16 91

−

k.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 6 -->
252

9. Basics of hypercontractivity

1
2 .

=

{
−

→

1
σ ( f

Proof. Let g
1. By
the Bonami Lemma, g is 9k-reasonable. The result now follows by applying
(cid:3)
Proposition 9.4 to g with t

µ), a function of degree at most k satisfying

2
k

−

=

=

g

k

Using this theorem, we can give a short proof of the FKN Theorem from
1, 1} has W1[ f ]
δ then f is O(δ)-close to

1, 1}n

1

=

−

Chapter 2.5: If f : {
[n].

χi for some i

−

±

∈

1, so E[`2]
δ by assumption.
Proof of the FKN Theorem. Write `
1
1600 . The goal of the proof
We may assume without loss of generality that δ
is to show that Var[`2] is small; speciﬁcally we’ll show that Var[`2]
6400δ.
This will complete the proof because (using Exercise 1.20 for the ﬁrst equality
below)

f =

≤

=

=

−

≤

1

1

2 Var[`2]

=

j
i
6=
X

f (i)2

f ( j)2

b

b

n

=

=

³

i
1
=
P

(1

−

b
δ)2

2

n

f (i)2

f (i)4

−

n

´

−

i
1
=
P

i
1
=
P
b
f (i)4

b

(1

−

≥

2δ)

−

n

i
1
=
P

f (i)4

b

and hence Var[`2]

6400δ implies

3202δ

1

−

≤

max
{
i

≤

max
{
i

≤

f (i)2}

max
{
|
i

f (i)
|

},

≤

n

≤
f (i)4

i
1
=
P

f (i)2}

n

f (i)2

i
1
=
P

as required.

b
To bound Var[`2] we ﬁrst apply Theorem 9.7 to the degree-2 function `2;

b

b

b

b

this yields

`2

Pr

16 91
Now suppose by way of contradiction that Var[`2]
implies

Var[`2]
i

h¯
¯

p

δ)

(1

−

−

≥

≥

1
2

¯
¯

1

>

2

−

1
144 .

=

6400δ; then the above

1
144 ≤
`

Pr

`2

(1

δ)

−

−

>

40pδ

Pr

`2

1

−

>

39pδ

.

(9.3)

h¯
¯

|

|

|

¯
is frequently far from 1. Since
¯

This says that
f
that
`
|
cise 9.5) shows that ( f
`)2]
plies E[( f
by assumption.

1 always, we can deduce
2 is frequently large. More precisely, a short calculation (Exer-
39pδ. But now (9.3) im-
1
δ
(cid:3)

169δ whenever
δ, a contradiction since E[( f

`)2
−
169δ

1
144 ·

W1[ f ]

`)2]

≥
>

`2

| =

| >

−

−

−

≥

−

=

−

=

1

¯
¯

|

i

≤

i

h¯
f
¯
|

9.2. Small subsets of the hypercube are noise-sensitive

An immediate consequence of the Bonami Lemma is that for any f : {
R and k

N,

−

1, 1}n

→

∈

T1/p3 f =

k

4
k

=

1
p3

k k

k

f =

4
k

≤ k

k

f =

2.
k

k

(9.4)

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 7 -->
9.2. Small subsets of the hypercube are noise-sensitive

253

This is a special case of the (2, 4)-Hypercontractivity Theorem (whose name
will be explained shortly), which says that the assumption of degree-k homo-
geneity is not necessary:

(2, 4)-Hypercontractivity Theorem. Let f : {

1, 1}n

R. Then

→

−

T1/p3 f
k

4
k

f

2.
k

≤ k

It almost looks as though you could prove this theorem simply by sum-
ming (9.4) over k. In fact that proof strategy can be made to work given a
few extra tricks (see Exercise 9.6), but it’s just as easy to repeat the induction
technique used for the Bonami Lemma.

Proof. We’ll prove E[T1/p3 f (x)4]
E[ f (x)2]2 using the same induction as in
the Bonami Lemma. Retaining the notation d and e, and using the shorthand
T

≤

T1/p3, we have

=

=
Similar computations to those in the Bonami Lemma proof yield

+

·

T f

xn

Td

Te.

1
p3

E[(T f )4]

=

≤

≤

≤

=

1
p3
E[(Td)4]
¢
¡

E[(Td)4]
E[d2]2

E[d2]

4 E[(Td)4]

6

+

1
p3

2 E[(Td)2(Te)2]

E[(Te)4]

+

2 E[(Td)2(Te)2]
¡

¢

E[(Te)4]

+

+

E[(Te)4]

+

2

E[(Td)4]
+
2 E[d2] E[e2]
2

E[(Te)4]
E[e2]2
p
+
E[ f 2]2,

E[e2]

p

=

+

+

where the second inequality is Cauchy–Schwarz, the third is induction, and
(cid:3)
the ﬁnal equality is a simple computation analogous to (9.2).

¡

¢

The name “hypercontractivity” in this theorem describes the fact that not
only is T1/p3 a “contraction” on L2({
2 for
−
k
all f (Exercise 2.33) – it’s even a contraction when viewed as an operator from
1, 1}n). You should think of hypercontractivity theorems
L2({
as quantifying the extent to which Tρ is a “smoothing”, or “reasonable-izing”
operator.

1, 1}n) – meaning

1, 1}n) to L4({

T1/p3 f
k

≤ k

2
k

−

−

f

Unfortunately the quantity

4 in the (2, 4)-Hypercontractivity The-
k
orem does not have an obvious combinatorial meaning. On the other hand,
the quantity

T1/p3 f
k

T1/p3 f

2
k

T1/p3 f , T1/p3 f

f , T1/p3T1/p3 f

Stab1/3[ f ],

k

=

〈
q

〈
q
does have a nice combinatorial meaning. And we can make this quantity
appear in the Hypercontractivity Theorem via a simple trick from analysis,
just using the fact that T1/p3 is a self-adjoint operator. We “ﬂip the norms
across 2” using Hölder’s inequality:

〉 =

〉 =

p

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 8 -->
254

9. Basics of hypercontractivity

(4/3, 2)-Hypercontractivity Theorem. Let f : {

1, 1}n

−

T1/p3 f
k

2

k

f

4/3;
k

≤ k

i.e.,

Proof. Writing T

Stab1/3[ f ]

2
4/3.
k
T1/p3 for brevity we have

≤ k

f

R. Then

→

(9.5)

=
T f , T f

T f

2
2 = 〈
k

k

〉 ≤ k
by Hölder’s inequality and the (2, 4)-Hypercontractivity Theorem. Dividing
2 (which we may assume is nonzero) completes the proof. (cid:3)
through by
k

T f
k

〉 = 〈

≤ k

f

4/3
k

TT f
k

4
k

f

4/3
k

T f
k

2
k

f , TT f

(9.6)

In the inequality (9.5) the left-hand side is a natural quantity. The right-
1, 1}, which is not very interesting.
{
→
−
{0, 1} we get something very interesting:

hand side is just 1 when f : {
But if we instead look at f : {

−
1, 1}n

1, 1}n

→

−
1, 1}n have volume α; i.e., let 1A : {

1, 1}n

−

{0, 1}

→

Corollary 9.8. Let A
α. Then
satisfy E[1A]

⊆

{
−

=

Stab1/3[1A]

=

Pr
1,1}n
x
{
−
∼
N1/3(x)
y
∼

[x

∈

A, y

A]

≤

∈

α3/2.

Equivalently (for α

0),

>

A]

[y

∈

≤

α1/2.

Pr
A
x
∼
N1/3(x)

∼

y

Proof. This is immediate from inequality (9.5), since

1A

k

2
4/3 =
k
³

[
E
|
x

1A(x)
|

2

4/3]3/4

[1A(x)]3/2

E
x

=

=

α3/2.

(cid:3)

´
See Section 9.5 for the generalization of this corollary to noise rates other

than 1/3.

=

2−

k, k

N+, and A is a subcube of codimension k;
{0, 1} is the logical AND function on the ﬁrst k coordinates.
A if and only if the
N1/3(x) we’ll have y

Example 9.9. Assume α
e.g., 1A : Fn
For every x
ﬁrst k coordinates of x do not change, which happens with probability (2/3)k
(2/3)log(1/α)
essentially sharp when A is a Hamming ball; see Exercise 9.24.

=
α1/2. In fact, the bound α1/2 in Corollary 9.8 is

A, when we form y

2 →
∈

αlog(3/2)

α.585

=

≈

∼

≤

∈

∈

We can phrase Corollary 9.8 in terms of the expansion in a certain graph:

N+ and ρ

∈

Deﬁnition 9.10. For n
1, 1], the n-dimensional ρ-stable hy-
[
percube graph is the edge-weighted, complete directed graph on vertex set
1, 1}n is equal
{
{
−
−
to Pr[(x, y)
[0, 1],
2δ for δ
we also call this the δ-noisy hypercube graph. Here the weight on (x, y) is

1, 1}n in which the weight on directed edge (x, y)

(x, y)] when (x, y) is a ρ-correlated pair. If ρ

1, 1}n
×
1
−

{
−

=

=

−

∈

∈

∈

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 9 -->
9.2. Small subsets of the hypercube are noise-sensitive

255

Pr[(x, y)
{
−
negating each coordinate independently with probability δ.

(x, y)] where x

∼

=

1, 1}n is uniform and y is formed from x by

∈

{
−

Remark 9.11. The edge weights in this graph are nonnegative and sum to 1.
1, 1}n the sum of
The graph is also “regular” in the sense that for each x
n. You can also consider the
all the edge weight leaving (or entering) x is 2−
graph to be undirected, since the weight on (x, y) is the same as the weight
on (y, x); in this viewpoint, the weight on the undirected edge (x, y) would be
∆(x,y). In fact, the graph is perhaps best thought of as the
21
−
−
1, 1}n in which a step from state
discrete-time Markov chain on state space {
−
x
Nρ(x). This is a reversible chain
with the uniform stationary distribution. Each discrete step is equivalent to
running the “usual” continuous-time Markov chain on the hypercube for time
t

1, 1}n consists of moving to state y

ln(1/ρ) (assuming ρ

∆(x,y)(1

[0, 1]).

{
−

δ)n

nδ

−

∼

∈

=

∈

With this deﬁnition in place, we can see Corollary 9.8 as saying that the
1/3-stable (equivalently, 1/3-noisy) hypercube graph is a “small-set expander”:
given any small α-fraction of the vertices A, almost all of the edge weight
touching A is on its boundary. More precisely, if we choose a random vertex
A and take a random edge out of x (with probability proportional to its
x
α1/2. You
edge weight), we end up outside A with probability at least 1
can compare this with the discussion surrounding the Level-1 Inequality in
Section 5.4, which is the analogous statement for the ρ-stable hypercube
graph “in the limit ρ
0+”. The appropriate statement for general ρ is
appears in Section 9.5 as the “Small-Set Expansion Theorem”.

→

−

∈

→

1, 1}n

1, 0, 1}, with α denoting Pr[g

Corollary 9.8 would apply equally well if 1A were replaced by a function g :
E[g2]. This situation
{
{
−
−
occurs naturally when g
1, 1}.
In this case Stab1/3[g]
[ f ], the 1/3-stable inﬂuence of i on f . We
conclude that for a Boolean-valued function, if the inﬂuence of i is small then
its 1/3-stable inﬂuence is much smaller:

0]
Di f for some Boolean-valued f : {
=
Inf(1/3)
i
=

1, 1}n

E[
|

{
−

→

6=

=

=

−

g

]

|

Corollary 9.12. Let f : {

1, 1}n

−

{
−

→

1, 1}. Then Inf(1/3)

i

Infi[ f ]3/2 for all i.

[ f ]

≤

We remark that the famous KKL Theorem (stated in Chapter 4.2) more or
[n]; if you’re impatient

less follows by summing the above inequality over i
to see its proof you can skip directly to Section 9.6 now.

∈

Let’s take one more look at the “small-set expansion result”, Corollary 9.8.
Since noise stability roughly measures how “low” a function’s Fourier weight
is, this corollary implies that a function f : {
{0, 1} with small mean α
cannot have much of its Fourier weight at low degree. More precisely, for any

1, 1}n

→

−

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 10 -->
256

9. Basics of hypercontractivity

k

∈

N we have

α3/2

≥

Stab1/3[ f ]

(1/3)kW≤

k[ f ]

W≤

k[ f ]

3kα3/2.

≤

=⇒

(9.7)

1 this gives W≤

3α3/2, which is nontrivial but not as strong
For k
as the Level-1 Inequality from Section 5.4. But (9.7) also gives us “level-k
inequalities” for larger values of k. For example,

=

≤

≥
1[ f ]

W≤

.25 log(1/α)[ f ]

.25 log 3

α−

3/2

+

α1.1

α

¿

= k

f

2
2;

k

≤

≤

i.e., almost all of f ’s Fourier weight is above degree .25 log(1/α). We will give
slightly improved versions of these level-k inequalities in Section 9.5.

9.3. (2, q)- and (p, 2)-hypercontractivity for a single bit

Although you can get a lot of mileage out of studying the 4-norm of random
variables, it’s also natural to consider other norms. For example, we would
get improved versions of our concentration and anticoncentration results,
Propositions 9.3 and 9.4, if we could bound the higher norms of a random
variable in terms of its 2-norm. As we’ll see, we can also get stronger “level-k
0.
inequalities” by bounding the (2

²)-norm of a Boolean function for small ²

+

>

We started with the 4-norm due to the simplicity of the proofs of the
Bonami Lemma and the (2, 4)-Hypercontractivity Theorem. To generalize
these results to other norms it’s a bit more elegant to work with the latter.
Partly this is because it’s “formally stronger” (see Theorem 9.21). But the
main reason is that the hypercontractivity version alleviates the inelegant
issue that being “B-reasonable” is not translation-invariant. Thus instead of
4-reasonable”) we’ll
generalizing the condition that
a
generalize the condition that
1 case of the
(2, 4)-Hypercontractivity Theorem).

2 (“X is ρ−
X
k
a
+

ρ X
4
k
k
ρbX
+

2 (cf. the n
k

≤ k
4
k

bX

≤ k

=

k

Deﬁnition 9.13. Let 1
random variable X (with

≤
k

p
X

q

≤ ∞

and let 0

ρ
) is (p, q, ρ)-hypercontractive if

≤

<

1. We say that a real

ρbX

a

k

+

q

k

≤ k

p

for all constants a, b

R.

∈

k

≤
q
k
a

+

< ∞
bX

R or for a

Remark 9.14. By homogeneity, it sufﬁces to check the condition for a
b
if X is (p, q, ρ)-hypercontractive then it is (p, q, ρ0)-hypercontractive for ρ0
as well.

1,
1 (cf. Exercise 9.9(a)). It’s also true (Exercise 9.11) that
ρ

R, b

<

=

=

∈

∈

In Exercise 9.10 you will show that if X is hypercontractive then E[X ]
must be 0. Thus hypercontractivity, like reasonableness, is not a translation-
invariant notion. Nevertheless, the fact that the deﬁnition involves transla-
tion by an arbitrary a greatly facilitates proofs by induction. For example, an
elegant property we gain from the deﬁnition is the following (Exercise 10.2):

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 11 -->
9.3. (2, q)- and (p, 2)-hypercontractivity for a single bit

257

Proposition 9.15. Let X and Y be independent (p, q, ρ)-hypercontractive ran-
dom variables. Then X

Y is also (p, q, ρ)-hypercontractive.

+

±

=

The n

1 case of our (2, 4)-Hypercontractivity Theorem precisely says that
1 bit x is (2, 4, 1/p3)-hypercontractive;
a single uniformly random
the (4/3, 2)-Hypercontractivity Theorem says that the bit x is also (4/3, 2, 1/p3)-
hypercontractive. We’ll spend the remainder of this section generalizing these
facts to (2, q, ρ)- and (p, 2, ρ)-hypercontractivity for other values of p and q.
We remark that in our study of hypercontractivity we’ll focus mainly on the
cases of p
2 and for
random variables other than uniform

2. The study of hypercontractivity for p, q

1 bits is deferred to Chapter 10.

2 or q

=

=

6=

We now consider hypercontractivity of a uniformly random

1 bit x. We
know that x is (2, q, 1/p3)-hypercontractive for q
4; what about other values
of q? Things are most pleasant when q is an even integer because then you
q. So let’s try
don’t need to take the absolute value when computing
q

ρbX

±

=

+

6.

a

k

k

±

=

Proposition 9.16. For x a uniform
R if (and only if) ρ
all a, b

1 bit, we have

2 for
a
k
1/p5. That is, x is (2, 6, 1/p5)-hypercontractive.

ρbx

≤ k

6
k

bx

±

+

+

a

k

∈

≤

Proof. Raising the inequality to the 6th power, we need to show

E[(a

+

ρbx)6]

E[(a

+

≤

bx)2]3.

(9.8)

The result is trivial when a
1 by homo-
geneity. We expand both quantities inside expectations and use the fact that
E[xk] is 0 when k is odd and 1 when k is even. Thus (9.8) is equivalent to

0; otherwise, we may assume a

=

=

1

15ρ2b2

15ρ4b4

ρ6b6

(1

b2)3

1

3b2

3b4

b6.

+

+

+

≤
Comparing the two sides term-by-term we see that the coefﬁcient on b2 is
R it is sufﬁcient that
the limiting factor: in order for (9.9) to hold for all b
15ρ2
0 it’s also easy to see that this
3; i.e., ρ
(cid:3)
condition is necessary.

1/p5. By considering b

→

+

=

+

+

+

≤

≤

∈

(9.9)

If you repeat this analysis for the case of q

8 you’ll ﬁnd that again the
limiting factor is the coefﬁcient on b2, and that x is (2, 8, ρ)-hypercontractive
1/p7. In light of this it is natural to guess
if (and only if)
that the following is true:
¢

; i.e., ρ

ρ2

≤

=

≤

8
2

4
1

¢

¡

¡

Theorem 9.17. Let x be a uniform

a

k

+

bx

±
R assuming ρ
Equivalent statements are that

2 for all a, b
k

∈

≤
a

1 bit and let q
q

1.

1/

−

(1/
p
+
1)-hypercontractive, and that
R.

k

q
−
T1/pq
p
k

−

(2, q, 1/

q

f : {

1, 1}
p

−

→

(2,

∈

]. Then

∞

ρbx

a

k

+

q

k

≤

1)bx
1 f
−

k

2
q ≤
k
q
≤ k

a2
f

b2, that x is
+
2 holds for any

k

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 12 -->
258

9. Basics of hypercontractivity

=

For q an even integer it is not hard (see Exercise 9.36) to prove Theo-
rem 9.17 just as we did for q
6. Indeed, the proof works even under more
general moment conditions on x, as in Corollary 9.6. Unfortunately, obtaining
Theorem 9.17 for all real q
2 takes some more tricks. A natural idea is to try
ρbx)q
forging ahead as in Proposition 9.16, using the series expansions for (1
b2)q/2 provided by the Generalized Binomial Theorem. However, even
and (1
when
1 (so that convergence is not an issue) there is a difﬁculty because
the coefﬁcients in the expansion of (1

b2)q/2 are sometimes negative.

+
b
|

| <

>

+

Luckily, this issue of negative coefﬁcients in the series expansion goes
away if you try to prove the analogous (p, 2, ρ)-hypercontractivity statement.
Thus the slick proof of Theorem 9.17 proceeds by ﬁrst proving that statement,
then “ﬂipping the norms across 2”.

+

Theorem 9.18. Let x be a uniform

1 bit and let 1

a

bx

p for all a, b

+

k
k
hypercontractive.

∈

±
R assuming 0

ρ

≤

≤

p

−

p

p

2. Then

a

≤

+
1. That is, x is (p, 2,

<

k

ρbx
p

2
≤
1)-

k
−

p

Proof. By Remark 9.14 we may assume a
we may also assume without loss of generality that 1
i.e., that
b
|
need to show

1 case follows by continuity. Writing b

1. It then sufﬁces to prove the result for all

1. By Exercise 9.7
1, 1};
{
−
∈
≥
b
1 because the
| <
² for the sake of intuition, we

1 and ρ

p
−
bx

0 for x

p
+

| =

| ≤

=

=

=

b

|

|

1

k

+

E[(1

p
p
−

p

p
²x
1
1
2 ≤ k
k
²x)2]p/2

+
E[(1

·

−
1

²x

p
p
k
²x)p].

(9.10)

(9.11)

·
Here we were able to drop the absolute value on the right-hand side because
²

1. The left-hand side of (9.10) is

⇐⇒

p

+

≤

+

|

| <

(p

(1

+

−

1)²2)p/2

²2,

1

≤
1

1)

p(p
−
2

+
θt for t

1 (easily
where we used the inequality (1
≤
proved by comparing derivatives in t). As for the right-hand side of (9.10),
1 we may use the Generalized Binomial Theorem to show it equals
since

0 and 0

+

+

≥

≤

≤

θ

²x

t)θ

E

1

h
+

=

|
1

| <
p²x

+

+
p² E[x]

1

1)

p(p
−
2

+
²2

1)

p(p
−
2!

²2x2

p(p

1)(p
3!

−

2)

−

²3x3

p(p

1)(p
−
4!

−

2)(p

3)

−

²4x4

p(p
−
2!
p(p

1)

+
²2 E[x2]
1)(p
2)(p
−
4!

−

−

p(p

2)

−

−

1)(p
3!
p(p

1)(p

−

+
3)

²4

+
²3 E[x3]
2)(p
−
6!

−

+
3)(p
−

p(p

4)(p

−

1)(p
−
4!
²6

5)

−

.

+ · · ·
3)

2)(p

−

i
²4 E[x4]

+ · · ·

+

+

=
In light of (9.11), to verify (9.10) it sufﬁces to note that each “post-quadratic”
term above,

+ · · ·

+

p(p

1)(p

−

−

2)(p

3)
−
(2k)!

(p

(2k

−

1))

−

²2k,

···

is nonnegative. This follows from 1
factors and an even number of negative factors.

2: the numerator has two positive
(cid:3)

≤

≤

p

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 13 -->
9.4. Two-function hypercontractivity and induction

259

1, 1}, π

To deduce Theorem 9.17 from Theorem 9.18 we again just need to ﬂip the
norms across 2 using the fact that Tρ is self-adjoint. This is accomplished
by taking Ω
2, T
1 in the following

{
−
proposition (and noting that 1/

=
p0 −
Proposition 9.19. Let T be a self-adjoint operator on L2(Ω, π), let 1
C

, and let p0, q0 be their conjugate Hölder indices. Assume

1, and C
−
1):

Tpp
p

≤
p for

π1/2, q

p, q

T f

p

p

=

=

=

=

=

−

1

q

k

k

≤

≤
f
k

k

∞
all f . Then

T g

p0 ≤

k

C

g

k

k

k

q0 for all g.

Proof. This follows from

T g

k

p0 =

k

k

sup
f
p

k

1〈
=

f , T g

〉 =

k

sup
f
p

k

1〈
=

T f , g

〉 ≤

k

sup
f
p

k

1 k
=

T f

g

q

k

k

q0 ≤

k

C

g

k

k

q0,

where the ﬁrst equality is the sharpness of Hölder’s inequality, the second
equality holds because T is self-adjoint, the subsequent inequality is Hölder’s,
(cid:3)
and the ﬁnal inequality uses the hypothesis

T f

C

f

k

q

k

≤

p.

k

k

q

1)-hypercontractive and (p, 2,

At this point we have established that if x is a uniform

1 bit, then it
±
is (2, q, 1/
1)-hypercontractive. In the
next section we will give a very simple induction which transforms these
facts into the full (2, q)- and (p, 2)-Hypercontractivity Theorems stated at the
beginning of the chapter.

p

p

−

−

p

9.4. Two-function hypercontractivity and induction

At this point we have established that if f : {

1, 1}

Tpp

1 f
−

2
k

f

p,

k

k
R;
We would like to extend these facts to the case of general f : {
i.e., establish the (p, 2)- and (2, q)-Hypercontractivity Theorems stated at the
beginning of the chapter. A natural approach is induction.

1, 1}n

≤ k

≤ k

→

−

k

−
T1/pq
k

1 f
−

q

f

2.
k

R then for any p

2

≤

≤

q,

→

−

→

1, 1}n

In analysis of Boolean functions, there are two methods for proving state-
R by induction on n. One method, which might be

ments about f : {
called “induction by derivatives”, uses the decomposition f (x)
+
En f (x). We saw this approach in our inductive proof of the Bonami Lemma.
The other method, which might be called “induction by restrictions”, goes via
the subfunctions f
1. We
saw this approach in our proof of the OSSS Inequality in Chapter 8.6. In both
methods we reduce inductively from one function f to two functions: either
Dn f and En f , or f
1. Because of this, when trying to prove a fact
+
by induction on n it’s often helpful to try proving a generalized fact about
two functions. Our proof of the OSSS Inequality gives a good example of this
technique.

1 obtained by restricting the nth coordinate of f to
±

1 and f
−

xnDn f (x)

=

±

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 14 -->
260

9. Basics of hypercontractivity

So to facilitate induction, let’s ﬁnd a two-function version of the hypercon-
tractivity statements we’ve proven so far. Perhaps the most natural statement
we’ve seen is the noise-stability rephrasing of the (4/3, 2)-Hypercontractivity
2
4/3. At least in the case n
Theorem, namely Stab1/3[ f ]
1, our work in
=
≤ k
k
2
f
1[ f ]
the previous section (Theorem 9.18) generalizes this to Stabp
p for
k
−
1

2. I.e.,

≤ k

p

f

≤

≤

Stabρ[ f ]

=

E
(x,y)
ρ-correlated

[ f (x) f (y)]

f

2
1
k

ρ

+

≤ k

ρ

for 0
ization for two functions f , g : {

≤

≤

1. Looking at this, you might naturally guess a (correct) general-

1, 1}n

−
→
[ f (x)g(y)]

R, namely

f

1
k

ρk
+

g

1

ρ.
+

k

≤ k

(9.12)

E
(x,y)
ρ-correlated

We have a nice interpretation of this inequality when f , g : {
{0, 1}
1, 1}n as in Corollary 9.8; it gives an upper
are indicators of subsets A, B
bound on the probability of going from A to B in one step on the ρ-stable
hypercube graph. This bound is sharp when A and B have the same volume,
but for A and B of different sizes you might imagine it’s helpful to measure f
and g by different norms in (9.12). To see what we can expect, let’s break up
the ρ-correlation in (9.12) into two parts; say, write

{
−

→

−

⊆

1, 1}n

prs,

ρ

=

r, s

0

≤

≤

1,

and use

E
(x,y)
prs-correlated
Then Cauchy–Schwarz implies

[ f (x)g(y)]

E[Tpr f

Tps g].

·

=

E
(x,y)
ρ-correlated

[ f (x)g(y)]

E[Tpr f

Tps g]

·

Tpr f

≤ k

Tps g
k

2
k

2
k

f

r

1
k

+

k

g

1
k

+

s,

≤ k

=

(9.13)
where the last step used (p, 2)-hypercontractivity – which we have so far
only proven in the case n
1 (Theorem 9.18). The inequality (9.13), restated
below, is precisely the desired two-function version of the (2, q)- and (p, 2)-
Hypercontractive Theorems.

=

(Weak) Two-Function Hypercontractivity Theorem. Let f , g : {
R, let 0
ρ

1, and assume 0

1. Then

prs

r, s

−

1, 1}n

→

≤

≤

≤

≤
[ f (x)g(y)]

≤

f

r

1
k

+

k

g

1
k

+

s.

≤ k

E
(x,y)
ρ-correlated

We call this the “Weak” Two-Function Hypercontractivity Theorem be-
1 is not actually necessary; see Chapter 10.1. As
1. However,

cause the hypothesis r, s
mentioned, we have so far established this theorem in the case n

≤

=

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 15 -->
9.4. Two-function hypercontractivity and induction

261

the beauty of hypercontractivity in this form is that it extends to general n
by an almost trivial induction. The form of the induction is “induction by
restrictions”. (It’s also possible – but a little trickier – to extend the (2, q)-
1 to general n via “induction by deriva-
Hypercontractivity Theorem from n
tives”; see Exercise 9.16.) For future use, we will write the induction in more
general notation.

=

Two-Function Hypercontractivity Induction Theorem. Let 0
and assume that

ρ

≤

≤

1

[ f (x)g(y)]

E
(x,y)
ρ-correlated

f

p

k

k

g

q

k

≤ k

holds for every f , g
L2(Ωn, π⊗

n).

∈

L2(Ω, π). Then the inequality also holds for every f , g

∈

>

1, let f , g

L2(Ωn, π⊗

∈
n. We’ll use the notation x

Proof. The proof is by induction on n, with the n
1 case holding by assump-
n) and let (x, y) denote a ρ-correlated pair
tion. For n
under π⊗
1), and
=
−
similar notation for y. Note that (x0, y0) and (xn, yn) are both ρ-correlated
1 and 1, respectively). We’ll also write f xn =
pairs (of length n
xn for the
restriction of f in which the last coordinate is ﬁxed to value xn, and similarly
for g. Now

(x0, xn) where x0

(x1, . . . , xn

f[n

−

=

=

1]

−

|

[ f (x)g(y)]

E
(x,y)

E
(xn,yn)

=

E
(x0,y0)

[ f xn (x0)g yn (y0)]

E
(xn,yn)

[
k

f xn k

p

g yn k

k

q]

≤

by induction. If we write F
larly write G(yn)

L2(Ω, π) for the function xn
7→ k
q, then we may continue the above as
g yn k
where we used the base case of the induction. Finally,

[F(xn)G(yn)]

= k
f xn k

E
(xn,yn)

E
(xn,yn)

g yn k

p,xn k

[
k

≤ k

q]

=

F

∈

k

k

p

G

q,yn ,

k

p and simi-

f xn k

F

k

p,xn =

k

E
xn

[
|

F(xn)
|

p]1/p

E
xn

=

by deﬁnition, and similarly for

p
p]1/p

=

E
xn

E
x0 |

f xn k
[
k
q,yn . Thus we have established E[ f (x)g(y)]
≤
(cid:3)

f xn (x0)
|

= k

k

¡

¢

f

p

k

G
k

1/p

p]

f

p

g

q, completing the induction.

k

k

k

k
Remark 9.20. More generally, if we assume the inequality holds over each
of (Ω1, π1), . . . , (Ωn, πn), then it also holds over (Ω1
πn); the
only change needed to the proof is notational.

Ωn, π1

× · · · ×

⊗ · · · ⊗

At this point, we have fully established the Weak Two-Function Hyper-
contractivity Theorem. By taking g
ρ in the theorem we
=
obtain the full (p, 2)-Hypercontractivity Theorem stated at the beginning of
the chapter. Finally, by applying Proposition 9.19 we also obtain the (2, q)-
Hypercontractivity Theorem for all f : {

f and r

1, 1}n

R.

=

=

s

−

→

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 16 -->
262

9. Basics of hypercontractivity

9.5. Applications of hypercontractivity

With the (2, q)- and (p, 2)-Hypercontractivity Theorems in hand, let’s revisit
some applications we saw in Sections 9.1 and 9.2. We begin by deducing a
generalization of the Bonami Lemma:

Theorem 9.21. Let f : {

k

1

q

−

f

2 for any q
k

k

≥

p
Proof. We have

−
2.

1, 1}n

R have degree at most k. Then

→

f

k

q

k

≤

f

k

2
q = k
k

T1/pq

1Tpq
−

1 f
−

2
2

2
q ≤ k
k

1 f
−

Tpq
(Here we are extending the
j; see also Remark 8.29.) The result

k

using the (2, q)-Hypercontractivity Theorem.
deﬁnition of Tρ to ρ
now follows since

1 via Tρ f

j ρ j f =

>

=

Tpq

k

1 f
−

2
2 =
k

k

j
0
=
X

(q

−

P
1) jW j[ f ]

1)k

(q

−

≤

k

j
0
=
X

W j[ f ]

(q

1)k

f

2
2.
k

k

−

=

(cid:3)

Using a trick similar to the one in our proof of the (4/3, 2)-Hypercontractivity
p when f has de-
p
2; see Exercise 9.14. However, a different trick yields a

Theorem you can use this to deduce
gree k for any 1
p
strictly better result, including a ﬁnite bound for p

1)k

2
k

(1/

p

≤

≤

≤

−

k

k

k

f

f

1:

=

Theorem 9.22. Let f : {

1, 1}n

R have degree at most k. Then

More generally, for 1

≤

→

2 it holds that

−
p

≤

f

k

2
k

≤

2
p −

1)k

(e

p.

f

k

k

f

k

2
k

≤

ek

f

1.
k

k

2 to Exercise 9.15. For ²

Proof. We prove the statement about the 1-norm, leaving the case of general
1
θ
p
1
−
2
²
≤
+
1
(namely, θ
² ). Applying the general version of Hölder’s inequality and
2
+
then Theorem 9.21, we get

1 be the solution of 1

0, let 0

θ
1 +

2 =

≤

>

<

<

=

θ

1

²

k
1
Dividing by
2
k
result to the power of 1/θ yields

≤ k

k

−

f

θ

f

2

f

1
2
k

θ
−
² k
+

f

θ
1 ≤
k

p1

k(1

θ)

−

²

f

θ

−

1
2
k

f

θ
1.

k
k
(which we may assume is nonzero) and then raising the

+

k

k

f

(1

1
θ
−
2θ

²)

k

f

2
k
=
The result follows by taking the limit as ²

1
k

+

≤

k

k

³

´

k

1
² +

1
2

²)

´

f

1.
k

k

(cid:3)

(1

+
0.

³
→

In the linear case of k

i ai xi

that c p
≤ k
depending only on p
P
P
∈

2
k

k

=
i ai xi
[1,

1, Theorems 9.21 and 9.22 taken together show
C p

k
). This fact is known as Khintchine’s Inequality.

2 for some constants 0
k

i ai xi

C p

c p

≤

<

<

k

p

∞

P

Theorem 9.21 can be used to get a strong concentration bound for degree-k
ai xi

Boolean functions. Chernoff tells us that the probability a linear form

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.

P



<!-- pdf-page: 17 -->
9.5. Applications of hypercontractivity

263

exceeds t standard deviations decays like exp(
generalizes this to degree-k forms, with decay exp(

−

Θ(t2)). The following theorem

Θ(t2/k)):

−

Theorem 9.23. Let f : {

k

p2e

we have

t

≥

1, 1}n

−

R have degree at most k. Then for any

→

Pr
{
−
∼

1,1}n

[
|

x

f (x)

| ≥

f

t

k

k

2]

≤

exp

k

2e t2/k

.

´

−
³

f
Proof. We may assume
k
parameter to be chosen later. By Markov’s inequality,

2
k

1 without loss of generality. Let q

=

2 be a

≥

Pr[
|

f (x)

| ≥

t]

Pr[
|

f (x)
|

=

tq]

q

≥

≤

E[
|

f (x)
|
tq

q]

.

By Theorem 9.21 we have

q]

(

q

E[
|

f (x)
|
(qk/2/t)q. It’s not hard to see that the q that minimizes
Thus Pr[
|
this expression should be just slightly less than t2/k. Speciﬁcally, by choosing
q

2 we get

t2/k/e

f (x)

| ≥

p

(q

≤

≤

−

−

≤

t]

1

k

f

1)(k/2)q

q(k/2)q.

q
2 =
k

k

)q

=

≥

Pr[
|

f (x)

| ≥

t]

≤

as claimed.

exp(

(k/2)q)

−

exp

=

−
³

k

2e t2/k

´

(cid:3)

We can use Theorem 9.22 to get a “one-sided” analogue of Theorem 9.7,
showing that a low-degree function exceeds its mean with noticeable proba-
bility:

Theorem 9.24. Let f : {
most k. Then

−

1, 1}n

R be a nonconstant function of degree at

→

f (x)

>

E[ f ]

≥

1
4 e−

2k.

£
0 without loss of generality. We then have

¤

Pr
{
−
∼

1,1}n

x

Proof. We may assume E[ f ]

f

1
2 k

1
k

=

1
2

E[ f

1{ f (x)

·

=
0}]
>

hence,

f

1
4 k

2
1 =
k

E[ f

¡

·

E[ f

(1

·

−

1{ f (x)

0})]
>

=

E[ f

1{ f (x)

0}];
>

·

−

¢

1{ f (x)

0}]2
>

≤

E[ f 2]

E[12

{ f (x)

0}]
>

≤

e2k

f

2
1 ·
k

k

·

Pr[ f (x)

0]

>

using Cauchy–Schwarz and Theorem 9.22. The result follows.

(cid:3)

Next we turn to noise stability. Using the (p, 2)-Hypercontractivity Theo-
rem we can immediately deduce the following generalization of Corollary 9.8:

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 18 -->
264

9. Basics of hypercontractivity

Small-Set Expansion Theorem. Let A
1A : {

{0, 1} satisfy E[1A]

1, 1}n

⊆
α. Then for any 0

{
−

−

→

Stabρ[1A]

=

[x

∈

A, y

A]

∈

≤

ρ

1,

≤
2
ρ .
+

1

≤
α

=
Pr
1,1}n
x
{
−
∼
Nρ(x)
y
∼

1, 1}n have volume α; i.e., let

Equivalently (for α

0),

>

y

1
1

ρ
−
ρ .
+

α

A]

≤

∈

[y

Pr
A
x
∼
Nρ(x)

∼

In other words, the δ-noisy hypercube is a small-set expander for any δ

0:
A stays inside A is at most
the probability that one step from a random x
αδ/(1
δ). It’s also possible to derive a “two-set” generalization of this fact using
−
the Two-Function Hypercontractivity Theorem; we defer the discussion to
Chapter 10.1 since the most general result requires the non-weak form of the
theorem. We can also obtain the generalization of Corollary 9.12:

>

∼

Corollary 9.25. Let f : {
Inf(ρ)
Infi[ f ]
i

[ f ]

ρ for all i.
+

−

1

2

1, 1}n

≤

1, 1}. Then for any 0

{
−

ρ

≤

≤

1 we have

→

Finally, from the Small-Set Expansion Theorem we see that indicators
of small-volume sets are not very noise-stable and hence can’t have much
of their Fourier weight at low levels. Indeed, using hypercontractivity we
can deduce the Level-1 Inequality from Chapter 5.4 and also generalize it to
higher degrees.

Level-k Inequalities. Let f : {
N+ be at most 2 ln(1/α). Then
k
k[ f ]

∈

W≤

−

2e
k ln(1/α)

k

α2.

≤

1, 1}n

{0, 1} have mean E[ f ]

α and let

=

→

¢
Proof. By the Small-Set Expansion Theorem,
kα2/(1
+

kStabρ[ f ]

k[ f ]

W≤

ρ−

ρ−

¡

≤

≤

ρ)

ρ−

kα2(1
−

ρ)

≤

1. Basic calculus shows the right-hand side is minimized when
(cid:3)

≤
1; substituting this into ρ−

kα2(1
ρ) yields the claim.
−

1, a slightly different argument gives the sharp Level-1
=
2α2 ln(1/α); see Exercise 9.18.

ρ

<

for any 0
ρ

=

k
2 ln(1/α) ≤
For the case k
Inequality W1[ f ]

≤

9.6. Highlight: The Kahn–Kalai–Linial Theorem

Recalling the social choice setting of Chapter 2.1, consider a 2-candidate, n-
voter election using a monotone voting rule f : {
1, 1}. We assume
the impartial culture assumption (that the votes are independent and uni-
formly random), but with a twist: one of the candidates, say b
1, 1}, is able

1, 1}n

{
−

→

−

∈
Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.

{
−



<!-- pdf-page: 19 -->
9.6. Highlight: The Kahn–Kalai–Linial Theorem

265

to secretly bribe k voters, ﬁxing their votes to b. (Since f is monotone, this is
always the optimal way for the candidate to ﬁx the bribed votes.) How much
can this inﬂuence the outcome of the election? This question was posed by
Ben-Or and Linial in a 1985 work [BL85, BL90]; more precisely, they were
interested in designing (unbiased) voting rules f that minimize the effect of
any bribed k-coalition.

1.

Let’s ﬁrst consider k

If voter i is bribed to vote for candidate b
(but all other votes remain uniformly random), this changes the bias of f by
b
bInfi[ f ]. Here we used the assumption that f is monotone (i.e., Propo-
sition 2.21). This led Ben-Or and Linial to the question of which unbiased
b
f : {
1, 1} has the least possible maximum inﬂuence:

1, 1}n

f (i)

=

=

−

→
Deﬁnition 9.26. Let f : {

{
−

1, 1}n

−
MaxInf[ f ]

R. The maximum inﬂuence of f is

max{Infi[ f ] : i

[n]}.

∈

→

=

1, 1}n
Ben-Or and Linial constructed the (nearly) unbiased Tribesn : {
→
O( log n
n ).
1, 1} function (from Chapter 4.2) and noted that MaxInf[Tribesn]
{
−
Ω( log n
They further conjectured every unbiased function f has MaxInf[ f ]
n ).
This conjecture was famously proved by Kahn, Kalai, and Linial [KKL88]:

−
=

=

Kahn–Kalai–Linial (KKL) Theorem. For any f : {

1, 1}n

1, 1},

{
−

→

MaxInf[ f ]

Var[ f ]

≥

Ω

·

log n
n

³

−
.

´

Notice that the theorem says something sensible even for very biased
functions f , i.e., those with low variance. The variance of f is indeed the right
“scaling factor” since

1
n

Var[ f ]

≤

MaxInf[ f ]

Var[ f ]

≤

holds trivially, by the Poincaré Inequality and Exercise 2.8.

Before proving the KKL Theorem, let’s see an additional consequence for

Ben-Or and Linial’s problem.

Proposition 9.27. Let f : {

1, 1}n
.99. Then there exists a subset J

−

−
vote 1” causes the outcome to be 1 almost surely; i.e.,

| ≤

|

{
→
−
[n] with
⊆

1, 1} be monotone and assume E[ f ]

J

≥
O(n/ log n) that if “bribed to

.99 there exists J

E[ f J

(1,...,1)]

|

.99.

≥
[n] with

(9.14)

J

|

| ≤

O(n/ log n) such that

⊆

Similarly, if E[ f ]
E[ f J

1,...,

(

≤
.99.

1)]
−

≤ −

|

−

Proof. By symmetry it sufﬁces to prove the result regarding bribery by can-
1. The candidate executes the following strategy: First, bribe the
didate
f ; then bribe the voter i2 with
voter i1 with the largest inﬂuence on f0

+

=

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 20 -->
266

9. Basics of hypercontractivity

the largest inﬂuence on f1
inﬂuence on f2

f (i1,i2

7→

7→
1); etc. For each t

=

=

N we have

∈

f (i1

1); then bribe the voter i3 with the largest

E[ f t

1]
+

≥

E[ f t]

+

MaxInf[ f t].

.99; thus Var[ f t]

If after t bribes the candidate has not yet achieved (9.14) we have
≤
E[ f t]
≥
<
Ω( log n
n ). Thus the candidate will achieve a bias of at least .99 after bribing at
(cid:3)
most (.99

.99
Ω(1) and the KKL Theorem implies MaxInf[ f t]

O(n/ log n) voters.

≥

−

.99))/Ω( log n
n )

(
−

−

=

Thus in any monotone election scheme, there is always a candidate b
∈
1, 1} and a o(1)-fraction of the voters that b can bribe such that the election
{
−
becomes 99%-biased in b’s favor. And if the election scheme was not terribly
biased to begin with, then both candidates have this ability. For a more
precise version of this result, see Exercise 9.27; for a nonmonotone version,
see Exercise 9.28. Note also that although the Tribesn function is essentially
optimal for standing up to a single bribed voter, it is quite bad at standing
up to bribed coalitions: by bribing just a single tribe (DNF term) – about
log n voters – the outcome can be completely forced to True. Nevertheless,
Proposition 9.27 is close to sharp: Ajtai and Linial [AL93] constructed an
unbiased monotone function f : {
1, 1} such that bribing any set of
−
at most ²n/ log2 n voters changes the expectation by at most O(²).

1, 1}n

{
−

→

≤

The remainder of this section is devoted to the proof of the KKL The-
orem and some variants. As mentioned earlier, the proof quickly follows
from summing Corollary 9.12 over all coordinates; but let’s give a more
leisurely description. We’ll focus on the main case of interest: showing that
1). If f ’s total inﬂu-
MaxInf[ f ]
ence is at least, say, .1 log n, then even the average inﬂuence is Ω( log n
n ). So we
may as well assume I[ f ]

n ) when f is unbiased (i.e., Var[ f ]

Ω( log n

.1 log n.

≥

=

This leads us to the problem of characterizing (unbiased) functions with
small total inﬂuence. (This is the same issue that arose at the end of Chap-
ter 8.4 when studying sharp thresholds.) It’s helpful to think about the case
that the total inﬂuence is very small – say I[ f ]
100,
.1 log n. Let’s think of f as the indi-
though we eventually want to handle K
1, 1}n, so I[ f ]
cator of a volume-1/2 set A
n is the fraction of Hamming cube
edges on the boundary of A. The edge-isoperimetric inequality (or Poincaré
Inequality) tells us that I[ f ]
n fraction of the cube’s edges must
be on A’s boundary, with dictators and negated-dictators being the minimiz-
ers. Now what can we say if I[ f ]
K; i.e., A’s boundary has only K times
more edges than the minimum? Must f be “somewhat similar” to a dictator
or negated-dictator? Kahn, Kalai, and Linial showed that the answer is yes:

1: at least a 1

K where K

10 or K

{
−

≤

≥

≤

=

⊂

=

=

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 21 -->
9.6. Highlight: The Kahn–Kalai–Linial Theorem

267

O(K). This should be con-
f must have a coordinate with inﬂuence at least 2−
sidered very large (and dictator-like), since a priori all of the inﬂuences could
have been equal to K
n .

KKL Edge-Isoperimetric Theorem. Let f : {
I[ f ]/ Var[ f ]
stant and let

I[ f ]

−

1 (which is just I[ f ] if f is unbiased). Then

1, 1}n

{
−

→

1, 1} be noncon-

=

≥

e

MaxInf[ f ]

9
I[ f ]2

·

´

≥

³

9−

I[ f ].

e

This theorem is sharp for

1 (cf. Exercises 1.19, 5.35), and it’s non-
trivial (in the unbiased case) for I[ f ] as large as Θ(log n). This last fact lets us
e
complete the proof of the KKL Theorem as originally stated:

I[ f ]

=

e

Proof of the KKL Theorem from the Edge-Isoperimetric version.
We may assume f is nonconstant. If
are done: the total inﬂuence is at least .1 Var[ f ]
.1 Var[ f ]

log n
n . Otherwise, the KKL Edge-Isoperimetric Theorem implies

log n and hence MaxInf[ f ]

I[ f ]/ Var[ f ]

.1 log n, then we

I[ f ]

≥

=

≥

e

·

·

MaxInf[ f ]

≥

Ω

1
log2 n

³

·

´

.1 log n

9−

=

Ω(n−

.1 log 9)

=

Ω(n−

.317)

Var[ f ]

À

e

log n
n

Ω

·

³

.
(cid:3)

´

(You are asked to be careful about the constant factors in Exercise 9.30.)

We now turn to proving the KKL Edge-Isoperimetric Theorem. The high-
level idea is to look at the contrapositive: supposing all of f ’s inﬂuences are
small, we want to show its total inﬂuence must be large. The assumption here
is that each derivative Di f is a {
1, 0, 1}-valued function which is nonzero only
on a “small” set. Hence “small-set expansion” implies that each derivative has
“unusually large” noise sensitivity. (We are really just repeating Corollary 9.12
in words here.) In turn this means that for each i
[n], the Fourier weight
of f on coefﬁcients containing i must be quite “high up”. Since this holds for
all i we deduce that all of f ’s Fourier weight must be quite “high up” – hence
f must have “large” total inﬂuence. We now make this story formal:

−

∈

Proof of the KKL Edge-Isoperimetric Theorem. We treat only the case
that f is unbiased, leaving the general case to Exercise 9.29 (see also the ver-
sion for product space domains in Chapter 10.3). The theorem is an immediate
consequence of the following chain of inequalities:

I[ f ]

3−

3

·

(a)

≤

3Stab1/3[ f ]

(b)

≤

I(1/3)[ f ]

(c)

≤

n

i
1
=
X

Infi[ f ]3/2 (d)
≤

MaxInf[ f ]1/2

I[ f ].

·

The key inequality is (c), which comes from summing Corollary 9.12 over all
MaxInf[ f ]1/2
[n]. Inequality (d) is immediate from Infi[ f ]3/2
coordinates i

∈
≤
Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.

·



<!-- pdf-page: 22 -->
268

9. Basics of hypercontractivity

Infi[ f ]. Inequality (b) is trivial from the Fourier formulas (recall Fact 2.53):

I(1/3)[ f ]

S

|

=

1 |

S
|≥
X|

(1/3)|

S

1

|−

f (S)2

3

≥

S

|

f (S)2

=

3Stab1/3[ f ]

(1/3)|
S
1
|≥
X|

(the last equality using
=
using the spectral sample: for S

)
;

f (

b
(1/3)|

S

|

3Stab1/3[ f ]

3

=

[n]

S
⊆
X

b

b
0). Finally, inequality (a) is quickly proved

b

∼
f (S)2

S f we have

3 E[3−|

S

|]

3−

S

E[
|

]

|

3

·

≥

3

·

=

=

3−

I[ f ],

(9.15)

the inequality following from convexity of s

3−

s.

7→

(cid:3)

We end this chapter by deriving an even stronger version of the KKL Edge-
Isoperimetric Theorem, and deducing Friedgut’s Junta Theorem (from the end
of Chapter 3.1) as a consequence. The KKL Edge-Isoperimetric Theorem tells
K then f must look somewhat like a 1-junta,
us that if f is unbiased and I[ f ]
O(K). Friedgut’s
in the sense of having a coordinate with inﬂuence at least 2−
Junta Theorem shows that in fact f must essentially be a 2O(K)-junta. To
obtain this conclusion, you really just have to sum Corollary 9.12 only over
the coordinates which have small inﬂuence on f . It’s also possible to get
even stronger conclusions if f is known to have particularly good low-degree
Fourier concentration. In aid of this, we’ll start by proving the following
somewhat technical-looking result:

≤

Theorem 9.28. Let f : {

1, 1}n

−

1, 1}. Given 0

{
−

1 and k

²

<

≤

≥

0, deﬁne

→

²2
I[ f ]2

τ

=

9−

k,

J

{ j

∈

=

[n] : Inf j[ f ]

τ},

≥

so

J

|

| ≤

(I[ f ]3/²2)9k.

Then f ’s Fourier spectrum is ²-concentrated on

F

=

{S : S

J}

{S :

S

|

| >

k}.

∪

⊆

In particular, suppose f ’s Fourier spectrum is also ²-concentrated on degree up
to k. Then f ’s Fourier spectrum is 2²-concentrated on

and f is ²-close to a

J

|

|

-junta h : {

F 0

=

{S : S

⊆
1, 1}J

−

J,

S

|

| ≤

k},

1, 1}.

{
−

→

Proof. Summing Corollary 9.12 just over i

J we obtain

Inf(1/3)
i

[ f ]

Infi[ f ]3/2

≤

≤

J
i
6∈
X

J
i
6∈
X

max
J
i
6∈

Infi[ f ]

τ1/2

≤

I[ f ]

·

≤

3−

k²,

·

J
i
6∈
X

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.

6∈
{Infi[ f ]1/2}



<!-- pdf-page: 23 -->
9.6. Highlight: The Kahn–Kalai–Linial Theorem

269

where the last two inequalities used the deﬁnitions of J and τ, respectively.
On the other hand,

Inf(1/3)
i

[ f ]

J
i
6∈
X

=

J
i
6∈
X

i
S
3
X

(1/3)|

S

1

|−

f (S)2

=

S

J

| ·

∩

31

S

|

f (S)2

−|

S |
X
S

J

| ·

∩

b

≥

F |
S
6∈
X

31

−|

S

|

f (S)2
b

k

3−

f (S)2.

≥

F
S
6∈
X
b
1 and 31
J
∩
², as claimed.
≤

| ≥

−|

F implies
F

S
|
f (S)2

S

6∈

b
S
|

≥

3−

k.

Here the last inequality used that S
6∈
Combining these two deductions yields

J

-junta sgn( f ⊆

As for the second part of the theorem, when f ’s Fourier spectrum is 2²-
P
concentrated on F 0 it follows from Proposition 3.31 that f is 2²-close to the
J). From Exercise 3.34 we may deduce that f
Boolean-valued
(cid:3)
is in fact ²-close to some h : {

{
−
Remark 9.29. As you are asked to show in Exercise 9.31, by using Corol-
η/²1
lary 9.25 in place of Corollary 9.12, we can achieve junta size (I[ f ]2
+
C(η)k in Theorem 9.28 for any η

0, where C(η)

1, 1}J

1, 1}.

1)2.

(2/η

η)
+

→

−

b

·

|

|

>

=

+

In Theorem 9.28 we may always take k
Proposition 3.2. Thus we obtain as a corollary:

=

I[ f ]/², by the “Markov argument”

Friedgut’s Junta Theorem. Let f : {
−
f is ²-close to an exp(O(I[ f ]/²))-junta.
J
|
J :

I[ f ]/²}.

| ≤
S
|

| ≤

1, 1}n
<
Indeed, there is a set J

1, 1} and let 0

{
−

→

1. Then
[n] with

²

≤
⊆

⊆

exp(O(I[ f ]/²)) such that f ’s Fourier spectrum is 2²-concentrated on {S

As mentioned, we can obtain stronger results for functions f that are ²-
concentrated up to degree much less than I[ f ]/². Width-w DNFs, for example,
are ²-concentrated on degree up to O(w log(1/²)) (by Theorem 4.22). Thus:

Corollary 9.30. Any width-w DNF is ²-close to a (1/²)O(w)-junta.

Uniformly noise-stable functions do even better. From Peres’s Theorem we
know that linear threshold functions are ²-concentrated up to degree O(1/²2).
Thus Theorem 9.28 and Remark 9.29 imply:

Corollary 9.31. Let f : {
let 0

², η

−

1/2. Then f is ²-close to a junta on I[ f ]2
+

→

{
−

1, 1} be a linear threshold function and
(1/η)O(1/²2) coordinates.

η

1, 1}n

<

≤

·

1/ log(O(I[ f ])) and
Assuming ² is a small universal constant we can take η
deduce that every LTF is ²-close to a junta on I[ f ]2
polylog(I[ f ]) coordinates.
Θ(pn), but Majn is not even
This is essentially best possible since I[Majn]
.1-close to any o(n)-junta. By virtue of Theorem 5.37 on the uniform noise
stability of PTFs, we can also get this conclusion for any constant-degree PTF.

=

=

·

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 24 -->
270

9. Basics of hypercontractivity

One more interesting fact we may derive is that every Boolean function
has a Fourier coefﬁcient that is at least inverse-exponential in the square of
its total inﬂuence:

Corollary 9.32. Assume f : {
S
there exists S

[n] with 0

1, 1}n
{
−
O(I[ f ]) such that

1, 1} satisﬁes Var[ f ]
f (S)2

exp(

→

1/2. Then

≥
O(I[ f ]2)).

⊆

−
| ≤

< |

≥

−

=

exp(O(I[ f ])) such that f has Fourier weight at least 1

1/8 in Friedgut’s Junta Theorem we get a set of coordinates

Proof. Taking ²
J with
J
|
)2
3/4 on F
=
| ≤
that f has Fourier weight at least 1/4 on F 0
=
=
exp(O(I[ f ]2)), so the result follows by the Pigeonhole Principle. (Here we used
(cid:3)
that (1/4) exp(

=
1/2 we conclude
J

O(I[ f ]2)) because I[ f ]

8I[ f ]}. Since

1
−
F \ {

O(I[ f ]2))

≤
}. But

| ≤
{S
=

Var[ f ]

Var[ f ]

exp(

| ≤ |

F 0

8I[ f ]

J :

2²

f (

;

;

⊆

−

S

b

b

|

|

|

≥

1
2 .)

≥

−

=

−

Remark 9.33. Of course, if Var[ f ]
)2
f (
coefﬁcient:
Exercise 9.32.
b

;

≥

1/2, then f has a large empty Fourier
1/2. For a more reﬁned version of Corollary 9.32, see

<

It is an open question whether Corollary 9.32 can be improved to give a

Fourier coefﬁcient satisfying

f (S)2

≥

b
9.7. Exercises and notes

exp(

O(I[ f ])) (but see Exercise 9.33).

−

<
+

9.1 For every 1
such that 1

B show that there is a b-reasonable random variable X

b
X is not B-reasonable.

<

9.2 For k

−

1, 1}n

1, improve the 9 in the Bonami Lemma to 3. More precisely,
=
R has degree at most 1 and that x1, . . . , xn are
suppose f : {
independent 3-reasonable random variables satisfying E[xi]
0.
1 bits.) Show that f (x) is also
(For example, the xi’s may be uniform
3-reasonable. (Hint: By direct computation, or by running through the
Bonami Lemma proof with k

1 more carefully.)

E[x3
i ]

→

=

±

=

9.3 Let k be a positive multiple of 3 and let n

2k be an integer. Deﬁne

≥

=

f : {

1, 1}n

−

R by

→

f (x)

=

(a) Show that

xS.

[n]
k

S
⊆
X
S
|=

|

E[ f 4]

≥ ¡

n

k/3, k/3, k/3, k/3, k/3, k/3, n

2

n
k

E[ f 2]2,

2k

−

¢

where the numerator of the fraction is a multinomial coefﬁcient –
speciﬁcally, the number of ways of choosing six disjoint size-k/3 sub-
sets of [n]. (Hint: Given such size-k/3 subsets, consider quadruples of
size-k subsets that hit each size-k/3 subset twice.)

¡

¢

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 25 -->
9.7. Exercises and notes

271

(b) Using Stirling’s Formula, show that

n

k/3, k/3, k/3, k/3, k/3, k/3, n

2

n
k

lim
n
→∞ ¡

2k

−

=

¢

Θ(k−

29k).

k

¢

¡

1/2)

Deduce the following lower bound for the Bonami Lemma:
≥
Ω(k−
2 and such an
4
k
k
upper bound holds for all f homogeneous of degree k; see Exercise
and 9.38(f ).)

(In fact,

Θ(k−

1/4)

p3

p3

2.

=

k

k

k

k

k

k

f

f

f

k

4

·

·

f

9.4 Prove Corollary 9.6.

δ

9.5 Let 0
≤
f
| =

|

and
ones are possible.)

1
1600 and let f , ` be real numbers satisfying

39pδ
169δ. (This is a loose estimate; stronger

≤
1. Show that

| >

`2

−

1

2

|

f

|

`

|

−

≥

9.6 Theorem 9.21 shows that the (2, 4)-Hypercontractivity Theorem implies
the Bonami Lemma. In this exercise you will show the reverse implication.

(a) Let f : {

1, 1}n

−
show that

R. For a ﬁxed δ

∈

→

(0, 1), use the Bonami Lemma to

f =

k

2
k

≤

f

1
δ k

2.
k

(b) For g : {

δ)/p3 f
T(1
k
−

∞

δ)k

k

−

≤

4
k

(1
k
0
=
X
N+, let g⊕
R and d
∈
→
d(x(1), . . . , x(d))
Tρ(g⊕
k

=
d)
k

−

1, 1}n
deﬁned by g⊕
{
−
ρ
∈

1, 1}n). Show that
[
−

1, 1]. Note the special case ρ
(c) Deduce from parts (a) and (b) that in fact

Tρ g
1.

k

= k
=

1, 1}dn

d : {
−
g(x(1))g(x(2))
d
p holds for every p

· · ·

→

p

g(x(d)) (where each x(i)

R be the function

∈
R+ and

∈

δ)/p3 f
−

4
k

f

k

≤ k

2. (Hint:

T(1
d for larger and larger d.)
f
T1/p3 f
k

4
k

k

Apply part (a) to f ⊕
(d) Deduce that in fact

2; i.e., the (2, 4)-Hypercontractivity
k
Theorem follows from the Bonami Lemma. (Hint: Take the limit as
δ

≤ k

0+.)

→

∈

9.7 Suppose we wish to show that

q
k
that it sufﬁces to show this for all nonnegative f . (Hint: Exercise 2.34.)
N. The goal of this exercise is to show that “projection to degree k

≤ k

→

−

k

9.8 Fix k

f

p for all f : {

Tρ f
k

1, 1}n

R. Show

1”. Let f : {

1, 1}n

R.

−

→

f

q. (Hint: Use Theorem 9.21

2. Show that

is a bounded operator in all L p norms, p
(a) Let q
1
−
k
f ≤

to show the stronger statement
p
k
k
f ≤
k

2. Show that

(b) Let 1

f ≤

≤

≥

≤

q

k

k

k

q

>
k

k

k
q
k
(1/

≤

q

1
−
1)k

k

k
f
k

f

2.)
k
q.
k

q

<

(Hint: Either
q
≤
give a similar direct proof using the (p, 2)-Hypercontractivity Theo-
rem, or explain how this follows from part (a) using the dual norm
Proposition 9.19.)

q
p

p

−

k

9.9 Let X be (p, q, ρ)-hypercontractive.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 26 -->
272

9. Basics of hypercontractivity

(a) Show that cX is (p, q, ρ)-hypercontractive for any c
(b) Show that ρ

.

p

R.

∈

X
X

k
k

k
k

q

≤

9.10 Let X be (p, q, ρ)-hypercontractive. (For simplicity you may want to as-

sume X is a discrete random variable.)
(a) Show that E[X ] must be 0. (Hint: Taylor expand
0; note that ρ
p
q

<
1
1 . (Hint: Taylor expand
−
−

1 by deﬁnition.)

term around ²

(b) Show that ρ
around ²

≤
0.)

1
k

=

+

q

=

ρ²X

1
k

+

k

r to one

ρ²X

r to two terms

k

9.11 (a) Suppose E[X ]

1. (Hint: Use monotonicity of norms to reduce to the case q

0. Show that X is (q, q, 0)-hypercontractive for all
1.)

=

(b) Show further that X is (q, q, ρ)-hypercontractive for all 0

q

≥

1.
X ) and employ the triangle

≤

<

=
ρ

(Hint: Write (a
inequality for

ρ X )
q.)

+
k · k

(1

−

=

ρ)a

+

ρ(a

+

(c) Show that if X is (p, q, ρ)-hypercontractive, then it is also (p, q, ρ0)-
ρ. (Hint: Use the previous exercise

hypercontractive for all 0
≤
along with Exercise 9.10(a).)

ρ0

<

9.12 Let X be a (nonconstant) (2, 4, ρ)-hypercontractive random variable. The
goal of this exercise is to show the following anticoncentration result: For
all θ

R and 0

1,

t

∈

<

<

X

Pr[
|

−

θ

| >

X

t

k

2]
k

≥

(1

−

t2)2ρ4.

(a) Reduce to the case
(b) Letting Y
(c) Using the Paley–Zygmund inequality, show that

1.
θ)2, show that E[Y ]

2
k

(X

X

=

=

−

=

+

1

k

θ2 and E[Y 2]

2
(ρ−

+

≤

θ2)2.

X

Pr[
|

−

θ

| >

t]

≥

µ

ρ2θ2

ρ2(1
−
1
+

t2)
+
ρ2θ2

2

.

¶

(d) Show that the right-hand side above is minimized for θ

0, thereby

=

completing the proof.
N+ and let f : {

1, 1}n

∈

=

9.13 Let m
1
i]
m for all i
Show that Pr[ f (x)
show that this is an upper bound on Stabρ[ f ] for all f : {
with E[ f ]
m ); see Exercise 8.33.)

[m] be “unbiased”, meaning Pr[ f (x)
=
1 and let (x, y) be a ρ-correlated pair.
ρ). (More generally, you might
+

→
ρ
≤
≤
(1/m)(1

[m]. Let 0

m

→ 4

1, 1}n

f (y)]

ρ)/(1

−

−

≤

∈

−

R have deg( f )

k. Prove that

f

p
→
−
k
for any 1
2 using the Hölder inequality strategy from our proof of
the (4/3, 2)-Hypercontractivity Theorem, together with Theorem 9.21.
2; i.e., the trickier

p
Theorem 9.22 strictly improves on the bound from part (a).

1 for all 1

(b) Verify that exp( 2

p −

2
k

p

1)

1/

<

−

≤

<

≤

≤

−

≤

≤

p

k

k

(1/

p

1)k

f

p

=
( 1
m , . . . , 1
1, 1}n
p

=
9.14 (a) Let f : {

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 27 -->
9.7. Exercises and notes

273

9.15 Prove Theorem 9.22 in full generality.
² . You will need to show that 1

θ

1
2 =

θ
p +

1
−
2
+

(Hint: Let θ be the solution of
( 1
θ
−
p −
2θ =

( 2
p −

1
2 ).)

1) 1

² +

9.16 As mentioned, it’s possible to deduce the (2, q)-Hypercontractivity The-
orem from the n
1 case using induction by derivatives. From this
one can also obtain the (p, 2)-Hypercontractivity Theorem via Proposi-
Dn f (x0),
tion 9.19. Employing the notation x
En f (x0), ﬁll in details and justiﬁcations for the following proof

(x0, xn), T

1, d
−

T1/pq

=

=

=

=

and e
=
sketch:

2/q

q

Te

(1/

q

1)xnTd

T1/pq
k
(Te)2

2
1 f
q =
k
−
(Td)2

E
x0

E
xn

+

= k

k
9.17 Deduce the p

−
(Td)2

+
|
h
£
(Te)2
q/2
≤ k
2

≤
¤
£
2
2
Td
q+k
2 = k
k
k
q cases of the Hypercontractivity Theorem from the
(2, q)- and (p, 2)-Hypercontractivity Theorems. (Hint: Use the semigroup
property of Tρ, Exercise 2.32.)

¤i
Te
= k

2
q ≤ k
k

2
2+k
k

p
+k

q/2

q/2

<

<

+

d

e

k

k

|

f

((Te)2

(Td)2)q/2

2/q

E
x0

2
2.
k

9.18 Let f : {

−

1, 1}n
α.
α2) for any 0
(a) Show that W1[ f ]
(b) Deduce the sharp Level-1 Inequality W1[ f ]

{0, 1} have E[ f ]
1
ρ)

ρ (α2/(1

=
−

→

≤

+

1.

ρ
2α2 ln(1/α). (Hint: Take

≤

<

≤

9.19 For f : {

the limit ρ
1, 1}n

−

→

→

0+.)
{0, 1} with E[ f ]

provided k

.373 ln(1/α).

≤

α, show that W≤

k[ f ]

=

o(α) (as α

0)

→

=

9.20 Show that the KKL Theorem fails for functions f : {

under the assumption Var[ f ]

Ω(1). (Hint: f (x)

9.21 (a) Show C

1, 1}n

{ f : {

1, 1}
|
−
queries to any constant error ²
rem 9.28.)

→

=

>

I[ f ]

O(

≤

0 in time poly(n).

p

1, 1}n
−
trunc[

[
→
−
1,1]( x1
−

1, 1], even
xn

).)

+···+
pn

=
log n)} is learnable from
(Hint: Theo-

(b) Show C

{monotone f : {

1, 1}n

=

able from random examples to any constant error ²

(c) Show that C

{monotone f : {

{
−

→

1, 1}n

1, 1}

I[ f ]

|

≤

1, 1}

{
−

O(

log n)} is learn-
0 in time poly(n).
p
>
poly(n)}
DTsize( f )
0 in

≤

−
is learnable from random examples to any constant error ²
time poly(n). (Hint: the OS Inequality and Exercise 8.43.)

→

=

|

>

≥
{
−

−

9.22 Deduce the following generalization of the (2, q)-Hypercontractivity The-

orem: Let f : {
1/

1 for some 0

−

q

1, 1}n

R, q
≥
1. Then

2, and assume 0

ρ

≤

≤

1 satisﬁes ρλ

≤

−

p

(Hint: Show

Tρ f
k
k
1, 1}n
[

→

−

9.23 Let f : {

≤

→
λ
≤
Tρ f
k

k
S(ρ2
2
q ≤
1, 1], let 0
P

|

q

Tρ f

1
2
≤ k
k
S
f (S)2)1

−

|

λ

−

λ

·

f

λ
2 .
k

k
f (S)2)λ and use Hölder.)
(

−
² f
T1
k
−

k

²
≤
≤
b
q
T 1
q ≤ k
p1
+

1, and assume q
b
(
k

2)1
2
k

q
q ≤

².
+

k

f

f

2²

2

+

≥

2². Show that

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 28 -->
274

9. Basics of hypercontractivity

9.24 Recall the Gaussian quadrant probability Λρ(µ) deﬁned in Exercise 5.32
t], where z1, z2 are standard Gaussians with
µ. The goal of this

by Λρ(µ)
>
=
correlation E[z1 z2]
exercise is to show that for ﬁxed 0

ρ and t is deﬁned by Φ(t)
ρ

=
1 we have the estimate

Pr[z1

t, z2

=

>

<

<

Λρ(µ)

Θ(µ

=

2

1

ρ )
+

(9.16)

→

e
0. In light of Exercise 5.32, this will show that the Small-Set
as µ
Expansion Theorem for the ρ-stable hypercube graph is essentially sharp
due to the example of Hamming balls of volume µ.
(a) First let’s do an imprecise “heuristic” calculation. We have Pr[z1

t]

=

=

≥

Pr[z1

>
t]
µ by deﬁnition. Conditioned on a Gaussian being
at least t it is unlikely to be much more than t, so let’s just pretend
ρ2 y,
t. Then the conditional distribution of z2 is ρt
that z1
=
where y
N(0, 1) is an independent Gaussian. Using the fact that
∼
Φ(u)
“hence” (9.16) holds.

, deduce that Pr[z2

φ(u)/u as u

ρ
−
ρ ) and
+

p
1
Θ(µ
1

→ ∞

z1

−

>

=

=

+

∼

t]

1

t

|

(b) Let’s now be rigorous. Recall that we are treating 0

1 as ﬁxed
). Let φρ(z1, z2) denote the joint pdf of

<

ρ

e
<

and letting µ
z1, z2 so that

→

0 (hence t

→ ∞

Λρ(µ)

∞

∞
t
t Z
Z

=

φρ(z1, z2) dz1 dz2.

Derive the following similar-looking integral:

∞
t
t Z
Z

∞

(z2

−

ρz1)(z1

−

ρt)φρ(z1, z2) dz1 dz2

(1

ρ2)3/2
2π

−

=

exp

t2
2

2

+

ρ

¶

−

1

µ

(9.17)

and show that the right-hand side is

(c) Show that

Θ(µ

1

2

ρ ).
+

e

Pr

z1

t

1

−
ρ

>

h

i

∞

=

1

t
−
Z
ρ

φ(z1) dz1

=

Θ(µ

1
ρ2 ),

e
and that this is asymptotically smaller than

Θ(µ

2

1

ρ ).
+

(d) Deduce (9.16).

(Hint: Try to arrange that the extraneous factors
ρt) in (9.17) are both at least 1.)

e

(z2

−
9.25 Let f : {

−
{
−
→
coalitional inﬂuence of J on f to be

1, 1}, let J

−

⊆

ρz1), (z1
1, 1}n

[n], and write J

[n] \ J. Deﬁne the

=

InfJ[ f ]

=

z

Pr
{
−
∼

1,1}J

[ f J

|

z is not constant].

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.

g



<!-- pdf-page: 29 -->
9.7. Exercises and notes

275

Furthermore, for b
on f to be

1,

{
−

∈

1} deﬁne the coalitional inﬂuence toward b of J

+

Inf

b
J[ f ]

g

=

z

=

z

Pr
{
−
∼
Pr
{
−
∼

1,1}J

1,1}J

[ f J

[ f J

|

|

z can be made b]

Pr[ f

b]

=

−

z

6≡ −

b]

−

Pr[ f

=

b].

Inf ±J [ f ] rather than

For brevity, we’ll sometimes write
(a) Show that for coalitions of size 1 we have Infi[ f ]
(b) Show that 0
(c) Show that
InfJ[ f ]
g
(d) Show that if f is monotone, then
g

1.
≤
Inf +J [ f ]

Inf −J [ f ].

Inf ±J [ f ]

g

g

≤

=

+

=

Inf

b
J[ f ]

g
Pr[ f J

=

(b,...,b) =

|

Pr[ f

b]

−

=

b].

1
J [ f ].
Inf ±
Inf{i}[ f ]
2
g

=

g

g

Inf ±{i}[ f ].

g
(e) Show that
InfJ[χ[n]]
(f ) Supposing we write t

and hence
o(pn) and
J
|
Limit Theorem.)
(g) Show that max{

g

| =

1 for all J

.
6= ;

=
= |
=

g
InfJ[Majn]

InfJ[Majn]

/pn, show that
J
|
2Φ(t)
1
−
±
o(1) if
1
−

o(1). Thus
g
J
| =

=

|

Inf ±J [Majn]

Φ(t)
=
InfJ[Majn]

1
o(1)
2 ±
o(1) if
ω(pn). (Hint: Central

−
=

g
Inf

True
J

[Tribesn] :

J

log n}

1/2

other hand, show that max{
≤
duce that for some positive constant c we have max{
J
.51. (Hint: Refer to Proposition 4.12.)

[Tribesn] :

cn/ log n}

Inf

g

g

| ≤

|

|

| ≤

≤

| ≤

|
False
J

g

=
J

+
k}

Θ( log n

n ). On the
O( log n
k
n ). De-
InfJ[Tribesn] :

·

g

9.26 Show that the exponential dependence on I[ f ] in Friedgut’s Junta Theo-

rem is necessary. (Hint: Exercise 4.15.)

<

{
−

1, 1}n
→
1/2 be given.

1, 1} be a monotone function with Var[ f ]

9.27 Let f : {
−
let 0
²
<
(a) Improve Proposition 9.27 as follows: Show that there exists J
n
log n such that E[ f J

with
many bribes are required to move f ’s mean outside the interval [1
2η, 1

O(log 1
²δ )

[n]
(Hint: How

(1,...,1)]

0, and

η]?)

| ≤

².

≥

>

⊆

≥

−

−

J

1

δ

|

·

|

(b) Show that there exists J

−

n
log n such that
| ≤
². (Hint: Use Exercise 9.25(d) and take the union of two

O(log 1
²δ )

[n] with

⊆

J

|

·

1

InfJ[ f ]
≥
inﬂuential sets.)
g
1, 1}n
9.28 Let f : {
(a) Let f ∗ : {

−

−

1, 1}.
{
−

{
→
−
1, 1}n
Exercise 2.52. Show that
1, 1}, and hence also
{
−

→

−

1, 1} be the “monotonization” of f as deﬁned in

b
J[ f ] for all J

[n] and b

∈

⊆

b
J[ f ∗]

Inf
InfJ[ f ∗]

≤

g

Inf
≤
InfJ[ f ].
g

g

g

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 30 -->
276

9. Basics of hypercontractivity

(b) Let Var[ f ]
exists J
J
|
Combine part (a) with Exercise 9.27(b).)

0 and let 0
<
O(log 1
²δ )

δ
>
[n] with

| ≤

≥

⊆

·

²
<
n
log n such that

1/2 be given. Show that there
InfJ[ f ]
². (Hint:

1

≥

−

9.29 Establish the general-variance case of the KKL Edge-Isoperimetric Theo-

g

rem. (Hint: You’ll need to replace (9.15) with

3

(1/3)|
S
1
|≥
X|

S

|

f (S)2

3 Var[ f ]

·

≥

3−

I[ f ]/ Var[ f ].

b
Use the same convexity argument, but applied to the random variable S
that takes on each outcome

[n] with probability

f (S)2/ Var[ f ].)

⊆
9.30 The goal of this exercise is to attain the best known constant factor in the

; 6=

S

statement of the KKL Theorem.
(a) By using Corollary 9.25 in place of Corollary 9.12, obtain the follow-
ing generalization of the KKL Edge-Isoperimetric Theorem: For any
(nonconstant) f : {
1, 1} and 0

1, 1}n

1,

δ

b

−

{
−
δ
δ

→
1
1

1
δ

1
δ

1
I[ f ]

<
1
δ

<
1
1

δ
δ

I[ f ]

,

MaxInf[ f ]

+
−
I[ f ] denotes I[ f ]/ Var[ f ]. (Hint: Write ρ
e2 we have

where
for any constant C

−
+

≥

³

´

³

´

³

´

e

e

·

e

>
MaxInf[ f ]

1
1

δ
δ .) Deduce that
−
+

=

≥

I[ f ]).

Ω(C−
e
=
I[ f ]1/3
e

e

2

2

(b) More carefully, show that by taking δ

1
I[ f ]1/3 we can achieve

MaxInf[ f ]

exp(

≥

2

I[ f ])

−

e2

·

·

1
I[ f ]

exp(

−

I[ f ]1/3).

1
4

·

(Hint: Establish

1
1

1
e
δ

≥

δ
δ

−
+

exp(

(c) By distinguishing whether or not

´

³

e

´
δ2) for 0

³
2

−

e
−
I[ f ]

<
1
2 (ln n

δ

≤

−

≥

e
1/2.)

following form of the KKL Theorem: For any f : {
p
−
on(1)).

e
1
2 Var[ f ]

MaxInf[ f ]

(1

ln n
n

·

−

≥

log n), establish the
1, 1}n
{
−

1, 1},

→

9.31 Establish the claim in Remark 9.29.

9.32 Show that if f : {

1, 1}n

S

−

→

< |

1, 1} is nonconstant, then there exists S

{
−
O(I[ f ]/ Var[ f ]) such that

[n]
O(I[ f ]2/ Var[ f ]2)).
with 0
(Hint: By mimicking Corollary 9.32’s proof you should be able to establish
the lower bound Ω(Var[ f ])
O(I[ f ]2/ Var[ f ]2)). To show that this
quantity is also exp(

O(I[ f ]2/ Var[ f ]2)), use Theorem 2.39.)

f (S)2

exp(

exp(

| ≤

⊆

≥

−

−

b

·

−
1, 1} be a nonconstant monotone function. Improve

9.33 Let f : {

1, 1}n

−

{
−

→

on Corollary 9.32 by showing that there exists S
O(I[ f ]/ Var[ f ])). (Hint: You can even get
exp(
Isoperimetric Theorem and Proposition 2.21.)
R. Prove that

sparsity(

1, 1}n

−

S

f

|

4

| ≤

f )1/4

9.34 Let f : {

−

→

k
Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.

≤

k

k

f

2.
k

b

satisfying

f (S)2

6= ;

≥
1; use the KKL Edge-

b



<!-- pdf-page: 31 -->
9.7. Exercises and notes

277

9.35 Let q
=
1, 1}n
{
−
ing that

→

2r be a positive even integer, let ρ

1, and let f1, . . . , f r :
R. Generalize the (2, q)-Hypercontractivity Theorem by show-

1/

−

=

q

p

r

(Tρ f i)2
i
1
=
Y
(Hint: Hölder’s inequality.)

E

"

r

# ≤

i
1
=
Y

E[ f 2

i ].

9.36 In this exercise you will give a simpler, stronger version of Theorem 9.17

under the assumption that q
(a) Using the idea of Proposition 9.16, show that if x is a uniformly

2r is a positive even integer.

=

1 bit then x is (2, q, ρ)-hypercontractive if and only if ρ

(b) Show the same statement for any random variable x satisfying E[x2]

≤

=

random
q
1/

±
1.

−

p
1 and

E[x2 j
i

1

−

]

=

0, E[x2 j
i ]

(2r

−

≤

1) j

r
j
2r
¢
¡
2 j

for all integers 1

r.

j

≤

≤

¡
(c) Show that none of the even moment conditions in part (b) can be

¢

relaxed.

9.37 Let q

2r be a positive even integer and let f : {

=

neous of degree k
=
slightly on the generalized Bonami Lemma, Theorem 9.21.
(a) Show that

1 (i.e., f

f =

≥

R be homoge-
1, 1}n
k). The goal of this problem is to improve

→

−

E[ f q]

=

f (S1)

· · ·

f (Sq)

≤

|

f (S1)

| · · · |

f (Sq)
|

,

(9.18)

X

X

b

where the sum is over all tuples S1, . . . , Sk satisfying S1
b

.
= ;
(b) Let G denote the complete q-partite graph over vertex sets V1, . . . , Vq,
each of cardinality k. Let M denote the set of all perfect matchings
in G. Show that the right-hand side of (9.18) is equal to

4 · · · 4

Sq

b

b

1
(k!)q

`:M

[n] |

M

M
∈
X

→
X
where T j(M, `) denotes
(c) Show that (9.19) is equal to

S

n

n

n

1
(k!)q

·

(rk)!

M

M
X
∈

i1
1
=
X

1 · · ·
i2
=
X

1 |
i rk
=
X

f (T1(M, `))

f (Tq(M, `))

,

|

| · · · |

(9.19)

b
{`(e) : e

M, e

∈

b
Vj

∩

}.

6= ;

f (U1(M, i1, . . . , i rk))

| · · · |

f (Uq(M, i1, . . . , i rk))
|

,

(9.20)
where M is the set of ordered perfect matchings of G, and now
U j(M, i1, . . . , i rk) denotes

{i t : M(t)

Vj

}.

b

b

∩

6= ;

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.

S



<!-- pdf-page: 32 -->
278

9. Basics of hypercontractivity

(d) Show that for any M

M we have

∈

n

n

n

i1
1
=
X

1 · · ·
i2
=
X

1 |
i rk
=
X

f (U1(M, i1, . . . , i rk))

| · · · |

f (Uq(M, i1, . . . , i rk))

|

b

b

n

≤ Ã

j1,..., jk
X

1

=

f ({ j1, . . . , jk})2

r

!

b

(Hint: Use Cauchy–Schwarz rk times.)
(k!)r

(e) Deduce that

M

f

q
q ≤

1
(k!)q · |
(rk)!

·

k

k

f

2r
2 and hence
k

k

| ·
1/q

M

|
pk! k
9.38 The goal of this problem is to estimate

≤

k

k

q

|

f

f

2.

k
M

give a concrete improvement on Theorem 9.21.
4, k
(a) Show that for q
60.
(b) Show that
(qk

=
|
1)!!. (Hint: Show that (qk

2 we have

| =

M

M

1)!! is the number
of perfect matchings in the complete graph on qk vertices.) Deduce

−

−

=
| ≤

from Exercise 9.37 so as to

|

|

|
pqk
q
k
(c) Show that

≤

k

f

f
2.
k
k
M
|
| ≤

1

( 2r
−
r

)rk(rk)!2, and thereby deduce

f

q

k
1/q

≤

k
(rk)!
k!r rrk

Cq,k

·

k

1

q

−

f

2,
k

k

p

=

. (Hint: Suppose that the ﬁrst t edges of the
where Cq,k
perfect matching have been chosen; show that there are ( 2r
t)2
−
r
choices for the next edge. The worst case is if the vertices used up so
far are spread equally among the q parts.)

)(rk

−

³

´

1

(d) Give a simple proof that Cq,k
Θ(1)
(e) Show that in fact Cq,k
(f ) Can you obtain the improved estimate

≤
k−
·

=

1, thereby obtaining Theorem 9.21.
1/4

1/(2q). (Hint: Stirling’s Formula.)
+

M

1/q

|

|

pk! =

Θq(1)

1/4

k−

·

·

k

1

?

q

−

p

(Hint: First exactly count – then estimate – the number of perfect
matchings with exactly e i j edges between parts i and j. Then sum
your estimate over a range of the most likely values for e i j.)

p

< ∞

there are constants 0

Notes. The history of the Hypercontractivity Theorem is complicated. Its
earliest roots are in the work of Paley [Pal32] from 1932; he showed that for
1

S f
≤ k
≤
k
<
n
1(dt f )2 is the
C p
t
→
=
“square function” of f , and dt f
f (S) χS is the martingale differ-
S:max(S)
ence sequence for f deﬁned in Exercise 8.17. The main task in Paley’s work
is to prove the statement when p is an even integer; other values of p follow

such that c p
n
t

<
R. Here S f

p holds for any f : {

<
1, 1}n

S f
k

qP

< ∞

C p

c p

P

P

=

−

=

b

k

k

k

=

=

f

p

p

1

t

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 33 -->
9.7. Exercises and notes

279

by the Riesz(–Thorin) interpolation theorem. Using this result, Paley showed
R is homogeneous of
the following hypercontractivity result: If f : {
→
R+. Some extensions of
degree 2, then c0pk
k
Paley’s work are in [Wat64].

2 for any p

C0pk

1, 1}n

≤ k

2
k

≤

−

∈

k

f

f

f

p

k

→

In 1968 Bonami [Bon68] stated the following variant of Theorem 9.21:
R is homogeneous of degree k, then for all q

1, 1}n
If f : {
−
≤
ckpq
2, where the constant ck may be taken to be 1 if q is an even integer.
f
k
She remarks that this theorem can be deduced from Paley’s result but with a
much worse (exponential) dependence on q. The proof she gives is combinato-
rial and actually only treats the case k
2 and q an even integer; it is similar
to Exercise 9.37.

2,

≥

=

k

k

f

q

Independently in 1969, Kiener [Kie69] published his Ph.D. thesis, which
R is
extended Paley’s hypercontractivity result as follows: If f : {
R+.
homogeneous of degree k, then c p,k
f
k
The proof is an induction on k, and again the bulk of the work is the case of
even integer p. Kiener also gave a long combinatorial proof showing that if
51 E[ f 2]2. (Exer-
f : {
cise 9.38(a) improves this 51 to 15.)

R is homogeneous of degree 2, then E[ f 4]

1, 1}n
→
2 for any p
∈
k

1, 1}n

C p,k

≤ k

2
k

→

−

≤

−

≤

k

k

f

f

p

Also independently in 1969, Schreiber [Sch69] considered multilinear
polynomials f over a general orthonormal sequence x1, . . . , xn of centered real
(or complex) random variables. He showed that if f has degree at most k,
2, where C depends
then for any even integer q
k
only on k, q, and the q-norms of the xi’s. Again, the proof is very similar to
Exercise 9.37; Schreiber does not estimate his analogue of
but merely
notes that it’s ﬁnite. Schreiber was interested mainly in the case that the xi’s
are Gaussian; indeed, his 1969 work [Sch69] is a generalization of his earlier
work [Sch67] speciﬁc to the Gaussian case.

4 it holds that

M

C

≤

≥

k

k

k

f

f

q

|

|

In 1970, Bonami published her Ph.D. thesis [Bon70], which contains the
full Hypercontractivity Theorem as stated at the beginning of the chapter. Her
proof follows the standard template seen in essentially all proofs of hypercon-
tractivity: ﬁrst an elementary proof for the case n
1 and then an induction
to extend to general n. She also gives the sharper combinatorial result appear-
ing in Exercises 9.37 and 9.38(c). (The stronger bound from Exercise 9.38(f )
is due to Janson [Jan97, Remark 5.20].) As in Corollary 9.6, Bonami notes
that her combinatorial proof can be extended to a general sequence of sym-
metric orthonormal random variables, at the expense of including factors of
xi
q into the bound. She points out that this includes the Gaussian case
k
independently studied by Schreiber.

=

k

Bonami’s work was published in French, and it remained unknown to
most English-language mathematicians for about a decade. In the late 1960s
and early 1970s, researchers in quantum ﬁeld theory developed the theory

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 34 -->
280

9. Basics of hypercontractivity

q

xn

Cq

+···+
pn

→ ∞

of hypercontractivity for the Gaussian analogue of Tρ, namely, the Ornstein–
Uhlenbeck operator Uρ. This is now recognized as essentially being a special
case of hypercontractivity for bits, in light of the fact that x1
tends
to a Gaussian as n
by the CLT (see Chapter 11.1). We summarize
here some of the work in this setting. In 1966 Nelson [Nel66] showed that
1 f
2. Glimm [Gli68] gave the alternative result
U1/pq
≤
k
−
that for each q
2.
k
Segal [Seg70] observed that hypercontractive results can be proved by induc-
tion on the dimension n. In 1973 Nelson [Nel73] gave the full Hypercon-
p for all
tractivity Theorem in the Gaussian setting:
k
1
. He also proved the combinatorial Exercise 9.37. The equiva-
lence to the Two-Function Hypercontractivity Theorem is from the work of
Neveu [Nev76].

≥
2 there is a sufﬁciently small ρ q

2 for all q
k

0 such that

Uρ q f
k

Up(p

≤ ∞

≤ k

≤ k

1)/(q

≥

>

≤

<

p

q

1)

k

k

k

k

k

−

−

f

f

f

f

q

q

In 1975 Gross [Gro75] introduced the notion of Log-Sobolev Inequalities
(see Exercise 10.23) and showed how to deduce hypercontractivity inequalities
from them. He established the Log-Sobolev Inequality for 1-bit functions, used
induction (citing Segal) to obtain it for n-bit functions, and then used the CLT
to transfer results to the Gaussian setting. (For some earlier results along
these lines, see the works of Federbush and Gross [Fed69, Gro72].) This gave
a new proof of Nelson’s result and also independently established Bonami’s
full Hypercontractivity Theorem. Also in 1975, Beckner [Bec75] published his
Ph.D. thesis, which proved a sharp form of the hypercontractive inequality for
purely complex ρ. (It is unfortunate that the inﬂuential paper of Kahn, Kalai,
and Linial [KKL88] miscredited the Hypercontractivity Theorem to Beckner.)
The case of general complex ρ was subsequently treated by Weissler [Wei79],
with the sharp result being obtained by Epperson [Epp89]. Weissler [Wei80]
also appears to have been the ﬁrst to make the connection between this line
of work and Bonami’s thesis.

Independently of all this work, the (q, 2)-Hypercontractivity Theorem was
reproved (without sharp constant) in the Banach spaces community by Rosen-
thal [Ros76] in 1975, using methods similar to those of Paley and Kiener. For
additional early references, see Müller [Mül05, Chapter 1].

The term “hypercontractivity” was introduced in a work of Simon and
Høegh-Krohn [SHK72]; Deﬁnition 9.13 of a hypercontractive random vari-
able is due to Krakowiak and Szulga [KS88]. The short inductive proof
of the Bonami Lemma may have appeared ﬁrst in Mossel, O’Donnell, and
Oleszkiewicz [MOO05a]. Theorems 9.22 and 9.24 appear in Janson [Jan97].
Theorem 9.23 dates back to Pisier and Zinn and to Borell [PZ78, Bor79].
As discussed further in the notes to Chapter 10, the Small-Set Expansion
Theorem originates in the work of Ahlswede and Gács [AG76]. The Level-k
Inequalities appear in several places but can probably be fairly credited to

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 35 -->
9.7. Exercises and notes

281

+

1
p2

Kahn, Kalai, and Linial [KKL88]. The optimal constants for Khintchine’s
Inequality were established by Haagerup [Haa82]; see also Nazarov and Pod-
x2
korytov [NP00]. They always occur either when

x1

i ai xi is just 1
p2

≡

, n

.
P
→ ∞

or in the limiting Gaussian case of ai

1
pn
Ben-Or and Linial’s work [BL85, BL90] was motivated both by game
theory and by the Byzantine Generals problem [LSP82] from distributed
computing; the content of Exercise 9.25 is theirs. In turn it motivated the
watershed paper by Kahn, Kalai, and Linial [KKL88]. (See also the intermedi-
ate work of Chor and Geréb-Graus [CGG87].) The “KKL Edge-Isoperimetric
Theorem” (which is essentially a strengthening of the basic KKL Theorem)
was ﬁrst explicitly proved by Talagrand [Tal94] (possibly independently of
Kahn, Kalai, and Linial [KKL88]?); he also treated the p-biased case. There
is no known combinatorial proof of the KKL Theorem (i.e., one which does not
involve real-valued functions). However, several slightly different analytic
proofs are known; see Falik and Samorodnitsky [FS07], Rossignol [Ros06],
and O’Donnell and Wimmer [OW13]. The explicit lower bound on the “KKL
constant” achieved in Exercise 9.30 is the best known; it appeared ﬁrst in
Falik and Samorodnitsky [FS07]. It is still a factor of 2 away from the best
known upper bound, achieved by the tribes function.

Friedgut’s Junta Theorem dates from 1998 [Fri98]. The observation that
its junta size can be improved for functions which have Wk[ f ]
I[ f ]/²
was independently made by Li-Yang Tan in 2011; so was the consequence
Corollary 9.31 and its extension to constant-degree PTFs. A stronger result
than Corollary 9.31 is known: Diakonikolas and Servedio [DS09] showed
that every LTF is ²-close to a I[ f ]2poly(1/²)-junta. As for Corollary 9.30, it’s
incomparable with a result from Gopalan, Meka, and Reingold [GMR12],
which shows that every width-w DNF is ²-close to a (w log(1/²))O(w)-junta.

² for k

¿

≤

Exercise 9.3 was suggested to the author by Krzysztof Oleszkiewicz.
Exercise 9.12 is from Gopalan et al. [GOWZ10]. Exercise 9.21 appears in
O’Donnell and Servedio [OS07]; Exercise 9.22 appears in O’Donnell and Wu
[OW09]. The estimate in Exercise 9.24 is from de Klerk, Pasechnik, and
Warners [dKPW04] (see also works of Rinott and Rotar’ [RR01] and Khot
et al. [KKMO07]). Exercises 9.27 and 9.28 are due to Kahn, Kalai, and
Linial [KKL88]. Exercise 9.34 was suggested to the author by John Wright.
Exercise 9.36 appears in Kauers et al. [KOTZ16].

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 36 -->

