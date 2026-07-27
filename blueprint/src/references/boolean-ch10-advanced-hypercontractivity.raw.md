<!-- generated-by: proofmatch local extraction -->
<!-- source-pdf-sha256: 9d1751394783984d0665eeac7d363a555809c0c07e3a27b4df65efd6df4dd555 -->
<!-- extractor: pdfminer.six v20260107 -->

<!-- pdf-page: 1 -->
Chapter 10

Advanced
hypercontractivity

In this chapter we complete the proof of the Hypercontractivity Theorem for
1 bits. We then generalize the (p, 2) and (2, q) statements to the
uniform
setting of arbitrary product probability spaces, proving the following:

±

The General Hypercontractivity Theorem. Let (Ω1, π1), . . . , (Ωn, πn) be
ﬁnite probability spaces, in each of which every outcome has probability at
least λ. Let f

πn). Then for any q

Ωn, π1

L2(Ω1

2 and 0

ρ

× · · · ×

⊗ · · · ⊗

>

≤

≤

∈
1/q,
λ1/2
−

1
pq

1 ·

−

Tρ f

k

q

k

≤ k

k

f

2 and

Tρ f
k

2
k

f

q0.

≤ k

k

(And in fact, the upper bound on ρ can be slightly relaxed to the value stated
in Theorem 10.18.)

−

1, 1}n

We can thereby extend all the consequences of the basic Hypercontrac-
R to functions f
n), except with
tivity Theorem for f : {
quantitatively worse parameters depending on “λ”. We also introduce the tech-
nique of randomization/symmetrization and show how it can sometimes elim-
inate this dependence on λ. For example, it’s used to prove Bourgain’s Sharp
n) with
Threshold Theorem, a characterization of Boolean-valued f
low total inﬂuence that has no dependence at all on π.

L2(Ωn, π⊗

L2(Ωn, π⊗

→

∈

∈

10.1. The Hypercontractivity Theorem for uniformly random

bits

In this section we’ll prove the full Hypercontractivity Theorem for uniform
bits stated at the beginning of Chapter 9:

1

±

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.

283



<!-- pdf-page: 2 -->
284

10. Advanced hypercontractivity

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

Actually, when neither p nor q is 2, the following equivalent form of

theorem seems easier to interpret:

Two-Function Hypercontractivity Theorem. Let f , g : {
prs
r, s

0, and assume 0

1. Then

ρ

−

1, 1}n

R, let

→

≥

≤

≤

≤
E
(x,y)
ρ-correlated

[ f (x)g(y)]

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

As a reminder, the only difference between this theorem and its “weak” form
(proven in Chapter 9.4) is that we don’t assume r, s
1. Below we will show
that the two theorems are equivalent, via Hölder’s inequality. Given the
Two-Function Hypercontractivity Induction Theorem from Chapter 9.4, this
implies that to prove the Hypercontractivity Theorem for general n we only
need to prove it for n
1. This is an elementary but technical inequality,
which we defer to the end of the section.

≤

=

Before carrying out these proofs, let’s take some time to interpret the
Two-Function Hypercontractivity Theorem. One interpretation is simply as
a generalization of Hölder’s inequality. Consider the case that the strings x
and y in the theorem are fully correlated; i.e., ρ
1. Then the theorem states
that

=

E[ f (x)g(x)]

f

g

1
k
+
1 is equivalent to s

≤ k

k

k

+

1

r

1/r

(10.1)

1

+

=

=

+

r)0

1/r. This statement is
because the condition prs
=
1/r. Hölder’s inequality is
identical to Hölder’s inequality, since (1
often used to “break the correlation” between two random variables; in the
absence of any information about how f and g correlate then we can at least
bound E[ f (x)g(x)] by the product of certain norms of f and g. (If f and g
have different “sizes”, then Hölder lets us choose different norms for them; if f
and g have roughly the same “size”, then we can take r
1 and get Cauchy–
Schwarz.) Now suppose we are considering E[ f (x)g(y)] for ρ-correlated x, y
1. In this case we might hope to improve (10.1) by using smaller
with ρ
norms on the right-hand side; in the extreme case of independent x, y (i.e.,
E[ f ] E[g]
1. The Two-Function
ρ
k
Hypercontractivity Theorem gives a precise interpolation between these two
cases; the smaller the correlation ρ is, the smaller the norms we may take on
the right-hand side.

0) we can use E[ f (x)g(y)]

≤ k

1
k

<

=

=

=

=

g

k

s

f

In the case that f and g have range {0, 1}, these ideas yield another inter-
pretation of the Two-Function Hypercontractivity Theorem, namely a two-set
generalization of the Small-Set Expansion Theorem:

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 3 -->
10.1. The Hypercontractivity Theorem for uniformly random bits

285

Generalized Small-Set Expansion Theorem. Let 0
a2
b2
2 ) and assume 0
2 ), exp(
{
−

1, 1}n have volumes exp(

−

−

≤

ρ
≤
ρa

1. Let A, B
a. Then
b

≤

≤
≤

⊆

[x

Pr
(x,y)
ρ-correlated

∈

A, y

B]

∈

≤

exp

a2

1
2

−

³

−

2ρab
ρ2
1

−

b2

+

.

´

Proof. Apply the Two-Function Hypercontractivity Theorem with f
g

1B and minimize the right-hand side by selecting r

ρ

ρ

b
a

ρa
ρb , s
−
−

=

=

1A,
=
ρb
ρa . (cid:3)
−
−

a
b

Remark 10.1. When a and b are not too close the optimal choice of s in the
proof exceeds 1. Thus the Generalized Small-Set Expansion Theorem really
needs the full (non-weak) Two-Function Hypercontractivity Theorem; equiv-
alently, the full Hypercontractivity Theorem. Also note that the assumption
b

ρa is needed to prevent r

0.

=

≥

<

Remark 10.2. This theorem is essentially sharp in the case that A and B
are concentric Hamming balls; see Exercise 10.5. In the case b
a we recover
=
the Small-Set Expansion Theorem. In the case b
ρa we get only the trivial
A]. However, not much better
bound that Pr[x
=
than this can be expected; in the concentric Hamming ball case it indeed holds
that Pr[x

A] whenever b

Pr[x

Pr[x

a2
2 )

exp(

A, y

A, y

B]

B]

=

≤

−

∈

∈

∈

ρa.

∈

∈

∼

∈

<

Remark 10.3. There is also a reverse form of the Hypercontractivity Theorem
and its Two-Function version; see Exercises 10.6–10.9. It directly implies the
following:

Reverse Small-Set Expansion Theorem. Let 0
a2
have volumes exp(
2 ), exp(

b2
2 ), where a, b

ρ
0. Then

≤

−

−

≥

1. Let A, B

≤

1, 1}n

{
−

⊆

[x

Pr
(x,y)
ρ-correlated

∈

A, y

B]

∈

≥

exp

a2

1
2

−
³

+

2ρab
ρ2
1

−

b2

+

.

´

We now turn to the proofs. We begin by showing that the Hypercontrac-
tivity Theorem and the Two-Function version are indeed equivalent. This is
1/s):
a consequence of the following general fact (take T

r, q

1

1

Tρ, p

=
Proposition 10.4. Let T be an operator on L2(Ω, π) and let 1

=

+

=

+

p, q

≤

. Then

≤ ∞

(10.2)

k
L2(Ω, π) if and only if

k

T f

q

f

p

k

≤ k

holds for all f

∈

T f , g

f

p

k

k

g

q0

k

〉 ≤ k

〈

(10.3)

holds for all f , g

L2(Ω, π).

∈

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 4 -->
286

10. Advanced hypercontractivity

T f , g
Proof. For the “only if ” statement,
q0 by Hölder’s
inequality and (10.2). As for the “if” statement, by Hölder’s inequality and (10.3)
we have

q0 ≤ k

〉 ≤ k

T f

g

g

k

k

k

k

k

k

〈

f

p

q

T f

k

q

k

=

sup
g
kq0 =

1〈

k

T f , g

〉 ≤

sup
g
kq0 =

1 k

k

f

g

p

k

k

q0 = k

k

p.

f

k

(cid:3)

=

Now suppose we prove the Hypercontractivity Theorem in the case n
1.
By the above proposition we deduce the Two-Function version in the case
n
1. Then the Two-Function Hypercontractivity Induction Theorem from
Chapter 9.4 yields the general-n case of the Two-Function Hypercontractivity
Theorem. Finally, applying the above proposition again we get the general-n
case of the Hypercontractivity Theorem, thereby completing all needed proofs.
These observations all hold in the context of more general product spaces, so
let’s record the following for future use:

=

Hypercontractivity Induction Theorem. Let 0
assume that
≤ k
it also holds for every f

p holds for every f
k
Ωn, π1
L2(Ω1
∈

∈
⊗ · · · ⊗

Tρ f
k

× · · · ×

k

f

q

πn).

ρ

, and
≤
L2(Ω1, π1), . . . , L2(Ωn, πn). Then

≤ ∞

1, 1

p, q

≤

≤

Remark 10.5. In traditional proofs of the Hypercontractivity Theorem for
1
bits, this theorem is proven directly; it’s a slightly tricky induction by deriva-
tives (see Exercise 10.3). For more general product spaces the same direct
induction strategy also works but the notation becomes quite complicated.

±

1; in other words, to show that a uniformly random

Our remaining task, therefore, is to prove the Hypercontractivity Theorem
in the case n
1 bit is
(p, q,
1))-hypercontractive. This fact is often called the “Two-
Point Inequality” because (for ﬁxed p, q, and ρ) it’s just an “elementary”
inequality about two real variables.

=
1)/(q

(p

p

−

−

±

Two-Point Inequality. Let 1
Then
k
formly random bit x
p for all a, b

≤
p for any f : {

Tρ f
k

≤ k

bx

a

k

f

q

{
∼
−
R.
∈

k

+

k

p
q
≤
1, 1}

(p
R. Equivalently (for ρ
p
1, 1} is (p, q, ρ)-hypercontractive; i.e.,

≤ ∞
→

and let 0

≤

≤

−

ρ

−
6=
a

−

1)/(q
1).
1), a uni-
ρbx

k

+

q

k

≤

p

≤

<

≤

2. Having done this, the 2

Proof. As in Section 9.3, our main task will be to prove the inequality for
q
1
cases follow from Propo-
q cases follow using the semigroup property of Tρ
sition 9.19, the p
(Exercise 9.17), and the p
q cases follow from Exercise 2.33 (or continuity).
=
2 will be very similar to that of Theorem 9.18 (the
The proof for 1
q
1),

2 case). As in that proof we may reduce to the case that ρ

1)/(q

≤ ∞

(p

<

<

<

≤

≤

≤

<

p

p

2

q

q

=

−

−

=

p
Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 5 -->
10.2. Hypercontractivity of general random variables

287

1, and b

a

=

=

² satisﬁes

²

|

| <

1. It then sufﬁces to show

⇐⇒

1
2 (1

+

ρ²)q

+

1
k
1
2 (1

−

ρ²x

+
ρ²)q

p
1
q ≤ k
+
k
p/q
1
2 (1

≤

²x

p
p

k
²)p

1
2 (1

−

+

²)p

¡

1
⇐⇒ Ã

+

∞

q
2k

ρ2k²2k

k
1
=
X

¡

¢

+

∞

p/q

¢

!

1

+

≤

k
1
=
X

¡

¢

p
2k

²2k.

(10.4)

²

1 to drop the absolute value signs and justify the Gen-
Again we used
eralized Binomial Theorem. For each of the binomial coefﬁcients on the left
in (10.4) we have

| <

|

q
2k

=

q(q

1)(q

−

2)(q

−

3)

−

(2k

(q
···
−
(2k)!

2))(q

−

(2k

−

1))

−

q(q

=

−

1)(2

−

q)(3

q)

((2k
···
(2k)!

−

2)

−

−

q)((2k

1)

−

−

q)

0.

≥

¢

¡
(Here we reversed an even number of signs, since 1
the same when expanding
t)θ
1
(1
is at most

q
2. We will later do
≤
.) Thus we can again employ the inequality
1 to deduce that the left-hand side of (10.4)
θ
¢

0 and 0
¡

θt for t

p
2k

+

≤

≤

≤

≥

≤

+

p
q

q
2k

ρ2k²2k

1

+

=

1

+

∞

k
1
=
X

p
q

∞

k
1
=
X

³

p
q

1
1

−
−

k

q
2k

²2k.

´

¡

¢

We can now complete the proof of (10.4) by showing the following term-by-
term inequality: for all k

1,

¡

¢

≥

p
q

k

p
q

1
1

−
−
´
((2k
−

q
2k

¢
q)

¡
1)
−

k q(q

1)(2

−

−

³
q)
···
(2k)!

p
2k

¡
¢
p(p
−

1)(2

≤

≤

((2k

p)
···
(2k)!

−

1)

−

−

p)

´
2
−
pq

q

−

1 ·

3
−
pq

q

−

1 · · ·

(2k

1)

−
pq

q
−
1 ≤

−

2
−
pp

p

−

1 ·

3
−
pp

p

−

1 · · ·

p

.

(2k

1)
−
pp

−
1

−

p
q

1
1

−
−

⇐⇒

p
q

³
⇐⇒

And indeed this inequality holds factor-by-factor. This is because p
<
2, as is evident from d
dr

1 for all j

≥

r
1

j
is a decreasing function of r
−
pr
−
r
j
2
1)3/2 .
+
−
2(r
−

−

≥

q and
r
j
−
pr
1 =
−
(cid:3)

Remark 10.6. The upper-bound ρ
possible; see Exercise 9.10(b).

≤

1)/(q

(p

−

−

p

1) in this theorem is best

10.2. Hypercontractivity of general random variables

Let’s now study hypercontractivity for general random variables. By the end
of this section we will have proved the General Hypercontractivity Theorem
stated at the beginning of the chapter.

Recall Deﬁnition 9.13 which says that X is (p, q, ρ)-hypercontractive if
X

and

q]

E[
|

|

< ∞

a

ρbX

q

a

bX

p

for all constants a, b

+

k
Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.

≤ k

+

∈

k

k

R.



<!-- pdf-page: 6 -->
288

10. Advanced hypercontractivity

(By homogeneity, it’s sufﬁcient to check this either with a ﬁxed to 1 or with b
ﬁxed to 1.) Let’s also collect some additional basic facts regarding the concept:

Fact 10.7. Suppose X is (p, q, ρ)-hypercontractive (1
Then:

q

p

≤

≤

, 0

≤ ∞

ρ

≤

<

1).

(1) E[X ]

0 (Exercise 9.10).

=

(2) cX is (p, q, ρ)-hypercontractive for any c

(3) X is (p, q, ρ0)-hypercontractive for any 0

(4) ρ

≤

q

p
q

1
1 and ρ
−
−

≤

X
X

k
k

p

q

k
k

(Exercises 9.10, 9.9).

R (Exercise 9.9).

ρ (Exercise 9.11).

ρ0

<

∈

≤

Proposition 10.8. Let X be (2, q, ρ)-hypercontractive. Then X is also (q0, 2, ρ)-
hypercontractive, where q0 is the conjugate Hölder index of q.

=

Proof. The deduction is essentially the same as (9.6) from Chapter 9.2. Since
E[X ]

0 (Fact 10.7(1)) we have

ρbX

a

k

+

E[a2

2
2 =
k

+

2ρabX

+

ρ2b2 X 2]

E[(a

+

=

bX )(a

+

ρ2bX )].

By Hölder’s inequality and then the (2, q, ρ)-hypercontractivity of X this is at
most

Dividing through by
a
ρbX

bX

2
k

≤ k

+

k

a

k

a

bX

+

q0k
k
+
a
ρbX
+
q0 as needed.

k

k

ρ2bX

q

a

2.
k
2 (which can’t be 0 unless X

ρbX

q0k

bX

≤ k

+

+

a

k

k

≡

0) gives

a

k

+
(cid:3)

Remark 10.9. The converse does not hold; see Exercise 10.4.

Remark 10.10. As mentioned in Proposition 9.15, the sum of independent
hypercontractive random variables is equally hypercontractive. Furthermore,
low-degree polynomials of independent hypercontractive random variables
are “reasonable”. See Exercises 10.2 and 10.3.

Given X , p, and q, computing the largest ρ for which X is (p, q, ρ)-
hypercontractive can often be quite a chore. However, if you’re not overly
concerned about constant factors then things become much easier. Let’s focus
on the most useful case, p
2. By Fact 10.7(2) we may assume
1. Then we can ask:

2 and q

X

=

>

2
k

=

k
Question 10.11. Let E[X ]
=
is X (2, q, ρ)-hypercontractive?

0,

X

k

2
k

=

1, and assume

X

k

q

k

. For what ρ

< ∞

In this section we’ll answer the question by showing that ρ

Θq(1/
q)
is sufﬁcient. By the second part of Fact 10.7(4), ρ
q is also necessary.
So for a mean-zero random variable X , the largest ρ for which X is (2, q, ρ)-
hypercontractive is always within a constant (depending only on q) of k
k

1/
k

X
X

X

X

=

≤

k
k

k

k

k

.

q

2

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 7 -->
10.2. Hypercontractivity of general random variables

289

Let’s arrive at this result in steps, introducing the useful techniques of
symmetrization and randomization along the way. When studying hypercon-
tractivity of a random variable X , things are much more convenient if X is
a symmetric random variable, meaning
X has the same distribution as X .
One advantage of symmetric random variables X is that they have E[X k]
0
N. Using this it is easy to prove (Exercise 10.11) the following
for all odd k
fact, similar to Corollary 9.6. (The proof similar to that of Proposition 9.16.)

=

−

∈

Proposition 10.12. Let X be a symmetric random variable with
Assume that
X
k
hypercontractive if and only if ρ

1.
C (and hence X is “C4-reasonable”). Then X is (2, 4, ρ)-

X

=

=

k

k

k

2

4

min( 1
p3

, 1
C ).

≤

Given a symmetric random variable X , the randomization trick is to
replace X by the identically distributed random variable r X , where r
1, 1}
is an independent uniformly random bit. This trick sometimes lets you reduce
a probabilistic statement about X to a related one about r.

{
−

∼

Theorem 10.13. Let X be a symmetric random variable with
let

X
2. Then X is (2, q, ρ)-hypercontractive for ρ

C, where q

X

k

k

q

k

=

>

2
k
=

1 and
=
1
.
Cpq

1

−

Proof. Let r
any a

R,

∈

ρ X

a

k

+

k

1, 1} be uniformly random and let

{
−

∼

X denote X /C. Then for

a

2
q = k
E
X

=

ρr X

2
q
k

+

[
E
r

ρr X

a

|

+

|

e

(by symmetry of X )

2/q

q]

i
2]q/2

a

+

1
C r X

|
)q/2]2/q

2

X

2/q

i

(r is (2, q,

1
pq

1

−

)-hypercontractive)

(Parseval)

(norm with respect to X )

(triangle inequality for

q/2)

k · k

X

2
2,
k

+

(cid:3)

a

= k
0.

=

E[X 2]

+

where the last step also used E[X ]

Next, if X is not symmetric then we can use a symmetrization trick to
make it so. One way to do this is to replace X with the symmetric random
variable X
X 0
has similar properties to X . In particular, if E[X ]
0 we can compare norms
using the following one-sided bound:

X 0, where X 0 is an independent copy of X . In general X

−

−

=

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.

≤

=

E
X

h
[
E
r

|
h
[(a2

E
X
a2

≤

= k
a2
a2
a2

=

=

+

+ k

+ k
1

+

+

X

X
e
X
e

e
=

q/2

2
e
k

2

q/2

k
2
q
k
a2



<!-- pdf-page: 8 -->
290

10. Advanced hypercontractivity

Lemma 10.14. Let X be a random variable satisfying E[X ]
where q

1. Then for any a

R,

0 and

X

q

k

,
< ∞

k

=

≥

∈
a

k

+

X

q

k

≤ k

a

X

X 0

q,

k

−

+

where X 0 denotes an independent copy of X .

Proof. We have

+
k
where we used the fact that E[X 0

+

k

|

|
X ]

a

X

E[

a

X

q]

q
q =

X

a

E[
|

=
−
+
0. But now

q],

E[X 0]
|

a

E[
|

+

X

E[X 0]
|

−

q]

E[

|

=

E[a

X

+

where we used convexity of t

t

7→ |

−
q.

|

|

≡
X 0]
|

q]

a

E[
|

+

≤

X

−

X 0

q]

|

X

a

+

= k

X 0

q
q,

k

−

(cid:3)

A combination of the randomization and symmetrization tricks is to re-
place an arbitrary random variable X by r X , where r
1, 1} is an indepen-
dent uniformly random bit. This often lets you extend results about symmet-
ric random variables to the case of general mean-zero random variables. For
example, the following hypercontractivity lemma lets us reduce to the case of
a symmetric random variable while only “spending” a factor of 1
2 :

{
−

∼

Lemma 10.15. Let X be a random variable satisfying E[X ]
where q

1. Then for any a

R,

0 and

X

q

k

,
< ∞

k

=

≥

where r

∼

{
−

∈
a

k
1, 1} is an independent uniformly random bit.

≤ k

+

+

k

k

1
2 X

q

a

r X

q,

Proof. Letting X 0 be an independent copy of X we have

a

k

+

1
2 X

q

k

≤ k

a

+

+

1
2 X
−
r( 1
2 X
−
1
2 r X
1
2 r X
1
2 r X
q.

+
r X

+

k

k

k

+
q

a

= k

= k

≤ k

= k

= k

+
1
2 a
1
2 a
1
2 a
a

+

q

1
2 X 0
k
1
2 X 0)
1
2 a

q

k

q

1
2 r X 0
k
1
2 r X 0
1
2 r X 0

−
1
2 a
1
2 a

−

+

+ k

q

+ k

(Lemma 10.14 applied to 1
2 X )
1
(since 1
2 X 0 is symmetric)

2 X

−

q

q

k

k

(triangle inequality for

q)

k · k

(
−

r distributed as r)

(cid:3)

By employing these randomization/symmetrization techniques we obtain
a (2, q)-hypercontractivity statement for all mean-zero random variables X
with k
k

bounded, giving a good answer to Question 10.11:

k
2
k

X
X

q

Theorem 10.16. Let X satisfy E[X ]
Then X is (2, q, 1

0,
2 ρ)-hypercontractive for ρ

=

the factor of 1

2 may be omitted.)

k
=

X

1,
2.
. (If X is symmetric, then

C, where q

=

>

k

k

q

X

2
k
1
Cpq

=
1

−

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 9 -->
10.2. Hypercontractivity of general random variables

291

Proof. By Lemma 10.15 we have

k
Since r X is a symmetric random variable satisfying
Theorem 10.13 implies

+

+

a

1
2 ρ X

2
q ≤ k
k

a

ρr X

2
q.
k

r X

2
k

=

1,

r X

k

q

k

=

C,

k

ρr X

a

k

+

2
q ≤ k
k

a

+

r X

a2

2
2 =
k

+

1

a

X

2
2.

k

+

= k

This completes the proof.

(cid:3)

If X is a discrete random variable then instead of computing k
k

it can
sometimes be convenient to use a bound based on the minimum value of
X ’s probability mass function. The following is a simple generalization of
Proposition 9.5, whose proof is left for Exercise 10.17:

k
k

q

2

X
X

Proposition 10.17. Let X be a discrete random variable with probability
mass function π. Write

min(π)

λ

=

=

x

min
range(X )

{Pr[X

x]}.

=

∈
(1/λ)1/2
−

1/q

X

2.
k

Then for any q

2 we have

X

q

k

k

>

is (2, q, 1

≤
As a consequence of Theorem 10.16, if in addition E[X ]

0 then X
1
2 ρ)-
pq
hypercontractive by Proposition 10.8. (If X is symmetric then the factor of 1
2
may be omitted.)

1/q, and X is also (q0, 2, 1
λ1/2
−

2 ρ)-hypercontractive for ρ

1 ·

· k

=

=

−

=

>

For each q

2, the value ρ

Θq(λ1/2
1/q) in Proposition 10.17 has the
−
optimal dependence on λ, up to a constant. In fact, a perfectly sharp version
of Proposition 10.17 is known. The most important case is when X is a
λ-biased bit; more precisely, when X
πλ in the notation of
Deﬁnition 8.39. In that case, the below theorem (whose very technical proof
is left to Exercises 10.19–10.21) is due to Latała and Oleszkiewicz [LO00].
The case of general discrete random variables is a reduction to the two-valued
case due to Wolff [Wol07].

φ(xi) for xi

=

∼

Theorem 10.18. Let X be a mean-zero discrete random variable and let
1/2 be the least value of its probability mass function, as in Proposi-
λ
tion 10.17. Then for q
2 it holds that X is (2, q, ρ)-hypercontractive and
(q0, 2, ρ)-hypercontractive for

<

>

ρ

= s

exp(u/q)
exp(u/q0)

exp(
exp(

−
−

−
−

u/q)
u/q0) = s

sinh(u/q)
sinh(u/q0)

, with u deﬁned by exp(

−

u)

λ

1

λ .
=
−
(10.5)

This value of ρ is optimal, even under the assumption that X is two-valued.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 10 -->
292

10. Advanced hypercontractivity

Remark 10.19. It’s not hard to see that for λ

1/2 (hence u

0) we get

1

ρ

q

→

1
pq

1/q)
−
1/q0) =
−

→
, consistent with the Two-Point Inequality from Sec-

1/q
(
−
1/q0−
(
1/q, showing
λ1/2
tion 10.1. Also, for λ
−
that Proposition 10.17 is sharp up to a q-dependent constant. Exercise 10.18
asks you to investigate the function deﬁning ρ in (10.5) more carefully. In
1/q holds for all λ. Hence we can
λ1/2
particular, you’ll show that ρ
−

0 (hence u

) we get ρ

1/q0 =

→ ∞

λ−
λ−

→

→

q

∼

1/q

−

omit the factor of 1
nonsymmetric random variables.

2 from the simpler bound in Proposition 10.17 even for

1
pq

≥

1 ·

−

Corollary 10.20. Let (Ω, π) be a ﬁnite probability space,
every outcome has probability at least λ. Let f
and 0

1/q,
λ1/2
−

∈

ρ

Ω
|
L2(Ω, π). Then for any q

2, in which
2

| ≥

>

≤

≤

1
pq

1 ·

−

Tρ f

q

k

≤ k

f

k

k

2 and

Tρ f
k

2
k

f

q0.

k

≤ k

{1}, under which Tρ f

Proof. Recalling Chapter 8.3, this follows from the decomposition f (x)
ρ f =
f ;
f =
variable f =
function is at least λ.

=
π the random
{1}(x) has mean zero, and the least value of its probability mass
(cid:3)

{1}. Note that for x

f ;

+

∼

=

+

The General Hypercontractivity Theorem stated at the beginning of the chap-
ter now follows by applying the Hypercontractivity Induction Theorem from
Section 10.1.

10.3. Applications of general hypercontractivity

In this section we will collect some applications of the General Hypercontrac-
tivity Theorem, including generalizations of the facts from Section 9.5. We
begin by bounding the q-norms of low-degree functions. The proof is essen-
tially the same as that of Theorem 9.21; see Exercise 10.28.

Theorem 10.21. In the setting of the General Hypercontractivity Theorem,
if f has degree at most k, then

f

k

q

k

≤

(

q

1

·

−

λ1/q

1/2)k
−

2.

f

k

k

p

Next we turn to an analogue of Theorem 9.22, getting a relationship
between the 2-norm and the 1-norm for low-degree functions. The proof (Ex-
ercise 10.31) needs (2, q, ρ)-hypercontractivity with q tending to 2, so to get
the most elegant statement requires appealing to the sharp bound from Theo-
rem 10.18:

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 11 -->
10.3. Applications of general hypercontractivity

293

Theorem 10.22. In the setting of the General Hypercontractivity Theorem, if
f has degree at most k, then

c(λ)k

f

≤

2
k
k
1/pλ as λ

→

We have c(λ)

∼

f

1, where c(λ)
k
k
0, c(λ)

e as λ

→

→

1/(1

2λ)

−

.

1

λ

−
λ

=
1
2 , and in general, c(λ)

q

e/p2λ.

≤

Just as in Chapter 9.5 we obtain (Exercise 10.32) the following as a corol-

lary:

Theorem 10.23. In the setting of the General Hypercontractivity Theorem, if
f is a nonconstant function of degree at most k, then

f (x)

>

E[ f ]

≥

1

4 (e2/2λ)−

k

≥

(15/λ)−

k.

Pr
π⊗
∼

n

x

£

¤

Extending Theorem 9.23, the concentration bound for degree-k functions,
is straightforward (see Exercise 10.33). We again get that the probability of
Θ(t2/k)), though the constant
exceeding t standard deviations decays like exp(
in the Θ(
·

) is linear in λ:

−

Theorem 10.24. In the setting of the General Hypercontractivity Theorem, if

f has degree at most k, then for any t

p2e/λ

k

,

[
|

n

Pr
π⊗
∼

x

f (x)

| ≥

f

t

k

≥
2]
k

≤

λk exp

k

2e λt2/k

.

´

−
³

Next, we give a generalization of the Small-Set Expansion Theorem, the

proof being left for Exercise 10.34.

Theorem 10.25. Let (Ω, π) be a ﬁnite probability space,
outcome has probability at least λ. Let A
α. Let q
Prx

n [x

A]

2, in which every
Ωn have “volume” α; i.e., suppose

| ≥

|

Ω

π⊗

∼

∈

=

≥

⊆
2. Then for any
λ1
−

0

ρ

1

≤

≤

q

1 ·
−

2/q

(or even ρ as large as the square of the quantity in Theorem 10.18) we have

Stabρ[1A]

=

Pr
n
π⊗
∼
Nρ(x)

x
y

∼

[x

∈

A, y

A]

≤

∈

2/q.
α2
−

Similarly, we can generalize Corollary 9.25, bounding the stable inﬂuence of
a coordinate by a power of the usual inﬂuence:

Theorem 10.26. In the setting of Theorem 10.25, if f : Ωn
ρInf(ρ)
i

Infi[ f ]2

2/q.
−

[ f ]

≤

for all i

∈

[n]. In particular, by selecting q

=

4 we get
Infi[ f ]3/2.

1, 1}, then

{
−

→

(10.6)

(pλ/3)|

S

S

f =

|

k

k

2
2 ≤

i
S
3
X

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 12 -->
294

10. Advanced hypercontractivity

Proof. Applying the General Hypercontractivity Theorem to Li f and squar-
ing we get

2
Li f
q0
k
By deﬁnition, the left-hand side is ρInf(ρ)
[ f ]. The right-hand side is
i
Li f
Li f
(
k

Infi[ f ] by Exercise 8.10(b).

2/q, and
−

2
2 ≤ k
k

TpρLi f

q0
q0 ≤

q0
q0

)2

(cid:3)

k

k

k

k

.

The KKL Edge-Isoperimetic Theorem in this setting now follows by an

almost verbatim repetition of the proof from Chapter 9.6.

KKL Isoperimetric Theorem for general product space domains. In
the setting of the General Hypercontractivity Theorem, suppose f has range
{
−

1, 1} and is nonconstant. Let

I[ f ]/ Var[ f ]

1. Then

I[ f ]

=

As a consequence, MaxInf[ f ]

Ω(

≥

MaxInf[ f ]

e

≥
I[ f ].

1
I[ f ]2 ·

≥
1
log(1/λ) )
e

·

(9/λ)−

e
Var[ f ]

log n
n .

·

Proof. (Cf. Exercise 9.29.) The proof is essentially identical to the one in
Chapter 9.6, but using (10.6) from Theorem 10.26. Summing this inequality
over all i

[n] yields

∈

[n] |
S
⊆
X

n

i
1
=
X

S

|

(pλ/3)|

S

S

f =

2
2 ≤

k

|

k

Infi[ f ]3/2

≤

MaxInf[ f ]1/2

I[ f ].

·

(10.7)

=

=

S
On the left-hand side above we will drop the factor of
|
troduce a set-valued random variable S deﬁned by Pr[S
for S

I[ f ]. Thus

S

]

|

for

S
|
S]

0. We also in-
2
2/ Var[ f ]
f =
k

S

| >
= k

6= ;
LHS(10.7)

. Note that E[
|
E
S

Var[ f ]

≥

·

|

=
[(pλ/3)|

e

S

|]

≥

Var[ f ]

·

(pλ/3)E[
|

S

]

|

Var[ f ]

·

(pλ/3)

I[ f ],

e

(pλ/3)s is convex. The ﬁrst statement of the theorem
where we used that s
now follows after rearrangement. As for the second statement, there is some
universal c

0 such that

7→

I[ f ]

>
c

≤

1
log(1/λ) ·

·

log n

=⇒

1
I[ f ]2 ·

(9/λ)−

I[ f ]

e

=

e

say, in which case our lower bound for MaxInf[ f ] is 1
hand,

e

pn À

O(1/λ)−

I[ f ]

1
pn

,

≥

e
log n
n . On the other

I[ f ]

c

1
log(1/λ) ·

·

≥

log n

I[ f ]

Ω(

≥

=⇒

1
log(1/λ) )

Var[ f ]

log n,

·

in which case even the average inﬂuence of f is Ω(

e

·
1
log(1/λ) )

Var[ f ]

·

log n
n .

·

(cid:3)

Similarly, essentially no extra work is required to generalize Theorem 9.28
and Friedgut’s Junta Theorem to general product space domains; see Exer-
cise 10.35. For example, we have:

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 13 -->
10.3. Applications of general hypercontractivity

295

Friedgut’s Junta Theorem for general product space domains. In the
1, 1} and
setting of the General Hypercontractivity Theorem, if f has range {
1, then f is ²-close to a (1/λ)O(I[ f ]/²)-junta h : Ωn
1, 1} (that is,
0
<
n [ f (x)
Prx

h(x)]

{
−

²).

→

−

²

≤
π⊗

∼

6=

≤

We conclude this section by establishing “sharp thresholds” – in the sense
of Chapter 8.4 – for monotone transitive-symmetric functions with critical
probability in the range [1/no(1), 1
1, 1} be a
nonconstant monotone function and deﬁne the (strictly increasing) curve
F : [0, 1]
1]. Recall that the critical proba-
=
bility pc is deﬁned to be the value such that F(pc)
1/2; equivalently, such
that Var[ f (pc)]
1. Recall also the Margulis–Russo Formula, which says that

1/no(1)]. Let f : {

[0, 1] by F(p)

1, 1}n

[ f (x)

Prx

{
−

= −

→

→

π⊗
p

−

−

=

∼

n

=

d
d p

F(p)

1
σ2 ·

=

I[ f (p)],

where

σ2

=

σ2(p)

Var
πp

[xi]

=

=

4p(1

p)

=

−

Θ(min(p, 1

p)).

−

Remark 10.27. Since we will not be concerned with constant factors, it’s
helpful in the following discussion to mentally replace σ2 with min(p, 1
p).
1/2 and replace σ2 with p.
In fact it’s even more helpful to always assume p

−

≤

Now suppose f is a transitive-symmetric function, e.g., a graph property.

This means that all of its inﬂuences are the same, i.e.,

Infi[ f (p)]

=

MaxInf[ f (p)]

1
n

=

I[ f (p)]

for all i
spaces that

∈

[n]. It thus follows from the KKL Theorem for general product

hence

I[ f (p)]

Ω

≥

1

log(1/ min(p,1

Var[ f (p)]

log n;

·

p))

−

·

¢

d
d p

F(p)

¡

≥

Var[ f (p)]

Ω

·

1
σ2 ln(e/σ2)

log n.

·

(10.8)

(As mentioned in Remark 10.27, assuming p
p log(1/p).)

¡

≤

¢

1/2 you can read σ2 ln(e/σ2) as

=

If we take p

pc in inequality (10.8) we conclude that F(p) has a large
Ω(
log n, assuming

derivative at its critical probability: F 0(pc)
1/2. In particular if log(1/pc)
pc
=
≤
ω( 1
). This suggests that f has a “sharp threshold”; i.e., F(p) jumps from
pc
near 0 to near 1 in an interval of the form pc(1
o(1)). However, largeness of
F 0(pc) is not quite enough to establish a sharp threshold (see Exercise 8.30);
we need to have F 0(p) large throughout the range of p near pc where Var[ f (p)]
is large. Happily, inequality (10.8) provides precisely this.

1/no(1) – then F 0(pc)

log n – that is, pc

1
pc log(1/pc) )

¿

±

≥

>

·

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 14 -->
296

10. Advanced hypercontractivity

=

Remark 10.28. Even if we are only concerned about monotone functions f
with pc
1/2, we still need the KKL Theorem for general product spaces to
Ω(log n) can be derived using
establish a sharp threshold. Though F 0(1/2)
just the uniform-distribution KKL Theorem from Chapter 9.6, we also need
to know that F 0(p)

Ω(log n) continues to hold for p

O(1/ log n).

1/2

≥

≥

=

±

Making the above ideas precise, we can establish the following result of

Friedgut and Kalai [FK96] (cf. Exercises 8.28, 8.29):

1, 1}n

−

1, 1} be a nonconstant, monotone, transitive-
Theorem 10.29. Let f : {
{
−
symmetric function and let F : [0, 1]
[0, 1] be the strictly increasing function
→
1]. Let pc be the critical probability such
deﬁned by F(p)
that F(pc)
1/2. Fix
0

1/2 and assume without loss of generality that pc

=
1/4 and let

[ f (x)

Prx

= −

→

π⊗
p

=

≤

∼

n

²

<

<

B log(1/²)

η

=

·

log(1/pc)
log n

,

where B

>

0 is a certain universal constant. Then assuming η

1/2,

≤

F(pc

(1

η))

²,

F(pc

(1

η))

1

².

·

−

≤
Proof. Let p be in the range pc
η). By the assumption η
1/2 we also
3
have 1
4 . It follows that the quantity σ2 ln(e/σ2) in the KKL
2 pc
corollary (10.8) is within a universal constant factor of pc log(1/pc). Thus for
all p in the range pc

2 pc

(1

(1

≤

≤

+

≥

−

±

≤

≤

p

3

·

·

±
·
F 0(p)

≥
4F(p)(1

η) we obtain
Var[ f (p)]

Ω

·

¡

1
pc log(1/pc)

log n.

·

F(p)), the deﬁnition of η, and a suitable choice

¢

Using Var[ f (p)]
of B, this is equivalent to

=

−

F 0(p)

2 ln(1/2²)
ηpc

≥

F(p)(1

F(p)).

−

(10.9)

We now show that (10.9) implies that F(pc
F(pc
+
hence

−
² to Exercise 10.36. For p

ηpc)

−

≥

1

≤

ηpc)

² and leave the implication
F(p)
1/2 and

pc we have 1

≤

−

≥

F 0(p)

ln(1/2²)
ηpc

≥

F(p)

=⇒

d
d p

ln F(p)

F 0(p)
F(p) ≥

ln(1/2²)
ηpc

.

=

It follows that

ln F(pc

i.e., F(pc

ηpc)

−

≤

ηpc)

ln F(pc)

−
≤
² as claimed.

ln(1/2²)

ln(1/2)

ln(1/2²)

ln ²;

=

−

=

−

(cid:3)

This proof establishes that every monotone transitive-symmetric func-
tion with critical probability at least 1/no(1) (and at most 1
1/no(1)) has a
sharp threshold. Unfortunately, the restriction on the critical probability
can’t be removed. The simplest example illustrating this is the logical OR

−

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 15 -->
10.4. More on randomization/symmetrization

297

{True,False} (equivalently, the graph property
function ORn : {True,False}n
→
ln 2
of containing an edge), which has critical probability pc
n . Even though
ORn is transitive-symmetric, it has constant total inﬂuence at its critical
probability, I[OR(pc)
2 ln 2. Indeed, ORn doesn’t have a sharp threshold;
n ]
i.e., it’s not true that Prπp [ORn(x)
o(1)). For
example, if x is drawn from the (2pc)-biased distribution we still just have
Pr[ORn(x)
3/4. On the other hand, most “interesting” monotone
transitive-symmetric functions do have a sharp threshold; in Section 10.5
we’ll derive a more sophisticated method for establishing this.

o(1) for p

True]

True]

pc(1

=

∼

≈

=

∼

=

−

=

+

1

10.4. More on randomization/symmetrization

In Section 10.3 we collected a number of consequences of the General Hy-
n). All of these had a
percontractivity Theorem for functions f
dependence on “λ”, the least probability of an outcome under π. This can
sometimes be quite expensive; for example, the KKL Theorem and its conse-
quence Theorem 10.29 are trivialized when λ

L2(Ωn, π⊗

1/nΘ(1).

∈

However, as mentioned in Section 10.2, when working with symmetric
random variables X , the “randomization” trick sometimes lets us reduce
to the analysis of uniformly random
1/2). Further,
±
Lemma 10.15 suggests a way of “symmetrizing” general mean-zero random
variables (at least if we don’t mind applying T 1
). In this section we will de-
2
velop the randomization/symmetrization technique more thoroughly and see
an application: bounding the L p
L p norm of the “low-degree projection”
operator.

1 bits (which have λ

→

=

=

Informally, applying the randomization/symmetrization technique to f
n) means introducing n independent uniformly random bits r

∈
L2(Ωn, π⊗
=
1, 1}n and then “multiplying the ith input to f by r i”. Of course
(r1, . . . , rn)
Ω is just an abstract set so this doesn’t quite make sense. What we really
mean is “multiplying Li f , the ith part of f ’s Fourier expansion (orthogonal
decomposition), by r i”. Let’s see some examples:

{
−

∼

Example 10.30. Let f : {
expansion

−

1, 1}n

f (x)

→

=

R be a usual Boolean function with Fourier

f (S)

xi.

Its randomization/symmetrization will be the function

b

[n]

S
⊆
X

S
i
∈
Y

f (r, x)

=

f (S)

r i xi

=

f (S) xS rS.

[n]

S
⊆
X
The key observation is that for random inputs x, r
variables f (x) and
xi is a symmetric random variable, so it has the same distribution as r i xi.

1, 1}n, the random
f (r, x) are identically distributed. This is simply because

S
⊆
X

S
i
∈
Y

{
−

[n]

∼

e

b

b

e

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 16 -->
298

10. Advanced hypercontractivity

Example 10.31. Let’s return to Examples 8.10 and 8.15 from Chapter 8.1.
Here we had Ω
{a, b, c} with π the uniform distribution, and we deﬁned a
R here might look like
certain Fourier basis {φ0
2
3 ·

1, φ1, φ2}. A typical f : Ω3

≡
φ1(x1)

f (x1, x2, x3)

φ2(x3)

φ2(x2)

1
3 −

=

=

−

1
4 ·
1
6 ·
1
10 ·

+

3
2 ·
+
φ2(x3)

φ1(x2)

φ2(x1)
1
8 ·
φ3(x3)

+ ·
φ1(x2)
·
1
5 ·

+
φ2(x2)

·

φ1(x1)

·
φ1(x1)

→
1
2 ·
+
φ1(x3)

·
The randomization/symmetrization of this function would be the following
3):
function

1, 1}3

L2({

+

−

f

·

·

π⊗

φ2(x1)

φ2(x2)

φ2(x3).

f (r, x)

=

e

∈

1
e
3 −

+

−

·

−
1
4 φ1(x1)
1
6 φ1(x1)
·
1
10 φ1(x1)

×

Ω3, π⊗
3
1/2 ⊗
3
2 φ2(x1)
r1r3

·

r1

+
φ2(x3)

·
φ2(x2)

·

·

+
φ3(x3)

1
2 φ2(x2)
r2r3

φ1(x2)

+

r1
1
8 φ1(x2)
·
r1r2r3

r2

·

+
φ1(x3)
·
1
5 φ2(x1)

+

·

φ2(x2)

φ2(x3)

·

·

·

r1r2r3.

r2

·

−

2
3 φ2(x3)

r3

·

f (r, x). How-
There’s no obvious way to compare the distributions of f (x) and
ever, looking carefully at Example 8.10 we see that the basis function φ2 has
the property that φ2(xi) is a symmetric real random variable when xi
π.
In particular, r i
φ2(xi) has the same distribution as φ2(xi). Therefore if
L2(Ωn, π⊗
n) has the lucky property that its Fourier expansion happens
g
g(r, x) are
to only use φ2 and never uses φ1, then we do have that g(x) and
identically distributed.

∼

∈

e

·

e
Let’s give a formal deﬁnition of randomization/symmetrization.

Deﬁnition 10.32. Let f
of f is the function

∈
L2({

f

L2(Ωn, π⊗
1, 1}n

n). The randomization/symmetrization
Ωn, π⊗

n) deﬁned by

∈

e

−
f (r, x)

×

=

n
1/2 ⊗
rS f =

π⊗
S(x),

where we recall the notation rS

e

=

[n]

S
⊆
X
S r i.

i

∈

(10.10)

Remark 10.33. Another way of deﬁning
f
the function
|
Fourier coefﬁcient on S is f =
swap the positions of rS and f =
e

S(x).)

1, 1}n

x : {

→

−

Q

f is to stipulate that for each x

Ωn,
R is deﬁned to be the Boolean function whose
S(x). (This is more evident from (10.10) if you

∈

e

In light of this remark, the basic Parseval formula for Boolean functions

implies that for all x

Ωn,

∈

f

2
2,r =
k

x

|

k

f =

S(x)2.

[n]

S
⊆
X

k · k

(The notation
the random inputs r.) If we take the expectation of the above over x
2
2,r,x and the right-hand side becomes
the left-hand side becomes
k
by Parseval’s formula for L2(Ωn, π⊗

2,r emphasizes that the norm is computed with respect to
n,
π⊗
2
2,x,
k

n). Thus:

∼
f
k

k

f

e

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.

e



<!-- pdf-page: 17 -->
10.4. More on randomization/symmetrization

299

Proposition 10.34. Let f

L2(Ωn, π⊗

n). Then

∈

f

k

2

k

f

2.
k

= k

e

6=

Thus randomization/symmetrization doesn’t change 2-norms. What about
q-norms for q
2? As discussed in Examples 10.30 and 10.31, there may be
cases where f ’s Fourier expansion is already symmetric; in such cases
f (r, x)
and f (x) will have identical distributions, so their q-norms will be identical.
The essential feature of the randomization/symmetrization technique is that
even for general f the q-norms don’t change much – if you are willing to apply
Tρ for some constant ρ:

e

Theorem 10.35. For f

L2(Ωn, π⊗

∈

n) and q

1,

>
Tc−

q

1

f

T 1
2

k

q

k

f

q

k

≤ k

≤ k

f

q.

k

(10.11)

Equivalently,

Here 0
c4

<
c4/3

=

cq
≤
2
5 .

=

e
f

Tcq f
k

q

k

≤ k

q

k

≤ k

T2 f

q.

k

1 is a constant depending only on q; in particular, we may take
g

‚

The two inequalities in (10.11) are not too difﬁcult to prove; for example,
you might already correctly guess that the left-hand inequality follows from
our ﬁrst randomization/symmetrization Lemma 10.15 and an induction. We’ll
give the proofs at the end of this section. But ﬁrst, let’s illustrate how you
might use them by solving the following basic problem concerning low-degree
projections:

Question 10.36. Let k

q be much larger than

n). Can
q? To put the question in reverse, suppose
f ≤
k
n) has degree at most k; is it possible to make the q-norm of g
g
much smaller by adding terms of degree exceeding k to its Fourier expansion?

k
k
L2(Ωn, π⊗

N, let 1
f

L2(Ωn, π⊗

, and let f

< ∞

<

∈

∈

∈

q

k

k

The question has a simple answer if q
2 always. This follows from Paresval:
k

f

k

=

2: in this case we have

k

f ≤

2
2 =

k

k

W j[ f ]

≤

W j[ f ]

f

2
2.
k

= k

k

j
0
=
X

n

j
0
=
X

k

f ≤

k

2
k

≤

(10.12)

When q
setting of Ω
2-norm via the Hypercontractivity Theorem:

2 things are not so simple, so let’s ﬁrst consider the most familiar
π1/2. In this case we can relate the q-norm and the

1, 1}, π

{
−

6=

=

=

Proposition 10.37. Let k

k

g≤

k

q

k

≤

q

−

k

1

g

k

k

N and let g : {
q

1, 1}n
−
2 we have

∈
q and for 1

R. Then for q
k
(1/

q

q

→
g≤

<

≤

k

k

≤

2 we have
q.

g

≥
1)k

−

k

k

p

This proposition is an easy consequence of the Hypercontractivity Theo-
4, follows

rem and already appeared as Exercise 9.8. The simplest case, q

p

=

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 18 -->
300

10. Advanced hypercontractivity

from the Bonami Lemma alone:

k

g≤

k

p3

k

g≤

k

p3

g

k

p3

4

k

k

k

k

≤

≤

2
k

Now let’s consider functions f

2
k
≤
L2(Ωn, π⊗
n) on general product spaces;
for simplicity, we’ll continue to focus on the case q
4. One possibility is to
repeat the above proof using the General Hypercontractivity Theorem (more
4. How-
speciﬁcally, Theorem 10.21). This would give us
k
ever, we will see that it’s possible to get a bound completely independent of λ
– i.e., independent of (Ω, π) – using randomization/symmetrization.

p3/λ

f ≤

=

≤

∈

k

k

k

k

f

k

k

4

(10.13)

g

4.
k

First, suppose we are in the lucky case described in Example 10.31 in
which f ’s Fourier spectrum only uses symmetric basis functions. In this case
k(r, x) have the same distribution for any k, and we can leverage
f ≤
the L2({

1, 1}) bound (10.13) to get the same result for f . First,

k(x) and

f ≤

−

g

k

f ≤

k

4
k

= k

k

f ≤

4
k

=

k

f ≤

x(r)
4,r
k

|

k

.

4,x

g
1, 1}n. Therefore we can apply (10.13) with this g to deduce

x, the inner function g(r)

x(r) is a degree-k func-

g

f ≤

=

=

°
°
°

°
°
k
°
|

For each outcome x
tion of r
{
∈
−
k
f ≤

x(r)
4,r
k

|

k

°
°
°

4,x ≤

°
°
°

°
°
°

k

p3

f

x(r)
k

|

k

4,r

g
k
p3

f

k

4
k

=

k

p3

f

4.
k

k

4,x =

°
°
°

g

e

Thus we see that we can deduce (10.13) “automatically” for these luckily sym-
metric f , with no dependence on “λ”. We’ll now show that we can get some-
thing similar for a completely general f using the randomization/symmetrization
Theorem 10.35. This will cause us to lose a factor of (2
of T2 and T 5
slightly.

2 )k, due to application
; to prepare for this, we ﬁrst extend the calculation in (10.13)

e

5

·

2

Lemma 10.38. Let k

∈

Proof. We have

N and let g : {

1, 1}n

R. Then for any 0

k

g≤

k

4
k

≤

−
(p3/ρ)k

→
Tρ g

k

4.
k

ρ

<

≤

1,

k

g≤

k

4

k

≤

k

p3

k

g≤

k

2
k

≤

(p3/ρ)k

Tρ g
k

2
k

≤

(p3/ρ)k

Tρ g
k

4.
k

Here the ﬁrst inequality is Bonami’s Lemma and the second is because

k

g≤

2
2 =
k

k

k

j
0
=
X

W j[ f ]

≤

(1/ρ2)k

k

j
0
=
X

ρ2 jW j[ f ]

(1/ρ2)k

≤

n

j
0
=
X

ρ2 jW j[ f ]

(1/ρ2)k

k

=

Tρ g

2
2.
k
(cid:3)

We can now give a good answer to Question 10.36, showing that low-

degree projection doesn’t substantially increase any q-norm:

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 19 -->
10.4. More on randomization/symmetrization

301

k

Theorem 10.39. Let k
Ck
qk

k
≤
may take C4, C4/3

5p3

f ≤

k

k

f

q

=

9.

≤

L2(Ωn, π⊗
1 we have
q. Here Cq is a constant depending only on q; in particular we

n). Then for q

N and let f

>

∈

∈

Proof. We will give the proof for q
cise 10.16. Using the randomization/symmetrization Theorem 10.35,

4; the other cases are left for Exer-

=

k

f ≤

4
k

k

≤ k

T2 f ≤

k

4
k

=

T2 f ≤
k

k

|

x(r)

4,r
k

.

4,x

°
°
x, let’s write g
°

â

=

g≤

For a given outcome x

R, so that we have
â
T2 f
k(r)
4 on the inside above. For clarity, we remark that g is the Boolean
k
k
g
S(x). We apply Lemma 10.38
S
function whose Fourier coefﬁcient on S is 2|
1
5 . Note that Tρ g is then the Boolean function whose
to this g, with ρ
Fourier coefﬁcient on S is ( 2
T 2
5 )|
5

. Thus we deduce

S(x); i.e., it is

1, 1}n

x : {

| f =

| f =

=

−

=

S

f

|

°
°
°
→

k

T2 f ≤
k

x(r)
k

|

4,r

4,x ≤

(5p3)k

f

T 1
k
5

(r)
k

x

4,r

‚
4,x =

f

T 2
k
5

4

k

≤

(5p3)k

f

4,

k

k

â

|
°
°
where the last step is the “un-randomization/symmetrization” inequality from
°
Theorem 10.35.
(cid:3)

‚

‚

°
°
°

°
°
°

°
°
°

x

|
(5p3)k

The remainder of this section is devoted to the proof of Theorem 10.35,
which lets us compare norms of a function and its randomization/symmetrization.
It will help to view randomization/symmetrization from an operator perspec-
tive. To do this, we need to slightly extend our Tρ notation, allowing for
“different noise rates on different coordinates”.

Deﬁnition 10.40. For i
deﬁned by

∈

[n] and ρ

∈

R, let Ti

ρ be the operator on L2(Ωn, π⊗

n)

Ti

ρ f

ρ f

(1

+

−

=

ρ)Ei f

=

Ei f

+

ρLi f

=

+

S

f =

ρ

f =

S.

(10.14)

i
S
3
X
Rn, let Tr be the operator on L2(Ωn, π⊗

i
S
63
X

n)

. From the third formula in (10.14) we have

Furthermore, for r
T1
deﬁned by Tr
r1

=

(r1, . . . , r n)
Tn
r n

=
T2
r2 · · ·

∈

Tr f

=

where we use the notation rS
operator. We remark that when r
Q

=

i

∈
∈

rS f =

S,

(10.15)

[n]

S
⊆
X
S r i. In particular, T(ρ,...,ρ) is the usual Tρ
[0, 1]n we have

Tr f (x)

=

y1∼

E

Nr1 (x1),...,yn∼

Nrn (xn)

[ f (y1, . . . , yn)].

These generalizations of the noise operator behave the way you would ex-
pect; you are referred to Exercise 8.11 for some basic properties. Now compar-
ing (10.15) and (10.10) reveals the connection to randomization/symmetrization:

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 20 -->
302

10. Advanced hypercontractivity

Fact 10.41. For f

L2(Ωn, π⊗

∈

n), x

Ωn, and r

1, 1}n,

{
−

∈

∈
f (r, x)

Tr f (x).

=

In other words, randomization/symmetrization of f means applying
1) to f for a random choice of signs. We use this viewpoint to prove
±

T(
±
Theorem 10.35, which we do in two steps:

1,...,

e

1,

±

Theorem 10.42. Let f

L2(Ωn, π⊗

n). Then for any q

1,

≥

∈

for x

∼

π⊗

n, r

∼

{
−

T 1
2

f (x)

q,x

k

≤ k
1, 1}n. In other words,

k

Tr f (x)
k

f

T 1
2

k

q

k

f

q.

k

≤ k

q,r,x

(10.16)

Proof. In brief, the result follows from our ﬁrst randomization/symmetrization
result, Lemma 10.15, and an induction. To ﬁll in the details, we begin by
showing that if h
1, 1},
then

L2(Ω, π) is any one-input function and ω

π, b

{
−

∼

∼

∈

e

T 1
k
2

h(ω)
k

q,ω

≤ k

Tbh(ω)

k

q,b,ω.

(10.17)

{1}(x) is a mean-zero
This follows immediately from Lemma 10.15 because h=
random variable (cf. the proof of Corollary 10.20). Next, we show that for any
g

n) and any i

[n],

L2(Ωn, π⊗

∈

∈
Ti

1
2

k

g(x)

q,x

k

Ti
r i

≤ k

g(x)
k

q,r i,x.

Assuming i
(x2, . . . , xn), we have

=

1 for notational simplicity, and writing x

(10.18)

(x1, x0) where x0

=

=

Ti
k

1
2

g(x)

q,x

k

=

Ti
k

1
2

g(x1, x0)

q,x1

k

(T 1
k
2

g

|

x0)(x1)

q,x1

k

.

q,x0

(You are asked to carefully justify the second equality here in Exercise 10.10.)
Now for each outcome of x0 we can apply (10.17) with h

g

(T 1
2

g

k

x0)(x1)
k

q,x1

q,x0 ≤

(Tr1 g
k

x0)(x1)
k

q,x1,r1

q,x0 = k

|
Finally, we illustrate the ﬁrst step of the induction. For distinct indices i, j,

|

°
°

°
°

°
°
°

°
°
°
x0 to deduce
Ti
r i

g(x)
k

q,r i,x.

=

|

=

q,x0

°
°
°

°
°
°
°

T j

1
2

f (x)
k

q,x

Ti
r i

≤ k

T j

1
2

f (x)
k

q,r i,x

°
°
°
°

°
°
°
Ti
k

1
2

by applying (10.18) with g

T j

1
2

=

f . Then

Ti
r i
k

T j

1
2

f (x)

q,r i,x

k

=

Ti
r i
k

T j

1
2

f (x)
k

q,x

q,r i =

T j

1
2

k

Ti
r i

f (x)
k

q,x

,

q,r i

ρ j commute. Now for each outcome of r i we can

°
°
°
°

°
°
°
°

°
°
°
°

°
°
and T j
°
where we used that Ti
°
ρ i
Ti
apply (10.18) with g
r i

f to get

T j
k

1
2

Ti
r i

f (x)

q,x

k

T j
r j Ti
r i

k

f (x)
k

q,r j,x

Ti
r i

q,r i = k

T j

r j f (x)
k

q,r i,r j,x.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.

°
°
°

°
°
°
°

=

°
°
°
°

q,r i ≤

°
°
°



<!-- pdf-page: 21 -->
10.4. More on randomization/symmetrization

303

Thus we have shown

Ti
k

1
2

T j

1
2

f (x)
k

q,x

Ti
r i

≤ k

T j

r j f (x)
k

q,r i,r j,x.

Continuing the induction in the same way completes the proof.

(cid:3)

To prove the “un-randomization/symmetrization” inequality in Theorem
10.35, we ﬁrst establish an elementary lemma about mean-zero random vari-
ables:

Lemma 10.43. Let q

≥

2. Then there is a small enough 0

cq

<

≤

1 such that

a

k

−

cq X

q

k

≤ k

a

X

q

k

+

R and any random variable X satisfying E[X ]

for any a
In particular we may take c4

∈

2
5 .

=

0 and

X

q

k

.
< ∞

k

=

Proof. We will only prove the statement for q
the general case in Exercise 10.13. By homogeneity we may assume a
then raising the inequality to the 4th power we need to show

4; you are asked to establish
1;

=

=

E[(1

−

cX )4]

E[(1

+

≤

X )4]

for small enough c. Expanding both sides and using E[X ]
lent to

E[(1

−

c4)X 4

(4

+

+

4c3)X 3

(6

+

−

6c2)X 2]

≥

0, this is equiva-

(10.19)

=

0.

It sufﬁces to ﬁnd c such that

(1

c4)x2

(4

4c3)x

(6

6c2)

0

x

R;

(10.20)

−

+

+

−

+
then we can multiply (10.20) by x2 and take expectations to obtain (10.19).
This last problem is elementary, and Exercise 10.14 asks you to ﬁnd the
2
largest c that works (the answer is c
5 sufﬁces, we
9
use the fact that x
8 for all x (because the difference of the left- and
−
right-hand sides is 1
9)2). Putting this into (10.20), it remains to ensure

.435). To see that c

≥

≈

=

∀

∈

2

2

9

+

−

6c2

c4)x2

( 1
9 −

( 3
2 −
∀
∈
5 this is the trivially true statement 161
5625 x2
n). Then for any q

L2(Ωn, π⊗

2 c3)

1,

−

≥

0

x

R,

>

and when c

=

Theorem 10.44. Let f

∈

63
250 ≥

0.

(cid:3)

+

Tcq r f (x)
k
k

q,r,x

f (x)
k

q,x

≤ k

π⊗

n, r

q. Here 0
for x
constant depending only on q; in particular we may take c4, c4/3

1, 1}n. In other words,

Tcq f
k

{
−

≤ k

∼

∼

k

k

f

q

1 is a

≤

cq
<
2
5 .
=

‚

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.

9 x2
≥ −
72 (4x
9 c3

8

+



<!-- pdf-page: 22 -->
304

10. Advanced hypercontractivity

Proof. In fact, we can show that for every outcome r

r

∈

=

1, 1}n we have

{
−

q,x

q,x

≤ k

f (x)

Tcq r f (x)
k
k
k
0. Note that on the left-hand side we have
T1
k
±

Tn
±

q,x.

cq

>

T2
k
±
ρ is a contraction in Lq for any ρ

cq · · ·

f (x)

cq

is a contraction in Lq, i.e., that

≥

0 (Exercise 8.11). Hence it

for sufﬁciently small cq

We know that Ti
sufﬁces to show that Ti
−

cq

Ti
k
−

g(x)

g(x)
k
n). Similar to the proof of Theorem 10.42, it sufﬁces to

(10.21)

≤ k

q,x

q,x

cq

k

for all g
show

∈

L2(Ωn, π⊗

q

k

h

cq h

T
(10.22)
−
L2(Ω, π), because then (10.21) holds point-
for all one-input functions h
1, . . . , xn. By Proposition 9.19, if we
wise for all outcomes of x1, . . . , xi
+
prove (10.22) for some q, then the same constant cq works for the conjugate
Hölder index q0; thus we may restrict attention to q
2. Now the result
≥
{1}(x).
h=
follows from Lemma 10.43 by taking a
(cid:3)

h=; and X

1, xi
−

≤ k

∈

k

k

q

=

=

10.5. Highlight: General sharp threshold theorems

n

∼

π⊗
p

= −

1, 1}n

{
→
−
[ f (x)

In Chapter 8.4 we described the problem of “threshold phenomena” for mono-
1, 1}. As p increases from 0 to 1, we are inter-
tone functions f : {
−
1] has a “sharp threshold”, jumping quickly
ested in whether Prx
from near 0 to near 1 around the critical probability p
pc. The “sharp
threshold principle” tells us that this occurs (roughly speaking) if and only
if the total inﬂuence of f under its critical distribution, I[ f (pc)], is ω(1). (See
Exercise 8.28 for more precise statements.) This motivates ﬁnding a charac-
terization of functions with small total inﬂuence. Indeed, ﬁnding such a char-
acterization is a perfectly natural question even for not-necessarily-monotone
Boolean-valued functions f

L2(Ωn, π⊗

n).

=

−

1, 1}n

For the usual uniform distribution on {

1, 1}n, Friedgut’s Junta Theorem
from Chapter 9.6 provides a very good characterization: f : {
1, 1}
can only have O(1) total inﬂuence if it’s (close to) an O(1)-junta. By the
version of Friedgut’s Junta Theorem for general product spaces (Section 10.3),
n
the same holds for Boolean-valued f
p ) so long as p is not too
∈
close to 0 or to 1. However, for p as small as 1/nΘ(1), the “junta”-size promised
by Friedgut’s Junta Theorem may be larger than n. (Cf. the breakdown of
1/nΘ(1).)
Friedgut and Kalai’s sharp threshold result Theorem 10.29 for p
This is a shame, as many natural graph properties for which we’d like to show
1/nΘ(1). At a technical
a sharp threshold – e.g., (non-)3-colorability – have p
level, the reason for the breakdown for very small p is the dependence on the

1, 1}n, π⊗

L2({

{
−

→

≤

=

−

−

∈

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 23 -->
10.5. Highlight: General sharp threshold theorems

305

“λ” parameter in the General Hypercontractivity Theorem. But there’s a more
fundamental reason for its failure, as suggested by the example at the end of
Section 10.3: Friedgut’s Junta Theorem simply isn’t true for such small p.

Example 10.45. Here are some examples of Friedgut’s Junta Theorem failing
for small p:

•

•

−

∼

∼

ln 2

→

{
−

1, 1}n
1, 1} has critical probabil-
The logical OR function ORn : {
n , and its total inﬂuence at this probability is I[OR(pc)
ity pc
2 ln 2,
n ]
a small constant. Yet it’s easy to see that under the pc-biased distri-
bution, ORn is not even, say, .1-close to any junta on o(n) coordinates.
(That is, for every o(n)-junta h, Prx
Consider the function f : {
1) if and only
if there exists a “run” of three consecutive
1’s in its input. (We allow
runs to “wrap around”, thus making f a transitive-symmetric function.)
It’s not hard to show that the critical probability for this f satisﬁes pc
=
Θ(1/n1/3). Furthermore, since f is a computable by a DNF of width 3,
Exercise 8.26(b) shows that I[ f (pc)]
12, a small constant. But again,
this f is not close to any o(n)-junta under the pc-biased distribution.
A similar example is Clique3 : {True,False}(v
2)
{True,False}, the graph
property of containing a triangle.

[ f (x)
.1.)
n
π⊗
pc
∼
1, 1} that is True (
{
−

1, 1}n

h(x)]

→

→

>

6=

−

−

−

≤

We see from these examples that for p very small, we can’t hope to show
that low-inﬂuence functions are close to juntas. However, these counterex-
ample functions still have low complexity in a weaker sense – they are com-
putable by narrow DNFs. Indeed, Friedgut [Fri99] suggests this as a charac-
terization:

Friedgut’s Conjecture. There is a function w : R+
the following holds: If f : {True,False}n
1/2, and I[ f (p)]
0
width at most w(K, ²).

→
K, then f is ²-close under π⊗

R+ such that
{True,False} is a monotone function,
n
p to a monotone DNF of

(0, 1)

→

≤

≤

<

×

p

The assumption of monotonicity is essential in this conjecture; see Exer-
cise 10.38.

Short of proving his conjecture, Friedgut managed to show:

Friedgut’s Sharp Threshold Theorem. The above conjecture holds when
f is a graph property.

This gives a very good characterization of monotone graph properties with
low total inﬂuence, one that works no matter how small p is. Friedgut also
extended his result to monotone hypergraph properties; this was sufﬁcient
for him to show that several interesting hypergraph (or hypergraph-like)
properties have sharp thresholds – for example, the property of a random

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 24 -->
306

10. Advanced hypercontractivity

3-uniform hypergraph containing a perfect matching, or the property of a
random width-3 DNF formula being a tautology. (Interestingly, for neither
of these properties do we know precisely where the critical probability pc
is; nevertheless, we know there is a sharp threshold around it.) Roughly
speaking one needs to show that at the critical probability, these properties
can’t be well-approximated by narrow DNFs because they are almost surely
not determined just by “local” information about the (hyper)graph. This kind
of deduction takes some effort in random graph theory and we won’t discuss
it further here beyond Exercise 10.42; for a survey, see Friedgut [Fri05].

Friedgut’s proof is rather long and it relies heavily on the function being a
graph or hypergraph property. Following Friedgut’s work, Bourgain [Bou99]
gave a shorter proof of an alternative characterization. Bourgain’s characteri-
zation is not as strong as Friedgut’s for monotone graph properties; however,
it has the advantage that it works for low-inﬂuence functions on any product
probability space. (In particular, there is no monotonicity assumption since
the domain need not be {True,False}n.) We ﬁrst make a quick deﬁnition and
then state Bourgain’s theorem.

1, 1}-valued. For T
0, we say that the restriction yT is a τ-booster if f ⊆
y].) In case τ

ΩT ,
τ.
0 we say that yT is a τ-booster if

L2(Ωn, π⊗

n) be {

∈
E[ f ]

⊆
T (y)

E[ fT

[n], y

≥

+

−

∈

Deﬁnition 10.46. Let f
and τ
>
(Recall that f ⊆
f ⊆

T (y)
.

T (y)

E[ f ]

=

τ

≤

− |

|

|

<

Bourgain’s Sharp Threshold Theorem. Let f
valued with I[ f ]
positive or negative) with

K. Assume Var[ f ]

O(K 2)) such that

exp(

≥

≤

τ

L2(Ωn, π⊗
1, 1}-
.01. Then there is some τ (either

n) be {

−

∈

Pr
π⊗
∼

x

T

[
∃

n

⊆

[n],

|

O(K) such that xT is a τ-booster]

τ

≥ |

.

|

| ≤

| ≥

−

|
T

(We emphasize that here and throughout, the constants hidden in the O(
·
absolute and do not depend on Ω or π.)

) are

∈

L2({True,False}n, π⊗

Thinking of K as an absolute constant, the above theorem says that for a
typical input string x, there is a large chance that it contains a constant-sized
substring that is an Ω(1)-booster for f . In the particular case of monotone
n
p ) with p small, it’s not hard to deduce (Exercise 10.40)
f
O(K) such that restricting all coordi-
that in fact there exists a T with
T
| ≤
nates in T to be True increases Prπ⊗
O(K 2)). This is a
[ f
n
p
qualitatively weaker conclusion than what you get from Friedgut’s Sharp
Threshold Theorem when f is a graph property with I[ f ]
O(1) – in that case,
by taking T to be any of the width-O(1) terms in the approximating DNF one
True] not just by Ω(1) but up to almost 1. Nevertheless,
can increase Prπ⊗
Bourgain’s theorem apparently sufﬁces to deduce any of the sharp thresholds
results obtainable from Friedgut’s theorem [Fri05]. For a very high-level

True] by exp(

[ f

=

−

=

≤

|

n

p

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 25 -->
10.5. Highlight: General sharp threshold theorems

307

sketch of how Bourgain’s theorem would apply in the case of 3-colorability of
random graphs, see Exercise 10.42.

The last part of this section will be devoted to proving Bourgain’s Sharp
Threshold Theorem. Before doing this, we add a remark. Hatami [Hat12] has
signiﬁcantly generalized Bourgain’s work, establishing the following charac-
terization of Boolean-valued functions with low total inﬂuence:

Hatami’s Theorem. Let f
I[ f ]
K. Then for every ²
exp(O(K 3/²3))-“pseudo-junta” h : Ωn

∈
>

≤

L2(Ωn, π⊗
−
0, the function f is ²-close (under π⊗

1, 1}-valued function with
n) to an

n) be a {

→

1, 1}.

{
−
The term “pseudo-junta” is deﬁned in Exercise 10.39. A K-pseudo-junta h
has the property that I[h]
4K; thus Hatami’s Theorem shows that having
O(1) total inﬂuence is essentially equivalent to being an O(1)-pseudo-junta.
A downside of the result, however, is that being a K-pseudo-junta is not a
“syntactic” property; it depends on the probability distribution π⊗

n.

≤

Let’s now turn to proving Bourgain’s Sharp Threshold Theorem. In fact,

Bourgain proved the theorem as a corollary of the following main result:
Theorem 10.47. Let (Ω, π) be a ﬁnite probability space and let f : Ωn
Let 0
a set of “notable coordinates” Jx

1, 1}.
Ωn it’s possible to deﬁne
exp(O(k)) such that

I[ f ]/². Then for each x
Jx
[n] satisfying

1/2 and write k

{
−

→

<

<

=

²

⊆

∈
| ≤

|

Here Fx

{S : S

Jx,

S

|

| ≤

⊆

=

E
π⊗
∼

x

n "
Fx
S
6∈
X

f =

S(x)2

2².

# ≤

k}, a collection always satisfying

Fx

|

| ≤

exp(O(k2)).

j

3

S

−

You may notice that this theorem looks extremely similar to Friedgut’s
O(I[ f ]2)) quantity in Bour-
Junta Theorem from Chapter 9.6 (and the exp(
gain’s Sharp Threshold Theorem looks similar to the Fourier coefﬁcient lower
bound in Corollary 9.32). Indeed, the only difference between Theorem 10.47
and Friedgut’s Junta Theorem is that in the latter, the “notable coordinates” J
can be “named in advance” – they’re simply the coordinates j with Inf j[ f ]

j f =
1, 1} we have f =

=
f (S)2 large. By contrast, in Theorem 10.47 the notable coordinates de-
pend on the input x. As we will see in the proof, they are precisely the
P
S(x)2 is large. Of course, in the setting of
coordinates j such that
S(x)2
f (S)2 for all x, so the two deﬁnitions
f : {
n) it makes sense that
coincide. But in the general setting of f
b
we can’t name the notable coordinates in advance and rather have to “wait
until x is chosen”. For example, for the ORn function as in Example 10.45,
there are no notable coordinates to be named in advance, but once x is chosen
the few coordinates on which x takes the value True (if any exist) will be the
notable ones.

b
1, 1}n

L2(Ωn, π⊗

{
−

→

P

−

=

∈

S

3

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 26 -->
308

10. Advanced hypercontractivity

The proof of Theorem 10.47 mainly consists of adding the randomiza-
tion/symmetrization technique to the proof of Friedgut’s Junta Theorem (more
precisely, Theorem 9.28) to avoid dependence on the minimum probability of π.
This randomization/symmetrization is applied to what are essentially the key
inequalities in that proof:

T 1
k
p3

Li f

2
2 ≤ k
k

Li f

2
4/3 = k
k

Li f

2/3
4/3 · k
k

Li f

4/3
4/3 ≤ k

Li f

2/3
4/3 ·
k

k

Infi[ f ].

(The last inequality here is Exercise 8.10(b).) The overall proof needs one
more minor twist: since we work on a “per-x” basis and not in expectation, it’s
possible that the set of notable coordinates can be improbably large. (Think
n
again about the example of ORn; for x
1/n we expect only a constant number
π⊗
∼
of coordinates of x to be True, but it’s not always uniformly bounded.) This
is combated using the principle that low-degree functions are “reasonable”
(together with randomization/symmetrization).

Proof of Theorem 10.47. By the simple “Markov argument” (see Proposi-
tion 3.2) we have

E
π⊗
∼

x

n "

S
|>
X|

f =

S(x)2

k

# =

S

f =

2
2 ≤

k

k k

I[ f ]/k

².

=

S
|>
X|

Thus it sufﬁces to deﬁne the sets Jx so that

E
π⊗
∼

x

n "

k, S
S
X|
|≤

Jx

6⊆

f =

S(x)2

².

# ≤

(10.23)

We’ll ﬁrst deﬁne “notable coordinate” sets J0x ⊆

[n] which almost do the trick:

j

J0x = (

∈

[n] :

f =

S(x)2

,

τ

τ

≥

)

=

c−

k.

j
S
3
X

(where c
the proof will be to show

>

1 is a universal constant). Using this deﬁnition, the main effort of

E
π⊗
∼

x

n "

k, S
S
X|
|≤

J0x

6⊆

f =

S(x)2

²/2.

# ≤

(10.24)

This looks better than (10.23); the only problem is that the sets J0x don’t always
J0x| ≤
satisfy
ought not be
much larger than 1/τ

exp(O(k)) as needed. However, “in expectation”

ck. Thus we introduce the event

J0x|

|

|

=
“J0x is too big”

⇐⇒ |

Ck

J0x| ≥

(where C

>

c is another universal constant) and deﬁne

Jx

J0x

= (

;

if J0x is not too big,
if J0x is too big.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 27 -->
10.5. Highlight: General sharp threshold theorems

309

The last part of the proof will be to show that

E
π⊗
∼

x

1[J0x is too big]

n "

·

0

S
|≤
X

<|

k

f =

S(x)2

²/2.

# ≤

(10.25)

Together, (10.25) and (10.24) establish (10.23). We will ﬁrst prove (10.24) and
then prove (10.25). As a small aside, we’ll see that for both inequalities we
could obtain a bound much less than ²/2 if desired.

To prove (10.24), we mimic the proof of Theorem 9.28 but add in random-
ization/symmetrization. The key step is encapsulated in the following lemma.
Note that the lemma also holds with the more natural deﬁnition g
Li f ; the
additional T 2
5

is to facilitate future “un-randomization/symmetrization”.

=

Lemma 10.48. Fix x

Ωn and i

∈

6∈

J0x. Then writing g

T 2
5

=

Li f we have

T 1
p3

k

g

2
2 ≤
k

x

|

τ1/3

g

4/3
4/3.
k

x

|

k

e

e

g is the randomization/symmetrization of g, so

x(r) is a
Proof. Here
function on the uniform-distribution hypercube. Applying the basic (4/3, 2)-
Hypercontractivity Theorem we have

=

g

g

x

|

|

e

e

e

T 1
k
p3

g

2
2 ≤ k
k

x

|

g

2
4/3 =
k

x

|

g

(
k

x

|

k

2

4/3)1/3

g

4/3
4/3 ≤
k

x

|

(

k

g

2)1/3
2
k

x

|

g

x

|

k

· k

4/3
4/3.

· k

e

e

e

e

e

e

But by the usual Parseval Theorem,

g

2
2 =
k

x

|

k

e

[n]

S
⊆
X

g=

S(x)2

=

i
S
3
X

(2/5)2

|

S

| f =

S(x)2

f =

S(x)2

τ,

≤

≤

i
S
3
X

the last inequality due to the assumption that i

J0x.

6∈

(cid:3)

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 28 -->
310

10. Advanced hypercontractivity

We now establish (10.24):

E
x "

k, S
S
X|
|≤

J0x

6⊆

f =

S(x)2

# ≤

(5p3/2)2k

·

E
x "
J0x
S
X
6⊆

(T 2
5p3

f =

S)(x)2

#

(T 2
5p3

f =

S)(x)2

#

gi

2
xk
2

|

#

f
gi

|

4/3
4/3

xk

#

i

S

3

J0x X
i
X
6∈
T 1
p3

k

J0x
i
X
6∈

E
x "
n

1 k
i
=
X
n

k

J0x
i
X
6∈
Li f

f
4/3
4/3
k

20k

E
x "

·

20k

E
x "

·

20kτ1/3

20kτ1/3

20kτ1/3

20kτ1/3

·

·

·

·

≤

=

≤

≤

≤

=

Infi[ f ]

(Exercise 8.10(b))

i
1
=
X
I[ f ]

=

(20c−

1/3)kk²

²/2,

≤

(for gi

T 2
5

Li f )

=

(Lemma 10.48)

(Theorem 10.35)

the last inequality because (20c−
enough constant.

1/3)kk

1/2 for all k

≤

≥

0 once c is a large

The last task in the proof is to establish (10.25). Using Cauchy–Schwarz,

E
π⊗
∼

x

1[J0x is too big]

n "

f =

S(x)2

#

·

0

S
|≤
X

<|

k

≤

E
x

r

1[J0x is too big]2

£

E
x "

v
u
u
¤
t

S
0
³ X
|≤
<|

f =

S(x)2

k

2

.

#

´

(10.26)

For the ﬁrst factor on the right of (10.26) we use Markov’s inequality:

E
x

1[J0x is too big]2
£

Pr
x

=

[J0x is too big]

[
Pr
x

J0x| ≥

|

=

Ck]

C−

k E
[
x

≤

¤
J0x|

|

]

≤

C−

k E

x "
³

n

f =

S(x)2

/τ

i
1
=
X
Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.

i
S
3
X

´

C−

k ck

·

# =

I[ f ].

(10.27)



<!-- pdf-page: 29 -->
10.5. Highlight: General sharp threshold theorems

311

As for the second factor on the right of (10.26), let’s write h

( f

T 2
5

=

−

f =;). (We

are being slightly ﬁnicky about f =; just in case it’s very large.) Then

E
x "

S
0
³ X
|≤
<|

f =

S(x)2

k

2

´

(5/2)4k

·

# ≤

E
x "Ã

f =

S)(x)2

2

!

#

(T 2
5

S
6=;
X
h
x

4
2
k

¤

(5/2)4k

E
x

=

≤

≤

≤

40k

40k
40k

·

·

x

E
x

k
|
4
£
h
e
4
k
k
|
£
f =;
f
e
−
· k
22 E
x

[( f

−
Var[ f ]

·
40k

4

4
¤
4
k
f =;)2]

4

40k

(Theorem 10.35)

(since

f

|

−

f =;

| ≤

2 always)

I[ f ].

(10.28)

·
=
Substituting (10.27) and (10.28) into (10.26) gives

≤

·

·

·

E
π⊗
∼

x

1[J0x is too big]

n "

·

0

S
|≤
X

<|

k

f =

S(x)2

#

the last inequality again holding for all k
compared to c.

≥

≤

p

C−

k ck

4

40k

I[ f ]

2( 40c

C )k/2k²

²/2,

·

·

=

·
0 once C is chosen large enough
(cid:3)

≤

We end this chapter by deducing Bourgain’s Sharp Threshold Theorem

from Theorem 10.47.

Proof of Bourgain’s Sharp Threshold Theorem. We take ²
.001 in The-
orem 10.47 and obtain the associated collections of subsets Fx, where each
Fx satisﬁes
Fx
O(K). Using the fact that
|
| ≤
f =;(x)2

exp(O(K 2)) and each S

.99 for each x we get

Var[ f ]

| ≤

=

S

∈

1

|

=

−

≤

x

E
n "
π⊗
Fx\{
S
∼
∈
X
Fx \ {
}
| ≤
;
0. It follows that

|

}
;

We always have
Fx \ {
}
| >
;

|

f =

S(x)2

2²

1

−

−

.99

=

.008.

# ≥

exp(O(K 2)), and there’s also no harm in assuming

max
Fx\{
∈
Thus for each x we can deﬁne a set Sx with 0

{ f =
}
;

E
π⊗
∼

S(x)2}
¸

≥

·

S

x

n

.008
exp(O(K 2)) =

exp(

O(K 2)).

−

E
π⊗
∼
h
Sx (x)
f =
By Exercise 8.19 we have
|
always. It follows from (10.29) that we must have

exp(

| ≤

i
Sx

f =

2|

≤

≥

−

x

n

|

Sx (x)2

2O(K) and hence f =

(10.29)

Sx (x)2

≤

exp(O(K))

O(K) such that

Sx
< |
| ≤
O(K 2)).

Pr
π⊗
∼

n

x

h

f =

Sx (x)2

exp(

≥

O(K 2))

−

exp(

O(K 2)).

−

≥

i

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 30 -->
312

10. Advanced hypercontractivity

We will complete the proof by showing that whenever f =
occurs, there exists T
we either have a
exp(
or a
exp(
the proof will be complete.

O(K 2))-booster with probability at least 1

Sx such that xT is a
O(K 2))-booster with probability at least 1

O(K 2))
O(K 2))-booster for f . So
O(K 2)),
O(K 2)); either way,

2 exp(

2 exp(

Sx (x)2

exp(

exp(

⊆
−

−

+

≥

−

±

−

−

−

−

Assume then that f =

Sx (x)2

exp(

O(K 2)); equivalently,

≥
Sx (x)

f =

−
exp(

| ≥

O(K 2)).

|
f

−

|

=
the above inequality tells us that

−

T
E[ f ]. Of course g=
Sx (x)

g=

Let’s now work with g
Sx
6= ;
formula

f =
exp(

T for all T

; since
6= ;
O(K 2)). Recall the

−

=
| ≥

g=

Sx (x)

=

Sx

T

| g⊆

T (x);

|−|

(

1)|

−

Sx

T
⊆
X;6=

we dropped the T
|
−
terms in the above sum, we deduce there must exist some T
T

term since it’s 0. As there are only 2|

O(K) such that

= ;

⊆

1

exp(O(K))

=
Sx with 0

<

Sx

|

| ≤

g⊆

T (x)

| ≥

exp(

O(K 2))/ exp(O(K))

−

exp(

O(K 2)).

−

T

But g⊆
−
This precisely says that xT is a

=

E[ f ], so the above gives us

T (x)
O(K 2))-booster, as desired.

E[ f ]

| ≥

−

|

exp(

O(K 2)).
(cid:3)

−

exp(

−

±

|
T
f ⊆

=
f ⊆

For a relaxation of the assumption Var[ f ]

cise 10.41.

.01 in this theorem, see Exer-

≥

10.6. Exercises and notes

10.1 Let X be a random variable and let 1

(Minkowski) inequality implies that for real-valued functions f1, f2,

r

. Recall that the triangle

≤

≤ ∞

f1(X )

f2(X )
k

r

+

f1(X )
k

r

f2(X )
k

r.

+ k

≤ k

k

More generally, if w1, . . . , wm are nonnegative reals f1, . . . , f m are real func-
tions, then

w1 f1(X )

wm f m(X )
k

r

w1

f1(X )
k

r

k

+ · · · +

k
Still more generally, if Y is a random variable independent of X and
f (X , Y ) is a (measurable) real-valued function, then it holds that

+ · · · +

≤

k

wm

f m(X )
k

r.

[ f (X , Y )]

E
Y

r,X ≤

E
Y

[
k

f (X , Y )
k

r,X ].

Using this last fact, show that whenever 0

p

°
°

f (X , Y )
k

k

p,Y

q,X ≤

k

<
f (X , Y )
k

q

≤

q,X

,
≤ ∞
p,Y .

(Hint: Raise the inequality to the power of p and use r

°
°

°
°

q/p.)

=

°
°

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.

°
°

°
°



<!-- pdf-page: 31 -->
10.6. Exercises and notes

313

10.2 The goal of this exercise is to prove Proposition 9.15: If X and Y are
independent (p, q, ρ)-hypercontractive random variables, then so is X
Y .
Let a, b
∈
(a) First obtain

R.

+

ρb(X

a

k

+

Y )
k

+

q,X ,Y

≤

ρbX

a

k

+

+

bY

p,Y

k

q,X .

(b) Next, upper-bound this by

k
(Hint: Exercise 10.1.)

°
°

(c) Finally, upper-bound this by

a

bY

+

+

°
°

°
°
ρbX

q,X

k

p,Y .

°
°

bY

a

k

+

+

bX

p,X

k

p,Y = k

b(X

a

+

Y )

k

+

p,X ,Y .

°
°

10.3 Let X 1, . . . , X n be independent (p, q, ρ)-hypercontractive random variables.
F(S)xS be an n-variate multilinear polynomial. Deﬁne
F(S)xS. The goal

Let F(x)
formally the multilinear polynomial Tρ F(x)
of this exercise is to show

[n] ρ|
⊆

P

[n]

=

=

b

⊆

S

S

S

|

°
°

P

b

Tρ F(X 1, . . . , X n)
k

q

F(X 1, . . . , X n)

p.

(10.30)

k

k

≤ k
Note that this result yields an alternative deduction of the Hypercontrac-
tivity Theorem for
1 bits from the Two-Point Inequality. A (notationally
intense) generalization of this exercise can also be used as an alternative
inductive strategy for deducing the General Hypercontractivity Theorem
from Proposition 10.17 or Theorem 10.18.
(a) Why is Exercise 10.2 a special case of (10.30)?
(b) Begin the inductive proof of (10.30) by showing that the base case

±

n

0 is trivial.

=

(c) For the case of general n, ﬁrst establish

Tρ F(X )

q

k

≤

T0ρ E(X 0)
k

+

k

X nT0ρ D(X 0)

p,X n

k

,

q,X 0

°
°
where we are using the notation x0
°
xnD(x0), and T0ρ for the operator acting formally on (n
multilinear polynomials.

°
°
1), F(x)
(x1, . . . , xn
°
−

=

−

E(x0)
=
+
1)-variate

(d) Complete the inductive step, using steps similar to Exercises 10.2(b),(c).

(Hint: For X n a real constant, why is T0ρ E(X 0)
X nD)(X 0)?)

+

X nT0ρ D(X 0)

T0ρ(E

+

=

10.4 This exercise is concerned with the possibility of a converse for Proposi-

tion 10.8.
(a) In our proof of the Two-Point Inequality we used Proposition 9.19 to
deduce that a uniform bit x
1, 1} is (p, q, ρ)-hypercontractivity if
it’s (q0, p0, ρ)-hypercontractive. Why can’t we use Proposition 9.19 to
deduce this for a general random variable X ?

{
−

∼

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 32 -->
314

10. Advanced hypercontractivity

(b) For each 1

p

2, exhibit a random variable X that is (p, 2, ρ)-

hypercontractive (for some ρ) but not (2, p0, ρ)-hypercontractive.

<

<

10.5 (a) Regarding Remark 10.2, heuristically justify (in the manner of Exer-
1, 1}n are concentric
a

cise 9.24(a)) the following statement: If A, B
Hamming balls with volumes exp(
1), then
(where 0

{
−
a2
2 ) and exp(

b2
2 ) and ρa

⊆

−

−

≤

≤

b

ρ

<

<

[x

Pr
(x,y)
ρ-correlated

∈

A, y

∈

B] ' exp

a2

1
2

−
³

−

2ρab
ρ2
1

−

b2

+

;

´

<

ρa, then Pr[x

and further, if b
should treat ρ as ﬁxed and a, b

A, y
∈
.
→ ∞
(b) Similarly, heuristically justify that the Reverse Small-Set Expansion
Theorem is essentially sharp by considering diametrically opposed
Hamming balls.

A]. Here you

Pr[x

B]

∼

∈

∈

10.6 The goal of this exercise (and Exercise 10.7) is to prove the Reverse Hy-
percontractivity Theorem and its equivalent Two-Function version:

Reverse Hypercontractivity Theorem. Let f : {
nonnegative function and let
1. Then
0

−∞ ≤

p)/(1

q).

(1

<

≤

p

q

ρ

−
k

≤

≤

−

−

1, 1}n
Tρ f

R≥
f

0 be a
p for

→
q

k

≥ k

k

p
1, 1}n

Reverse Two-Function Hypercontractivity Theorem. Let
f , g : {
−
1. Then

0 be nonnegative, let r, s

0, and assume 0

R≥

prs

→

≤

≤

≤

≤

ρ

[ f (x)g(y)]

E
(x,y)
ρ-correlated

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

≥ k

f

k

k

p

−∞ <

0 and for positive functions f

<
p retains the deﬁnition E[ f p]−

L2(Ω, π) the
Recall that for
, p
“norm”
0,
and nonnegative functions are deﬁned by appropriate limits; in particular
0 is the geometric mean of f ’s
k
p is 0 whenever f is not everywhere positive. We also
1
p0 =

k
values, and
k
k
deﬁne p0 by 1
p +

is the minimum of f ’s values,

∈
1/p. (The cases of p

The Reverse Two-Function Hypercontractivity Theorem can be thought

1, with 00

= −∞

k−∞

0.)

=

=

k

f

f

f

of as a generalization of the lesser known “reverse Hölder inequality” in
the setting of L2({

1, 1}n, π⊗

n
1/2):

−

Reverse Hölder inequality. Let f
for any p

1,

<

L2(Ω, π) be a positive function. Then

∈

k
In particular, for r

f

p

k

=

inf {E[ f g] : g

0,

g

>

p0 =
k
0 we have E[ f g]

k

1}.

0 and f , g

k
Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.

≥ k

<

>

+

f

1
k

r

g

1/r.
+

1
k



<!-- pdf-page: 33 -->
10.6. Exercises and notes

315

(a) Show that to prove these two Reverse Hypercontractivity Theorems it
R+, i.e., strictly positive

1, 1}n

sufﬁces to consider the case of f , g : {
functions.

−

→

(b) Show that the Reverse Two-Function Hypercontractivity Theorem is
equivalent (via the reverse Hölder inequality) to the Reverse Hyper-
contractivity Theorem.

(c) Reduce the Reverse Two-Function Hypercontractivity Theorem to the
1 case. (Hint: Virtually identical to the Two-Function Hypercon-

n
tractivity Induction.) Further reduce to following:

=

Reverse Two-Point Inequality. Let

q

(1

p)/(1

q). Then

Tρ f

q

k
10.7 The goal of this exercise is to prove the Reverse Two-Point Inequality.

≥ k

→

p

−

−

−

k

k

−∞ ≤
<
p for any f : {

f

p
≤
1, 1}

1 and let 0
R+.

ρ

≤

≤

(a) Similar to the non-reverse case, the main effort is proving the inequal-
q). Do this
ity assuming that 0
by mimicking the proof of the Two-Point Inequality. (Hint: You will
θt for θ
need the inequality (1
1, and you will need to show
that

is an increasing function of r on [0, 1) for all j

1 and that ρ

p)/(1

t)θ

2.)

p

(1

+

<

<

≤

=

−

−

≥

+

≥

p

q

1

r

j
−
p1
−

r
(b) Extend to the case of 0

q). (Hint: Use the fact that
−
−
for any f : {
q
q.
≤
−∞ ≤
You can prove this generalization of Exercise 1.13 by reducing to the
case of negative p and q to the case of positive p and q.)

ρ
≤
0 and
p

p)/(1
p

we have

1, 1}n

≤
R≥

≤ ∞

≤ k

→

(1

−

k

k

k

f

f

p

≥

(c) Establish the q
= −∞
(d) Show that the cases

q
Proposition 9.19 but with the reverse Hölder inequality.)

−∞ <

0 follow by “duality”. (Hint: Like

<

<

p

case of the Reverse Two-Point Inequality.

(e) Show that the cases q
<
(f ) Finally, treat the cases of p

<

0

0 or q

0.

=

=

p follow by the semigroup property of Tρ.

10.8 Give a simple proof of the n

s

1 case of the Reverse Two-Function Hyper-
=
1/2. (Hint: Replace f and g by f 2
contractivity Theorem when r
= −
and g2; then you don’t even need to assume f and g are nonnegative.)
Can you also give a simple proof when r
2?

s
= −
ρb
b , prove the Reverse Small-
= −
Set Expansion Theorem mentioned in Remark 10.3. (Hint: The negative
norm of a 0-1-indicator is 0, so be sure to verify no negative norms arise.)

b
ρ ρa
ρb and “s”
+
a
+

1/k for integers k

=
a
+
ρa

= −

=

+

>

1

ρ

+

10.9 By selecting “r”

10.10 Let g

L2(Ωn, π⊗

n). Writing x

(x1, x0), where x0

∈

justify the following identity of one-input functions: (T1
(Hint: You may want to refer to Exercise 8.21.)

=

=

(x2, . . . , xn), carefully
x0).
x0 =

ρ g)
|

Tρ(g

|

10.11 Prove Proposition 10.12.

10.12 Let X be a random variable and let Y denote its symmetrization X
R that Pr[

where X 0 is an independent copy of X . Show for any t, θ
t]

t/2].

X

∈

θ

X 0,

| ≥

−
Y
|

2 Pr[
|

≤

−

| ≥

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 34 -->
316

10. Advanced hypercontractivity

10.13 The goal of this exercise is to establish Lemma 10.43.

(a) Show that we may take c2

1 (and that equality holds). Henceforth

assume q

2.
(b) By following the idea of our q

>

=

exists 0

cq

1 such that

<
1

<
cq x

q

+
(c) Further reduce to showing there exists 0

≤ |

−

−

+

−

|

|

|

cq qx

1

1

q

x

qx

cq x

1

|

−

q

|

+
x2

cq qx

1

−

1

|

+

x

|

qx

q

−
x2

≤

4 proof, reduce to showing that there

=

1

cq

1

−

<

−

R.

x

∀

∈

1 such that

<

R.

x

∀

∈

(10.31)

Here you should also establish that both sides are continuous func-
tions of x

R once the value at x

0 is deﬁned appropriately.

=

0 such that for every 0

1
2 , inequal-
>
M. (Hint: Consider the limit of both sides

cq

<

<

∈
(d) Show that there exists M
ity (10.31) holds once
.)
as

x

x

|

| ≥

|

| → ∞

(e) Argue that it sufﬁces to show that

1

|

+

q

x

|

−
x2

qx

1

−

η

≥
for some universal positive constant η
>
[0, 1
ity argument for (x, cq)
2 ].)

M, M]

[
−

∈

×

(10.32)

0. (Hint: A uniform continu-

(f ) Establish (10.32). (Hint: The best possible η is 1, but to just achieve
is
.)
(g) Possibly using a different argument, what is the best asymptotic

some positive η, argue using Bernoulli’s inequality that |
everywhere positive and then observe that it tends to

| → ∞

+
as

−
x2
x

∞

qx

−

1

1

x

|

q

|

bound you can achieve for cq? Is cq

Ω( log q

q ) possible?

≥

10.14 Show that the largest c for which inequality (10.20) holds is the smaller

real root of c4

2c3

−
10.15 (a) Show that 1
c

2c
−
6c2x2

+

1
=
c4x4

+
1/2. (Can you also establish it for c

+

≤

+

+

1

6x2

0, namely, c

.435.

≈
4x3

≈

=

x4 holds for all x

+
.5269?)

R when

∈

(b) Show that if X is a random variable satisfying E[X ]
a

0 and
4 for all a
{
∞
k
−
uniformly random bit independent of X . (Cf. Lemma 10.15.)

=
R, where r

1
2 r X

, then

≤ k

X

+

+

∼

∈

a

k

k

4

X
4
<
k
1, 1} is a

k

(c) Establish the following improvement of Theorem 10.44 in the case of

4: for all f

q

=

∈

L2(Ωn, π⊗

n),

(where x

π⊗

n, r

∼

4,r,x

f (x)
4,x
k

≤ k

T 1
k

2 r f (x)
k
1, 1}n).

{
−

∼

10.16 Complete the proof of Theorem 10.39. (Hint: You’ll need to rework Exer-

cise 9.8 as in Lemma 10.38.)

10.17 Prove Proposition 10.17.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 35 -->
10.6. Exercises and notes

317

10.18 Recall from (10.5) the function ρ

2) by

q

>

ρ(λ) deﬁned for λ

∈

=

(0, 1/2) (and ﬁxed

ρ

=

ρ(λ)

exp(u/q)
exp(u/q0)

−
−
u(λ) is deﬁned by exp(

= s

exp(
exp(

−
−

u/q)
u/q0) = s

sinh(u/q)
sinh(u/q0)

,

λ

−

=

where u
u)
(a) Show that ρ is an increasing function of λ. (Hint: One route is to
), reduce
(1,
),
∞
), and

reduce to showing that ρ2 is a decreasing function of u
∞
to showing that q tanh(u/q) is an increasing function of q
reduce to showing tanh r
(0,
reduce to showing sinh(2r)

is a decreasing function of r

λ .
−

∈
∞

2r.)

(0,

=

∈

∈

1

r

(b) Verify the following statements from Remark 10.19:

≥

for ﬁxed q and λ

1/2, ρ

→

→

for ﬁxed q and λ

0, ρ

∼

→

Also show:

1

;

q
1
−
1/q.
λ1/2
p
−

for ﬁxed λ and q

, ρ

→ ∞

∼

r

u
sinh u s

1
q

,

and

u
sinh u ∼

(c) Show that ρ

q

p2λ ln(1/λ) for λ
0.
1/q holds for all λ.
λ1/2
−

→

1
pq

1

−

ρ

p

∈

<

<

Ω

|
| ≥
2 and 0

≥
10.19 Let (Ω, π) be a ﬁnite probability space,
has probability at least λ. Let 1
exercise is to prove the result of Wolff [Wol07] that, subject to
every f
k
there is at least one minimizing f ).
(a) We consider the equivalent problem of minimizing F( f )

2, in which every outcome
1. The goal of this
1,
p takes on at most two values (and

L2(Ω, π) that minimizes

p
p subject
1. Show that both F( f ) and G( f ) are C 1 function-

to G( f )
als (identifying functions f with points in RΩ).
(b) Argue from continuity that the minimum value for

p
p subject to
1 is attained. Henceforth write f0 to denote any minimizer;

Tρ f
k
the goal is to show that f0 takes on at most two values.

Tρ f
k

2
2 =

2
2 =

Tρ f

= k

= k

2
k

=

<

<

k

k

k

k

k

k

f

f

f

(c) Show that f0 is either everywhere nonnegative or everywhere nonpos-
itive. (Hint: By homogeneity our problem is equivalent to maximizing
Tρ f
1; now use Exercise 2.34.) Replacing f0 by
k
f0
|

2 subject to
k
if necessary, henceforth assume f0 is nonnegative.
1

g signi-
∇
ﬁes the pointwise product of functions on Ω, with π thought of as a
function Ω
0. (Hint: For the latter, write G( f )

2Tρ2 f0. Here π

|
(d) Show that

=
p f p
0

G( f0)

F( f0)

and

∇

=

=

.)

π

π

k

k

−

f

p

·

·

·

R≥

Tρ2 f , f

= 〈

〉

→

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 36 -->
318

10. Advanced hypercontractivity

(e) Use the method of Lagrange Multipliers to show that c f p
−
0
0.)
f (ω) satisﬁes the equa-

R+. (Hint: You’ll need to note that
E[ f0], argue that each value y

for some c
(f ) Writing µ

Tρ2 f0

G( f0)

6=

∇

=

1

=

∈
=

tion

c yp

1

−

ρ2 y

=

(1

+

−

ρ2)µ.

(10.33)

(g) Show that (10.33) has at most two solutions for y

R+, thereby com-
pleting the proof that f0 takes on at most two values. (Hint: Strict
concavity of yp

∈

1.)
−

(h) Suppose q
2. By slightly modifying the above argument, show that
>
g
subject to
q takes
k
on at most two values (and there is at least one maximizing g). (Hint:
At some point you might want to make the substitution g
Tρ f ; note
that g is two-valued if f is.)

L2(Ω, π) that maximizes

1, every g

Tρ g
k

2
k

=

=

∈

k

10.20 Fix 1

p

2 and 0

λ

1/2. Let Ω

1, 1} and π

πλ, meaning π(

1)

<

<
1

=
λ. The goal of this exercise is to show the result of Latała

<
λ, π(1)
and Oleszkiewicz [LO00]: the largest value of ρ for which
holds for all f

≤ k
L2(Ω, π) is as given in Theorem 10.18; i.e., it satisﬁes

f

p

k

Tρ f

2
k

<

=

−

=

=

−

k

{
−

∈

ρ2

r∗

=

=

exp(u/p0)
exp(u/p)

exp(
exp(

−
−

−
−

u/p0)
u/p)

,

(10.34)

q0 to facili-
where u is deﬁned by exp(
tate the proof; we get the (2, q)-hypercontractivity statement by Proposi-
tion 9.19.)
(a) Let’s introduce the notation α

λ . (Here we are using p
−

λ)1/p. Show that

λ1/p, β

u)

(1

−

=

=

1

λ

=
p

−

=
pβp

.

r∗

=

αpβ2
−
α2

−

α2
β2

−
−
E[ f ] and δ

=

(b) Let f

L2(Ω, π). Write µ

∈
to show

D1 f

=

=

ˆf (1). Our goal will be

µ2

+

δ2r∗

Tpr∗

f

2
2 ≤ k
k

f

2
p.
k

= k

(10.35)

In the course of doing this, we’ll also exhibit a nonconstant function f
that makes the above inequality sharp. Why does this establish that
no larger value of ρ is possible?

(c) Show that without loss of generality we may assume

f (

1)

−

y

,

1

+
α

=

f (1)

y

1

−
β

=

y

1

for some
argument to show that we may assume f
of (10.35).)

1. (Hint: First use Exercise 2.34 and a continuity
0; then use homogeneity

−

<

<

>

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 37 -->
10.6. Exercises and notes

319

(d) The left-hand side of (10.35) is now a quadratic function of y. Show

that our r∗ is precisely such that

LHS(10.35)

A y2

C

+

=

for some constants A, C; i.e., r∗ makes the linear term in y drop
out. (Hint: Work exclusively with the α, β notation and recall from
Deﬁnition 8.44 that δ2
1))2.)
λ)( f (1)

αpβp( f (1)

1))2

λ(1

f (

f (

=

−

−

−

=

−

−

(e) Compute that

βp

1

−
β

A

2

=

1

−

.

αp
α

−
−

(Hint: You’ll want to multiply the above expression by αp

(f ) Show that

RHS(10.35)

((1

+

=

y)p

(1

+

−

y)p)2/p.

(10.36)

βp

1.)

=

+

β
β

α
−
α >
+

Why does it now sufﬁce to show (10.35) just for 0
0. Show that if y

y
<
y∗, then f is a constant function

(g) Let y∗

1?

≤

=

= −
and both sides of (10.35) are equal to

4
β)2 .
+
(h) Deduce that both sides of (10.35) are equal to

(α

y∗. Verify
that after scaling, this yields the following nonconstant function for
which (10.35) is sharp: f (x)
pz for 0

1. By now we have reduced to showing

xu/p).

exp(

4
β)2 for y
+

=

=

−

(α

z

(i) Write y

=

≤
C

<
((1

Az

pz)p

(1

pz)p)2/p,

+

≤
knowing that both sides are equal when pz
sion on the right φ(z), show that

+

+

−

y∗. Calling the expres-

=

d
dz

φ(z)

A.

pz

y∗ =

=

(Hint: You’ll need αp
+
4
φ(z)
β)2 when pz
=
+
by showing that φ(z) is convex for z

=

=

(α

¯
¯
βp
1, as well as the fact from part (h) that
¯
y∗.) Deduce that we can complete the proof

(j) Show that φ is indeed convex on [0, 1) by showing that its derivative
is a nondecreasing function of z. (Hint: Use the Generalized Binomial
pz)p is
Theorem as well as 1
expressible as

+
0 b j z j where each b j is positive.)

2 to show that (1

pz)p

(1

<

<

+

−

p

[0, 1).

∈

∞j
=

P

10.21 Complete the proof of Theorem 10.18.

(Hint: Besides Exercises 10.19

and 10.20, you’ll also need Exercise 10.18(a).)

10.22 (a) Let Φ : [0,

R be deﬁned by Φ(x)
Verify that Φ is a smooth, strictly convex function.

)
∞

→

=

x ln x, where we take 0 ln 0

0.

=

(b) Consider the following:

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 38 -->
320

10. Advanced hypercontractivity

Deﬁnition 10.49. Let g
entropy of g is deﬁned by

∈

L2(Ω, π) be a nonnegative function. The

Verify that Ent[g]
constant, and that Ent[c g]

≥

Ent[g]

=

Φ

[Φ(g(x))]

E
x
π
∼
0 always, that Ent[g]

E
x
π
∼

−

³

[g(x)]

.

cEnt[g] for any constant c

=

´
0 if and only if g is
0.

=

≥

(c) Suppose ϕ is a probability density on {

1, 1}n (recall Deﬁnition 1.20).
n
Show that Ent[ϕ]
1/2), the Kullback–Leibler divergence of
π⊗
the uniform distribution from ϕ (more precisely, the distribution with
density ϕ).

DKL(ϕ

−

=

∥

10.23 The goal of this exercise is to establish:

The Log-Sobolev Inequality. Let f : {

1, 1}n

R. Then 1

2 Ent[ f 2]

I[ f ].

≤

→

−

(a) Writing ρ

e−

=

t, the (p, 2)-Hypercontractivity Theorem tells us that

t f

Te−
k

2
2 ≤ k
k

f

2
1
k

exp(

2t)

−
0. Denote the left- and right-hand sides as LHS(t), RHS(t).

+

≥

for all t
Verify that these are smooth functions of t
RHS(0). Deduce that LHS0(0)

RHS0(0).

≤

tation; cf. Exercise 2.18.)

= −

(b) Compute LHS0(0)

2I[ f ]. (Hint: Pass through the Fourier represen-

[0,

∈

) and that LHS(0)

∞

=

(c) Compute RHS0(0)

= −

Ent[ f 2], thereby deducing the Log-Sobolev In-
2t)]
−

exp(

+

f

1

equality. (Hint: As an intermediate step, deﬁne F(t)
and show that RHS0(0)
1, 1}n

+
R. Show that Ent[(1

F 0(0).)
² f )2]

F(0) ln F(0)

=

E[
|

=

|

+

∼

2 Var[ f ]²2 as ²

0.

→

−

→

(b) Deduce the Poincaré Inequality for f from the Log-Sobolev Inequality.

10.24 (a) Let f : {

10.25 (a) Deduce from the Log-Sobolev Inequality that for f : {

with α

=

min{Pr[ f

=

1], Pr[ f

1]},

= −
2α ln(1/α)

I[ f ].

≤

1, 1}n

−

1, 1}

{
−

→

(10.37)

This is off by a factor of ln 2 from the optimal edge-isoperimetric in-
1
equality Theorem 2.39. (Hint: Apply the inequality to either 1
2 f
or 1

2 −

1
2 f .)

2 +

(b) Give a more streamlined direct derivation of (10.37) by differentiating

the Small-Set Expansion Theorem.

10.26 This exercise gives a direct proof of the Log-Sobolev Inequality.

(a) The ﬁrst step is to establish the n

may assume f : {
Exercise 2.14, Exercise 10.22(b).)

1, 1}

→

−

1 case. Toward this, show that we
R is nonnegative and has mean 1. (Hints:

=

(b) Thus it remains to establish 1
b2

bx)2]
bx)2] is smooth on [

2 Ent[(1

that g(b)

+

1
2 Ent[(1

=

−

+

≤
−

b2 for b
[
−
1, 1] and satisﬁes g(0)

1, 1]. Show

∈

=

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 39 -->
10.6. Exercises and notes

321

0, g0(0)
0, and g00(b)
b2 +
this completes the proof of the n
=
(c) Show that for any two functions f

0 for b

ln 1
1, 1). Explain why
+
1
−
1 case of the Log-Sobolev Inequality.
R,

1, 1}n

(
−

, f

: {

=

=

∈

+

b2
b2 ≥

2b2
1

pE[ f 2
+

]

pE[ f 2
−

−
2

µ

→

2

]

≤

¶

+

−

f

E

+−

−
f
−2

·³
k · k

2.)

2

.

¸

´

(Hint: The triangle inequality for

(d) Prove the Log-Sobolev Inequality via “induction by restrictions” (as
described in Section 9.4). (Hint: For the right-hand side, establish
E[( f
Inf[ f ]
]. For the left-hand side, apply
+
induction, then the n

1
2 I[ f
1 base case, then part (c).)

1
2 I[ f

f
−2

)2]

+−

=

+

+

−

]

=

10.27 (a) By following the strategy of Exercise 10.23, establish the following:

Log-Sobolev Inequality for general product space domains.
L2(Ωn, π⊗
Let f
.
∈
Then 1
2 %Ent[ f 2]

n) and write λ
I[ f ], where

min(π), λ0

λ, exp(

λ
λ0

u)

=

=

−

−

=

1

≤

%(λ)

%

=

=

tanh(u/2)
u/2

2

=

λ0
−
ln λ0 −

λ
ln λ

.

(b) Show that %(λ)
1, 1}n
(c) Let f : {
distribution π⊗
1], Prπp [ f

−

∼
{
→
−
n
p . Write q
1]}, then

2/ ln(1/λ)) as λ

0.
1, 1} and treat {

→

1

−

=

−

= −

1, 1}n as having the p-biased

p. Show that if α

min{Prπp [ f

=

=

4

q
ln q

p
ln p

−
−

α ln(1/α)

I[ f (p)]

≤

and hence, for p

→
α logp α

0,

(1

+

≤

o p(1))p

·

x

E
π⊗
p

∼

n

[sens f (x)].

(10.38)

We remark that (10.38) is known to hold without the o p(1) for all
p

1/2.

≤

10.28 Prove Theorem 10.21. (Hint: Recall Proposition 8.28.)

10.29 Let X 1, . . . , X n be independent (2, q, ρ)-hypercontractive random variables
F(S) xS be an n-variate multilinear polynomial of

and let F(x)
=
degree at most k. Show that

|≤

S

k

|

P
F(X 1, . . . , X n)
k

b

q

≤
(Hint: You’ll need Exercise 10.3.)

k

(1/ρ)k

F(X 1, . . . , X n)
2.
k

k

10.30 Let 0

λ

Ω has π(ω0)

≤
<
outcome ω0
f
∈
pute
Corollary 10.20 cannot hold for ρ

1/2 and let (Ω, π) be a ﬁnite probability space in which some
πλ.) Deﬁne
2, com-
2 and deduce (in light of the proof of Theorem 10.21) that
k

L2(Ω, π) by setting f (ω0)

1, 1}, π
ω0. For q

λ. (For example, Ω

=
0 for ω

1, f (ω)

{
−
6=

q/
k

1/q.
λ1/2
−

=

≥

=

=

=

∈

k

k

f

f

>
Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 40 -->
322

10. Advanced hypercontractivity

10.31 Prove Theorem 10.22.

10.32 Prove Theorem 10.23.

10.33 Prove Theorem 10.24. (Hint: Immediately worsen q

the optimal choice of q is easier.)

10.34 Prove Theorem 10.25.

1 to q so that ﬁnding

−

10.35 Prove Friedgut’s Junta Theorem for general product spaces as stated in

Section 10.3.

10.36 Show that (10.9) implies F(pc

ηpc)

(Hint: Consider d

d p ln(1

−

+
F(p)).)

1

−

≥

² in the proof of Theorem 10.29.

10.37 Justify the various calculations and observations in Example 10.45.

10.38 (a) Let p

=
Show that I[ f ]

1
n and let f

L2({

1, 1}n, π⊗
4. (Hint: Proposition 8.45.)

−

∈

n
p ) be any Boolean-valued function.

≤

(b) Let us specialize to the case f

χ[n]. Show that f is not .1-close
to any width-O(1) DNF (under the 1
n -biased distribution, for n sufﬁ-
ciently large). This shows that the assumption of monotonicity can’t
be removed from Friedgut’s Conjecture. (Hint: Show that ﬁxing any
constant number of coordinates cannot change the bias of χ[n] very
much.)

=

10.39 A function h : Ωn

→

ing hold: There are “juntas” f1, . . . , f m : Ωn
[n] respectively. Further, g : (Ω
J1, . . . , Jm
symbol not in Ω. Finally, for each input x
for j

Σ is said to expressed as a pseudo-junta if the follow-
{True,False} with domains
})n
is a new
∗
g(y), where

→
{
∪
∗
→
Ωn we have h(x)

Σ, where

[n],

=

⊆

∈

∈

yj

x j

= (

∗

if j

∈
else.

Ji for some i with f i(x)

True,

=

An alternative explanation is that on input x, the junta f i decides whether
the coordinates in its domain are “notable”; then, h(x) must be determined
based only on the set of all notable coordinates. Finally, if π is a distribu-
tion on Ω, we say that the pseudo-junta has width-k under π⊗

n if

E
π⊗
∼

x

[#{ j : y j 6= ∗
}]

n

≤

k;

∈

L2(Ωn, π⊗

in other words, the expected number of notable coordinates is at most k.
n) we simply say that h is a k-pseudo-junta. Show that
For h
4k. (Hint: Re-
1, 1}-valued, then I[ f ]
if such a k-pseudo-junta h is {
ferring to the second statement in Proposition 8.24, consider the notable
(xi, . . . , xi
coordinates for both x and x0

≤

−

1, x0i, xi
−

1, . . . , xn).)
+

=

10.40 Establish the following further consequence of Bourgain’s Sharp Thresh-
{True,False} be a monotone function
cK 2), where c is a

old Theorem: Let f : {True,False}n
with I[ f (p)]

K. Assume Var[ f ]

→
.01 and 0

exp(

p

≤

≥

<

≤

−

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 41 -->
10.6. Exercises and notes

323

large universal constant. Then there exists T
that

⊆

[n] with

T

|

| ≤

O(K) such

Pr
π⊗
p

∼

n

x

[ f (x)

=

True

xi

|

=

True for all i

T]

∈

≥

x

Pr
π⊗
p

∼

n

[ f (x)

=

True]

exp(

+

O(K 2)).

−

(Hint: Bourgain’s Sharp Threshold Theorem yields a booster either to-
ward True or toward False. In the former case you’re easily done; to rule
out the latter case, use the fact that p

O(K 2)).)

exp(

T

|

| ¿

−

10.41 Suppose that in Bourgain’s Sharp Threshold Theorem we drop the as-
(Assume at least that f is nonconstant.)
O(I[ f ]2/ Var[ f ]2))
exp(

sumption that Var[ f ]
Show that there is some τ with
such that

stddev[ f ]

.01.

| ≥

≥

−

τ

·

|

Pr
π⊗
∼

x

T

[
∃

n

⊆

[n],

T

|

| ≤

(Cf. Exercise 9.32.)

O(I[ f ]/ Var[ f ]) such that xT is a τ-booster]

τ

≥ |

.

|

10.42 In this exercise we give the beginnings of the idea of how Bourgain’s Sharp
Threshold Theorem can be used to show sharp thresholds for interesting
monotone properties. We will consider
3Col, the property of a random
v-vertex graph G
(a) Prove that the critical probability pc satisﬁes pc

G (v, p) being non-3-colorable.

O(1/v); i.e., estab-

∼

¬

≤
lish that there is a universal constant C such that

Pr[G

∼

G (v, C/v) is 3-colorable]

on(1).

=

(Hint: Union-bound over all potential 3-colorings.)

|

|

τ

∼

G (v, pc), there is a

(b) Toward showing (non-)3-colorability has a sharp threshold, suppose
the property had constant total inﬂuence at the critical probability.
Bourgain’s Sharp Threshold Theorem would imply that there is a τ
of constant magnitude such that for G
chance
that G contains a τ-boosting induced subgraph GT . There are two
cases, depending on the sign of τ. It’s easy to rule out that the boost
is in favor of 3-colorability; the absence of a few edges shouldn’t in-
crease the probability of 3-colorability by much (cf. Exercise 10.40).
On the other hand, it might seem plausible that the presence of a
certain constant number of edges chould boost the probability of non-
3-colorability by a lot. For example, the presence of a 4-clique imme-
diately boosts the probability to 1. However, the point is that at the
critical probability it is very unlikely that G contains a 4-clique (or in-
deed, any “local” witness to non-3-colorability). Short of showing this,
G (v, p) is
prove at least that the expected number of 4-cliques in G
pc.
ov(1) unless p

Ω(v−

2/3)

∼

=

À

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 42 -->
324

10. Advanced hypercontractivity

Notes. As mentioned, the standard template introduced by Bonami [Bon70]
for proving the Hypercontractivity Theorem for
1 bits is to ﬁrst prove the
Two-Point Inequality, and then do the induction described in Exercise 10.3.
Bonami’s original proof of the Two-Point Inequality reduced to the 1
≤
2 case as we did, but then her calculus was a little more cumbersome. We fol-
lowed the proof of the Two-Point Inequality appearing in Janson [Jan97]. An-
other approach to proving the Hypercontractivity Theorem is to derive it from
the Log-Sobolev Inequality (Exercise 10.23), as was done by Gross [Gro75].

≤

±

<

p

q

Our use of two-function hypercontractivity theorems to facilitate an in-
ductive proof (and avoid the use of Exercise 10.1) follows the communica-
tion/coding theory viewpoint of Ahlswede and Gács [AG76]. (We were also
inspired by Mossel et al. [MOR+06], Barak et al. [BBH+12], and Kauers
et al. [KOTZ16].) Ahlswede and Gács established the close connection be-
tween hypercontractivity and small-set expansion in general product spaces,
1
and independently obtained the sharp Hypercontractivity Theorem for
bits, relying in part on a result of Witsenhausen [Wit75].

±

Our statement of the Generalized Small-Set Expansion Theorem is mod-
eled after the almost identical Reverse Small-Set Expansion Theorem, ﬁrst
proved by Mossel et al. [MOR+06]. The Reverse Hypercontractivity Inequal-
ity itself is due to Borell [Bor82]; the presentation in Exercises 10.6–10.9
follows Mossel et al. [MOR+06]. For more on reverse hypercontractivity, in-
cluding the very surprising fact that the Reverse Hypercontractivity Inequal-
ity holds with no change in constants for every product probability space, see
Mossel, Oleszkiewicz, and Sen [MOS12].

As mentioned in Chapter 9 the deﬁnition of a hypercontractive random
variable is due to Krakowiak and Szulga [KS88]. Many of the basic facts from
Section 10.2 (and also Exercise 10.2) are from this work and the earlier work of
Borell [Bor84]; see also various other works [KW92, Jan97, Szu98, MOO10].
As mentioned, the main part of Theorem 10.18 (the case of biased bits) is es-
sentially from Latała and Oleszkiewicz [LO00]; see also Oleszkiewicz [Ole03].
Our Exercise 10.20 ﬂeshes out (and slightly simpliﬁes) their computations but
introduces no new idea. Earlier works [BKK+92, Tal94, FK96, Fri98] had
established forms of the General Hypercontractivity Theorem for λ-biased
bits, giving as applications KKL-type theorems in this setting with the correct
asymptotic dependence on λ. We should also mention that the sharp Log-
Sobolev Inequality for product space domains (mentioned in Exercise 10.27)
was derived independently of Latała and Oleszkiewicz’s work by Higuchi and
Yoshida [HY95] (without proof), by Diaconis and Saloff-Coste [DSC96] (with
proof), and possibly also by Oscar Rothaus (see [BL98]). Unlike in the case of

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 43 -->
10.6. Exercises and notes

325

uniform
1 bits, it’s not known how to derive Latała and Oleszkiewicz’s opti-
mal biased hypercontractive inequality from the optimal biased Log-Sobolev
Inequality.

±

Kahane [Kah68] has been credited with pioneering the randomization/
symmetrization trick for random variables. The entirety of Section 10.4 is
due to Bourgain [Bou79], though our presentation was signiﬁcantly informed
by the expertise of Krzysztof Oleszkiewicz (and our proof of Lemma 10.43 is
slightly different). Like Bourgain, we don’t give any explicit dependence for
the constant Cq in Theorem 10.39; however, Kwapie ´n [Kwa10] has shown
O(q/ log q) for q
that one may take Cq0 =
2. Our proof of Bourgain’s
Theorem 10.47 follows the original [Bou99] extremely closely, though we also
valued the easier-to-read version of Bal [Bal13].

Cq

≥

=

The biased edge-isoperimetric inequality (10.38) from Exercise 10.27 was
proved by induction on n, without the additional o p(1) error, by Russo [Rus82]
(and also independently by Kahn and Kalai [KK07]). We remark that this
work and the earlier [Rus81] already contain the germ of the idea that
monotone functions with small inﬂuences have sharp thresholds. Regarding
the sharp threshold for 3-colorability discussed in Exercise 10.42, Alon and
Spencer [AS08] contains a nice elementary proof of the fact that at the critical
probability for 3-colorability, every subgraph on ²v vertices is 3-colorable, for
0. The existence of a sharp threshold for k-colorability was
some universal ²
proven by Achlioptas and Friedgut [AF99], with Achlioptas and Naor [AN05]
essentially determining the location.

>

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 44 -->

