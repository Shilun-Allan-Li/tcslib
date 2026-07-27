<!-- generated-by: proofmatch local extraction -->
<!-- source-pdf-sha256: fc447f3269100012c1e1bf10316f1acd21c186aa8f8f6bedce44bf0bdca4b4f5 -->
<!-- extractor: pdfminer.six v20260107 -->

<!-- pdf-page: 1 -->
Chapter 4

DNF formulas and
small-depth circuits

In this chapter we investigate Boolean functions representable by small DNF
formulas and constant-depth circuits; these are signiﬁcant generalizations
of decision trees. Besides being natural from a computational point of view,
these representation classes are close to the limit of what complexity theorists
can “understand” (e.g., prove explicit lower bounds for). One reason for this is
that functions in these classes have strong Fourier concentration properties.

4.1. DNF formulas

One of the commonest ways of representing a Boolean function f : {0, 1}n
{0, 1} is by a DNF formula:

→

Deﬁnition 4.1. A DNF (disjunctive normal form) formula over Boolean vari-
ables x1, . . . , xn is deﬁned to be a logical OR of terms, each of which is a logi-
cal AND of literals. A literal is either a variable xi or its logical negation xi.
We insist that no term contains both a variable and its negation. The number
of literals in a term is called its width. We often identify a DNF formula with
the Boolean function f : {0, 1}n

{0, 1} it computes.

→

Example 4.2. Recall the function Sort3, deﬁned by Sort3(x1, x2, x3)
only if x1
follows:

1 if and
x3. We can represent it by a DNF formula as

x3 or x1

x2

x2

=

≤

≤

≥

≥

Sort3(x1, x2, x3)

(x1

x2)

(x2

x3)

(x1

x3)

∧

∨

∨

(x1

∧

x3).

∧

∨

∧

=

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.

93



<!-- pdf-page: 2 -->
94

4. DNF formulas and small-depth circuits

The DNF representation says that the bits are sorted if either the ﬁrst two
bits are 1, or the last two bits are 0, or the ﬁrst bit is 0 and the last bit is 1, or
the ﬁrst bit is 1 and the last bit is 0.

The complexity of a DNF formula is measured by its size and width:

Deﬁnition 4.3. The size of a DNF formula is its number of terms. The width
is the maximum width of its terms. Given f : {
1, 1} we write
DNFsize( f ) (respectively, DNFwidth( f )) for the least size (respectively, width)
of a DNF formula computing f .

1, 1}n

{
−

→

−

The DNF formula for Sort3 from Example 4.2 has size 3 and width 2.
{0, 1} can be computed by a DNF of size at most 2n

Every function f : {0, 1}n
and width at most n (Exercise 4.1).

→

There is also a “dual” notion to DNF formulas:

Deﬁnition 4.4. A CNF (conjunctive normal form) formulas is a logical AND
of clauses, each of which is a logical OR of literals. Size and width are deﬁned
as for DNFs.

Some functions can be represented much more compactly by CNFs than
DNFs (see Exercise 4.14). On the other hand, if we take a CNF computing f
and switch its ANDs and ORs, the result is a DNF computing the dual func-
tion f † (see Exercises 1.8 and 4.2). Since f and f † have essentially the same
Fourier expansion, there isn’t much difference between CNFs and DNFs when
it comes to Fourier analysis. We will therefore focus mainly on DNFs.

DNFs and CNFs are more powerful than decision trees for representing

Boolean-valued functions, as the following proposition shows:

Proposition 4.5. Let f : {0, 1}n
{0, 1} be computable by a decision tree T of
size s and depth k. Then f is computable by a DNF (and also a CNF) of size
at most s and width at most k.

→

Proof. Take each path in T from the root to a leaf labeled 1 and form the
logical AND of the literals describing the path. These are the terms of the
required DNF. (For the CNF clauses, take paths to label 0 and negate all
(cid:3)
literals describing the path.)

Example 4.6. If we perform this conversion on the decision tree computing
Sort3 in Figure 3.1 we get the DNF

(x1

x3

x2)

(x1

x3)

(x1

x2

x3)

(x2

x3).

∧

∧

∨
This has size 4 (indeed at most the decision tree size 6) and width 3 (indeed
at most the decision tree depth 3). It is not as simple as the equivalent DNF
from Example 4.2, though; DNF representation is not unique.

∨

∧

∧

∧

∨

∧

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 3 -->
4.1. DNF formulas

95

The class of functions computable by small DNFs is intensively studied
in learning theory. This is one reason why the problem of analyzing spectral
concentration for DNFs is important. Let’s begin with the simplest method
for this: understanding low-degree concentration via total inﬂuence. We will
switch to

1 notation.

Proposition 4.7. Suppose that f : {
Then I[ f ]

2w.

−

1, 1}n

1, 1} has DNFwidth( f )

{
−

w.

≤

→

±

≤

Proof. We use Exercise 2.10, which states that

=

−

−

=

i)

1,1}n

[# (

I[ f ]

1)-pivotal” on input x if f (x)

1)-pivotal coordinates for f on x],

2 E
x
{
−
∼
1 (logical True) but
where coordinate i is “(
1 (logical False). It thus sufﬁces to show that on every input x there
f (x⊕
are at most w coordinates which are (
1)-pivotal
−
1 (True); this means that at least
coordinates at all on x we must have f (x)
one term T in f ’s width-w DNF representation must be made True by x. But
1)-pivotal coordinate then either xi or xi must appear in T;
now if i is a (
otherwise, T would still be made true by x⊕
1)-pivotal
coordinates on x is at most the number of literals in T, which is at most w. (cid:3)

i. Thus the number of (

1)-pivotal. To have any (

= −

= −

−

−

−

Since I[ f †]

=

I[ f ] the proposition is also true for CNFs of width at most w.

1, 1} has I[χ[w]]

The proposition is very close to being tight: The parity function χ[w] : {
→
w (the latter being true for all w-
{
−
juntas). In fact, the proposition can be improved to give the tight upper
bound w (Exercise 4.17).

w and DNFwidth(χ[w])

=

−

≤

1, 1}n

Using Proposition 3.2 we deduce:

Corollary 4.8. Let f : {
→
the Fourier spectrum of f is ²-concentrated on degree up to 2w/².

1, 1} have DNFwidth( f )

{
−

−

≤

1, 1}n

w. Then for ²

0,

>

The dependence here on w is of the correct order (by the example of the
parity χ[w] again), but the dependence on ² can be signiﬁcantly improved as
we will see in Section 4.4.

There’s usually more interest in DNF size than in DNF width; for example,
learning theorists are often interested in the class of n-variable DNFs of size
poly(n). The following fact (similar to Exercise 3.22) helps relate the two,
suggesting O(log n) as an analogous width bound:

Proposition 4.9. Let f : {
of size s and let ²
DNF of width log(s/²).

∈

1, 1}n

1, 1} be computable by a DNF (or CNF)
(0, 1]. Then f is ²-close to a function g computable by a

{
−

→

−

Proof. Take the DNF computing f and delete all terms with more than log(s/²)
literals; let g be the function computed by the resulting DNF. For any deleted

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 4 -->
96

4. DNF formulas and small-depth circuits

log(s/²)

term T, the probability a random input x
2−
that Pr[g(x)

1, 1}n makes T true is at most
{
−
∼
²/s. Taking a union bound over the (at most s) such terms shows
(cid:3)

². (A similar proof works for CNFs.)

f (x)]

=

6=

≤

By combining Proposition 4.9 and Corollary 4.8 we can deduce (using Exer-
cise 3.17) that DNFs of size s have Fourier spectra ²-concentrated up to degree
O(log(s/²)/²). Again, the dependence on ² will be improved in Section 4.4. We
will also later show in Section 4.3 that size-s DNFs have total inﬂuence at
most O(log s), something we cannot deduce immediately from Proposition 4.7.

In light of the Kushilevitz–Mansour learning algorithm it would also be
nice to show that poly(n)-size DNFs have their Fourier spectra concentrated
on small collections (not necessarily low-degree). In Section 4.4 we will show
they are ²-concentrated on collections of size nO(log log n) for any constant ²
0.
It has been conjectured that this can be improved to poly(n):

>

Mansour’s Conjecture. Let f : {
of size s
concentrated on a collection F with
poly(n) and ²

1 and let ²

>

∈

F

|

| ≤

>

1, 1} be computable by a DNF
(0, 1/2]. Strong conjecture: f ’s Fourier spectrum is ²-

{
−

→

−

1, 1}n

sO(log(1/²)). Weaker conjecture: if s

0 is any ﬁxed constant, then we have the bound

≤
poly(n).

F

|

| ≤

4.2. Tribes

In this section we study the tribes DNF formulas, which serve as an important
examples and counterexamples in analysis of Boolean functions. Perhaps the
most notable feature of the tribes function is that (for a suitable choice of
parameters) it is essentially unbiased and yet all of its inﬂuences are quite
tiny.

Recall from Chapter 2.1 that the function Tribesw,s : {

deﬁned by its width-w, size-s DNF representation:

1, 1}sw

−

1, 1} is

{
−

→

Tribesw,s(x1, . . . , xw, . . . , x(s

1)w

−

1, . . . , xsw)
+
(x1

=
(We are using the notation where
logical False.) As is computed in Exercise 2.13 we have:

∨ · · · ∨

−

xw)

(x(s
∧ · · · ∧
1 represents logical True and 1 represents

∧ · · · ∧

xsw).

1)w

−

+

1

Fact 4.10. Prx[Tribesw,s(x)

1]

1

−

=

(1

−

= −

2−

w)s.

The most interesting setting of parameters makes this probability as close

to 1/2 as possible (a slightly different choice than the one in Exercise 2.13):

Deﬁnition 4.11. For w
w)s
1
=
to be Tribesw,s. Note this is only deﬁned only for certain n: 1, 4, 15, 40, . . .

sw be the largest integer such that
1, 1}

=
sw we deﬁne Tribesn : {

1/2. Then for n

1, 1}n

{
−

nw

2−

→

(1

≤

−

−

−

=

∈

N+, let s

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 5 -->
4.2. Tribes

97

Here s
n/ log n. A slightly more careful accounting (Exercise 4.5) yields:

ln(2)w2w and therefore w

ln(2)2w, hence n

log n

≈

≈

≈

−

log ln n and

s

≈

Proposition 4.12. For the Tribesn function as in Deﬁnition 4.11:

s

n

w

=

=

=

•

•

•

•

Θw(1);

ln(2)2w
−
ln(2)w2w

log n

−

Pr[Tribesn(x)

−
log ln n

Θ(w), thus nw

1

(2

+

=
on(1), and 2w
log n
n

1/2

O

=
.

+
1]

= −

=

−

o(1))nw;
+
n
ln n (1

+

on(1));

´
Thus with this setting of parameters Tribesn is essentially unbiased. Re-

³

garding its inﬂuences:

Proposition 4.13. Infi[Tribesn]
(ln n)(1
I[Tribesn]

o(1)).

=

±

ln n
n (1

±

=

o(1)) for each i

[n] and hence

∈

Proof. Thinking of Tribesn
and only if: (a) all other voters in i’s “tribe” vote
produce the outcome 1 (False). The probability of this is indeed

Tribesw,s as a voting rule, voter i is pivotal if
1 (True); (b) all other tribes

=

−

(w

2−

1)

−

(1

·

−

2−

w)s

1

−

=

2
2w

1 ·
−

Pr[Tribesn

1]

=

=

ln n
n (1

±

o(1)),

where we used Fact 4.10 and then Proposition 4.12.

(cid:3)

Thus if we are interested in (essentially) unbiased voting rules in which
every voter has small inﬂuence, Tribesn is a much stronger example than
Majn where each voter has inﬂuence Θ(1/pn). You may wonder if the max-
imum inﬂuence can be even smaller than Θ
for unbiased voting rules.
Certainly it can’t be smaller than 1
n , since the Poincaré Inequality says that
I[ f ]
1 for unbiased f . In fact the famous KKL Theorem shows that the
Tribesn example is tight up to constants:

ln n
n

≥

¢

¡

Kahn–Kalai–Linial (KKL) Theorem. For any f : {

MaxInf[ f ]

=

max
[n]
i
∈

{Infi[ f ]}

Var[ f ]

·

≥

We prove the KKL Theorem in Chapter 9.

−
Ω

1, 1}n
log n
n

³

1, 1},

{
−

→
.

´

We conclude this section by recording a formula for the Fourier coefﬁcients

of Tribesw,s. The proof is Exercise 4.6.

Proposition 4.14. Suppose we index the Fourier coefﬁcients of the function
[sw], where Ti is the in-
Tribesw,s{
{
=
−
→
tersection of T with the ith “tribe”. Then

1, 1} by sets T

(T1, . . . , Ts)

1, 1}sw

−

⊆

Tribesw,s(T)

á

2(1

2−
−
1)k

+|

w)s
T

−
|2−

1
kw(1

= (

2(

−

if T

if k

2−

w)s

−

k

−

=

,
= ;

#{i : Ti

}
6= ;

>

0.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 6 -->
98

4. DNF formulas and small-depth circuits

4.3. Random restrictions

In this section we describe the method of applying random restrictions. This is
a very “Fourier-friendly” way of simplifying a Boolean function. As motivation,
let’s consider the problem of bounding total inﬂuence for size-s DNFs. One
plan is to use the results from Section 4.1: size-s DNFs are .01-close to width-
O(log s) DNFs, which in turn have total inﬂuence O(log s). This suggests that
size-s DNFs themselves have total inﬂuence O(log s). To prove this though
we’ll need to reverse the steps of the plan; instead of truncating DNFs to a
ﬁxed width and arguing that a random input is unlikely to notice, we’ll ﬁrst
pick a random (partial) input and argue that this is likely to make the width
small.

Let’s formalize the notion of a random partial input, or restriction:

∈

[0, 1], we say that J is a δ-random subset of N if it
Deﬁnition 4.15. For δ
is formed by including each element of N independently with probability δ.
1, 1}n to be a pair (J
We deﬁne a δ-random restriction on {
z), where ﬁrst
|
1, 1}J is chosen
J is chosen to be a δ-random subset of [n] and then z
{
−
J and is ﬁxed
[n] is free if i
uniformly at random. We say that coordinate i
if i
J. An equivalent deﬁnition is that each coordinate i is (independently)
free with probability δ and ﬁxed to

1 with probability (1

δ)/2 each.

−

∼

∉

∈

∈

±

−

−

R and a random restriction (J

1, 1}n
z), we can form the re-
Given f : {
|
R as usual. However, it’s inconvenient that
stricted function f J
the domain of this function depends on the random restriction. Thus when
dealing with random restriction we usually invoke the following convention:

1, 1}J

→
z : {

→

−

|

Deﬁnition 4.16. Given f : {
−
tify the restricted function f I
−
R in which the input coordinates {

1, 1}n
z : {

|

R, I

[n], and z

1, 1}I , we may iden-

→
1, 1}I

⊆
R with its extension f I

∈

→

1, 1}I are ignored.

1, 1}n

z : {

|

−

→

{
−

−

As mentioned, random restrictions interact nicely with Fourier expan-

sions:

Proposition 4.17. Fix f : {
random restriction on {

−
1, 1}n,

1, 1}n

R and S

⊆

→

[n]. Then if (J

z) is a δ-

|

E[

z(S)]

Pr[S

J]

·

⊆

f (S)

=

=

S

δ|

f (S),

|

and

d

b

b

z(S)2]

E[

f J

|

=

Pr[U

J

S]

·

=

∩

f (U)2

=

S

δ|

|(1

−

U\S

δ)|

f (U)2,

|

where we are treating f J

d

b
z as a function {

1, 1}n

R.

b

S
U
⊇
X

→

−

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.

−
f J

|

U

[n]

⊆
X

|



<!-- pdf-page: 7 -->
4.3. Random restrictions

99

Proof. Suppose ﬁrst that J
tions f J
that for any S

⊆
z as having domain {
−
[n],

|

⊆

[n] is ﬁxed. When we think of restricted func-
1, 1}n, Corollary 3.22 may be stated as saying

z

E
1,1}J

{
∼
−
E
1,1}J

[

[

f J

z(S)]

|
z(S)2]
d
f J
|

=

=

z

{
−
∼

f (S)

b
U

[n]

⊆
X

1S

J,

⊆

·
f (U)2

d

b

1U

S.

J

=

∩

·

The proposition now follows by taking the expectation over J.

(cid:3)

Corollary 4.18. Fix f : {
restriction, then E[Infi[ f J

1, 1}n
−
z]]

R and i

[n]. If (J
|
∈
δInfi[ f ]. Hence also E[I[ f J

→

|

=

z) is a δ-random
z]]

δI[ f ].

=

|

Proof. We have

E[Infi[ f J

z]]

|

=

E

"
i
S
3
X

z(S)2

f J

|

d
=

U

[n]

⊆
X

# =

i
S
3
X
Pr[U

where the second equality used Proposition 4.17.

b

Pr[U

J

∩

=

S]

f (U)2

U

[n]

⊆
X
J

∩

i]

f (U)2

3

=

i
U
3
X

f (U)2
b
δ

δInfi[ f ],

=

b

(cid:3)

(Proving Corollary 4.18 via Proposition 4.17 is a bit more elaborate than
necessary; see Exercise 4.9.)

Corollary 4.18 lets us bound the total inﬂuence of a function f by bounding
the (expected) total inﬂuence of a random restriction of f . This is useful if f
is computable by a DNF formula of small size, since a random restriction is
very likely to make this DNF have small width. This is a consequence of the
following lemma:

Lemma 4.19. Let T be a DNF term over {
a (1/2)-random restriction on {

1, 1}n and ﬁx w
∈
1, 1}n. Then Pr[width(TJ
z)

−

N+. Let (J

z) be

|
(3/4)w.

w]

≤

≥

|

−

Proof. We may assume the initial width of T is at least w, as otherwise its
z) cannot have width at least w. Now if any literal
restriction under (J
appearing in T is ﬁxed to False by the random restriction, the restricted term
TJ
w. Each literal is ﬁxed
to False with probability 1/4; hence the probability no literal in T is ﬁxed to
(cid:3)
False is at most (3/4)w.

z will be constantly False and thus have width 0

<

|

|

We can now bound the total inﬂuence of small DNF formulas.

Theorem 4.20. Let f : {
Then I[ f ]

O(log s).

−

1, 1}n

≤

1, 1} be computable by a DNF of size s.

{
−

→

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 8 -->
100

4. DNF formulas and small-depth circuits

Proof. Let (J
DNFwidth( f J
s(3/4)w. Hence

|

|

z) be a (1/2)-random restriction on {

z). By a union bound and Lemma 4.19 we have that Pr[w

1, 1}n and write w
w]

−

=
≤

≥

E[w]

=

∞

w
1
=
X

Pr[w

w]

≤

≥

3 log s

s(3/4)w

+

w

3 log s
>
X
3 log s

+
From Proposition 4.7 we obtain E[I[ f J
Corollary 4.18 we conclude I[ f ]

z]]
|
2 E[I[ f J

≤

≤
O(log s)
=
O(log s).

+

=
O(log s). And so from
(cid:3)

2
≤
z]]

|

·
≤

=

4s(3/4)3 log s

3 log s

4/s0.2

O(log s).

4.4. Håstad’s Switching Lemma and the spectrum of DNFs

¿

Let’s further investigate how random restrictions can simplify DNF formulas.
Suppose f is computable by a DNF formula of width w, and we apply to it a
1/w. For each term T in the DNF, one of three
δ-random restriction with δ
things may happen to it under the random restriction. First and by far most
likely, one of its literals may be ﬁxed to False, allowing us to delete it. If this
doesn’t happen, the second possibility is that all of T’s literals are made True,
in which case the whole DNF reduces to the constantly True function. With
1/w, this is in turn much more likely than the third possibility, which is
δ
that at least one of T’s literals is left free, but all the ﬁxed literals are made
True. Only in this third case is T not trivialized by the random restriction.

¿

This reasoning might suggest that f is likely to become a constant func-
tion under the random restriction. Indeed, this is true, as the following theo-
rem shows:

Baby Switching Lemma. Let f : {
−
or CNF of width at most w and let (J

1, 1}n

{
−

→

1, 1} be computable by a DNF

z) be a δ-random restriction. Then

|
z is not a constant function]

Pr[ f J

|

5δw.

≤

This is in fact the k

=

1 case of the following much more powerful theorem:

Håstad’s Switching Lemma. Let f : {
−
DNF or CNF of width at most w and let (J
for any k

N,

|

∈

Pr[DT( f J

k]

z)

|

≥

≤

(5δw)k.

1, 1}n
1, 1} be computable by a
z) be a δ-random restriction. Then

{
−

→

What is remarkable about this result is that it has no dependence on the
size of the DNF, or on n. In words, Håstad’s Switching Lemma says that when
1/w, it’s exponentially unlikely (in k) that applying a δ-random restriction
δ
to a width-w DNF does not convert (“switch”) it to a decision tree of depth
less than k. The result is called a “lemma” for historical reasons; in fact, its
proof requires some work. You are asked to prove the Baby Switching Lemma

¿

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 9 -->
4.4. Håstad’s Switching Lemma and the spectrum of DNFs

101

in Exercise 4.19; for Håstad’s Switching Lemma, consult Håstad’s original
proof [Hås87] or the alternate proof of Razborov [Raz93, Bea94].

Since we have strong results about the Fourier spectra of decision trees
(Proposition 3.16), and since we know random restrictions interact nicely with
Fourier coefﬁcients (Proposition 4.17), Håstad’s Switching Lemma allows us
to prove some strong results about Fourier concentration of narrow DNF
formulas. We start with an intermediate result which will be of use:

1, 1}n
Lemma 4.21. Let f : {
{
−
N+ and write ²
Pr[DT( f J
δ
|
f is 3²-concentrated on degree up to 3k/δ.

1, 1} and let (J
z)

0. Fix k

→
=

>

≥

−

∈

z) be a δ-random restriction,
k]. Then the Fourier spectrum of

|

Proof. The key observation is that DT( f J
sition 3.16), in which case the Fourier weight of f J
is 0. Since this weight at most 1 in all cases we conclude

z)

<

|

|

k implies deg( f J

k (Propo-
z)
|
z at degree k and above

<

E
(J
|

z)

[n]
S
h X
⊆
k
S
|≥
|

Using Proposition 4.17 we have

z(S)2

f J

|

d

².

≤

i

z(S)2

f J

|

E
(J
|

z)

[n]
S
h X
⊆
k
S
|≥
|

=

i

[n]
k

S
⊆
X
S
|≥

|

E
(J
|

z)

[

f J

|

z(S)2]

=

Pr
z)
(J
|

U
[
|

J

k]

·

| ≥

∩

f (U)2.

U

[n]

⊆
X

d

d
U
The distribution of random variable
| ≥
|
3k/δ this random variable has mean at least 3k, and a Chernoff bound shows
U
Pr[
|

U
is Binomial(
|

, δ). When

2/3. Thus

2
3 k)

exp(

U
|

k]

∩

≤

∩

≤

J

J

b

|

|

| <
²

U
[
|

−
Pr
z)
(J
|
f (U)2

≥

U

[n]

⊆
X
3k/δ

J

k]

·

| ≥

∩

f (U)2

3² as claimed.

b

≤

and hence

U
|

|≥

≥

3k/δ

U
|≥
X|

2/3)

(1

−

·

f (U)2

b

(cid:3)

We can now improve the dependence on ² in Corollary 4.8’s low-degree

b

P

spectral concentration for DNFs:

Theorem 4.22. Suppose f : {
→
width w. Then f ’s Fourier spectrum is ²-concentrated on degree up to O(w log(1/²)).

1, 1} is computable by a DNF of

{
−

−

1, 1}n

Proof. This follows immediately from Håstad’s Switching Lemma together
C log(1/²) for a sufﬁciently large
with Lemma 4.21, taking δ
(cid:3)
constant C.

1
10w and k

=

=

In Lemma 4.21, instead of using the fact that depth-k decision trees have
no Fourier weight above degree k, we could have used the fact that their
Fourier 1-norm is at most 2k. As you are asked to show in Exercise 4.11, this
would yield:

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 10 -->
102

4. DNF formulas and small-depth circuits

Lemma 4.23. Let f : {
Then

−

1, 1}n

1, 1} and let (J

{
−

|

→

z) be a δ-random restriction.

U

δ|

|

· |

f (U)

| ≤

E
(J
|

z)

[2DT( f J

z)].

|

U

[n]

⊆
X

b

We can combine this with the Switching Lemma to deduce that width-w

DNFs have small Fourier 1-norm at low degree:

Theorem 4.24. Suppose f : {
width w. Then for any k,

−

1, 1}n

1, 1} is computable by a DNF of

{
−

→

k |

U
|≤
X|

f (U)

| ≤

2

·

(20w)k.

b

Proof. Apply Håstad’s Switching Lemma to f with δ

1
20w to deduce

=

[2DT( f J

z)]

|

E
(J
|

z)

∞

≤

d
0
=
X

¡

5
20

d

2d

·

=

2.

¢

Thus from Lemma 4.23 we get

2

≥

as needed.

U

[n]

⊆
X

1
20w

U
|

|

f (U)

| ≥

· |

¡

¢

b

1
20w

k

·

¡

¢

U
|≤
X|

f (U)
|

,

k |

b

(cid:3)

Our two theorems about the Fourier structure of DNF are almost enough

to prove Mansour’s Conjecture:

Theorem 4.25. Let f : {
2. Then for any ²
collection F with

∈
F
|

| ≤

wO(w log(1/²)).

1, 1}n

−

≥
(0, 1/2], the Fourier spectrum of f is ²-concentrated on a

→

1, 1} be computable by a DNF of width w

{
−

=

Cw log(4/²) and let g

Proof. Let k
then Theorem 4.22 tells us that
g ˆ
gives ˆ
k1 ≤
k
collection F with
|
²-concentrated on this same collection.

k. If C is a large enough constant,
²/4. Furthermore, Theorem 4.24
wO(w log(1/²)). By Exercise 3.16, g is (²/4)-concentrated on some
wO(w log(1/²)). And so by Exercise 3.17, f is
(cid:3)

f ≤
2
2 ≤
k

4ˆ
k

g ˆ
k

2
1/²

=
g

| ≤

F

−

≤

k

f

For the interesting case of DNFs of width O(log n) and constant ², we get
concentration on a collection of cardinality O(log n)O(log n)
nO(log log n), nearly
polynomial. Using Proposition 4.9 (and Exercise 3.17) we get the same deduc-
tion for DNFs of size poly(n); more generally, for size s we have ²-concentration
on a collection of cardinality at most (s/²)O(log log(s/²) log(1/²)).

=

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 11 -->
4.5. Highlight: LMN’s work on constant-depth circuits

103

4.5. Highlight: LMN’s work on constant-depth circuits

Having derived strong results about the Fourier spectrum of small DNFs and
CNFs, we will now extend to the case of constant-depth circuits. We begin
by describing how Håstad applied his Switching Lemma to constant-depth
circuits. We then describe some Fourier-theoretic consequences coming from
a very early (1989) work in analysis of Boolean functions by Linial, Mansour,
and Nisan (LMN).

To deﬁne constant-depth circuits it is best to start with a picture. Here is

an example of a depth-3 circuit:

Figure 4.1. Example of a depth-3 circuit, with the layer 0 nodes at the
bottom and the layer 3 node at the top

This circuit computes the function

x1x2

where we suppressed the

(x1x3

x3x4)

(x3x4

x2),

∨

∧

∨

in concatenated literals. To be precise:

∧

∧

−

2, we deﬁne a depth-d circuit over
Deﬁnition 4.26. For an integer d
≥
Boolean variables x1, . . . , xn as follows: It is a directed acyclic graph in which
the nodes (“gates”) are arranged in d
1 layers, with all arcs (“wires”) going
from layer j
[d]. There are exactly 2n nodes in
1 to layer j for some j
layer 0 (the “inputs”) and exactly 1 node in layer d (the “output”). The nodes
in layer 0 are labeled by the 2n literals. The nodes in layers 1, 3, 5, etc. have
, and the nodes in layers 2, 4, 6, etc. have the
the same label, either
∧
1, 1}n
1, 1}: the literals
other label. Each node “computes” a function {
−
compute themselves and the
) nodes compute the logical
(respectively,
∨
AND (respectively, OR) of the functions computed by their incoming nodes.
The circuit itself is said to compute the function computed by its output node.

+
∈

{
−

→

or

∨

∧

In particular, DNFs and CNFs are depth-2 circuits. We extend the deﬁni-

tions of size and width appropriately:

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 12 -->
104

4. DNF formulas and small-depth circuits

Deﬁnition 4.27. The size of a depth-d circuit is deﬁned to be the number of
nodes in layers 1 through d
1. Its width is the maximum in-degree of any
node at layer 1. (As with DNFs and CNFs, we insist that no node at layer 1 is
connected to a variable or its negation more than once.)

−

The layering we assume in our deﬁnition of depth-d circuits can be achieved
with a factor-2d size overhead for any “unbounded fan-in AND/OR/NOT cir-
cuit”. We will not discuss any other type of Boolean circuit in this section.

We now show that Håstad’s Switching Lemma can be usefully applied not

just to DNFs and CNFs but more generally to constant-depth circuits:

1, 1} be computable by a depth-d circuit of

1, 1}n
Lemma 4.28. Let f : {
size s and width w, and let ²

{
−

−

→
(0, 1]. Set
∈
1
10`
z) is a δ-random restriction, Pr[DT( f J

, where `

1
10w

=

=

δ

¶

µ

−

d

2

log(2s/²).

log(2/²)]

z)

|

≥

².

≤

2 case is immediate from Håstad’s Switching Lemma, so we

=

Then if (J

|

Proof. The d
assume d
3.

≥

The ﬁrst important observation is that random restrictions “compose”.
That is, making a δ1-random restriction followed by a δ2-random restriction
to the free coordinates is equivalent to making a δ1δ2-random restriction.
Thus we can think of (J

z) as being produced as follows:

(1) make a 1

|
10w -random restriction;

(2) make d
(3) make a ﬁnal 1

−

3 subsequent 1

10` -random restrictions;

10` -random restriction.

∨

Without loss of generality, assume the nodes at layer 2 of the circuit are
. Thus any node g at layer 2 computes a DNF of width at most w.
labeled
1
10w -random restriction g can
By Håstad’s Switching Lemma, after the initial
be replaced by a decision tree of depth at most ` except with probability at
`. In particular, it can be replaced by a CNF of width at most `, using
most 2−
Proposition 4.5. If we write s2 for the number of nodes at layer 2, a union
bound lets us conclude:

[not all nodes at layer 2 replaceable by width-` CNFs]

Pr
1
10w -random
restriction

2−

`.

s2

·

≤

(4.1)

We now come to the second important observation: If all nodes at layer 2
can be switched to width-` CNFs, then layers 2 and 3 can be “compressed”,
producing a depth-(d
1) circuit of width at most `. More precisely, we can
form an equivalent circuit by shortening all length-2 paths from layer 1 to

−

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 13 -->
4.5. Highlight: LMN’s work on constant-depth circuits

105

layer 3 into single arcs, and then deleting the nodes at layer 2. We give an
illustration of this in Figure 4.2:

Figure 4.2. At top is the initial circuit. Under the restriction ﬁxing x3
=
True, all three DNFs at layer 2 may be replaced by CNFs of width at most 2.
Finally, the nodes at layers 2 and 3 may be compressed.

Assuming the event in (4.1) does not occur, the initial

1
10w -random restric-
1) and width at most `. The
−
-nodes at the new layer 2 is at most s3, the number of nodes at

tion reduces the circuit to having depth-(d
number of
layer 3 in the original circuit.

∧

Next we make a 1

10` -random restriction. As before, by Håstad’s Switching
Lemma this reduces all width-` CNFs at the new layer 2 to depth-` decision
`. We may
trees (hence width-` DNFs), except with probability at most s3
then compress layers and reduce depth again.

2−

·

Proceeding for all

bound gives

1
10` -random restrictions except the ﬁnal one, a union

1

10w ( 1

Pr
10` )d
3
−
restriction

-random

[circuit does not reduce to depth 2 and width `]

s2

·

≤

`
2−

`
2−

s3

·

+

+ · · · +

sd

1

−

·

`
2−

`
2−

s

·

≤

=

²/2.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 14 -->
106

4. DNF formulas and small-depth circuits

Assuming the event above does not occur, Håstad’s Switching Lemma tells us
that the ﬁnal 1
10` -random restriction reduces the circuit to a decision tree of
depth less than log(2/²) except with probability at most ²/2. This completes
(cid:3)
the proof.

We may now obtain the main theorem of Linial, Mansour, and Nisan:

LMN Theorem. Let f : {
1 and let ²
of size s
to degree O(log(s/²))d

1, 1} be computable by a depth-d circuit
(0, 1/2]. Then f ’s Fourier spectrum is ²-concentrated up
∈
1
−

log(1/²).

{
−

→

−

>

1, 1}n

·

Proof. If the circuit for f also had width at most w, we would be able to
deduce 3²-concentration up to degree 30w
log(2/²) by combin-
ing Lemma 4.28 with Lemma 4.21. But if we simply delete all layer-1 nodes
of width at least log(s/²), the resulting circuit computes a function which is
²-close to f , as in the proof of Proposition 4.9. Thus (using Exercise 3.17) f ’s
spectrum is O(²)-concentrated up to degree O(log(2s/²))d
log(2/²), and the
(cid:3)
result follows by adjusting constants.

(10 log(2s/²))d

−

−

1

2

·

·

·

Remark 4.29. Håstad [Hås01a] has slightly sharpened the degree in the
LMN Theorem to O(log(s/²))d

log(1/²).

log(s)

2

−

·

·

In Exercise 4.20 you are asked to use a simpler version of this proof, along

the lines of Theorem 4.20, to show the following:

Theorem 4.30. Let f : {
size s. Then I[ f ]

O(log s)d

−

1, 1}n
1.
−

≤

1, 1} be computable by a depth-d circuit of

{
−

→

These rather strong Fourier concentration results for constant-depth cir-
cuits have several applications. By introducing the Low-Degree Algorithm for
learning, Linial–Mansour–Nisan gave as their main application:

Theorem 4.31. Let C be the class of functions f : {
1, 1} computable
depth-d poly(n)-size circuits. Then C can be learned from random examples
with error any ²

1/poly(n) in time nO(log n)d

1, 1}n

{
−

→

−

.

=

In complexity theory the class of poly-size, constant-depth circuits is re-
ferred to as AC0. Thus the above theorem may be summarized as “AC0 is
learnable in quasipolynomial time”. In fact, under a strong enough assump-
tion about the intractability of factoring certain integers, it is known that
quasipolynomial time is required to learn AC0 circuits, even with query ac-
cess [Kha93].

The original motivation of the line of work leading to Håstad’s Switching
Lemma was to show that the parity function χ[n] cannot be computed in AC0.
Håstad even showed that AC0 cannot even approximately compute parity. We
can derive this result from the LMN Theorem:

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 15 -->
4.6. Exercises and notes

107

Corollary 4.32. Fix any constant ²0
over {
−
2Ω(n1/(d
−

1, 1}n with Prx[C(x)
1)).

χ[n](x)]

=

≥

0. Suppose C is a depth-d circuit
²0. Then the size of C is at least

>
1/2

+

Proof. The hypothesis on C implies
0 in the LMN Theorem.
taking ²

2²2

=

C([n])

2²0. The result then follows by
(cid:3)

≥

b

This corollary is close to being tight, since the parity χ[n] can be com-
puted by a depth-d circuit of size n2n1/(d
2; see Exercise 4.12.
The simpler result Theorem 4.30 is often handier for showing that certain
functions can’t be computed by AC0 circuits. For example, we know that
Θ(pn); hence any constant-depth circuit computing Majn must have
I[Majn]
=
size at least 2nΩ(1)

for any d

≥

.

1)

−

Finally, Linial, Mansour, and Nisan gave an application to cryptography.
1, 1}n
Informally, a function f : {
1, 1} is said to be a “pseudoran-
dom function generator with seed length m” if, for any efﬁcient algorithm A,

1, 1}m

{
−

{
−

→

−

×

1/nω(1).

Pr
1,1}{
−

1,1}n

[A(g)

=

≤

“accept”]
¯
¯
¯
¯

Pr
{
−
∼

s

1,1}m

[A( f (s,

))

“accept”]

·

=

−

g

∼

¯
¯
¯
¯

1,1}n

{
−

1, 1}{
−

{
−
∼
Here the notation A(h) means that A has query access to target function h,
means that g is a uniformly random n-bit function. In
and g
other words, for almost all “seeds” s the function f (s,
1, 1} is
nearly indistinguishable (to efﬁcient algorithms) from a truly random func-
tion. Theorem 4.30 shows that pseudorandom function generators cannot be
computed by AC0 circuits. To see this, consider the algorithm A(h) which
i),
chooses x
and accepts if these values are unequal. If h is a uniformly random function,
A(h) will accept with probability 1/2. In general, A(h) accepts with probability
I[h]/n. Thus Theorem 4.30 implies that if h is computable in AC0 then A(h)
accepts with probability at most polylog(n)/n

[n] uniformly at random, queries h(x) and h(x⊕

1, 1}n and i

1, 1}n

{
−

{
−

1/2.

) : {

→

∼

−

∈

·

¿

4.6. Exercises and notes

4.1 Show that every function f : {0, 1}n

formula of size at most 2n and width at most n.

→

{0, 1} can be represented by a DNF

4.2 Suppose we have a certain CNF computing f : {0, 1}n

{0, 1}. Switch
ANDs with ORs in the CNF. Show that the result is a DNF computing the
Boolean dual f † : {0, 1}n

{0, 1}.

→

4.3 A DNF formula is said to be monotone if its terms contain only unnegated
variables. Show that monotone DNFs compute monotone functions and
that any monotone function can be computed by a monotone DNF, but
that a nonmonotone DNF may compute a monotone function.

→

4.4 Let f : {

1, 1}n

−

1, 1} be computable by a DNF of size s.

{
−

→

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 16 -->
108

4. DNF formulas and small-depth circuits

(a) Show there exists S

[n] with

S

log(s)

O(1) and

(Hint: Use Proposition 4.9 and Exercise 3.30.)

⊆

|

| ≤

+

f (S)

| ≥

|

Ω(1/s).

(b) Let C be the concept class of functions : {

1, 1} computable
by DNF formulas of size at most s. Show that C is learnable using
queries with error 1
Ω(1/s) in time poly(n, s). (Such a result, with
error bounded away from 1

2 , is called weak learning.)

1, 1}n

{
−

2 −

→

−

b

4.5 Verify Proposition 4.12.

4.6 Verify Proposition 4.14.

≤

O

1, 1}n

function f : {
Infi[ f ]

1, 1} that is truly unbiased (E[ f ]

−
log n
n
4.8 Suppose f : {

4.7 For each n that is an input length for Tribesn, show that there exists a
0) and has

{
−
→
for all i
∈
1, 1} is computed by a read-once DNF (mean-
ing no variable is involved in more than one term) in which all terms
k1 exactly. Deduce that ˆ
f ˆ
have width exactly w. Compute ˆ
k
k
2
±
norm Ω(p3/2

k1 =
o(1)) and that there are n-variable width-2 DNFs with Fourier 1-

Tribesn ˆ

1, 1}n
¢

n
log n (1

{
−

[n].

→

=

−

).

¡

n

4.9 Give a direct (Fourier-free) proof of Corollary 4.18. (Hint: Condition on

whether i

J.)

∈

4.10 Tighten the constant factor on log s in Theorem 4.20 as much as you can
(avenues of improvement include the argument in Lemma 4.19, the choice
of δ, and Exercise 4.17).

4.11 Prove Lemma 4.23.

4.12 (a) Show that the parity function χ[n] : {

by a DNF (or a CNF) of size 2n

1.
−

1, 1}n

−

1, 1} can be computed

{
−

→

(b) Show that the bound 2n

1 above is exactly tight. (Hint: Show that
−

every term must have width exactly n.)

(c) Show that there is a depth-3 circuit of size O(n1/2)

computing χ[n].
(Hint: Break up the input into n1/2 blocks of size n1/2 and use (a) twice.
How can you compress the result from depth 4 to depth 3?)
(d) More generally, show there is a depth-d circuit of size O(n1
−

1))
−

1/(d

·

2n1/2

·

2n1/(d

−

1)

computing χ[n].

4.13 In this exercise we deﬁne the most standard class of Boolean circuits. A
(De Morgan) circuit C over Boolean variables x1, . . . , xn is a directed acyclic
graph in which each node (“gate”) is labeled with either an xi or with
,
∧
(logical NOT). Each xi is used as label exactly once; the associated

, or

¬

∨
nodes are called “input” gates and must have in-degree 0. Each
∨
node must have in-degree 2, and each
node must have in-degree 1. Each
node “computes” a Boolean function of the inputs as in Deﬁnition 4.26.
Finally, one node of C is designated as the “output” gate, and C itself is

and

∧

¬

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 17 -->
4.6. Exercises and notes

109

said to compute the function computed by the output node. For this type
of circuit we deﬁne its size, denoted size(C), to be the number of nodes.

Show that each of the following n-input functions can be computed by

De Morgan circuits of size O(n):
(a) The logical AND function.
(b) The parity function.
(c) The complete quadratic function from Exercise 1.1.

4.14 Show that computing Tribesw,s by a CNF formula requires size at least ws.
4.15 Show that there is a universal constant ²0
0 such that the following
4 n-junta g : {
1, 1} is ²0-far from Tribesn (assum-
1). (Hint: Letting J denote the coordinates on which g depends,
4 of the tribes/terms
Ω(1).)
x]
≥
1, 1} is a transitive-

holds: Every 3
ing n
show that if J has non-full intersection with at least 1
then when x

1, 1}J, there is a constant chance that Var[ f

4.16 Using the KKL Theorem, show that if f : {

1, 1}n

{
−

{
−

→

>

−

>

∼

|

symmetric function with Var[ f ]

1, 1}n
−
Ω(1), then I[ f ]

{
−
Ω(log n).

→
≥

≥

4.17 Let f : {True,False}n

{True,False} be computable by a CNF C of width w

→

over variables x1, . . . , xn. In this exercise you will show that I[ f ]

w.

Consider the following algorithm A , which takes as input a permu-
{True,False}n, and which “tries” to output a

Sn and a “seed” r

≤

tation π
string z satisfying C:

∈

∈

A (π, r) :
For i

=

π(1), π(2), . . . , π(n):

If C contains the clause (xi) and the clause (xi), abort.
Else if C contains just the clause (xi), set zi
Else if C contains just the clause (xi), set zi
Else set zi
Syntactically simplify C under the restriction xi

True.
False.
r i and say coordinate i was “unforced”.

=
=

zi.

=

Output z.

=

=

Q

We write F j(π, r) for the 0-1 indicator that coordinate j was forced in the
execution of A (π, r).
(a) Show that if A (π, r) does not abort, then its output z satisﬁes C.
(b) Fix any y satisfying C and write p(y)

and r are uniformly random. Show that p(y)

=

Prπ,r[A (π, r)
n
Eπ[
j

y], where π
F j(π,y)].

=
1(1/2)1

−

=

(c) Deduce 2n p(y)
(d) Suppose further that y⊕
(e) Deduce I[ f ]

w.

P

≥

2

n
j

≤

1 Eπ[F j(π, y)].
=

j does not satisfy C. Show Eπ[F j(π, y)]

1/w.

≥

4.18 Given Boolean variables x1, . . . , xn, a “random monotone term of width w

∈
N+” is deﬁned to be the logical AND of xi1, . . . , xiw , where i1, . . . , iw are
chosen independently and uniformly at random from [n]. (If the i j’s are
not all distinct then the resulting term will in fact have width strictly
less than w.) A “random monotone DNF of width w and size s” is deﬁned

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 18 -->
110

4. DNF formulas and small-depth circuits

to be the logical OR of s independent random monotone terms. For this
exercise we assume n is a sufﬁciently large perfect square, and we let ϕ
be a random monotone DNF of width pn and size 2pn.
(a) Fix an input x

pn, pn].
Let V j be the event that the jth term of ϕ is made 1 (logical False)
by x. Compute Pr[V j] and Pr[ϕ(x)
1], and show that the latter is
9 assuming
at least 10−

1, 1}n and deﬁne u

1 xi)/pn
=

[
−

{
−

2.

P

n
i

=

=

u

∈

∈

(

(b) Let U j be the event that the jth term of ϕ has exactly one 1 on input x.

|

V j]

Ω(w2−

(c) Suppose we condition on ϕ(x)

Show that Pr[U j

w) assuming
jV j. Argue that the events U j
1; i.e.,
are independent. Further, argue that for the U j’s that do occur, the
indices of their uniquely-1 variables are independent and uniformly
random among the 1’s of x.

| ≤

2.

=

∩

≥

u

|

(d) Show that Pr[sensϕ(x)
ciently small constant.

≥

cpn

ϕ(x)

1]

1

−

≥

=

|

10−

10 for c

0 a sufﬁ-

>

|

| ≤

(e) Show that Prx[
1 xi)/pn
=
(f ) Deduce that there exists a monotone function f : {

| ≤

2]

≥

(

|

Ω(1).

n
i

P
with the property that Prx[sens f (x)
constant c0

0.

c0pn]

≥

≥

1, 1}n

1, 1}
c0 for some universal

{
−

→

−

(g) Both Majn and the function f from the previous exercise have average
sensitivity Θ(pn). Contrast the “way” in which this occurs for the two
functions.

>

4.19 In this exercise you will prove the Baby Switching Lemma with constant 3
1 over

Ts be a DNF of width w

1/3, else the theorem is trivial.

≥

in place of 5. Let φ
∨ · · · ∨
variables x1, . . . , xn. We may assume δ
(J
(a) Suppose R

T1

T2

=

∨

≤

|

=

z) is a “bad” restriction, meaning that φJ

z is not a
constant function. Let i be minimal such that (Ti)J
z is neither con-
stantly True or False, and let j be minimal such that x j or x j appears in
this restricted term. Show there is a unique restriction R0
z0)
extending R that doesn’t falsify Ti.

(J\{ j}

=

|

|

|

(b) Suppose we enumerate all bad restrictions R, and for each we write
the associated R0 as in (a). Show that no restriction is written more
than w times.

(c) If (J

|
that Pr[(J

z) is a δ-random restriction and R and R0 are as in (a), show
R0].

z)

R]
=
(d) Complete the proof by showing Pr[(J

δ Pr[(J
−

z)

=

=

|

|

z) is bad]

2δ
1

3δw.

|

≤

4.20 In this exercise you will prove Theorem 4.30. Say that a “(d, w, s0)-circuit”
is a depth-d circuit with width at most w and with at most s0 nodes at
layers 2 through d (i.e., excluding layers 0 and 1).
(a) Show by induction on d

1, 1} computable

2 that any f : {

by a (d, w, s0)-circuit satisﬁes I[ f ]

≥

(b) Deduce Theorem 4.30.

1, 1}n
−
wO(log s0)d

→
2.
−

{
−

≤

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 19 -->
4.6. Exercises and notes

111

Notes. Mansour’s Conjecture dates from 1994 [Man94]. Even the weaker
version would imply that the Kushilevitz–Mansour algorithm learns the class
of poly(n)-size DNF with any constant error, using queries, in time poly(n). In
fact, this learning result was subsequently obtained in a celebrated work of
Jackson [Jac97], using a different method (which begins with Exercise 4.4).
Nevertheless, the Mansour Conjecture remains important for learning theory
since Gopalan, Kalai, and Klivans [GKK08] have shown that it implies the
same learning result in the more challenging and realistic model of “agnostic
learning”. Theorems 4.24 and 4.25 are also due to Mansour [Man95].

The method of random restrictions dates back to Subbotovskaya [Sub61].
Håstad’s Switching Lemma [Hås87] and his Lemma 4.28 are the culmina-
tion of a line of work due to Furst, Saxe, and Sipser [FSS84], Ajtai [Ajt83],
and Yao [Yao85]. Linial, Mansour, and Nisan [LMN89, LMN93] proved
Lemma 4.21, which allowed them to deduce the LMN Theorem and its con-
sequences. An additional cryptographic application of the LMN Theorem
is found in Goldmann and Russell [GR00]. The strongest lower bound cur-
rently known for approximately computing parity in AC0 is due to Impagli-
azzo, Matthews, and Paturi [IMP12] and independently to Håstad [Hås12].

Theorem 4.20 and its generalization Theorem 4.30 are from the work of
Boppana [Bop97]; Linial, Mansour, and Nisan had given the weaker bound
O(log s)d. Exercise 4.17 is due to Amano [Ama11], and Exercise 4.18 is due
to Talagrand [Tal96].

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 20 -->

