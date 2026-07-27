<!-- generated-by: proofmatch local extraction -->
<!-- source-pdf-sha256: 352ab7ff3113b27350fd645bdd03eb022164cc878f8ab7f025811981643322ba -->
<!-- extractor: pdfminer.six v20260107 -->

<!-- pdf-page: 1 -->
Chapter 2

Basic concepts and
social choice

In this chapter we introduce a number of important basic concepts including
inﬂuences and noise stability. Many of these concepts are nicely motivated
using the language of social choice. The chapter is concluded with Kalai’s
Fourier-based proof of Arrow’s Theorem.

2.1. Social choice functions

In this section we describe some rudiments of the mathematics of social choice,
a topic studied by economists, political scientists, mathematicians, and com-
puter scientists. The fundamental question in this area is how best to ag-
gregate the opinions of many agents. Examples where this problem arises
include citizens voting in an election, committees deciding on alternatives,
and independent computational agents making collective decisions. Social
choice theory also provides very appealing interpretations for a number of
important functions and concepts in the analysis of Boolean functions.

A Boolean function f : {

1, 1} can be thought of as a voting rule
{
−
or social choice function for an election with 2 candidates and n voters; it
maps the votes of the voters to the winner of the election. Perhaps the most
familiar voting rule is the majority function:

→

−

1, 1}n

Deﬁnition 2.1. For n odd, the majority function Majn : {
deﬁned by Majn(x)
+
that f is a majority function if f (x) equals the sign of x1
this number is nonzero.)

1, 1} is
−
xn). (Occasionally, for n even we say
xn whenever

sgn(x1

+ · · · +

+ · · · +

{
−

x2

→

=

1, 1}n

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.

43



<!-- pdf-page: 2 -->
44

2. Basic concepts and social choice

The Boolean AND and OR functions correspond to voting rules in which
a certain candidate is always elected unless all voters are unanimously op-
1 represents
posed. Recalling our somewhat nonintuitive convention that
True and

1 represents False:

−

+

Deﬁnition 2.2. The function ANDn : {

1 unless x

+
by ORn(x)

=
= −

1,

(
1, . . . ,
−
−
1 unless x

1, 1}n

{
−
−
1). The function ORn : {
−
(
+
=

1, . . . ,

1).

→

1,

+

+

−

1, 1} is deﬁned by ANDn(x)
=
1, 1} is deﬁned

1, 1}n

{
−

→

Another voting rule commonly encountered in practice:

Deﬁnition 2.3. The ith dictator function χi : {
χi(x)

xi.

−

1, 1}n

1, 1} is deﬁned by

{
−

→

=

Here we are simplifying notation for the singleton monomial from χ{i} to
χi. Even though they are extremely simple functions, the dictators play a very
important role in analysis of Boolean functions; to highlight this we prefer
the colorful terminology “dictator functions” to the more mathematically staid
“projection functions”. Generalizing:

Deﬁnition 2.4. A function f : {
if it depends on at most k of its input coordinates; i.e., f (x)
some g : {
“junta” if it depends on only a “constant” number of coordinates.

N
g(xi1, . . . , xi k ) for
=
[n]. Informally, we say that f is a

1, 1} is called a k-junta for k

1, 1} and i1, . . . , i k

1, 1}n

1, 1}k

{
−

{
−

→

→

−

−

∈

∈

±

For example, the number of functions f : {
is precisely 2n
1.
functions

1, 1}n
1, 1} which are 1-juntas
2: the n dictators, the n negated-dictators, and the 2 constant

{
−

→

−

+

The European Union’s Council of Ministers adopts decisions based on a

weighted majority voting rule:

Deﬁnition 2.5. A function f : {
or (linear) threshold function if it is expressible as f (x)
an xn) for some a0, a1, . . . , an

{
−

R.

→

−

1, 1} is called a weighted majority
sgn(a0

a1x1

+ · · · +

=

+

1, 1}n

∈

Exercise 2.2 has you verify that majority, AND, OR, dictators, and constants
are all linear threshold functions.

The leader of the United States (and many other countries) is elected via
a kind of “two-level majority”. We make a natural deﬁnition along these lines:

d
Deﬁnition 2.6. The depth-d recursive majority of n function, denoted Maj⊗
n ,
1
is the Boolean function of nd bits deﬁned inductively as follows: Maj⊗
n =
d
n (x(n))) for x(i)
Majn, and Maj⊗
n
∈
.
{
−

d
n (x(1)), . . . , Maj⊗

(x(1), . . . , x(n))

Majn(Maj⊗

1, 1}nd

=

(d

1)

+

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 3 -->
2.1. Social choice functions

45

In our last example of a 2-candidate voting rule, the voters are divided into
“tribes” of equal size and the outcome is True if and only if at least one tribe is
unanimously in favor of True. This rule is only somewhat plausible in practice,
but it plays a very important role in the analysis of Boolean functions:

Deﬁnition 2.7. The tribes function of width w and size s, Tribesw,s : {
{
−
where x(i)

1, 1}, is deﬁned by Tribesw,s(x(1), . . . , x(s))

→
ORs(ANDw(x(1)), . . . , ANDw(x(s))),

1, 1}w.

−

=

1, 1}sw

{
−

∈

Here are some natural properties of 2-candidate social choice functions

which may be considered desirable:

•

•

•

•

Deﬁnition 2.8. We say that a function f : {

monotone if f (x)

f (y) whenever x

odd if f (

x)

−

= −

≤
f (x);

1, 1}n

1, 1} is:

{
−

−
→
y coordinate-wise;

≤

unanimous if f (1, . . . , 1)
−
symmetric if f (xπ)
f (x) for all permutations π
from Exercise 1.30); i.e., f (x) only depends on the number of 1’s in x.

Sn (using the notation

1 and f (

1, . . . ,

= −

1)

1;

=

−

=

∈

→

R.

1, 1}n

The deﬁnitions of monotone, odd, and symmetric are also natural for f :
{
−
Example 2.9. The majority function (for n odd) has all four properties in
Deﬁnition 2.8; indeed, May’s Theorem (Exercise 2.3) states that it is the only
monotone, odd, symmetric function. The dictator functions have the ﬁrst
three properties above, as do recursive majority functions. The AND and OR
functions are monotone, unanimous, and symmetric, but not odd. The tribes
functions are monotone and unanimous; although they are not symmetric
they have an important weaker property:

Deﬁnition 2.10. A function f : {
all i, i0
∈
for all x

→
[n] there exists a permutation π

1, 1}n.

−

1, 1}n

∈

1, 1} is transitive-symmetric if for
{
−
Sn taking i to i0 such f (xπ)
f (x)

=

{
−

∈

Intuitively, a function is transitive-symmetric if any two coordinates i, j
are “equivalent”.

∈

[n]

One more natural desirable property of a 2-candidate voting rule is that
1. Of

it be unbiased as deﬁned in Chapter 1.4, i.e., “equally likely” to elect
course, this presupposes the uniform probability distribution on votes.

±

Deﬁnition 2.11. The impartial culture assumption is that the n voters’ pref-
erences are independent and uniformly random.

Although this assumption might seem somewhat unrealistic, it gives a
good basis for comparing voting rules in the absence of other information.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 4 -->
46

2. Basic concepts and social choice

One might also consider it as a model for the votes of just the “undecided” or
“party-independent” voters.

2.2. Inﬂuences and derivatives

Given a voting rule f : {
1, 1} it’s natural to try to measure the
“inﬂuence” or “power” of the ith voter. One can deﬁne this to be the “probability
that the ith vote affects the outcome”.

{
−

→

−

1, 1}n

Deﬁnition 2.12. We say that coordinate i
{
−
string (x1, . . . , xi

1, 1} on input x if f (x)
6=
xi, xi

f (x⊕
1, . . . , xn).
+

1,
−

−

[n] is pivotal for f : {
−
i). Here we have used the notation x⊕

∈

1, 1}n
→
i for the

1, 1}n
Deﬁnition 2.13. The inﬂuence of coordinate i on f : {
ﬁned to be the probability that i is pivotal for a random input:

−

→

1, 1} is de-

{
−

Infi[ f ]

=

x

Pr
{
−
∼

1,1}n

[ f (x)

6=

f (x⊕

i)].

Inﬂuences can be equivalently deﬁned in terms of “geometry” of the Ham-

ming cube:

1, 1}, the inﬂuence Infi[ f ] equals the fraction
Fact 2.14. For f : {
of dimension-i edges in the Hamming cube which are boundary edges. Here
(x, y) is a dimension-i edge if y

i; it is a boundary edge if f (x)

f (y).

{
−

→

−

1, 1}n

x⊕

=

6=

Figure 2.1. Boundary edges of the Maj3 function

=

1. On the other hand, if j

Example 2.15. For the ith dictator function χi we have that coordinate i
is pivotal for every input x; hence Infi[χi]
i
then coordinate j is never pivotal; hence Inf j[χi]
i. Note that
the same two statements are true about the negated-dictator functions. For
1, all inﬂuences are 0. For the ORn function, coordi-
the constant functions
1, 1, 1, . . . , 1) and (1, 1, 1, . . . , 1); hence
nate 1 is pivotal for exactly two inputs, (
−
n. Similarly, Infi[ORn]
21
[n].
Inf1[ORn]
=
=
The Maj3 is depicted in Figure 2.1; the points where it’s
1 are colored gray
1 are colored white. Its boundary edges are high-
and the points where it’s
lighted in black; there are 2 of them in each of the 3 dimensions. Since there

Infi[ANDn]

n for all i

0 for j

21

=

−

+

=

6=

6=

±

∈

−

−

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 5 -->
2.2. Inﬂuences and derivatives

47

are 4 total edges in each dimension, we conclude Infi[Maj3]
i

1/2 for all
[3]. For majority in higher dimensions, Infi[Majn] equals the probability
1 random bits, exactly half of them are 1. This is roughly p2/π
pn

that among n
for large n; see Exercise 2.22 or Chapter 5.2.

2/4

−

=

=

∈

Inﬂuences can also be deﬁned more “analytically” by introducing the de-

rivative operators.

Deﬁnition 2.16. The ith (discrete) derivative operator Di maps the function
f : {

R deﬁned by

1, 1}n

−

→

R to the function Di f : {
f (x(i

1, 1}n
1))

−
7→

→
f (x(i

Di f (x)

=

1))

.

7→−

−
2
(x1, . . . , xi

Here we have used the notation x(i
1, . . . , xn). Notice
7→
+
that Di f (x) does not actually depend on xi. The operator Di is a linear opera-
tor: i.e., Di( f

1, b, xi
−

Di g.

Di f

g)

=

b)

If f : {

−

1, 1} is Boolean-valued then

{
−

→

if coordinate i is not pivotal for x,

1 if coordinate i is pivotal for x.

(2.1)

=

+

+
1, 1}n

Di f (x)

0
= (

±

Thus Di f (x)2 is the 0-1 indicator for whether i is pivotal for x and we con-
E[Di f (x)2]. We take this formula as a deﬁnition for the
clude that Infi[ f ]
inﬂuences of real-valued Boolean functions.

=

Deﬁnition 2.17. We generalize Deﬁnition 2.13 to functions f : {
by deﬁning the inﬂuence of coordinate i on f to be

−

1, 1}n

R

→

Infi[ f ]

=

x

E
1,1}n
{
−
∼

[Di f (x)2]

Deﬁnition 2.18. We say that coordinate i
if and only if Infi[ f ]

0; i.e., f (x(i

1))

∈
f (x(i

7→

7→−

>

6=

= k

Di f

2
2.
k
[n] is relevant for f : {

−
1)) for at least one x

R
→
1, 1}n.

1, 1}n
{
−

∈

The discrete derivative operators are quite analogous to the usual partial
derivatives. For example, f : {
0
for all i and x. Further, Di acts like formal differentiation on Fourier expan-
sions:

R is monotone if and only if Di f (x)

1, 1}n

→

−

≥

Proposition 2.19. Let f : {
f (S) xS. Then

S

[n]

−

1, 1}n

R have the multilinear expansion f (x)

=

→

⊆

P

Di f (x)

=

f (S) xS\{i}.

(2.2)

b

[n]
S
⊆
X
i
S
3
Proof. Since Di is a linear operator, the claim follows immediately from the
observation that

b

Di xS

xS\{i}
= (
0

if i

if i

S,

S.

∈

6∈

(cid:3)

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 6 -->
48

2. Basic concepts and social choice

By applying Parseval’s Theorem to the Fourier expansion (2.2), we obtain

a Fourier formula for inﬂuences:

Theorem 2.20. For f : {

1, 1}n

R and i

−

→
Infi[ f ]

=

[n],
∈
f (S)2.

i
S
3
X
In other words, the inﬂuence of coordinate i on f equals the sum of f ’s
Fourier weights on sets containing i. This is another good example of being
able to “read off ” an interesting combinatorial property of a Boolean function
from its Fourier expansion. In the special case that f : {
1, 1} is
monotone there is a much simpler way to read off its inﬂuences: they are the
f ({i}).
degree-1 Fourier coefﬁcients. In what follows, we write

f (i) in place of

1, 1}n

{
−

→

−

b

Proposition 2.21. If f : {

1, 1}n

−

Proof. By monotonicity, the
indicator that i is pivotal for x. Hence Infi[ f ]
the third equality used Proposition 2.19.

±

{
−

1, 1} is monotone, then Infi[ f ]

→
1 in (2.1) is always 1; i.e., Di f (x) is the 0-1
b
f (i), where
(cid:3)

E[Di f ]

Di f (

)
;

=

=

=

=

f (i).
b

b

This formula allows us a neat proof that for any 2-candidate voting rule
that is monotone and transitive-symmetric, all of the voters have small inﬂu-
ence:

d

b

Proposition 2.22. Let f : {
tone. Then Infi[ f ]

1, 1}n
−
1/pn for all i

≤

→
∈

{
−
[n].

1, 1} be transitive-symmetric and mono-

Proof. Transitive-symmetry of f implies that
(using Exercise 1.30(a)); thus by monotonicity, Infi[ f ]
=
=
f (1)2; hence
b
i
n
∈
1/pn.

[n]. But by Parseval, 1

f (i0) for all i, i0

f (S)2

f (i)2
b

f (i)

f (i)

n
i

=

≥

=

=

b

b

=

S

1

[n]
f (1) for all

∈

b
This bound is slightly improved in Proposition 2.58 and Exercise 2.24.

b

b

P

P

f (1)

≤
(cid:3)

b

The derivative operators are very convenient for functions deﬁned on
1, 1}n. However they are less natural if we think of the Hamming cube
{
−
as {True,False}n; for the more general domains we’ll look at in Chapter 8
they don’t even make sense. We end this section by introducing some useful
deﬁnitions that will generalize better later.

Deﬁnition 2.23. The ith expectation operator Ei is the linear operator on
functions f : {

R deﬁned by

1, 1}n

−

→
Ei f (x)

[ f (x1, . . . , xi

E
xi

1, xi, xi
−

1, . . . , xn)].
+

=

Whereas Di f isolates the part of f depending on the ith coordinate, Ei f
isolates the part not depending on the ith coordinate. Exercise 2.15 asks you
to verify the following:

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 7 -->
2.3. Total inﬂuence

49

R,

1, 1}n
1))

7→−

−
f (x(i

→

,

Proposition 2.24. For f : {

f (x(i

1))

7→

+
2
f (S) xS,

Ei f (x)

=

Ei f (x)

f (x)

=

•

•

•

=

i
S
63
X
xiDi f (x)

b

Ei f (x).

+

Note that in the decomposition f

Ei f , neither Di f nor Ei f de-
=
pends on xi. This decomposition is very useful for proving facts about Boolean
functions by induction on n.

xiDi f

+

Finally, we will also deﬁne an operator very similar to Di called the ith

Laplacian:

Deﬁnition 2.25. The ith coordinate Laplacian operator Li is deﬁned by

=
Notational warning: Elsewhere you might see the negated deﬁnition, Ei f

−

Li f

f

Ei f .

f .

−

Exercise 2.16 asks you to verify the following:

1, 1}n

R,

→

Proposition 2.26. For f : {
i)

f (x)

−

Li f (x)

f (x⊕
−
2

,

•

•

=

=

Li f (x)

xiDi f (x)

f (S) xS,

f , Li f

• 〈

〉 = 〈

=
Li f , Li f

i
S
3
X
Infi[ f ].
b
〉 =

2.3. Total inﬂuence

A very important quantity in the analysis of a Boolean function is the sum of
its inﬂuences.

Deﬁnition 2.27. The total inﬂuence of f : {

1, 1}n

R is deﬁned to be

→

−

n

Infi[ f ].

I[ f ]

=

i
1
=
X
For Boolean-valued functions f : {

1, 1}n

1, 1} the total inﬂuence has
−
several additional interpretations. First, it is often referred to as the average
sensitivity of f because of the following proposition:

{
−

→

Proposition 2.28. For f : {

1, 1}n

−

I[ f ]

→
E
x

=

1, 1}

{
−
[sens f (x)],

where sens f (x) is the sensitivity of f at x, deﬁned to be the number of pivotal
coordinates for f on input x.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 8 -->
50

2. Basic concepts and social choice

Proof.

I[ f ]

n

=

i
1
=
X

Infi[ f ]

n

=

i
1
=
X
n

[ f (x)

Pr
x

6=

f (x⊕

i)]

E
x

[1 f (x)
6=

i)]

f (x⊕

E
x "

=

=

i
1
=
X

1, 1}n

−

{
−

→

n

i
1
=
X

1 f (x)

f (x⊕

i)

6=

# =

[sens f (x)]. (cid:3)

E
x

The total inﬂuence of f : {

1, 1} is also closely related to the size

of its edge boundary; from Fact 2.14 we deduce:

Fact 2.29. The fraction of edges in the Hamming cube {
boundary edges for f : {

1, 1} is equal to 1

1, 1}n

−

n I[ f ].

−

{
−

→

1, 1}n which are

→

1, 1}n

Example 2.30. (Recall Example 2.15.) For Boolean-valued functions f :
1, 1} the total inﬂuence ranges between 0 and n. It is minimized
{
{
−
−
by the constant functions
1 which have total inﬂuence 0. It is maximized by
the parity function χ[n] and its negation which have total inﬂuence n; every
coordinate is pivotal on every input for these functions. The dictator functions
(and their negations) have total inﬂuence 1. The total inﬂuence of ORn and
n. On the other hand, the total inﬂuence of Majn is
ANDn is very small: n21
fairly large: roughly p2/πpn for large n.

±

−

By virtue of Proposition 2.21 we have another interpretation for the total

inﬂuence of monotone functions:

Proposition 2.31. If f : {

1, 1}n

−

{
−

→

1, 1} is monotone, then

n

I[ f ]

=

i
1
=
X

f (i).

b

This sum of the degree-1 Fourier coefﬁcients has a natural interpretation

in social choice:

Proposition 2.32. Let f : {
election. Given votes x
with the outcome of the election, f (x). Then
n

→

=

1, 1}n

1, 1} be a voting rule for a 2-candidate
(x1, . . . , xn), let w be the number of votes that agree

{
−

−

E[w]

=

n
2 +

1
2

f (i).

i
1
=
X

b
Proof. By the formula for Fourier coefﬁcients,
n

n

f (i)

=

[ f (x)xi]

E
x

E
x

=

[ f (x)(x1

x2

xn)].

(2.3)

+

+ · · · +

b

i
1
=
X

+ · · · +

i
1
=
X
xn equals the difference between the number of votes for can-
Now x1
xn)
didate 1 and the number of votes for candidate
equals the difference between the number of votes for the winner and the
n. The result follows. (cid:3)
(n
number of votes for the loser; i.e., w

1. Hence f (x)(x1

+ · · · +

2w

w)

−

−

−

=

−

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 9 -->
b

x1

2.3. Total inﬂuence

51

Rousseau [Rou62] suggested that the ideal voting rule is one which max-
imizes the number of votes that agree with the outcome. Here we show that
the majority rule has this property (at least when n is odd):

Theorem 2.33. The unique maximizers of
{
−
O(n−

1/2) for all monotone f .

1, 1} are the majority functions. In particular, I[ f ]

P

=

1

n
i

f (i) among all f : {

I[Majn]

≤

=

1, 1}n
−
p2/πpn

→
+

Proof. From (2.3),

n

f (i)

[ f (x)(x1

x2

E
x

=

+

+ · · · +

xn)]

[
E
|
x

≤

x2

+

+ · · · +

xn

],

|

i
1
=
X
1, 1} always. Equality holds if and only if f (x)
since f (x)
{
b
−
∈
whenever x1
+ · · · +
Proposition 2.31 and Exercise 2.22.

xn)
0. The second statement of the theorem follows from
(cid:3)

sgn(x1

+ · · · +

xn

=

6=

Let’s now take a look at more analytic expressions for the total inﬂuence.

By deﬁnition, if f : {

1, 1}n

R, then

−
n

→

n

I[ f ]

=

Infi[ f ]

=

[Di f (x)2]

E
x

i
1
=
X
This motivates the following deﬁnition:

i
1
=
X

E
x "

=

n

i
1
=
X

Di f (x)2

.

#

(2.4)

Deﬁnition 2.34. The (discrete) gradient operator
{
−

R to the function

1, 1}n

1, 1}n

f : {

→

Rn deﬁned by

∇

−

∇
→
(D1 f (x), D2 f (x), . . . , Dn f (x)).

maps the function f :

Note that for f : {

1, 1} we have

is the usual Euclidean norm in Rn. In general, from (2.4) we deduce:

f (x)
k

2
2 =

k∇

sens f (x), where

2
k·k

Proposition 2.35. For f : {

1, 1}n

R,

−

I[ f ]

→
[
E
x

=

2
f (x)
2].
k

k∇

An alternative analytic deﬁnition involves introducing the Laplacian:

Deﬁnition 2.36. The Laplacian operator L is the linear operator on functions
f : {

R deﬁned by L

1, 1}n

−

→

Exercise 2.17 asks you to verify the following:

P

f (x)

=
1, 1}n

∇

−

{
−

→

n
i

1 Li.
=

=

1, 1}n

{ f (x⊕

R,

,

→
i)}

if f : {

¢
1, 1}n
−

1, 1},

{
−

→

Proposition 2.37. For f : {

−

f (x)

−
avg
i
[n]
∈
¡
sens f (x)
·
f (S) χS,

•

•

•

L f (x)

L f (x)

(n/2)

f (x)

=

=

L f

=

[n] |
S
⊆
X

S

|

b

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 10 -->
52

2. Basic concepts and social choice

f , L f

I[ f ].

〉 =

• 〈
We can obtain a Fourier formula for the total inﬂuence of a function using
[n] the Fourier weight

Theorem 2.20; when we sum that theorem over all i
f (S)2 is counted exactly
S
|
1, 1}n

times. Hence:
R,

Theorem 2.38. For f : {
b

→

−

|

∈

I[ f ]

S

f (S)2

Wk[ f ].

(2.5)

=

[n] |
S
⊆
X

|

k
0
=
X
1, 1} we can express this using the spectral sample:

b

=

n

k

·

For f : {

1, 1}n

−

{
−

→

∼
1, 1}n
Thus the total inﬂuence of f : {
“height” or degree of its Fourier weights.

−

I[ f ]

E
S f

=

S

].

S

[
|

|

1, 1} also measures the average

{
−

→

Finally, from Proposition 1.13 we have Var[ f ]

0 Wk[ f ]; comparing
>
this with (2.5) we immediately deduce a simple but important fact called the
Poincaré Inequality.

P

=

k

Poincaré Inequality. For any f : {

1, 1}n

R, Var[ f ]

I[ f ].

≤

→

−

Equality holds in the Poincaré Inequality if and only if all of f ’s Fourier
1[ f ]
E[ f 2]. For Boolean-valued f :
χi

1, 1}, Exercise 1.19 tells us this can only occur if f

weight is at degrees 0 and 1; i.e., W≤
1, 1}n
{
{
−
→
−
for some i.

1 or f

= ±

= ±

=

−

→

1, 1}n

For Boolean-valued f : {

R, the Poincaré Inequality can be viewed
as an (edge-)isoperimetric inequality, or (edge-)expansion bound, for the Ham-
1, 1}n
ming cube. If we think of f as the indicator function for a set A
α) (Fact 1.14) whereas I[ f ] is n
of “measure” α
=
times the (fractional) size of A’s edge boundary. In particular, the Poincaré
1, 1}n of measure α
Inequality says that subsets A
1/2 must have edge
boundary at least as large as those of the dictator sets.

/2n, then Var[ f ]

4α(1

{
−

{
−

= |

⊆

⊆

−

=

A

|

For α

{0, 1/2, 1} the Poincaré Inequality is not sharp as an edge-isoperimetric

∉

inequality for the Hamming cube; for small α even the asymptotic depen-
dence is not optimal. Precisely optimal edge-isoperimetric results (and also
vertex-isoperimetric results) are known for the Hamming cube. The following
simpliﬁed theorem is optimal for α of the form 2−

i:

Theorem 2.39. For f : {

1, 1}n

−

→

{
−
2α log(1/α)

I[ f ].

≤

1, 1} with α

min{Pr[ f

1], Pr[ f

1]},

= −

=

=

This result illustrates an important recurring concept in the analysis of
Boolean functions: The Hamming cube is a “small-set expander”. Roughly
1, 1}n have unusually
speaking, this is the idea that “small” subsets A
large “boundary size”.

{
−

⊆

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 11 -->
2.4. Noise stability

53

2.4. Noise stability

1, 1}n

−

→

{
−

Suppose f : {
1, 1} is a voting rule for a 2-candidate election. Mak-
ing the impartial culture assumption, the n voters independently and uni-
formly randomly choose their votes x
(x1, . . . , xn). Now imagine that when
=
each voter goes to the ballot box there is some chance that their vote is mis-
recorded. Speciﬁcally, say that each vote is correctly recorded with probability
[0, 1] and is garbled – i.e., changed to a random bit – with probability
ρ
(y1, . . . , yn) for the votes that are ﬁnally recorded, we may
ρ. Writing y
1
=
ask about the probability that f (x)
f (y), i.e., whether the misrecorded votes
affected the outcome of the election. This has to do with the noise stability
of f .

∈
−

=

Deﬁnition 2.40. Let ρ
denote that the random string y is drawn as follows: for each i
dently,

[0, 1]. For ﬁxed x

{
−

∈

∈

1, 1}n we write y

∈

Nρ(x) to
[n] indepen-

∼

yi = (
We extend the notation to all ρ

xi
uniformly random with probability 1

with probability ρ,

ρ.

−

[
−

1, 1] as follows:

∈
with probability 1
xi with probability 1

1
2 ρ,
1
2 ρ.

2 +
2 −

yi = (

xi

−

We say that y is ρ-correlated to x.

∼

∼

{
−

1, 1}n is drawn uniformly at random and then
Deﬁnition 2.41. If x
Nρ(x), we say that (x, y) is a ρ-correlated pair of random strings. This def-
y
inition is symmetric in x and y; it is equivalent to saying that independently
for each i
0 and
E[xi yi]

[n], the pair of random bits (xi, yi) satisﬁes E[xi]

E[yi]

∈
ρ.

=

=

=

With these deﬁnitions in hand we can now deﬁne the important concept
of noise stability, which measures the correlation between f (x) and f (y) when
(x, y) is a ρ-correlated pair.

Deﬁnition 2.42. For f : {
ρ is

−

1, 1}n

Stabρ[ f ]

→

=

R and ρ

∈

1, 1], the noise stability of f at

[
−

[ f (x) f (y)].

E
(x,y)
ρ-correlated

If f : {

1, 1} we have

−

1, 1}n

{
→
−
Stabρ[ f ]

=

Pr
(x,y)
ρ-correlated

[ f (x)

=

f (y)]

−

Pr
(x,y)
ρ-correlated

[ f (x)

6=

f (y)]

2

=

Pr
(x,y)
ρ-correlated

[ f (x)

f (y)]

1.

−

=

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 12 -->
54

2. Basic concepts and social choice

In the voting scenario described above, the probability that the misrecord-

ing of votes doesn’t affect the election outcome is 1

1
2 Stabρ[ f ].

2 +

When ρ is close to 1 (i.e., the “noise” is small) it’s sometimes more natu-
ral to ask about the probability that reversing a small fraction of the votes
reverses the outcome of the election.

[0, 1] we write NSδ[ f ] for
f (y) when
1, 1}n is uniformly random and y is formed from x by reversing each bit

Deﬁnition 2.43. For f : {
noise sensitivity of f at δ, deﬁned to be the probability that f (x)
x
independently with probability δ. In other words,

1, 1} and δ

{
−

{
−

→

∼

−

6=

∈

1, 1}n

NSδ[ f ]

1
2 −

1
2

=

Stab1

2δ[ f ].
−

Example 2.44. The constant functions
ery ρ. The dictator functions χi satisfy Stabρ[χi]
NSδ[χi]

δ for all δ). More generally,

±

=

1 have noise stability 1 for ev-
ρ for all ρ (equivalently,

=

Stabρ[χS]

=

[xS yS]

E
(x,y)
ρ-correlated

E

=

"

S
i
∈
Y

(xi yi)

# =

S
i
∈
Y

E[xi yi]

S

|,

ρ|

ρ

=

=

S
i
∈
Y

where we used the fact that the bit pairs (xi, yi) are independent across i to
convert the expectation of a product to a product of an expectation.

There is no convenient expression for the noise stability of the major-
ity function Stabρ[Majn]. However, for a ﬁxed noise rate, the noise stabil-
ity/sensitivity tends to a nice limit as n

:
→ ∞

Theorem 2.45. For any ρ

1, 1],

[
−

∈

lim
n
→∞n odd

Stabρ[Majn]

2
π arcsin ρ

1

−

=

=

2
π arccos ρ.

Equivalently, for δ

[0, 1],

∈

lim
n
→∞n odd

NSδ[Majn]

1
π arccos(1

2δ).

−

=

Using cos(z)

1

−

=

1

2 z2

+

O(z4), hence arccos(1

2δ)

−

=

2pδ

+

O(δ3/2), we deduce

lim
n
→∞n odd

NSδ[Majn]

pδ

2
π

+

=

O(δ3/2).

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 13 -->
2.4. Noise stability

55

Figure 2.2. Plot of 2

π arcsin ρ as a function of ρ

We prove Theorem 2.45 in Chapter 5.2.

There is a simple Fourier formula for the noise stability of a Boolean
function; it’s one of the most powerful links between the combinatorics of
Boolean functions and their Fourier spectra. To determine it, we begin by
introducing the most important operator in analysis of Boolean functions: the
noise operator, denoted Tρ for historical reasons.

Deﬁnition 2.46. For ρ
linear operator Tρ on functions f : {

1, 1], the noise operator with parameter ρ is the
R deﬁned by

1, 1}n

[
−

∈

Tρ f (x)

Proposition 2.47. For f : {
by

−

1, 1}n

=

→

−

→
[ f (y)].

E
Nρ(x)

y
∼
R, the Fourier expansion of Tρ f is given

S

ρ|

f (S) χS

|

Tρ f

=

[n]

S
⊆
X

b

ρk f =

k.

n

=

k
0
=
X

Proof. Since Tρ is a linear operator, it sufﬁces to verify that TρχS

S

ρ|

|χS:

TρχS(x)

[yS]

E
Nρ(x)

=

=

y

S
i
∈
Y
Here we used the fact that for y
ρxi.
satisfy E[yi]

∼

∼

=

=
|χS(x).

S

ρ|

E
Nρ(x)

[yi]

=

y

(ρxi)

=

S
i
∈
Y

∼
Nρ(x) the bits yi are independent and
(cid:3)

Exercise 2.25 gives an alternate way of looking at this proof. Yet another proof
using probability densities and convolution is outlined in Exercise 2.30.

The connection between Tρ and noise stability is that

Stabρ[ f ]

=

E
1,1}n
x
{
−
∼
Nρ(x)
y
∼

[ f (x) f (y)]

E
x

=

·

f (x) E
y

Nρ(x)

∼

[ f (y)]

;

¸

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 14 -->
56

hence:

2. Basic concepts and social choice

Fact 2.48. Stabρ[ f ]

f , Tρ f

.

〉

= 〈

From Plancherel’s Theorem and Proposition 2.47 we deduce the Fourier

formula for noise stability:

Theorem 2.49. For f : {

1, 1}n

−

Stabρ[ f ]

R,

→

S

|

ρ|

f (S)2

=

[n]

S
⊆
X
1, 1} we have

b

n

=

k
0
=
X

Wk[ f ].

ρk

·

Hence for f : {

1, 1}n

−

{
−

→

Stabρ[ f ]

NSδ[ f ]

1
2

=

n

(1
k
0
=
X

[ρ|

S

|],

=

S

E
S f

∼

(1

−

−

2δ)k)

·

Wk[ f ].

(2.6)

(2.7)

Thus the noise stability of f at ρ is equal to the sum of its Fourier weights,
attenuated by a factor which decreases exponentially with degree. A simple
but important corollary is that dictators (and their negations) maximize noise
stability:

Proposition 2.50. Let ρ
Stabρ[ f ]

(0, 1). If f : {
∈
ρ, with equality if and only if f

1, 1}n

{
−
χi for some i

→

−
= ±

[n].

1, 1} is unbiased, then

≤

Proof. For unbiased f we have W0[ f ]
Since ρk
weight is on degree 1. This occurs if and only if f

∈
1 ρkWk[ f ].
0 and hence Stabρ[ f ]
≥
1, noise stability is maximized if all of f ’s Fourier
χi, by Exercise 1.19(a).
(cid:3)

ρ for all k

= ±

P

>

<

=

=

k

For a ﬁxed function f , it’s often interesting to see how Stabρ[ f ] varies
as a function of ρ. From Theorem 2.49 we see that Stabρ[ f ] is a (univari-
ate) polynomial with nonnegative coefﬁcients; in particular, it’s an increasing
function of ρ on [0, 1]. The derivatives of this polynomial at 0 and 1 have nice
interpretations, as can be immediately deduced from Theorem 2.49:

Proposition 2.51. For f : {

1, 1}n

R,

→

Stabρ[ f ]

Stabρ[ f ]

−
d
dρ
d
dρ

W1[ f ],

I[ f ].

ρ

ρ

0 =

=

1 =

=

¯
¯
¯

¯
¯
¯

1, 1}n

For f : {
[0, 1/2], and the second identity is equivalent to

{
−

→

−

1, 1} we have that NSδ[ f ] is an increasing function of δ on

d
dδ

NSδ[ f ]

I[ f ].

0=

δ

=

¯
¯
Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.
¯



<!-- pdf-page: 15 -->
2.5. Highlight: Arrow’s Theorem

57

We conclude this section by introducing a version of inﬂuences that also

incorporates noise.

Deﬁnition 2.52. For f : {
ence of i on f is

−

1, 1}n

R, ρ

∈

→

[0, 1] and i

∈

[n], the ρ-stable inﬂu-

Inf(ρ)
i

[ f ]

=

Stabρ[Di f ]

=

i
S
3
X
with 00 interpreted as 1. We also deﬁne I(ρ)[ f ]

S

ρ|

1

|−

f (S)2,

b
1 Inf(ρ)

i

n
i

=

[ f ].

=

P
Exercise 2.40 asks you to verify the following:

Fact 2.53. I(ρ)[ f ]

d
dρ Stabρ[ f ]

=

=

n
k

1 kρk

=

Wk[ f ].

1

−

·

P
[ f ] increases from

The ρ-stable inﬂuence Inf(ρ)
f (i)2 up to Infi[ f ] as ρ
i
1 there isn’t an especially natural combi-
increases from 0 to 1. For 0
ρ
<
<
natorial interpretation for Inf(ρ)
b
[ f ] beyond Stabρ[Di f ]; however, we will see
i
later that the stable inﬂuences are technically very useful. One reason for
this is that every function f : {
1, 1} has at most “constantly” many
−
“stably-inﬂuential” coordinates:

1, 1}n

{
−

→

Proposition 2.54. Suppose f : {
[n] : Inf(1
let J
i

[ f ]

{i

δ)

−

²}. Then

−

1, 1}n
J

=

∈

→
| ≤

|

≥

R has Var[ f ]
1
δ² .

≤

1. Given 0

δ, ²

1,

≤

<

J

Proof. Certainly
paring Fact 2.53 with Var[ f ]
1k
1/δ for all k
that (1
−

δ)k

| ≤

δ)[ f ]/² so it remains to verify I(1
I(1
−

1/δ. Com-
0 Wk[ f ] term by term, it sufﬁces to show
6=
(cid:3)

1. This is the easy Exercise 2.45.
P

≤

δ)[ f ]
−

k

|

=
≥

≤

−

It’s good to think of the set J in this proposition as the “notable” coor-
dinates for function f . Had we used the usual inﬂuences in place of stable
inﬂuences, we would not have been guaranteed a bounded number of “notable”
coordinates (since, e.g., the parity function χ[n] has all n of its inﬂuences equal
to 1).

2.5. Highlight: Arrow’s Theorem

When there are just 2 candidates, the majority function possesses all of the
mathematical properties that seem desirable in a voting rule (e.g., May’s
Theorem and Theorem 2.33). Unfortunately, as soon as there are 3 (or more)
candidates the problem of social choice becomes much more difﬁcult. For
example, suppose we have candidates a, b, and c, and each of n voters has
a ranking of them. How should we aggregate these preferences to produce a
winning candidate?

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 16 -->
58

2. Basic concepts and social choice

In his 1785 Essay on the Application of Analysis to the Probability of Ma-
jority Decisions [dC85], Condorcet suggested using the voters’ preferences to
conduct the three possible pairwise elections, a vs. b, b vs. c, and c vs. a. This
calls for the use of a 2-candidate voting rule f : {
1, 1}; Condorcet
suggested f
Majn but we might consider any such rule. Thus a “3-candidate
Condorcet election” using f is conducted as follows:

1, 1}n

{
−

→

=

−

−

1) vs. b (
a (
+
b (
1) vs. c (
+
1) vs. a (
c (
−
+

−

1)

1)

1)

Voters’ Preferences
#3
1
1
1

· · ·
· · · =
· · · =
· · · =

#2
1
1
1

−
+
+

+
−
−

#1
1
1
1

+
+
−

Societal Aggregation
f (x)
f (y)
f (z)

x
y
z

In the above example, voter #1 ranked the candidates a

c, voter #2
>
b, voter #3 ranked them b
a, etc. Note that the ith
c
>
6 possible rankings, and these translate into a triple of

>

>

b

ranked them a
c
voter has one of 3!
bits (xi, yi, zi) from the following set:

>
=

>

(

1,

+

+

1,

−

1), (

1,

1,

1), (

1,

1,

1), (

1,

1,

1), (

1,

1,

1), (

1,

1,

1)

.

+

−

−

−

+

−

−

+

+

+

−

+

−

−

+

n
These are precisely the triples satisfying the not-all-equal predicate NAE3
(see Exercise 1.1(i)).

o

In the example above, if n
1,

Maj3 then the societal outcome
1), meaning that society elects a over b, b over c, and

would be (
a over c. In this case it is only natural to declare a the overall winner.

3 and f

1,

−

=

=

+

+

Deﬁnition 2.55. In an election employing Condorcet’s method with voting
1, 1}, we say that a candidate is a Condorcet winner if it
rule f : {
wins all of the pairwise elections in which it participates.

1, 1}n

{
−

→

−

Unfortunately, as Condorcet himself noted, there may not be a Condorcet
b
winner. In the example above, if voter #2’s ranking was instead c
1)), we would obtain the “paradoxical” outcome
(corresponding to (
1): society prefers a over b, b over c, and c over a! This lack of a
(
+
Condorcet winner is termed Condorcet’s Paradox; it occurs when the outcome
( f (x), f (y), f (z)) is one of the two “all-equal” triples {(
1)}.

1), (

1,

1,

1,

1,

1,

1,

1,

1,

+

+

−

+

>

>

+

a

−

−

−

+

+

+

One might wonder if the Condorcet Paradox can be avoided by using a
voting rule f : {
1, 1} other than majority. However, in 1950 Ar-
row [Arr50] famously showed that the only means of avoidance is an unap-
pealing one:

1, 1}n

{
−

→

−

1, 1}n
Arrow’s Theorem. Suppose f : {
1, 1} is a unanimous voting rule
used in a 3-candidate Condorcet election. If there is always a Condorcet winner,
then f must be a dictatorship.

{
−

→

−

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 17 -->
2.5. Highlight: Arrow’s Theorem

59

(In fact, Arrow’s Theorem is slightly stronger than this; see Exercise 2.51.)

In 2002 Kalai gave a new proof of Arrow’s Theorem; it takes its cue from
the title of Condorcet’s work and computes the probability of a Condorcet
winner. This is done under the “impartial culture assumption” for 3-candidate
elections: each voter independently chooses one of the 6 possible rankings
uniformly at random.

→
1, 1}. Under the impartial culture assumption, the probability of a Condorcet

Theorem 2.56. Consider a 3-candidate Condorcet election using f : {
{
−
winner is precisely 3

−

1, 1}n

3
1/3[ f ].
4 Stab
−

∈

1, 1}n be the votes for the elections a vs. b, b vs. c, and
Proof. Let x, y, z
c vs. a, respectively. Under impartial culture, the bit triples (xi, yi, zi) are
independent and each is drawn uniformly from the 6 triples satisfying the
not-all-equal predicate NAE3 : {
{0, 1}. There is a Condorcet winner if
−
and only if NAE3( f (x), f (y), f (z))

→
1. Hence

1, 1}3

4 −
{
−

=

Pr[

∃

Condorcet winner]

=

E[NAE3( f (x), f (y), f (z))].

(2.8)

The multilinear (Fourier) expansion of NAE3 is
1
4 w1w3

NAE3(w1, w2, w3)

1
4 w1w2

3
4 −

=

−

1
4 w2w3;

−

thus

(2.8)

3
4 −

=

1
4 E[ f (x) f (y)]

1
4 E[ f (x) f (z)]

1
4 E[ f (y) f (z)].

−

−

In the joint distribution of x, y the n bit pairs (xi, yi) are independent. Further,
by inspection we see that E[xi]
E[yi]
(4/6)(
1)
have E[ f (x) f (z)]

+
1/3[ f ]. Similarly we
−
(cid:3)
1/3[ f ] and the proof is complete.
−

=
1/3. Hence E[ f (x) f (y)] is precisely Stab

0 and that E[xi yi]

E[ f (y) f (z)]

(2/6)(

Stab

= −

1)

+

=

−

=

=

=

Arrow’s Theorem is now an easy corollary:

Proof of Arrow’s Theorem. By assumption, the probability of a Condorcet
winner is 1; hence

1

=

3
4 −

3
4 Stab

1/3[ f ]
−

=

3
4 −

3
4

1/3)kWk[ f ].

−

n

(
k
0
=
X

1/3)k

−

≥ −

1/3 for all k, the equality above can only occur if all of f ’s
Since (
Fourier weight is on degree 1; i.e., W1[ f ]
1. By Exercise 1.19(a) this implies
that f is either a dictator or a negated-dictator. Since f is unanimous, it must
(cid:3)
in fact be a dictator.

=

An advantage of Kalai’s analytic proof of Arrow’s Theorem is that we can
deduce several more interesting results about the probability of a Condorcet
winner. For example, combining Theorem 2.56 with Theorem 2.45 we get
Guilbaud’s Formula:

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 18 -->
60

2. Basic concepts and social choice

Guilbaud’s Formula. In a 3-candidate Condorcet election using Majn, the
probability of a Condorcet winner tends to

3
2π arccos(

1/3)

91.2%.

≈

−

as n

.
→ ∞
This is already a fairly high probability. Unfortunately, if we want to
improve on it while still using a reasonably fair election scheme, we can only
set our hopes higher by a sliver:

1, 1}n

≈

−

on(1)

1, 1} with all

Theorem 2.57. In a 3-candidate Condorcet election using an f : {
{
−
7
9 +

→
f (i) equal, the probability of a Condorcet winner is at most
91.9%.
b

4
9π +
The condition in Theorem 2.57 seems like it would be satisﬁed by most
1, 1}n
reasonably fair voting rules f : {
1, 1} (e.g., it is satisﬁed if f is
transitive-symmetric or is monotone with all inﬂuences equal). In fact, we will
show that Theorem 2.57’s hypothesis can be relaxed in Chapter 5.4; we will
4
further show in Chapter 11.7 that 7
9π can be improved to the tight value
3
1/3) of majority. To return to Theorem 2.57, it is an immediate
2π arccos(
consequence of the following two results, the ﬁrst being Exercise 2.24 and the
second being an easy corollary of Theorem 2.56.

{
−

9 +

→

−

−

Proposition 2.58. Suppose f : {
W1[ f ]
on(1).

2/π

−

≤

+

1, 1}n

1, 1} has all

{
−

→

f (i) equal. Then

b

1, 1}n

−

2

1, 1}, the probability of a Condorcet winner is at most 7

Corollary 2.59. In a 3-candidate Condorcet election using f : {
9 W1[ f ].
{
−
Proof. From Theorem 2.56, the probability is
3 W1[ f ]
−
36 W3[ f ]
+
36 (W3[ f ]
1
36 (1

4 (W0[ f ]
4 W1[ f ]
4 W1[ f ]
4 W1[ f ]

9 W2[ f ]
−
324 W5[ f ]
W5[ f ]

+
W1[ f ])

27 W3[ f ]

1/3[ f ]
−

3
4 Stab

+ · · ·
)

3
4 −

9 +

≤

≤

+

=

+

+

1

1

1

3

1

1

1

2

1

1

1

3
4 −
3
4 +
3
4 +
3
4 +

+ · · ·
7
9 +

=

+

−

≤

9 W1[ f ].

)

+ · · ·

→

(cid:3)

Finally, using Corollary 2.59 we can prove a “robust” version of Arrow’s
Theorem, showing that a Condorcet election is almost paradox-free only if it
is almost a dictatorship (possibly negated).

Corollary 2.60. Suppose that in a 3-candidate Condorcet election using f :
1, 1}n
². Then f is
{
{
−
−
O(²)-close to

1, 1}, the probability of a Condorcet winner is 1

χi for some i

[n].

→

−

±

∈

Proof. From Corollary 2.59 we obtain that W1[ f ]
now follows from the FKN Theorem.

1

−

≥

9
2 ². The conclusion
(cid:3)

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 19 -->
2.6. Exercises and notes

61

Friedgut–Kalai–Naor (FKN) Theorem. Suppose f : {
W1[ f ]
[n].

δ. Then f is O(δ)-close to

χi for some i

1

−

±

∈

≥

−

1, 1}n

1, 1} has

{
−

→

We will see the proof of the FKN Theorem in Chapter 9.1. We’ll also show
O(δ2 log(2/δ)).

in Chapter 5.4 that the O(δ) closeness can be improved to δ/4

+

2.6. Exercises and notes

2.1 For each function in Exercise 1.1, determine if it is odd, transitive-symmetric,

and/or symmetric.

2.2 Show that the n-bit functions majority, AND, OR,

linear threshold functions.

χi, and

±

1 are all

±

2.3 Prove May’s Theorem:
(a) Show that f : {

1, 1}n

{
−
if it can be expressed as a weighted majority with a1
1.

→

−

1, 1} is symmetric and monotone if and only

a2

=

= · · · =

an

=

(b) Suppose f : {

1, 1}n

−

{
−

→

that n must be odd, and that f

Majn.

=

1, 1} is symmetric, monotone, and odd. Show

2.4 Subset A

∈

−

⊆

=

{
−

{
−

a1x1

1, 1}n

{x : ∆(x, z)

sgn(a0
+
1, 1}n

1, 1}n and real r. Show that f : {

1, 1}n is called a Hamming ball if A
r} for some
=
<
z
1, 1} is the indicator of a
{
−
Hamming ball if and only if it’s expressible as a linear threshold function
f (x)

+ · · · +
[n]. We say that f is unate in the ith direc-
1, 1} and i
∈
f (x(i
1))
1)) for all x (monotone in the ith direction)
7→
1)) for all x (antimonotone in the ith direction). We

{
−
→
−
tion if either f (x(i
7→−
f (x(i
or f (x(i
say that f is unate if it is unate in all n directions.
(a) Show that

Infi[ f ] with equality if and only if f is unate in the

an xn) with

| = · · · = |

| = |

f (i)

1))

an

a1

a2

→

7→−

≤

≥

7→

.

|

|

2.5 Let f : {

|

| ≤

ith direction.
b

(b) Show that the second statement of Theorem 2.33 holds even for all

unate f .

2.6 Show that linear threshold functions are unate.

2.7 For each function f in Exercise 1.1, compute Inf1[ f ].

2.8 Let f : {

Infi[ f ]

−
≤
1], Pr[ f
=
2.9 Let f : {0, 1}6
31x2

31x1

−

+

2.10 Given b

{
−

1, 1}n
{
−
Var[ f ] for each i

1, 1}. Without using Fourier formulas, show that
(Hint: Show Infi[ f ]

2 min{Pr[ f

[n].

→

1]}.)

∈

{
→
−
28x3

1, 1} be given by the weighted majority f (x)

+
1, 1}, say that coordinate i is b-pivotal for f : {

=
2x6). Compute Infi[ f ] for all i
∈
1, 1}n

21x4

2x5

+

+

+

58

sgn(
−
[6].

∈
on input x if f (x)
1
2 Infi[ f ]. Deduce that I[ f ]

=

b and f (x⊕

i)

6=

=

b. Show that Prx[i is b-pivotal on x]

2 Ex[# b-pivotal coordinates on x].

1, 1}

{
−

→

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.

≤

−

=

+

=



<!-- pdf-page: 20 -->
62

2. Basic concepts and social choice

2.11 Let f : {
i

∈
2.12 Let f : {

1, 1}n
S is relevant for f .
1, 1}n

{
−

→

−

−

{
−

→

pute E[Inf1[ f ]] and E[I[ f ]].

1, 1} and suppose

f (S)

6=

0. Show that each coordinate

1, 1} be a random function (as in Exercise 1.7). Com-

b

2.13 Let w

N, n

∈

=

w2w, and write f for Tribesw,2w : {

1, 1}n

−

1, 1}.

{
−

→

(a) Compute E[ f ] and Var[ f ], and estimate them asymptotically in terms

of n.

(b) Describe the function D1 f .
(c) Compute Inf1[ f ] and I[ f ] and estimate them asymptotically.

2.14 Let f : {

1, 1}n

R, and write g

|
Infi[ f ] and I[g]

= |

f

. Show that
I[ f ].

≤

Di g

|

| ≤ |

Di f

|

pointwise.

−

→

Deduce that Infi[g]
2.15 Prove Proposition 2.24.

≤

2.16 Prove Proposition 2.26.

2.17 Prove Proposition 2.37.

2.18 Let f : {

1, 1}n

−

→

R. Show that
d
dρ

Tρ f (x)

L f (x)

=
1, 1}n

d
dt

Te−

t f (x)

.

t

0

=

¯
¯
¯

1 = −

ρ

=

¯
¯
¯

2.19 Suppose f , g : {

the ith coordinate and g does not depend on the jth coordinate (i
Show that E[xi x j f (x)g(x)]

E[D j f (x)Di g(x)].

R have the property that f does not depend on
j).

→

−

6=

]. Show that
=
2]. (Hint: Use Proposition 2.37.) Is it true that

S f [
∼

ES

S

|

|

=

2.20 For f : {

1, 1}n

1, 1} we have that E[sens f (x)]
{
−
→
−
also E[sens f (x)2]
E[
|
=
3]?
E[sens f (x)3]
S
E[
|
|
R and i
1, 1}n

−
(a) Deﬁne Vari f : {

=
1, 1}n

R by

[n].

→

S

|

2.21 Let f : {

−
Vari f (x)

=
Show that Infi[ f ]

(b) Show that

∈
→
[ f (x1, . . . , xi

Var
xi
Ex[Vari f (x)].

=

1, xi, xi
−

1, . . . , xn)].
+

Infi[ f ]

1
2

=

E
xi,x0i∼
1,1}
{
−
independent

·°
°
°
b denotes the function of n

f

xi −

|

f

x0i

|

,

¸

2

2
°
°
°

−

where f
ith input of f to bit b.

|

1 variables gotten by ﬁxing the

2.22 (a) Show that Infi[Majn]

n
1
−
n
1
−
2
(b) Show that Inf1[Majn] is a decreasing function of (odd) n.
(c) Use Stirling’s Formula m!

n for all i

[n].

21

=

∈

−

¡

Inf1[Majn]
(d) Deduce that 2/π

=

p2/π
pn +

O(n−
W1[Majn]

≤

¢
(m/e)m(p2πm
3/2). (Here the O(

=

2/π

+

≤

O(n−

·
1).

O(m−

1/2)) to deduce that
+
) terms are nonnegative.)

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 21 -->
2.6. Exercises and notes

63

f (i)

≤

b

(e) Deduce that p2/πpn
(f ) Suppose n is even and f : {

I[Majn]

≤

Show that I[ f ]

I[Majn

1]
−

=

=

p2/πpn

O(n−

1/2).

≤
1, 1}n
→
−
p2/πpn
+

{
−
O(n−

1/2).

+
1, 1} is a majority function.

2.23 Using only Cauchy–Schwarz and Parseval, give a very simple proof of the
1, 1} is monotone

1, 1}n

following weakening of Theorem 2.33: If f : {
then I[ f ]

pn. Extend also to the case of f unate (see Exercise 2.5).

{
−

→

−

2.24 Prove Proposition 2.58 with O(n−

1) in place of on(1). (Hint: Show

≤

O(n−

3/2) using Theorem 2.33.)

p2/π
pn +
2.25 Deduce Tρ f (x)
2.26 For each function f in Exercise 1.1, compute I[ f ].

f (S) xS using Exercise 1.4.

S ρ|

=

S

|

P

2.27 Which functions f : {
1, 1}n

2.28 Suppose f : {

→
the improved Poincaré Inequality Var[ f ]

−

−

→

{
−

1, 1} with #{x : f (x)

b
1, 1}n
3 maximize I[ f ]?
R is an even function (recall Exercise 1.8). Show
1
2 I[ f ].
0, and let MaxInf[ f ] denote

≤
1, 1} be unbiased, E[ f ]

1}

=

=

2.29 Let f : {

1, 1}n
→
[n]{Infi[ f ]}.
∈

−

{
−

maxi
(a) Use the Poincaré Inequality to show MaxInf[ f ]
(b) Prove that I[ f ]

1/n.
nMaxInf[ f ]2. (Hint: Prove I[ f ]
W1[ f ]) and use Exercise 2.5.) Deduce that MaxInf[ f ]

≥

≥

−

2

=

2.30 Use Exercises 1.1(e),(f ) to deduce the formulas Ei f

S

Tρ f

f (S) χS.
2.31 Show that Tρ is positivity-preserving for ρ

S ρ|

=

|

∈
Show that Tρ is positivity-improving for ρ
Tρ f

0.

b

P

>

P

1, 1]; i.e., f
[
−
(
−
∈

≥
1, 1); i.e., f

0

≥

b
=⇒
0, f

Tρ f
0

6=

0.

≥
=⇒

2.32 Show that Tρ satisﬁes the semigroup property: Tρ1Tρ2 =
2.33 For ρ

1, 1], show that Tρ is a contraction on L p({
p

1, 1}n

i.e.,

R.

−

f

Tρ1ρ2.

1, 1}n) for all p

1;

≥

k

p for all f : {
R. Further show
Tρ|
1, equality occurs if and only if f is everywhere nonneg-

pointwise for any f : {

1, 1}n

→

→

−

−

f

≤ k
Tρ f
ρ

[
−
∈
Tρ f
k
k
2.34 Show that
1

| ≤
that for
<
ative or everywhere nonpositive.

|
<

−

|

2.35 For i

[n] and ρ

∈
deﬁned by

∈

R, let Ti

ρ be the operator on functions f : {

1, 1}n

R

→

−

2(1

W1[ f ]
+
2
4
n2 .
n −
f (S) χS and
i

−

≥
≥
S

63

=

ρ f
(a) Show that for ρ

Ti

∈

(1

ρ)Ei f

+

−
1, 1] we have

Ei f

=

+

ρLi f .

Ti

ρ f (x)

=

[ f (x1, . . . , xi

1, yi, xi
−

1, . . . , xn)].
+

ρ f

=
[
−
E
Nρ(xi)

yi∼

(b) Show that Ti
ρ1
ρ and T j
ρ0

tors Ti

Ti

Ti

ρ1ρ2
ρ2 =
commute.

(cf. Exercise 2.32) and that any two opera-

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 22 -->
64

2. Basic concepts and social choice

∈

Rn we deﬁne T(ρ1,...,ρn)

(c) For (ρ1, . . . , ρn)

. Show that
T(ρ,...,ρ) is simply Tρ and that T(1,...,1,ρ,1,...,1) (with the ρ in the ith
position) is Ti
ρ.
(d) For ρ1, . . . , ρn
for all p

1, 1], show that T(ρ1,...,ρn) is a contraction on L p({

1 (cf. Exercise 2.33).

ρ2 · · ·

Tn
ρn

T1
ρ1

T2

−

=

−

∈

[

1, 1}n)

ρ[ f ]
−

Stabρ[ f ] if f is odd and Stab

= −

ρ[ f ]
−

=

Stabρ[ f ] if

≥

2.36 Show that Stab
f is even.

2.37 For each function f in Exercise 1.1, compute Stabρ[ f ].
2.38 Compute Stabρ[Tribesw,s].
2.39 Suppose f : {
that NSδ[ f ]
2.40 Verify Fact 2.53.

1, 1}n
{
−
2α for all δ

1, 1} has min(Pr[ f

1], Pr[ f

[0, 1].

−
≤

→

=

∈

1])

= −

=

α. Show

2.41 Fix f : {

2.42 Let f : {

−

1, 1}n
1, 1}n

→

→
2.43 (a) Deﬁne the average inﬂuence of f : {

−

≤
1, 1}n

R. Show that Stabρ[ f ] is a convex function of ρ on [0, 1].
{
−

1, 1}. Show that NSδ[ f ]

δI[ f ] for all δ
∈
R to be EEE [ f ]

[0, 1].
1
n I[ f ]. Now

−

→

=

for f : {

1, 1}n

1, 1}, show

EEE [ f ]

=

x

(b) Given f : {

1, 1}n

{
−

→
[ f (x)

6=

−
Pr
{
−
∼
i
∼

1,1}n
[n]

−

→
1
k

f (x⊕

i)] and 1

2
e−
−
2

EEE [ f ]

NS1/n[ f ]

≤

EEE [ f ].

≤

1, 1} and integer k

{
−

2, deﬁne

≥

Ak

=

(W≥

1[ f ]

W≥

2[ f ]

+

+ · · · +

W≥

k[ f ]),

2.44 Suppose f1, . . . , f s : {

the “average of the ﬁrst k tail weights”. Generalizing the second
statement in part (a), show that 1

NS1/k[ f ]

2
e−
2 Ak
−
1, 1} satisfy NSδ[ f i]
1, 1} by h

≤

Ak.
²i. Let g : {

≤

1, 1}s

≤

→
g( f1, . . . , f s). Show that

−

1, 1}n

−

{
−
→
1, 1}n
→

{
−

=

{
−
NSδ[h]

1, 1} and deﬁne h : {
s
i

−

1 ²i.
=

≤

2.45 Complete the proof of Proposition 2.54 by showing that (1

for all 0
δ)2
(1

−
2.46 Fixing f : {
when 0
ρ

P
δ

<

≤
+ · · · +

1 and k
δ)k
(1
−
1, 1}n
ρ
²

→
<

≤

−
−

≤

δ)k
N+. (Hint: Compare both sides with 1

−

1k
−
(1

∈
1.)
−
R, show the following Lipschitz bound for Stabρ[ f ]
1:

+

+

1/δ
δ)

≤
−

Stabρ[ f ]

Stabρ

²[ f ]
−

²

≤

·

1

−

Var[ f ].

ρ ·

1

−

¯
¯

(Hint: Use the Mean Value Theorem and Exercise 2.45.)

¯
¯
1, 1}n

2.47 Let f : {

1, 1} be a transitive-symmetric function; in the nota-
tion of Exercise 1.30, this means the group Aut( f ) acts transitively on [n].
Show that Prπ

1/n for all i, j

{
−

[n].

→

−

j]

Aut( f )[π(i)
∼

=

=

∈

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 23 -->
2.6. Exercises and notes

65

2.48 Suppose that F is a functional on functions f : {
f (S)2 where cS
S cS
as F[ f ]
=
Wk, Infi, I, Inf(1
−
i
b
λ)g]
F[λ f
(1
≤

, and Stabρ for ρ
(1

0 for all S

λ F[ f ]

P
−

+

≥

≥

+

−

δ)

1, 1}n

R expressible
[n]. (Examples include Var,
0.) Show that F is convex, meaning

→

−

⊆

λ) F[g] for all f , g, and λ

[0, 1].

2.49 Extend the FKN Theorem as follows: Suppose f : {

1, 1} has
δ. Show that f is O(δ)-close to a 1-junta. (Hint: Consider

{
−

→

−

∈
1, 1}n

1[ f ]
W≤
g(x0, x)

≥
=

1
x0 f (x0x).)

−

2.50 Compute the precise probability of a Condorcet winner (under impartial

culture) in a 3-candidate, 3-voter election using f

Maj3.

=

1, 1}n

2.51 (a) Arrow’s Theorem for 3 candidates is slightly more general than what
we stated: it allows for three different unanimous functions f , g, h :
1, 1} to be used in the three pairwise elections. But show
{
−
that if using f , g, h always gives rise to a Condorcet winner then
x) for all x by using the fact
g
f
that x, y
( f (x), . . . , f (x)) is always a valid possibility for
the votes.)

h. (Hint: First show g(x)

x, and z

{
−

= −

= −

→

f (

=

=

−

=

(b) Extend Arrow’s Theorem to the case of Condorcet elections with more

than 3 candidates.

2.52 The polarizations of f : {

→
shifts, or two-point rearrangements) are deﬁned as follows. For i
the i-polarization of f is the function f σi : {

R deﬁned by

R (also known as compressions, down-
[n],

1, 1}n

1, 1}n

−

∈

f σi (x)

max{ f (x(i
min { f (x(i

= (

1)), f (x(i
1)), f (x(i

7→+

7→+

7→−

7→−

−
1))}
1))}

→
if xi
if xi

= +

1,

1.

= −
p for all p.

p

k

f σi

E[ f ] and

k
Inf j[ f ] for all j

(a) Show that E[ f σi ]
=
(b) Show that Inf j[ f σi ]
≤
(c) Show that Stabρ[ f σi ]
Stabρ[ f ] for all 0
(d) Show that f σi is monotone in the ith direction (recall Exercise 2.5).
Further, show that if f is monotone in the jth direction for some
j
∈
(e) Let f ∗

[n] then f σi is still monotone in the jth direction.

σn . Show that f ∗ is monotone, E[ f ∗]

E[ f ], Inf j[ f ∗]

f
k
[n].

= k
∈

f σ1σ2

1.

≥

≤

≤

ρ

···
=
Inf j[ f ] for all j
2.53 The Hamming distance ∆(x, y)

[n], and Stabρ[ f ∗]
#{i : xi

∈

=

≥

Stabρ[ f ] for all 0
≤
yi} on the discrete cube {

≤

ρ

1.

1, 1}n
is an example of an `1 metric space. For D
1, we say that the discrete
cube can be embedded into `2 with distortion D if there is a mapping
N such that:
F : {

Rm for some m

1, 1}n

=

6=

−

≥

≤

−

F(x)

F(x)

k

k

−

−

→
F(y)
k
F(y)
k

2

2

≥

≤

∈
∆(x, y) for all x, y;

∆(x, y) for all x, y.

D

·

(“no contraction”)

(“expansion at most D”)

In this exercise you will show that the least distortion possible is D

pn.

=

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 24 -->
P

¸

°
°
°
°

66

2. Basic concepts and social choice

(a) Recalling the deﬁnition of f odd from Exercise 1.8, show that for any

f : {

1, 1}n

−

R we have

f odd

k

→

I[ f ] and hence

2
2 ≤
k
n

[( f (x)

E
x

f (

−

−

x))2]

≤

E
x

f (x)

−

i
1
=
X

h¡

f (x⊕

i)

2

.

i

¢

(b) Suppose F : {

1, 1}n

( f1(x), f2(x), . . . , f m(x)) for
R. By summing the above inequality over
[m], show that any F with no contraction must have expansion at

→
1, 1}n

Rm, and write F(x)

→

−

=

−
functions f i : {
i
least pn.

∈

(c) Show that there is an embedding F achieving distortion pn.

2.54 Give a Fourier-free proof of the Poincaré Inequality by induction on n.

2.55 Let V be a vector space with norm
1 xiwi
=

R by g(x)

= k

→

n
i

−

k · k
.
k

1, 1}n
g : {
(a) Show that Lg
≤
(b) Deduce 2 Var[g]
Inequality:

≤

g pointwise. (Hint: Triangle inequality.)

E[g2] and thus the following Khintchine–Kahane

and ﬁx w1, . . . , wn

V . Deﬁne

∈

n

xiwi

1
p2 ·

E
x

≥

E
x

i
1
=
P

·°
°
°
°

n

i
1
=
P

·°
°
°
°

1/2

2

.

xiwi

¸

°
°
°
°

(Hint: Exercise 2.28.)
(c) Show that the constant 1
p2

above is optimal, even if V

R.

=

2.56 In the correlation distillation problem, a source chooses x

∼

{
−

1, 1}n uni-
formly at random and broadcasts it to q parties. We assume that the
transmissions suffer from some kind of noise, and therefore the players
receive imperfect copies y(1), . . . , y(q) of x. The parties are not allowed to
communicate, and despite having imperfectly correlated information they
wish to agree on a single random bit. In other words, the jth party will
output a bit f j(y( j))
1, 1}, and the goal is to ﬁnd functions f1, . . . , f q that
∈
f q(y(q)). To avoid
maximize the probability that f1(y(1))
trivial deterministic solutions, we insist that E[ f j(y( j))] be 0 for all j
[q].
Nρ(x) independently for each j.
(a) Suppose q
[n]. (Hint:

(0, 1), and y( j)

f2(y(2))

∼
∈
Show that the optimal solution is f1
You’ll need Cauchy–Schwarz.)

χi for some i

= · · · =

2, ρ

{
−

= ±

f2

=

=

=

∈

∈

(b) Show the same result for q
(c) Let q

2 and ρ

=

3.

( 1
2 , 1). Suppose that y(1)

x exactly, but y(2)

∈

=

1, 0, 1}n has erasures: it’s formed from x by setting y(2)

{
−
probability ρ and y(2)
all i
there is an optimal solution in which f1
∈
Eliminate the source, and introduce a ﬁctitious party 10. . . )

[n]. Show that the optimal success probability is 1

∈
xi with
i =
ρ, independently for
1
2 ρ and
2 +
[n]. (Hint:

0 with probability 1

χi for any i

i =

= ±

−

=

∈

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 25 -->
2.6. Exercises and notes

67

(d) Consider the previous scenario but with ρ

(0, 1

2 ). Show that if n is

∈

sufﬁciently large, then the optimal solution does not have f1

χi.

0 have E[g]

R≥
n

=
n

δ. Show that for any ρ

∈

= ±
[0, 1],

2.57 (a) Let g : {

1, 1}n

−

→

ρ

g( j)

δ

+

| ≤

k

g=

ρk

k

.

k∞

k
2
=
X

1 |
j
=
X

(Hint: Exercise 2.31.)
(b) Assume further that g : {
k

b

ing ρ

(Hint: First bound
1
2pn
(c) Show that
2p2

n
j

≤

.

P
·
(d) Suppose f : {

1, 1}n
b

g( j)

1 |
=
δ7/4pn. (Hint: show

| ≤

g=

k

−
δ3/4

|

{
−
pn.

→
·

1, 1}n

→

−
2
2.) Deduce ρ
k

{0, 1}. Show that

g( j)

n
j

1 |
=

| ≤

k
δ

+

k

pδ
g=
.
2ρ2pδn, assum-
¢

k∞ ≤

q¡

n
k

2p2δ3/4pn (assuming δ

b

P

g( j)

δ for all j.)

| ≤

1/4). Deduce W1[g]

≤

≤

1, 1} is monotone and MaxInf[ f ]

δ. Show

≤

W2[ f ]

p2

I[ f ]

·

·

≤

b
(e) Suppose further that f is unbiased. Show that MaxInf[ f ]

2/3)
implies I[ f ]
o(1/n). (Hint: Extend
Exercise 2.29.) Use Exercise 2.52 to remove the assumption that f is
monotone for these statements.
2.58 Let V be a vector space (over R) with norm

o(1); conclude MaxInf[ f ]

3
n −

o(n−

−

≤

≥

≥

3

k · k

1, 1}n
V . If f : {
V by the usual formula
p
f

−

f (S)
1,1}n [ f (x)xS]. We may also deﬁne
{
−
∈

can deﬁne its Fourier coefﬁcients
Ex
nally, if the norm
can deﬁne an inner product on functions f , g : {
Ex
1,1}n [
{
〈
−
∈
R with
used V
this material extends to the more general setting.

∈
1,1}n [
{
k
k
−
∈
V arises from an inner product
〈·
1, 1}n
→

〉 =
V ]. The material developed so far in this book has
V being multiplication. Explore the extent to which

f (x), g(x)
〉
,
·〉

f (x)
k
,
·〉
V by

k · k

Ex

=

−

=

〈·

b

k

〈

p

V we
→
f (S)
=
V ]1/p. Fi-
b
V on V we
f , g

Notes. The mathematical study of social choice began in earnest in the late
1940s; see Riker [Rik61] for an early survey or the compilation [BGR09]
for some modern results. Arrow’s Theorem was the ﬁeld’s ﬁrst major re-
sult; Arrow proved it in 1950 [Arr50] under the extra assumption of mono-
tonicity (and with a minor error [Bla57]), with the reﬁned version appearing
in 1963 [Arr63]. He was awarded the Nobel Prize for this work in 1972.
May’s Theorem is from 1952 [May52]. Guilbaud’s Formula is also from
1952 [Gui52], though Guilbaud only stated it in a footnote and wrote that it is
computed “by the usual means in combinatorial analysis”. The ﬁrst published
proof appears to be due to Garman and Kamien [GK68]; they also introduced
the impartial culture assumption. The term “junta” appears to have been
introduced by Parnas, Ron, and Samorodnitsky [PRS01].

The notion of inﬂuence Infi[ f ] was originally introduced by the geneticist
. It was rediscovered

Penrose [Pen46], who observed that Infi[Majn]

p2/π
pn

∼

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 26 -->
68

2. Basic concepts and social choice

by the lawyer Banzhaf in 1965 [Ban65]; he sued the Nassau County (NY)
Board after proving that the voting system it used (the one in Exercise 2.9)
gave some towns zero inﬂuence. Inﬂuence is sometimes referred to as the
Banzhaf, Penrose–Banzhaf, or Banzhaf–Coleman index (Coleman being an-
other rediscoverer [Col71]). Inﬂuences were ﬁrst studied in the computer
science literature by Ben-Or and Linial [BL85]; they introduced also intro-
duced “tribes” as an example of a function with constant variance yet small
inﬂuences. The Fourier formulas for inﬂuence may have ﬁrst appeared in the
work of Chor and Geréb-Graus [CGG87].

Total inﬂuence of Boolean functions has long been studied in combina-
torics, since it is equivalent to edge-boundary size for subsets of the Ham-
ming cube. For example, the edge-isoperimetric inequality was ﬁrst proved
by Harper in 1964 [Har64]. In the context of Boolean functions, Karpovsky
[Kar76] proposed I[ f ] as a measure of the computational complexity of f ,
f (S)2.
and Hurst, Miller, and Muzio [HMM82] gave the Fourier formula
The terminology “Poincaré Inequality” comes from the theory of functional
inequalities and Markov chains; the inequality is equivalent to the spectral
gap for the discrete cube graph.

S |

P

S

b

|

The noise stability of Boolean functions was ﬁrst studied explicitly by
Benjamini, Kalai, and Schramm in 1999 [BKS99], though it plays an impor-
tant role in the earlier work of Håstad [Hås97]. See O’Donnell [O’D03] for a
survey. The noise operator was introduced by Bonami [Bon70] and indepen-
dently by Beckner [Bec75], who used the notation Tρ which was standardized
by Kahn, Kalai, and Linial [KKL88]. For nonnegative noise rates it’s often
natural to use the alternate parameterization Te−

t for t

[0,

].

The Fourier approach to Arrow’s Theorem is due to Kalai [Kal02]; he
also proved Theorem 2.57 and Corollary 2.60. The FKN Theorem is due to
Friedgut, Kalai, and Naor [FKN02]; the observation from Exercise 2.49 is
due to Kindler.

∈

∞

The polarizations from Exercise 2.52 originate in Kleitman [Kle66]. Exer-
cise 2.53 is a theorem of Enﬂo from 1970 [Enf70]. Exercise 2.55 is a theorem
of Latała and Oleszkiewicz [LO94]. In Exercise 2.56, part (b) is due to Mos-
sel and O’Donnell [MO05]; part (c) was conjectured by Yang [Yan04] and
proved by O’Donnell and Wright [OW12]. Exercise 2.57 is a polishing of the
1987 work by Chor and Geréb-Graus [CGG87, CGG88], a precursor of the
KKL Theorem. The weaker Exercise 2.29 is also due to them and Noga Alon
independently.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.


