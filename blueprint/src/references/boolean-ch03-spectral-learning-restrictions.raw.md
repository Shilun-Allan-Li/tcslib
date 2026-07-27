<!-- generated-by: proofmatch local extraction -->
<!-- source-pdf-sha256: 20e15a3d3d5e94a7b8771247aadec17f0ea241a8e4cd9335baa9c1fc7a2cfaf0 -->
<!-- extractor: pdfminer.six v20260107 -->

<!-- pdf-page: 1 -->
Chapter 3

Spectral structure and
learning

One reasonable way to assess the “complexity” of a Boolean function is in
terms how complex its Fourier spectrum is. For example, functions with
sufﬁciently simple Fourier spectra can be efﬁciently learned from examples.
This chapter will be concerned with understanding the location, magnitude,
and structure of a Boolean function’s Fourier spectrum.

3.1. Low-degree spectral concentration

One way a Boolean function’s Fourier spectrum can be “simple” is for it to be
mostly concentrated at small degree.

Deﬁnition 3.1. We say that the Fourier spectrum of f : {
concentrated on degree up to k if

−

1, 1}n

R is ²-

→

W>

k[ f ]

=

f (S)2

².

≤

b

[n]
k

S
⊆
X
S
|>

|

For f : {
sample: PrS

−

1, 1}n
→
S
S f [
|
∼

{
−
| >

≤

1, 1} we can express this condition using the spectral
k]

².

It’s possible to show such a concentration result combinatorially by show-

ing that a function has small total inﬂuence:

Proposition 3.2. For any f : {
→
f is ²-concentrated on degree up to I[ f ]/².

−

1, 1}n

R and ²

0, the Fourier spectrum of

>

69

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 2 -->
70

3. Spectral structure and learning

Proof. This follows immediately from Theorem 2.38, I[ f ]
1, 1}n
For f : {
of the spectral sample.

Wk[ f ].
1, 1}, this is Markov’s inequality applied to the cardinality
(cid:3)

0 k
=

{
−

→

P

−

=

·

n
k

For example, in Exercise 2.13 you showed that I[Tribesw,2w ]

O(log n),
w2w; thus this function’s spectrum is .01-concentrated on degree
where n
up to O(log n), a rather low level. Proving this by explicitly calculating Fourier
coefﬁcients would be quite painful.

≤

=

Another means of showing low-degree spectral concentration is through

noise stability/sensitivity:

Proposition 3.3. For any f : {
spectrum of f is ²-concentrated on degree up to 1/δ for

1, 1} and δ

{
−

→

−

1, 1}n

(0, 1/2], the Fourier

∈

²

=

2
e−

1

−

2 NSδ[ f ]

3NSδ[ f ].

≤

Proof. Using the Fourier formula from Theorem 2.49,

2NSδ[ f ]

=

≥

≥

2δ)|

S

|]

E
S f

[1

−

(1

S

∼
(1

(1

−

−
2δ)1/δ)

Pr
S f
S

∼

·

S

[

|

| ≥

1/δ]

e−

(1

−

Pr
S f
S

S

[

|

| ≥

1/δ],

·

−
2)

∼
(1

where the ﬁrst inequality used that 1
function of k. The claim follows.

−

2δ)k is a nonnegative nondecreasing
(cid:3)

−

0 sufﬁciently small and n
As an example, Theorem 2.45 tells us that for δ
pδ. Hence the Fourier
sufﬁciently large (as a function of δ), NSδ[Majn]
spectrum of Majn is 3pδ-concentrated on degree up to 1/δ; equivalently, it
is ²-concentrated on degree up to 9/²2.
(We will give sharp constants for
majority’s spectral concentration in Chapter 5.3.) This example also shows
there is no simple converse to Proposition 3.2; although Majn has its spectrum
.01-concentrated on degree up to O(1), its total inﬂuence is Θ(pn).

>
≤

Finally, suppose a function f : {

1, 1} has its Fourier spectrum
k. In
0-concentrated up to degree k; in other words, f has real degree deg( f )
this case f must be somewhat simple; indeed, if k is a constant, then f is a
junta:

{
−

→

−

≤

1, 1}n

Theorem 3.4. Suppose f : {
junta.

−

1, 1}n

1, 1} has deg( f )

{
−

≤

→

k. Then f is a k2k

1-
−

The bound k2k

1 cannot be signiﬁcantly improved; see Exercise 3.24. The
−
key to proving Theorem 3.4 is the following lemma, the proof of which is
outlined in Exercise 3.4:

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 3 -->
3.2. Subspaces and decision trees

71

Lemma 3.5. Suppose deg( f )
Then Pr[ f (x)

k.

0]

2−

6=

≥

≤

k, where f : {

1, 1}n

−

R is not identically 0.

→

Since deg(Di f )

and since Infi[ f ]

=

Proposition 3.6. If f : {
k for all i
or at least 21
−

6=
1, 1}n
[n].

−
∈

k

−
≤
Pr[Di f (x)

1 when deg( f )

k (by the “differentiation” formula)
0] for Boolean-valued f , we immediately infer:

≤

1, 1} has deg( f )

{
−

≤

k then Infi[ f ] is either 0

→

We can now give the proof of Theorem 3.4. From Proposition 3.6 the
k,

number of coordinates which have nonzero inﬂuence on f is at most I[ f ]/21
and this in turn is at most k2k

1 by the following fact:
−

−

Fact 3.7. For f : {

1, 1}n

−

1, 1}, I[ f ]

{
−

≤

→

deg( f ).

Fact 3.7 is immediate from the Fourier formula for total inﬂuence.

We remark that the FKN Theorem (stated in Chapter 2.5) is a “robust”
1. In Chapter 9.6 we will see Friedgut’s Junta
k then f is ²-close to a

version of Theorem 3.4 for k
Theorem, a related robust result showing that if I[ f ]
2O(k/²)-junta.

=

≤

3.2. Subspaces and decision trees

In this section we will treat the domain of a Boolean function as Fn
2 , an n-
dimensional vector space over the ﬁeld F2. As mentioned in Chapter 1.2, it
can be natural to index the Fourier characters χS : Fn
1, 1} not by subsets
S
2 ; thus

[n] but by their 0-1 indicator vectors γ

2 →

{
−

Fn

⊆

∈
1)γ
·

x,

χγ(x)

(

=

−

with the dot product γ
2 . For example, in this notation
we’d write χ0 for the constantly 1 function and χe i for the ith dictator. Fact 1.6
now becomes

x being carried out in Fn

·

χβχγ =

χβ

γ ∀
+
Thus the characters form a group under multiplication, which is isomorphic
to the group Fn
2 under addition. To distinguish this group from the input
2 ; we also tend to identify the character with its index.
domain we write it as
R can be written as
Thus the Fourier expansion of f : Fn

Fn

(3.1)

β, γ.

c

f (x)

=

2 →

Fn
Xγ
2
∈
c

f (γ)χγ(x).

b

The Fourier transform of f can be thought of as a function

can measure its complexity with various norms.

f :

Fn

2 →

R. We

b
Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.

c



<!-- pdf-page: 4 -->
72

3. Spectral structure and learning

Deﬁnition 3.8. The Fourier (or spectral) p-norm of f : {

1, 1}n

R is

→

−

1/p

f (γ)

|

p

|



.

ˆ
k

f ˆ
kp = 

Fn
Xγ
2
∈
c


Note that we use the “counting measure” on



b

Fn

rephrasing of Parseval’s Theorem:
relating to the simplicity of

f :

f

k

2
k

=

ˆ
k

2 , and hence we have a nice
f ˆ
k2. We make two more deﬁnitions

c

Deﬁnition 3.9. The Fourier (or spectral) sparsity of f : {
b

sparsity(

f )

supp(

= |

f )

| =

#

γ

∈

Fn
2 :

f (γ)

6=

1, 1}n

R is

→

−
0

.

ª

Deﬁnition 3.10. We say that
Fn
2 .
of ² for all γ

b

∈

b

b

f is ²-granular if
c

b

©

f (γ) is an integer multiple

b

c

To gain some practice with this notation, let’s look at the Fourier trans-
{0, 1} and probability density
2 is a subspace. Then one

forms of some indicator functions 1A : Fn
functions ϕA, where A
way to characterize A is by its perpendicular subspace A⊥:

2 →
2 . First, suppose A

Fn

Fn

⊆

≤

A⊥

{γ

Fn

2 : γ

x

0 for all x

A}.

=

∈

∈
dim A (this is called the codimension of A) and that

=

·

c

It holds that dim A⊥
A

(A⊥)⊥.

=

n

−

=

Proposition 3.11. If A

≤

Fn

2 has codim A
kχγ,

2−

1A

=

γ

A⊥
X
∈

k, then

=
χγ.

dim A⊥

=

ϕA

=

γ

A⊥
X
∈

Proof. Let γ1, . . . , γk form a basis of A⊥. Since A
if and only if χγi (x)

1 for all i

[k]. We therefore have

=

(A⊥)⊥ it follows that x

A

∈

=

∈

1
2 +

1
2 χγi (x)

=

k

2−

χγ(x)

´
as claimed, where the last equality used (3.1). The Fourier expansion of ϕA
(cid:3)
follows because E[1A]

2−

k.

∈

γ

span{γ1,...,γk}
X

1A(x)

k

=

i
1³
=
Y

=

More generally, suppose A is afﬁne subspace (or coset) of Fn

for some H

Fn

2 and a

≤

Fn

∈
{x

2 , or equivalently
Fn

2 : γ

x

·

=

·

∈

A

=

γ

a for all γ

H⊥}.

∈

2 ; i.e., A

H

a

+

=

Then it is easy (Exercise 3.11) to extend Proposition 3.11 to:

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 5 -->
3.2. Subspaces and decision trees

73

Proposition 3.12. If A

H

+

=

a is an afﬁne subspace of codimension k, then

1A(γ)

k

χγ(a)2−
= (
0

H⊥

if γ

∈
else;

c

hence ϕA
1A ˆ
ˆ
k

χγ(a)χγ. We have sparsity(
H⊥
γ
=
∈
1A ˆ
k, and ˆ
2−
P
k

k∞ =
In computer science terminology, any f : Fn

k1 =

1.

c

1A)

=

2k,

1A is 2−

k-granular,

c

{0, 1} that is a conjunction
of parity conditions is the indicator of an afﬁne subspace (or the zero function).
In the simple case that the parity conditions are all of the form “xi
ai”, the
function is a logical AND of literals, and we call the afﬁne subspace a subcube.

2 →

=

Another class of Boolean functions with simple Fourier spectra are the

ones computable by simple decision trees:

2 →

Deﬁnition 3.13. A decision tree T is a representation of a Boolean function
R. It consists of a rooted binary tree in which the internal nodes are
f : Fn
labeled by coordinates i
[n], the outgoing edges of each internal node are
labeled 0 and 1, and the leaves are labeled by real numbers. We insist that no
coordinate i

[n] appears more than once on any root-to-leaf path.

∈

∈

On input x

2 , the tree T constructs a computation path from the root
node to a leaf. Speciﬁcally, when the computation path reaches an internal
[n] we say that T queries xi; the computation
node labeled by coordinate i
path then follows the outgoing edge labeled by xi. The output of T (and
hence f ) on input x is the label of the leaf reached by the computation path.
We often identify a tree with the function it computes.

∈

∈

Fn

For decision trees, a picture is worth a thousand words; see Figure 3.1.

Figure 3.1. Decision tree computing Sort3

(It’s traditional to write xi rather than i for the internal node labels.) For
F3
example, the computation path of the above tree on input x
2
starts at the root, queries x1, proceeds left, queries x3, proceeds left, queries

(0, 1, 0)

=

∈

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 6 -->
74

3. Spectral structure and learning

x2, proceeds right, and reaches a leaf labeled 0. In fact, this tree computes the
x3.
function Sort3 deﬁned by Sort3(x)

1 if and only if x1

x3 or x1

x2

x2

=

≤

≤

≥

≥

Deﬁnition 3.14. The size s of a decision tree T is the total number of leaves.
The depth k of T is the maximum length of any root-to-leaf path. For decision
R we write DT( f )
trees over Fn
(respectively, DTsize( f )) for the least depth (respectively, size) of a decision
tree computing f . (Note that these are not necessarily achieved by the same
tree.)

2k. Given f : Fn

2 we have k

n and s

2 →

≤

≤

The example decision tree above has size 6 and depth 3.
Let T be a decision tree computing f : Fn

R and let P be one of its
root-to-leaf paths. The set of inputs x that follow computation path P in T is
precisely a subcube of Fn
2 , call it CP . The function f is constant on CP ; we
will call its value there f (P). Further, since every input x follows a unique
path in T, the subcubes {CP : P a path in T} form a partition of Fn
2 . These
observations yield the following “spectral simplicity” results for decision trees:

2 →

Fact 3.15. Let f : Fn

2 →

R be computed by a decision tree T. Then

Proposition 3.16. Let f : Fn
and depth k. Then:

2 →

f

=

f (P)

1CP .

·

paths P of T
X
R be computed by a decision tree T of size s

k;

f )

≤

deg( f )

≤
sparsity(
f ˆ
ˆ
k1 ≤ k
k
f is 2−

f

•

•

•

•

s2k

4k;

≤
f

s

2k;

k∞ ·
b

k∞ ·
k-granular assuming f : Fn

≤ k

Z.

2 →

Proposition 3.17. Let f : Fn
b
size s and let ²
to log(s/²).

∈

1, 1} be computable by a decision tree of
(0, 1]. Then the spectrum of f is ²-concentrated on degree up

2 →

{
−

You are asked to prove these propositions in Exercises 3.21 and 3.22. Sim-
ilar spectral simplicity results hold for some generalizations of the decision
tree representation (“subcube partitions”, “parity decision trees”); see Exer-
cise 3.26.

3.3. Restrictions

A common operation on Boolean functions f : {
subcubes. Suppose [n] is partitioned into two sets, J and J
inputs bits in J are ﬁxed to constants, the result is a function {
For example, if we take the function Maj5 : {

R is restriction to
[n] \ J. If the
R.
1, 1}J
1, 1} and restrict the

1, 1}n

1, 1}5

→

→

−

−

=

−

{
−

→

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 7 -->
3.3. Restrictions

75

4th and 5th coordinates to be 1 and
Maj3 : {
−
obtain the two-bit function which is 1 if and only if both input bits are 1.

1 respectively, we obtain the function
1, we

1, 1}. If we further restrict the 3rd coordinate to be

1, 1}3

{
−

→

−

−

We introduce following notation:

∈

−

{
−

→
z : {

1, 1}n
1, 1}J. Then we write f J

R and let (J, J) be a partition of [n]. Let
Deﬁnition 3.18. Let f : {
R (pronounced “the restriction
1, 1}J
z
of f to J using z”) for the subfunction of f given by ﬁxing the coordinates
in J to the bit values z. When the partition (J, J) is understood we may
1, 1}J we will sometimes write (y, z)
write simply f
{
−
|
1, 1}n, even though y and z are not literally
for the composite string in {
concatenated; with this notation, f J

1, 1}J and z

z. If y

f (y, z).

z(y)

{
−

→

−

−

∈

∈

|

|

=

Let’s examine how restrictions affect the Fourier transform by considering

an example.

Example 3.19. Let f : {

1, 1}4

−

f (x)

1

=

⇐⇒

x3

x4

=

= −

{
→
−
1 or x1

1, 1} be the function deﬁned by

x2

≥

≥

x3

≥

x4 or x1

x2

≤

≤

x3

≤

x4.

(3.2)

You can check that f has the Fourier expansion

f (x)

= +

+

1
1
8 x1
8 −
3
8 x1x2
+
1
8 x1x2x3

1
8 x2
+
−
1
8 x1x3
−
1
8 x1x2x4

1
1
8 x3
8 x4
−
3
3
8 x1x4
8 x2x3
1
8 x1x3x4

+

1
8 x2x4
−
+
1
8 x2x3x4

5
8 x3x4
1
8 x1x2x3x4.

(3.3)

+

+
Consider the restriction x3
1) be the restricted
−
function of x1 and x2. From the original deﬁnition (3.2) of f we see that
f 0(x1, x2) is 1 if and only if x1
1. This is the min2 function of x1 and x2,
which we know has Fourier expansion

1, and let f 0

f{1,2}
|

1, x4

= −

x2

=

−

+

−

=

=

=

(1,

f 0(x1, x2)

=

min2(x1, x2)

1
2 +

1
2 x1

+

1
2 x2

+

1
2 x1x2.

= −

(3.4)

We can of course obtain this expansion simply by plugging x3
1
= −
into (3.3). Now suppose we only wanted to know the coefﬁcient on x1 in the
Fourier expansion of f 0. We can ﬁnd it as follows: Consider all monomials
in (3.3) that contain x1 and possibly also x3, x4; substitute x3
1 into
the associated terms; and sum the results. The relevant terms in (3.3) are
1 gives us

1
8 x1x3x4, and substituting in x3

1, x4

1, x4

1, x4

= −

=

=

1
8 x1,
+
1
1
8 +
8 +

3
1
8 x1x4,
8 x1x3,
−
1
1
3
2 , as expected from (3.4).
8 =
8 +

−

−
−

= −

=

Now we work out these ideas more generally. In the setting of Deﬁni-
1, 1}J as its domain. Thus its
tion 3.18 the restricted function f J
z has {
Fourier coefﬁcients are indexed by subsets of J. Let’s introduce notation for
the Fourier coefﬁcients of a restricted function:

−

|

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 8 -->
76

3. Spectral structure and learning

Deﬁnition 3.20. Let f : {
J. Then we write FS
S

−
J f : {

→
1, 1}J

|

−

⊆

R for the function

→

1, 1}n

R and let (J, J) be a partition of [n]. Let

|
When the partition (J, J) is understood we may write simply FS

d

FS

J f (z)

f J

z(S).

=

|

(S); i.e.,

f J

|•

d

f .

|

In Example 3.19 we considered J

{3, 4}, S

{1}, and z

Figure 3.2 for an illustration of a typical restriction scenario.

=

=

(1,

=

1). See

−

Figure 3.2. Notation for a typical restriction scenario. Note that J and J
need not be literally contiguous.

|

z(S) is as a function of z

In general, for a ﬁxed partition (J, J) of [n] and a ﬁxed S

J, we may wish
⊆
1, 1}J. This is precisely asking for
f J
to know what
1, 1}J,
J f has domain {
the Fourier transform of FS
its Fourier transform has coefﬁcients indexed by subsets of J. The formula
for this Fourier transform generalizes the computation we used at the end of
Example 3.19:

∈
J f . Since the function FS

{
−

d

−

|

|

Proposition 3.21. In the setting of Deﬁnition 3.20 we have the Fourier expan-
sion

i.e.,

J f (z)

FS

|

=

T
J
X
⊆

T)zT ;

f (S

∪

b

J f (T)

FS

|

=

f (S

T).

∪

ƒ

b

= ;

case here is Exercise 1.15.) Every U

Proof. (The S
Fourier coefﬁcients can be written as a disjoint union U
and T
{
−

J. We can also decompose any x

{
∈
−
yS zT and so

1, 1}J. We have xU

⊆
1, 1}J and z

=

∈

[n] indexing f ’s
J
T, where S

⊆
S

⊆
∪
1, 1}n into two substrings y

∈

{
−
f (U) xU

=

f (S

∪

=
T) yS zT

=

f (x)

=

U

[n]

⊆
X

J
S
⊆
X
J b
T
⊆
Thus when z is ﬁxed, the resulting function of y indeed has
as its Fourier coefﬁcient on the monomial yS.

T
J³ X
J
⊆

S
X
⊆

b

b

f (S

∪

T) zT

yS.

´

T

J

⊆

f (S

T) zT
(cid:3)

∪

b

P

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 9 -->
3.3. Restrictions

77

Corollary 3.22. Let f : {
S

J. Suppose z

−

{
−

∼

⊆

1, 1}n

R, let (J, J) be a partition of [n], and ﬁx

1, 1}J is chosen uniformly at random. Then

→

E
z

[

f J

z(S)]

|
z(S)2]
f J
d
|

[
E
z

d

=

=

f (S),

b
J
T
X
⊆

T)2.

f (S

∪

b

Proof. The ﬁrst statement is immediate from Proposition 3.21, taking T
and unraveling the deﬁnition. As for the second statement,

= ;

z(S)2]

f J

[
E
z

|

d

=

=

=

E
z

[FS

J f (z)2]
J f (T)2

|
FS

|

T
J
X
⊆

T
J
X
⊆

ƒ
f (S
∪

T)2

b

(by deﬁnition)

(Parseval)

(Proposition 3.21) (cid:3)

We move on to discussing a more general kind of restriction; namely,
z. This generalizes
J}
span{e i : i
Fn
2 we have a

restricting a function f : Fn
restriction to subcubes as we’ve seen so far, by considering H
for a given subset J
[n]. For restrictions to a subspace H
natural deﬁnition:

R to an afﬁne subspace H

2 →

=
≤

⊆

+

∈

Deﬁnition 3.23. If f : Fn
2 →
for the restriction of f to H.

R and H

≤

Fn

2 is a subspace, we write f H : H

R

→

∈

=

For restrictions to afﬁne subspaces, we run into difﬁculties if we try to
extend our notation for restrictions to subcubes. Unlike in the subcube case
J}, we don’t in general have a canonical isomorphism
of H
span{e i : i
z. Thus it’s not natural to introduce notation
between H and a coset H
z), because such a deﬁnition
z : H
such as f H
+
z. As an example consider
depends on the choice of representative for H
H
H).
Here the nontrivial coset is H
{(1, 0), (0, 1)}, which has no
canonical representative.

2, a 1-dimensional subspace (which satisﬁes H⊥
(0, 1)

+
R for the function h

{(0, 0), (1, 1)}

(1, 0)

f (h

F2

7→

→

H

=

+

≤

=

+

=

+

=

|

To get around this difﬁculty we can view restriction to a coset H

z as
consisting of two steps: ﬁrst, translation of the domain by a ﬁxed representa-
tive z, and then restriction to the subspace H. Let’s introduce some notation
for the ﬁrst operation:

+

Deﬁnition 3.24. Let f : Fn
R by f +
f (x
f +

z : Fn

z(x)

2 →
z).
+

=

2 →

R and let z

Fn

2 . We deﬁne the function

∈

By substituting x

x

+

=

z into the Fourier expansion of f , we deduce:

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 10 -->
78

3. Spectral structure and learning

Fact 3.25. The Fourier coefﬁcients of f +

z are given by

f +

z(γ)

z

1)γ
·

(
−

=

f (γ); i.e.,

f +

z(x)

=

χγ(z)

f (γ) χγ(x).

d

b

Fn
Xγ
2
∈
c

b
ϕ{z}

z

=

∗

(This fact also follows by noting that f +

f ; see Exercise 3.31.)

We can now give notation for the restriction of a function to an afﬁne

subspace:

Deﬁnition 3.26. Let f : Fn
for the function ( f +
representative z made explicit.

Fn
z)H; namely, the restriction of f to coset H

2 . We write f +

2 , H

R, z

2 →

Fn

R
z
H : H
z with the

→

≤

∈

+

z

H . These can be indexed by the cosets of H⊥ in

Finally, we would like to consider Fourier coefﬁcients of restricted func-
tions f +
2 . However, we again
have a notational difﬁculty since the only coset with a canonical representa-
tive is H⊥ itself, with representative 0. There is no need to introduce extra
notation for

z, since it is just

Fn

c

z

H (0), the average value of f on coset H
f +
[ f (h

ϕH, f +

z)]

.

z

+

d

+

= 〈

〉

E
H
h
∼

Applying Plancherel on the right-hand side, as well as Proposition 3.11 and
Fact 3.25, we deduce the following classical fact:

Poisson Summation Formula. Let f : Fn

Fn

2 , z

∈

Fn

2 . Then

E
H
h
∼

[ f (h

z)]

=

+

R, H

2 →
χγ(z)

≤
f (γ).

γ

H⊥
X
∈

b

3.4. Learning theory

Computational learning theory is an area of algorithms research devoted to
the following task: Given a source of “examples” (x, f (x)) from an unknown
function f , compute a “hypothesis” function h that is good at predicting f (y)
on future inputs y. In this book we will focus on just one possible formulation
of the task:

Deﬁnition 3.27. In the model of PAC (“Probably Approximately Correct”)
1, 1}n, a learning problem is
learning under the uniform distribution on {
identiﬁed with a concept class C , which is just a collection of functions f :
1, 1}. A learning algorithm A for C is a randomized algorithm
{
−
C . The two access
which has limited access to an unknown target function f
models, in increasing order of strength, are:

1, 1}n

{
−

→

−

∈

•

random examples, meaning A can draw pairs (x, f (x)) where x
is uniformly random;

∈

1, 1}n

{
−

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 11 -->
3.4. Learning theory

79

•

queries, meaning A can request the value f (x) for any x
choice.

∈

1, 1}n of its

{
−

In addition, A is given as input an accuracy parameter ²
[0, 1/2]. The output
of A is required to be (the circuit representation of) a hypothesis function
C ,
h : {
with high probability A outputs an h which is ²-close to f :
i.e., satisﬁes
dist( f , h)

1, 1}. We say that A learns C with error ² if for any f

1, 1}n

{
−

→

−

∈

∈

².

≤

In the above deﬁnition, the phrase “with high probability” can be ﬁxed
to mean, say, “except with probability at most 1/10”.
(As is common with
randomized algorithms, the choice of constant 1/10 is unimportant; see Exer-
cise 3.40.)

For us, the main desideratum of a learning algorithm is efﬁcient running
O(2n) (see Exer-
time. One can easily learn any function f to error 0 in time
cise 3.33); however, this is not very efﬁcient. If the concept class C contains
very complex functions, then such exponential running time is necessary;
however, if C contains only relatively “simple” functions, then more efﬁcient
learning may be possible. For example, the results of Section 3.5 show that
the concept class

e

C

=

{ f : Fn

2 →

1, 1}

{
−

|

DTsize( f )

s}

≤

can be learned with queries to error ² by an algorithm whose running time is
poly(s, n, 1/²).

A common way of trying to learn an unknown target f : {

1, 1}
is by discovering “most of” its Fourier spectrum. To formalize this, let’s gener-
alize Deﬁnition 3.1:

{
−

→

−

1, 1}n

Deﬁnition 3.28. Let F be a collection of subsets S
Fourier spectrum of f : {

R is ²-concentrated on F if

1, 1}n

⊆

[n]. We say that the

−

→

f (S)2

².

≤

[n]
S
⊆
X
F
S
∉

b

1, 1}n

For f : {
sample: PrS

−

→
S f [S
∼

1, 1} we can express this condition using the spectral
{
−
F ]
∉

².

≤

Most functions don’t have their Fourier spectrum concentrated on a small
collection (see Exercise 3.35). But for those that do, we may hope to discover
“most of” their Fourier coefﬁcients. The main result of this section is a kind of
“meta-algorithm” for learning an unknown target f . It reduces the problem of
learning f to the problem of identifying a collection of characters on which f ’s
Fourier spectrum is concentrated.

Theorem 3.29. Assume learning algorithm A has (at least) random example
1, 1}. Suppose that A can – somehow – identify a
access to target f : {

1, 1}n

−

{
−

→

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 12 -->
80

3. Spectral structure and learning

collection F of subsets on which f ’s Fourier spectrum is ²/2-concentrated. Then
using poly(
, n, 1/²) additional time, A can with high probability output a
hypothesis h that is ²-close to f .

F

|

|

The idea of the theorem is that A will estimate all of f ’s Fourier coefﬁ-
cients in F , obtaining a good approximation to f ’s Fourier expansion. Then
A’s hypothesis will be the sign of this approximate Fourier expansion.

The ﬁrst tool we need to prove Theorem 3.29 is the ability to accurately

estimate any ﬁxed Fourier coefﬁcient:

Proposition 3.30. Given access to random examples from f : {
1, 1}, there is a randomized algorithm which takes as input S
{
−
δ, ²

1/2, and outputs an estimate

f (S) that satisﬁes

f (S) for

−
⊆

1, 1}n
[n], 0

→
<

≤

except with probability at most δ. The running time is poly(n, 1/²)
e

b

log(1/δ).

·

f (S)
e

|

−

f (S)

b
| ≤

²

=

f (S)

Ex[ f (x)χS(x)]. Given random examples (x, f (x)), the
Proof. We have
algorithm can compute f (x)χS(x)
1, 1} and therefore empirically estimate
Ex[ f (x)χS(x)]. A standard application of the Chernoff bound implies that
O(log(1/δ)/²2) examples are sufﬁcient to obtain an estimate within
² with
(cid:3)
probability at least 1

{
−

±

∈

b

δ.

−

The second observation we need to prove Theorem 3.29 is the following:

Proposition 3.31. Suppose that f : {
1, 1}n
satisfy
with sgn(0) chosen arbitrarily from {

². Let h : {

2
2 ≤
k

−

−

g

k

f

−
{
−

1, 1}n
1, 1} and g : {
1, 1} be deﬁned by h(x)

{
−

→

R
1, 1}n
→
sgn(g(x)),

−
=

→
−

1, 1}. Then dist( f , h)

².

≤

Proof. Since

dist( f , h)

=

f (x)

−
[ f (x)

2

g(x)
|
h(x)]

6=

|
Pr
x

1 whenever f (x)

6=

sgn(g(x)), we conclude

≥

[1 f (x)

E
x

sgn(g(x))]
6=

[
E
|
x

≤

=

f (x)

−

g(x)

2]

|

f

g

k

−

= k

2

2. (cid:3)

(See Exercise 3.34 for an improvement to this argument.)

We can now prove Theorem 3.29:

f (S) for

Proof of Theorem 3.29. For each S
to produce an estimate
except with probability at most 1/(10
|
time, and by the union bound, except with probability at most 1/10 all
|
estimates have the desired accuracy. Finally, A forms the real-valued function
sgn(g). By Proposition 3.31, it
g

F the algorithm uses Proposition 3.30
F
p²/(2p
)
|
|
F
, n, 1/²)
F

). Overall this requires poly(
e

f (S)χS and outputs hypothesis h

f (S) which satisﬁes

f (S)

f (S)

| ≤

F

−

∈

e

b

b

F

|

|

|

|

|

=

S

∈

=

P

e

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 13 -->
3.4. Learning theory

81

sufﬁces to show that

f

k

². And indeed,

g

2
2 ≤
−
k
g(S)2

(Parseval)

f

k

−

g

2
2 =
k

=

≤

=

as desired.

f

−

[n]

S
⊆
X

F
S
∈
X

(

(cid:129)
f (S)

−

f (S))2

+

F
S
∉
X

2

e

b

p²
F

F µ
S
∈
X
²/4

2p
|

²/2

+

| ¶
≤

²/2

+

²,

f (S)2

b
(estimates, concentration assumption)

(cid:3)

As we described, Theorem 3.29 reduces the algorithmic task of learning f
to the algorithmic task of identifying a collection F on which f ’s Fourier
spectrum is concentrated. In Section 3.5 we will describe the Goldreich–Levin
algorithm, a sophisticated way to ﬁnd such an F assuming query access to f .
For now, though, we observe that for several interesting concept classes we
don’t need to do any algorithmic searching for F ; we can just take F to be
all sets of small cardinality. This works whenever all functions in C have
low-degree spectral concentration.

1 and let C be a concept class for
The “Low-Degree Algorithm”. Let k
1, 1} in C is ²/2-concentrated up to de-
which every function f : {
{
−
gree k. Then C can be learned from random examples only with error ² in time
poly(nk, 1/²).

1, 1}n

→

−

≥

Proof. Apply Theorem 3.29 with F

k
j

0

=

O(nk).

n
j

≤

{S

=

⊆

[n] :

S

|

| ≤

k}. We have

F

|

| =
(cid:3)

¢

P

¡
The Low-Degree Algorithm reduces the algorithmic problem of learning C
from random examples to the analytic task of showing low-degree spectral
concentration for the functions in C . Using the results of Section 3.1 we can
quickly obtain some learning-theoretic results. For example:

1, let C
Corollary 3.32. For t
I[ f ]
learnable from random examples with error ² in time nO(t/²).

1, 1}n

{ f : {

1, 1}

{
−

→

≥

−

=

|

t}. Then C is

≤

Proof. Use the Low-Degree Algorithm with k
Proposition 3.2.

2t/²; the result follows from
(cid:3)

=

Corollary 3.33. Let C
learnable from random examples with error ² in time nO(pn/²).

1, 1}n

{ f : {

1, 1}

{
−

→

=

−

|

f is monotone}. Then C is

Proof. Follows from the previous corollary and Theorem 2.33.

(cid:3)

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 14 -->
82

3. Spectral structure and learning

You might be concerned that a running time such as nO(pn) does not
seem very efﬁcient. Still, it’s much better than the trivial running time of
O(2n). Further, as we will see in the next section, learning algorithms are
sometimes used in attacks on cryptographic schemes, and in this context even
e
subexponential-time algorithms are considered dangerous.

Continuing with applications of the Low-Degree Algorithm:

²/6}.
Corollary 3.34. For δ
=
Then C is learnable from random examples with error ² in time poly(n1/δ, 1/²).

NSδ[ f ]

{ f : {

1, 1}

{
−

→

−

≤

(0, 1/2], let C

1, 1}n

∈

|

Proof. Follows from Proposition 3.3.

(cid:3)

Corollary 3.35. Let C
−
learnable from random examples with error ² in time nO(log(s/²)).

DTsize( f )

1, 1}n

{ f : {

1, 1}

{
−

→

=

≤

|

s}. Then C is

Proof. Follows from Proposition 3.17.

(cid:3)

With a slight extra twist one can also exactly learn the class of degree-k

functions in time poly(nk); see Exercise 3.36:

k} (e.g., C
{ f : {
Theorem 3.36. Let k
contains all depth-k decision trees). Then C is learnable from random exam-
ples with error 0 in time nk

poly(n, 2k).

1 and let C

deg( f )

1, 1}n

1, 1}

{
−

→

≥

=

≤

−

|

·

3.5. Highlight: the Goldreich–Levin Algorithm

We close this chapter by brieﬂy describing a topic which is in some sense the
“opposite” of learning theory: cryptography. At the highest level, cryptography
is concerned with constructing functions which are computationally easy to
compute but computationally difﬁcult to invert. Intuitively, think about the
task of encrypting secret messages: You would like a scheme where it’s easy
to take any message x and produce an encrypted version e(x), but where it’s
hard for an adversary to compute x given e(x). Indeed, even with examples
e(x(1)), . . . , e(x(m)) of several encryptions, it should be hard for an adversary
to learn anything about the encrypted messages, or to predict (“forge”) the
encryption of future messages.

A basic task in cryptography is building stronger cryptographic functions
from weaker ones. Often the ﬁrst example in “Cryptography 101” is the
Goldreich–Levin Theorem, which is used to build a “pseudorandom generator”
from a “one-way permutation”. We sketch the meaning of these terms and
the analysis of the construction in Exercise 3.45; for now, sufﬁce it to say that
the key to the analysis of Goldreich and Levin’s construction is a learning
algorithm. Speciﬁcally, the Goldreich–Levin learning algorithm solves the
F2, ﬁnd
following problem: Given query access to a target function f : Fn

2 →

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 15 -->
3.5. Highlight: the Goldreich–Levin Algorithm

83

all of the linear functions (in the sense of Chapter 1.6) with which f is at
least slightly correlated. Equivalently, ﬁnd all of the noticeably large Fourier
coefﬁcients of f .

Goldreich–Levin Theorem. Given query access to a target f : {
{
−
with high probability outputs a list L

→
1, there is a poly(n, 1/τ)-time algorithm that
{U1, . . . ,U`} of subsets of [n] such that:

1, 1} as well as input 0

<

−

≤

τ

1, 1}n

=

f (U)

| ≥

τ

• |

=⇒

L;

U

∈

L

U
b

∈

•

=⇒ |

f (U)

τ/2.

| ≥

(By Parseval’s Theorem, the second guarantee implies that

b

4/τ2.)

L

|

| ≤

Although the Goldreich–Levin Theorem was originally developed for cryp-
tography, it was soon put to use for learning theory. Recall that the “meta-
algorithm” of Theorem 3.29 reduces learning an unknown target f : {
→
1, 1} to identifying a collection F of sets on which f ’s Fourier spectrum is
{
−
²/2-concentrated. Using the Goldreich–Levin Algorithm, a learner with query
access to f can “collect up” its largest Fourier coefﬁcients until only ²/2 Fourier
weight remains unfound. This strategy straightforwardly yields the following
result (see Exercise 3.39):

1, 1}n

−

Theorem 3.37. Let C be a concept class such that every f : {
1, 1}
in C has its Fourier spectrum ²/4-concentrated on a collection of at most M
sets. Then C can be learned using queries with error ² in time poly(M, n, 1/²).

1, 1}n

{
−

→

−

The algorithm of Theorem 3.37 is often called the Kushilevitz–Mansour Al-
gorithm. Much like the Low-Degree Algorithm, it reduces the computational
problem of learning C (using queries) to the analytic problem of proving that
the functions in C have concentrated Fourier spectra. The advantage of the
Kushilevitz–Mansour Algorithm is that it works so long as the Fourier spec-
trum of f is concentrated on some small collection of sets; the Low-Degree
Algorithm requires that the concentration speciﬁcally be on the low-degree
characters. The disadvantage of the Kushilevitz–Mansour Algorithm is that
it requires query access to f , rather than just random examples. An example
concept class for which the Kushilevitz–Mansour Algorithm works well is the
set of all f for which ˆ
k
Theorem 3.38. Let C
s} (e.g., C contains
→
any f computable by a decision tree of size at most s). Then C is learnable
from queries with error ² in time poly(n, s, 1/²).

f ˆ
k1 is not too large:
{
−

f ˆ
k1 ≤

1, 1}n

{ f : {

1, 1}

ˆ
k

=

−

|

This is proved in Exercise 3.38.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 16 -->
84

3. Spectral structure and learning

Let’s now return to the Goldreich–Levin Algorithm itself, which seeks
f (U) with magnitude at least τ. Given any candi-
the Fourier coefﬁcients
[n], Proposition 3.30 lets us easily distinguish whether the associ-
date U
ated coefﬁcient is large,
τ/2. The trouble is that
τ, or small,
there are 2n potential candidates. The Goldreich–Levin Algorithm overcomes
this difﬁculty using a divide-and-conquer strategy that measures the Fourier
weight of f on various collections of sets. Let’s make a deﬁnition:

b
f (U)
|

f (U)

| ≥

| ≤

⊆

b

b

|

Deﬁnition 3.39. Let f : {

1, 1}n

−
WS

|

→
J[ f ]

[n]. We write

R and S

⊆

J

f (S

∪

=

T
J
X
⊆

b

⊆
T)2

for the Fourier weight of f on sets whose restriction to J is S.

The crucial tool for the Goldreich–Levin Algorithm is Corollary 3.22,

which says that

WS

|

J[ f ]

=

E
1,1}J

|

[

f J

z(S)2].

(3.5)

z

{
−
∼
This identity lets a learning algorithm with query access to f efﬁciently esti-
d
J[ f ] of its choosing. Intuitively, query access to f allows query
mate any WS
1, 1}J; with this one can estimate any
access to f J
z(S) and
{
−
hence (3.5). More precisely:

|
z for any z

f J

∈

|

|

d

log(1/δ).

·

Proposition 3.40. For any S
f : {
within

1, 1}n

{
−

→

−

J
1, 1} can compute an estimate of WS

[n] an algorithm with query access to
J[ f ] that is accurate to

⊆

⊆

|

² (except with probability at most δ) in time poly(n, 1/²)

±

Proof. From (3.5),

WS

|

J[ f ]

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

=

z

d

E
1,1}J

E
1,1}J "

{
−
∼
E
1,1}J

y

{
−
∼
E
y,y0∼
{
−

=

[ f (y, z)χS(y)]2

[ f (y, z)χS(y)

·

#
f (y0, z)χS(y0)],

z

{
∼
−
f (y0, z)χS(y0)
where y, y0 are independent. As in Proposition 3.30, f (y, z)χS(y)
1-valued random variable that the algorithm can sample from using
is a
queries to f . A Chernoff bound implies that O(log(1/δ)/²2) samples are sufﬁ-
(cid:3)
cient to estimate its mean with accuracy ² and conﬁdence 1

δ.

1,1}J

±

·

−

We’re now ready to prove the Goldreich–Levin Theorem.

Proof of the Goldreich–Levin Theorem. We begin with an overview of
how the algorithm works. Initially, all 2n sets U are (implicitly) put in a
single “bucket”. The algorithm then repeats the following loop:

Select any bucket B containing 2m sets, m

1.

≥

•

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 17 -->
3.6. Exercises and notes

85

Split it into two buckets B1, B2 of 2m
“Weigh” each Bi, i
1, 2; i.e., estimate
Discard B1 or B2 if its weight estimate is at most τ2/2.

1 sets each.
−

f (U)2.

Bi
∈

=

U

P

b

•

•

•

The algorithm stops once all buckets contain just 1 set; it then outputs the
list of these sets.

±

We now ﬁll in the details. First we argue the correctness of the algorithm,
assuming all weight estimates are accurate (this assumption is removed later).
On one hand, any set U with
f (U)
τ will never be discarded, since it
always contributes weight at least τ2
τ2/2 to the bucket it’s in. On the other
hand, no set U with
τ/2 can end up in a singleton bucket because
such a bucket, when created, would have weight only τ2/4
τ2/2 and thus
be discarded. Notice that this correctness proof does not rely on the weight
estimates being exact; it sufﬁces for them to be accurate to within

| ≥
≥

f (U)

τ2/4.

| ≤

≤

b

b

|

|

The next detail concerns running time. Note that any “active” (undis-
carded) bucket has weight at least τ2/4, even assuming the weight estimates
τ2/4. Therefore Parseval tells us there can only
are only accurate to within
ever be at most 4/τ2 active buckets. Since a bucket can be split only n times, it
follows that the algorithm repeats its main loop at most 4n/τ2 times. Thus as
long as the buckets can be maintained and accurately weighed in poly(n, 1/τ)
time, the overall running time will be poly(n, 1/τ) as claimed.

±

Finally, we describe the bucketing system. The buckets are indexed (and
[k]. The

n and a subset S

k

thus maintained implicitly) by an integer 0
bucket Bk,S is deﬁned by

≤

≤

⊆

Bk,S

S

T : T

{k

1, k

2, . . . , n}

.

∪

=

⊆
k. The initial bucket is B0,

+

+

n

o

Bk,S

2n

|

−

;

| =

Note that
splits a bucket Bk,S into the two buckets Bk
ﬁnal singleton buckets are of the form Bn,S
bucket Bk,S is precisely WS

. The algorithm always
1,S and Bk
1}. The
1,S
+
+
{S}. Finally, the weight of
1,...,n}[ f ]. Thus it can be estimated to accuracy
+
log(1/δ) using Proposition 3.40.
±
Since the main loop is executed at most 4n/τ2 times, the algorithm overall
needs to make at most 8n/τ2 weighings; by setting δ
τ2/(80n) we ensure that
all weighings are accurate with high probability (at least 9/10). The overall
(cid:3)
running time is therefore indeed poly(n, 1/τ).

τ2/4 with conﬁdence 1

δ in time poly(n, 1/τ)

−

=

=

{k

{k

+

∪

·

|

3.6. Exercises and notes

3.1 Let M : Fn
let f

2 →
M : Fn

Fn

2 be an invertible linear transformation. Given f : Fn
R be deﬁned by f

f (Mx). Show that

M(x)

f

2 →
M(γ)

R,

◦

2 →

◦
Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.

=

◦

=

ƒ



<!-- pdf-page: 18 -->
86

3. Spectral structure and learning

f (M−>γ). What if M is an invertible afﬁne transformation? What if M is
not invertible?
b
2
e−
−
be taken in Proposition 3.3.

2 is smallest constant (not depending on δ or n) that can

1

3.2 Show that

3.3 Generalize Proposition 3.3 by showing that any f : {
Stab1

concentrated on degree up to 1/δ for ²

(E[ f 2]

=

−

1, 1}n
−
δ[ f ])/(1
−

→
−

R is ²-
1/e).

3.4 Prove Lemma 3.5 by induction on n. (Hint: If one of the subfunctions

f (x1, . . . , xn,
1.)

1) is identically 0, show that the other has degree at most k

±

−

[1,

] that ˆ
k·

∞

ˆ
kp is a norm on the vector space of functions

∈

3.5 Verify for all p

2 →

f : Fn
R.
3.6 Show that ˆ
k
1, 1}n

3.7 Let f : {

f g ˆ

−

→

k1 ≤

ˆ
k

k1 ˆ
f ˆ
k
R and let J

k1 for all f , g : Fn
g ˆ
[n], z

2 →
1, 1}J.

R.

⊆

{
−

∈

(a) Show that restriction reduces spectral 1-norm: ˆ
f ˆ
ˆ
z ˆ
f J
k1.
k1 ≤
k
k
|
f J
f ).
(b) Show that it also reduces Fourier sparsity: sparsity(
sparsity(
z)
≤
|
f ˆ
ˆ
f ˆ
kq. (Cf. Ex-
kp ≥
k
d
b

. Show that ˆ
k

R and let 0

1, 1}n

≤ ∞

→

−

<

≤

p

q

3.8 Let f : {

ercise 1.13.)

3.9 Let f : {

1, 1}n

−

R. Show that ˆ
k

f ˆ
k∞ ≤ k

f

1 and
k

→

f

k

k∞ ≤

ˆ
k

f ˆ
k1. (These are

easy special cases of the Hausdorff–Young Inequality.)

f (i) when-
3.10 Suppose f : {
| ≤
ever i
} is achieved by an S of
cardinality 0 or 1. (Hint: Apply the previous exercise to f ’s derivatives.)

1, 1} is monotone. Show that
maxS{
|

−
→
[n]. Deduce that ˆ
k

f ˆ
k∞ =

f (S)
|

f (S)

{
−

⊆

S

∈

b

b

|

1, 1}n

3.11 Prove Proposition 3.12.

b

3.12 Verify Parseval’s Theorem for the Fourier expansion of subspaces given

in Proposition 3.11.

3.13 Let f : Fn

{0, 1} be the indicator of A

f ˆ
k1 =
is an afﬁne subspace. So assume that A is not an afﬁne subspace.
(a) Show that there exists an afﬁne subspace B of dimension 2 on which f

2 . We know that ˆ
k

2 →

1 if A

⊆

Fn

takes the value 1 exactly 3 times.

(b) Let b be the point in B where f is 0 and let ψ

ψˆ
that ˆ
k
(c) Show that

1/2.
k∞ =
ψ, f
〈
1, 1}n

〉 =

3/4 and deduce ˆ
k
R satisﬁes E[ f 2]

f ˆ
k1 ≥

3/2.

3.14 Suppose f : {

2n/2, and
show that for any even n the upper bound can be achieved by a function
f : {

1. Show that ˆ
k

f ˆ
k1 ≤

1, 1}n

→

≤

−

{
→
−
−
3.15 Given f : Fn
2 →

1, 1}.
R, deﬁne its (fractional) sparsity to be

ϕB

−

=

(1/2)ϕb. Show

sparsity( f )

supp( f )
|

= |

/2n

=

Pr
Fn
x
2
∈

[ f (x)

0].

6=

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 19 -->
3.6. Exercises and notes

87

·

f )

sparsity(

In this exercise you will prove the uncertainty principle: If f is nonzero,
then sparsity( f )
≥
(a) Show that we may assume
(b) Suppose F
(c) Suppose G

, and deduce the

1
k
b
0}. Show that ˆ
6=
k
0}. Show that
6=

f (γ)
{γ :
{x : f (x)
b
uncertainty principle.

2
f ˆ
2 ≤ |
k
2
f
2 ≥
k

F
.
|
2n/

=
=

1.

1.

=

G

k

k

f

|

|

(d) Identify all cases of equality.

−

1, 1}n

3.16 Let f : {

collection F

0. Show that f is ²-concentrated on a
>
2
f ˆ
1/².
k
3.17 Suppose the Fourier spectrum of f : {
−
f

R is ²1-concentrated on F
²2. Show that the Fourier

R and let ²
ˆ
F
k

→
2[n] with

| ≤

⊆

|

1, 1}n
→
R satisﬁes
2
g
2 ≤
k
²2)-concentrated on F .

−

k

1, 1}n
and that g : {
spectrum of g is 2(²1

−

3.18 Show that every function f : Fn

R is computed by a decision tree with

→
+

depth at most n and size at most 2n.

2 →

3.19 Let f : Fn
Show that
trees of size s and depth k.

2 →
−

R be computable by a decision tree of size s and depth k
f and the Boolean dual f † are also computable by decision

3.20 For each function in Exercise 1.1 with 4 or fewer inputs, give a decision
tree computing it. Try primarily to use the least possible depth, and
secondarily to use the least possible size.

3.21 Prove Proposition 3.16.
3.22 Let f : Fn

{
−

2 →

1, 1} be computed by a decision tree T of size s and let ²

∈
(0, 1]. Suppose each path in T is truncated (if necessary) so that its length
does not exceed log(s/²); new leaves with labels
1 and 1 may be created
in an arbitrary way as necessary. Show that the resulting decisions tree
T0 computes a function that is ²-close to f . Deduce Proposition 3.17.

−

3.23 A decision list is a decision tree in which every internal node has an
outgoing edge to at least one leaf. Show that any function computable by
a decision list is a linear threshold function.

3.24 A read-once decision tree is one in which every internal node queries a
distinct variable. Bearing this in mind, show that the bound k2k
1 in
−
Theorem 3.4 cannot be reduced below 2k

1.

3.25 Suppose that f is computed by a read-once decision tree in which every
root-to-leaf path has length k and every internal node at the deepest level
has one child (leaf) labeled
1 and one child labeled 1. Compute the
inﬂuence of each coordinate on f , and compute I[ f ].

−

−

3.26 The following are generalizations of decision trees:

Subcube partition: This is deﬁned by a collection C1, . . . , Cs of sub-
R. It

cubes that form a partition of Fn

2 , along with values b1, . . . , bs

∈

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 20 -->
88

3. Spectral structure and learning

computes the function f : Fn
R which has value bi on all inputs in Ci.
The subcube partition’s size is s and its “codimension” k (analogous to
depth) is the maximum codimension of the cubes Ci.

2 →

Parity decision tree: This is similar to a decision tree except that
2 . At such a node the
the internal nodes are labeled by vectors γ
computation path on input x follows the edge labeled γ
x. We insist that
for each root-to-leaf path, the vectors appearing in its internal nodes are
linearly independent. Size s and depth k are deﬁned as with normal
decision trees.

Fn

∈

·

Afﬁne subspace partition: This is similar to a subcube partition except

the subcubes Ci may be arbitrary afﬁne subspaces.
(a) Show that subcube partition size/codimension and parity decision
tree size/depth generalize normal decision tree size/depth, and are
generalized by afﬁne subspace partition size/codimension.

(b) Show that Proposition 3.16 holds also for the generalizations, except
that the statement about degree need not hold for parity decision
trees and afﬁne subspace partitions.

(c) Show that the class of functions with afﬁne subspace partition size at
most s is learnable from queries with error ² in time poly(n, s, 1/²).

1, 1}3

3.27 Deﬁne Equ3 : {

−

{
−
(a) Show that deg(Equ3)
=
(b) Show that DT(Equ3)
=
(c) Show that Equ3 is computable by a parity decision tree of codimen-

1, 1} by Equ3(x)
2.
3.

1 if and only if x1

= −

x3.

x2

→

=

=

sion 2.

(d) For d

N, deﬁne f {

1, 1}3d

∈

−
from Deﬁnition 2.6). Show that deg( f )
R and J

1, 1}n

→

3.28 Let f : {
⊆
→
1,1}J [ f (xJ, y)], where xJ
Ey
{
−
∼
nates J. Verify the Fourier expansion

{
−

−

∈

=

1, 1} by f

{
−

d

Equ⊗
3
=
2d but DT( f )

(using the notation

=

3d.
R by f (x)

[n]. Deﬁne f ⊆

1, 1}n
=
1, 1}J is the projection of x to coordi-

J : {

→

−

f (S) χS.

J

f ⊆

=

J
S
⊆
X

b

3.29 Let ϕ : Fn

2 →

0 be a probability density function corresponding to prob-

R≥
ability distribution φ on Fn
⊆
(a) Consider the marginal probability distribution of φ on coordinates J.
0) in

What is its probability density function (a function FJ
terms of ϕ?

2 . Let J

2 →

R≥

[n].

(b) Consider the probability distribution of φ conditioned on a substring
2 . Assuming it’s well deﬁned, what is its probability density

FJ

z
function in terms of ϕ?

∈

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 21 -->
3.6. Exercises and notes

89

3.30 Suppose f : {

1, 1}n

−

R is computable by a decision tree that has a leaf
/2k.
(Hint: You may ﬁnd

b

→

at depth k labeled b. Show that ˆ
k
Exercise 3.28 helpful.)

f ˆ
k∞ ≥ |

|

3.31 Prove Fact 3.25 by using Theorem 1.27 and Exercise 1.1(d).
3.32 (a) Suppose f : Fn
supp(
coefﬁcient.

2 →
f ) there exists nonzero β

R has sparsity(
Fn

2 such that fβ⊥

has

f )

<

∈

b
(b) Prove by induction on n that if f : Fn
log s

c

b
f is 21

1, 1} has sparsity(
2 →
c-granular. (Hint: Distinguish the cases s

{
−

−b

b

2n. Show that for any γ

∈
f (γ) as a Fourier

f )

s
1
=
>
2n and

=
b

then
s

<

2n. In the latter case use part (a).)

(c) Prove that there are no functions f : {

b

1, 1}n

−

1, 1} with sparsity(

{
−

f )

∈

→

{2, 3, 5, 6, 7, 9}.

3.33 Show that one can learn any target f : {

random examples only in time

O(2n).

1, 1}n

−

b
1, 1} with error 0 from

{
−

→

3.34 Improve Proposition 3.31 as follows. Suppose f : {

e
g
1
k
{
−

−
→

². Pick θ
≤
1, 1} by h(x)

∈
=

1, 1}n

−

1, 1} and
{
−
1, 1] uniformly at ran-
θ). Show that

[
−
sgn(g(x)

→

−

R satisfy

−

1, 1}n

g : {
dom and deﬁne h : {
E[dist( f , h)]

²/2.

→

−

f
k
1, 1}n

≤

3.35 (a) For n even, ﬁnd a function f : {
concentrated on any F
1, 1}n

1, 1} such that f is not 1/2-
1. (Hint: Exercise 1.1.)
−
1, 1} be a random function as in Exercise 1.7. Show
that with probability at least 1/2, f is not 1/4-concentrated on degree
up to

(b) Let f : {

2[n] with

→
| <

{
−
2n

{
−

→

−

⊆

−

|

1, 1}n
F

n/2
.
c

b

3.36 Prove Theorem 3.36. (Hint: In light of Exercise 1.11 you may round off

certain estimates with conﬁdence.)

3.37 Show that each of the following classes C (ordered by inclusion) can be
learned exactly (i.e., with error 0) using queries in time poly(n, 2k):
(a) C
(b) C
(c) C

f is a k-junta}. (Hint: Estimate inﬂuences.)
DT( f )
≤
sparsity(

2O(k)}. (Hint: Exercise 3.32.)

1, 1}n
1, 1}n
1, 1}n

{ f : {
{ f : {
{ f : {

1, 1}
1, 1}
1, 1}

k}.
f )

{
−
{
−
{
−

→
→
→

|
|
|

=
=
=

−
−
−

≤
3.38 Prove Theorem 3.38. (Hint: Exercise 3.16.)

b

3.39 Deduce Theorem 3.37 from the Goldreich–Levin Algorithm.
3.40 Suppose A learns C from random examples with error ²/2 in time T –

with probability at least 9/10.
(a) After producing hypothesis h on target f : {

1, 1}, show that
A can “check” whether h is a good hypothesis in time poly(n, T, 1/²)
·
log(1/δ). Speciﬁcally, except with probability at most δ, A should out-
². (Hint: Time poly(T)
²/2 and ‘NO’ if dist( f , h)
put ‘YES’ if dist( f , h)
may be required for A to evaluate h(x).)

{
−

→

≤

>

−

1, 1}n

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 22 -->
90

3. Spectral structure and learning

(b) Show that for any δ

∈

(0, 1/2], there is a learning algorithm that learns
log(1/δ) – with probability at least

C with error ² in time poly(n, T, ²)
1

δ.

·

−

3.41 (a) Our description of the Low-Degree Algorithm with degree k and er-
ror ² involved using a new batch of random examples to estimate each
low-degree Fourier coefﬁcient. Show that one can instead simply draw
a single batch E of poly(nk, 1/²) examples and use E to estimate each
of the low-degree coefﬁcients.

(b) Show that when using the above form of the Low-Degree Algorithm,

the ﬁnal hypothesis h : {

1, 1}n

−

1, 1} is of the form

{
−

→

h(y)

sgn

=

Ã

E

(x, f (x))
X

∈

w(∆(y, x))

f (x)

,

!

·

R. In other words, the hypothe-
for some function w : {0, 1, . . . , n}
→
sis on a given y is equal to a weighted vote over all examples seen,
where an example’s weight depends only on its Hamming distance
to y. Simplify your expression for w as much as you can.

3.42 Extend the Goldreich–Levin Algorithm so that it works also for functions
f : {
1, 1]. (The learning model for targets f : {
1, 1]
assumes that f (x) is always a rational number expressible by poly(n)
bits.)

1, 1}n

1, 1}n

[
−

→

→

−

−

−

[

Fn

3.43 (a) Assume γ, γ0
(b) Fix γ

Fn

∈

2 are distinct. Show that Prx[γ

x

γ0

x]

1/2.

∈

2 and suppose x(1), . . . , x(m)

c
independently. Show that if m
then with high probability, the only γ0
for all i

[m] is γ0

c

γ.

=

·

∼

=

Fn

·
2 are drawn uniformly and
Cn for C a sufﬁciently large constant
x(i)
2 satisfying γ0

x(i)

Fn

=

γ

·

=

·

∈

∈

=

(c) Essentially improve on Exercise 1.27 by showing that the concept
F2 can be learned from random
R is such
n matrix multiplication can be done in O(nω) time, then the

class of all linear functions Fn
examples only, with error 0, in time poly(n). (Remark: If ω
that n
learning algorithm also requires only O(nω) time.)

2 →

×

∈

c

3.44 Let τ

+

≥

1/2

² for some constant ²

0. Give an algorithm simpler than
>
Goldreich and Levin’s that solves the following problem with high proba-
1, 1}n
bility: Given query access to f : {
1, 1}, in time poly(n, 1/²) ﬁnd
→
−
the unique U
f (U)
τ, assuming it exists. (Hint: Use
Proposition 1.31 and Exercise 1.27.)

[n] such that

{
−

| ≥

⊆

|

b
3.45 Informally: a “one-way permutation” is a bijective function f : Fn

Fn
2
that is easy to compute on all inputs but hard to invert on more than a
negligible fraction of inputs; a “pseudorandom generator” is a function g :
Fk
k whose output on a random input “looks unpredictable”
to any efﬁcient algorithm. Goldreich and Levin proposed the following

2 for m

2 →

2 →

Fm

>

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 23 -->
3.6. Exercises and notes

91

construction of the latter from the former: for k

2n, m

2n

+

=

=

1, deﬁne

g(r, s)

=

(r, f (s), r

s),

·

Fn

∈

2 . When g’s input (r, s) is uniformly random, then so is the
where r, s
ﬁrst 2n bits of its output (using the fact that f is a bijection). The key to
the analysis is showing that the ﬁnal bit, r
s, is highly unpredictable to
efﬁcient algorithms even given the ﬁrst 2n bits (r, f (s)). This is proved by
contradiction.
(a) Suppose that an adversary has a deterministic, efﬁcient algorithm A

·

good at predicting the bit r

s:

·

[A(r, f (s))

Pr
∼

Fn
2

r,s

s]

r

·

≥

=

1
2 +

γ.

Show there exists B

Fn

2 with

/2n

B

|

|

≥

⊆

Pr
Fn
r
2
∼

[A(r, f (s))

s]

r

·

≥

=

1
2 γ such that
1
2 +

1
2

γ

B.
for all s
(b) Switching to
B.

∈

s

∈

1 notation in the output, deduce

±

f (s)(s)

A

|

≥

γ for all

(c) Show that the adversary can efﬁciently compute s given f (s) (with
high probability) for any s
B. If γ is nonnegligible, this contradicts
the assumption that f is “one-way”. (Hint: Use the Goldreich–Levin
Algorithm.)

∈

ƒ

(d) Deduce the same conclusion even if A is a randomized algorithm.

Notes. The fact that the Fourier characters χγ : Fn
1, 1} form a group
isomorphic to Fn
2 is not a coincidence; the analogous result holds for any ﬁnite
abelian group and is a special case of the theory of Pontryagin duality in
harmonic analysis. We will see further examples of this in Chapter 8.

2 →

{
−

f )
Regarding spectral structure, Karpovsky [Kar76] proposed sparsity(
as a measure of complexity for the function f . Brandman’s thesis [Bra87]
b
(see also [BOH90]) is an early work connecting decision tree and subcube
partition complexity to Fourier analysis. The notation introduced for restric-
tions in Section 3.3 is not standard; unfortunately there is no standard nota-
tion. The uncertainty principle from Exercise 3.15 dates back to Matolcsi and
Szücs [MS73]. The result of Exercise 3.13 is due to Green and Sanders [GS08],
with inspiration from Saeki [Sae68]. The main result of Green and Sanders
is the sophisticated theorem that any f : Fn
s can be
expressed as

{0, 1} with ˆ
k

2 →
and each Hi

f ˆ
k1 ≤

1Hi , where L

22poly(s)

L
i

1 ±
=

≤

P

Theorem 3.4 is due to Nisan and Szegedy [NS94]. That work also showed
a nontrivial kind of converse to the ﬁrst statement in Proposition 3.16: Any f :
1, 1} is computable by a decision tree of depth at most poly(deg( f )).
{
−

1, 1}n

{
−

→

Fn
2 .

≤

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 24 -->
92

3. Spectral structure and learning

The best upper bound currently known is deg( f )3 due to Midrij ¯anis [Mid04].
Nisan and Szegedy also gave the example in Exercise 3.27 showing the depen-
dence cannot be linear.

The ﬁeld of computational learning theory was introduced by Valiant
in 1984 [Val84]; for a good survey with focus on learning under the uni-
form distribution, see the thesis by Jackson [Jac95]. Linial, Mansour, and
Nisan [LMN93] pioneered the Fourier approach to learning, developing the
Low-Degree Algorithm. We present their strong results on constant-depth
circuits in Chapter 4. The noise sensitivity approach to the Low-Degree Al-
gorithm is from Klivans, O’Donnell, and Servedio [KOS04]. Corollary 3.33
is due to Bshouty and Tamon [BT96] who also gave certain matching lower
bounds. Goldreich and Levin’s work dates from 1989 [GL89]. Besides its
applications to cryptography and learning, it is important in coding theory
and complexity as a local list-decoding algorithm for the Hadamard code. The
Kushilevitz–Mansour algorithm is from their 1993 paper [KM93]; they also
are responsible for the results of Exercise 3.37(b) and 3.38. The results of
Exercise 3.32 and 3.37(c) are from Gopalan et al. [GOS+11].

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.


