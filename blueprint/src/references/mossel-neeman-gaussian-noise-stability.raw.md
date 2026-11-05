<!-- generated-by: proofmatch local extraction -->
<!-- source-pdf-sha256: b53c1a5aa27d0b526ee170ef1dd81e525a7c661ce586b811f68ddc6b60525352 -->
<!-- extractor: pdfminer.six v20260107 -->

<!-- pdf-page: 1 -->
3
1
0
2

b
e
F
2
2

]

R
P
.
h
t
a
m

[

3
v
6
2
1
4
.
0
1
2
1
:
v
i
X
r
a

Robust Optimality of Gaussian Noise Stability

Elchanan Mossel∗and Joe Neeman†

September 3, 2018

Abstract

We prove that under the Gaussian measure, half-spaces are uniquely the most noise
stable sets. We also prove a quantitative version of uniqueness, showing that a set which
is almost optimally noise stable must be close to a half-space. This extends a theorem
of Borell, who proved the same result but without uniqueness, and it also answers a
question of Ledoux, who asked whether it was possible to prove Borell’s theorem using a
direct semigroup argument. Our quantitative uniqueness result has various applications
in diverse ﬁelds.

1

Introduction

Gaussian stability theory is a rich extension of Gaussian isoperimetric theory. As such it
connects numerous areas of mathematics including probability, geometry [9], concentration
and high dimensional phenomena [33], re-arrangement inequalities [10, 20] and more. On
the other hand, this theory has recently found fascinating applications in combinatorics and
theoretical computer science. It was essential in [36] for proving the “majority is stablest”
conjecture [21, 27], the “it ain’t over until it’s over” conjecture [23], and for establishing the
unique games computational hardness [26] of numerous optimization problems including, for
example, constraint satisfaction problems [2, 16, 28, 39].

The standard measure of stability of a set is the probability that positively correlated
standard Gaussian vectors both lie in the set. The main result in this area, which is used
in all of the applications mentioned above, is that half-spaces have optimal stability among
all sets with a given Gaussian measure. This fact was originally proved by Borell [9], in
a diﬃcult proof using Ehrhard symmetrization. Recently, two diﬀerent proofs of Borell’s
result have emerged. First, Isaksson and the ﬁrst author [20] applied some recent advances
in spherical symmetrization [10] to give an proof that also generalizes to a problem involving
more than two Gaussian vectors. Then Kindler and O’Donnell [29], using the sub-additivity
idea of Kane [24], gave a short and elegant proof, but only for sets of measure 1
2 and for
/
some special values of the correlation.

In this paper, we will give a novel proof of Borell’s result.

In doing so, we answer a
question posed 18 years ago by Ledoux [31], who used semigroup methods to show that
Borell’s inequality implies the Gaussian isoperimetric inequality and then asked whether
similar methods could be used to give a short and direct proof of Borell’s inequality. Moreover,
our proof will allow us to strengthen Borell’s result and its discrete applications. First, we will

U.C. Berkeley. Supported by grants NSF (DMS 1106999 ) and ONR (DOD ONR N000141110140)
∗
†U.C. Berkeley. Supported by grants NSF (DMS 1106999 ) and ONR (DOD ONR N000141110140)

1

 
 
 
 
 
 


<!-- pdf-page: 2 -->
demonstrate that half-spaces are the unique optimizers of Gaussian stability (up to almost
sure equality). Then we will quantify this statement, by showing that if the stability of a set
is close to optimal given its measure, then the set must be close to a half-space.

The questions of equality and robustness of isoperimetric inequalities can be rather more
subtle than the inequalities themselves. In the case of the standard Gaussian isoperimetric
result, it took about 25 years from the time the inequality was established [8, 40] before the
equality cases were fully characterized [11] (although the equality cases among suﬃciently
nice sets were known earlier [17]). Robust versions of the standard Gaussian isoperimetric
result were ﬁrst established only recently [13, 35]. Here, for the ﬁrst time since Borell’s
original proof [9] more than 25 years ago, we establish both that half-spaces are the unique
maximizers and that a robust version of this statement is also true.

1.1 Discrete applications

x
{

∶ ∑

.
}

≤

From our Gaussian results, we derive robust versions of some of the main discrete applications
of Borell’s result, including a robust version of the “majority is stablest” theorem [36]. The
n with the
1, 1
“majority is stablest” theorem concerns subsets A of the discrete cube
}
property that each coordinate xi has only a small inﬂuence on whether x
A (see [36] for
a precise deﬁnition); the theorem says that over all such sets A, the ones with that are
x
. From the results we prove here, it is
most noise stable take the form
}
{
n with small
possible to obtain a robust version of this, which says that any sets A
1, 1
}
coordinate inﬂuences and almost optimal noise sensitivity must be close to some set of the
form

{−
∈

⊂ {−

aixi

∶ ∑

≤

b

b

aixi

A robust form of the “majority is stablest” theorem immediately implies a robust version
of the quantitative Arrow theorem. In economics, Arrow’s theorem [1] says that any non-
dictatorial election system between three candidates which satisﬁes two natural properties
(namely, the “independence of irrelevant alternatives” and “neutrality”) has a chance of
producing a non-rational outcome. (By non-rational outcome, we mean that there are three
candidates, A, B and C say, such that candidate A is preferred to candidate B, B is preferred
to C and C is preferred to A.) Kalai [21, 22] showed that if the election system is such that
each voter has only a small inﬂuence on the outcome, then the probability of a non-rational
outcome is substantial; moreover, the “majority is stablest” theorem [36] implies that the
probability of a non-rational outcome can be minimized by using a simple majority vote to
decide, for each pair of candidates, which one is preferred. A robust version of the “majority
is stablest” theorem implies immediately that (weighted) majority-based voting methods are
essentially the only low-inﬂuence methods that minimizes the probability of a non-rational
outcome.

In a diﬀerent direction, our robust noise stability result has an application in hardness of
approximation, speciﬁcally in the analysis of the well-known Max-Cut optimization problem.
The Max-Cut problem seeks a partition of a graph G into two pieces such that the number
of edges from one piece to the other is maximal. This problem is NP-hard [25] but Goemans
and Williamson [19] gave an approximation algorithm with an approximation ratio of about
0.878. Their algorithm works by embedding the graph G on a high-dimensional sphere and
then cutting it using a random hyperplane. Feige and Schechtman [18] showed that a random
hyperplane is the optimal way to cut this embedded graph; with our robust noise stability
theorem, we can show that any almost-optimal cutting procedure is almost the same as using
a random hyperplane. The latter result is derived via a novel isoperimetric result for spheres
in high dimensions where two points are connected if their inner product is exactly some

2



<!-- pdf-page: 3 -->
prescribed number ρ.

1.2 Borell’s theorem and a functional variant

Let γn be the standard Gaussian measure on Rn. For
1 let X and Y be jointly
Gaussian random vectors on Rn, such that X and Y are standard Gaussian vectors and
EXiYj
δijρ. We will write Prρ for the joint probability distribution of X and Y . We will
also write φ for the density of γ1 and Φ for its distribution function:

−

<

<

=

ρ

1

x
φ
(

) =

x2

e−

2
/

1
√2π
x

y
φ
(

)

dy.

Φ

x
(

) = ∫
ρ

<
A1, Y

<
A2

∈

∈

Theorem 1.1 (Borell [9]). For any 0

Prρ

X
(

∈

where

−∞
1 and any measureable A1, A2

Rn,

⊂

Prρ

X
(

∈

) ≤

B1, Y

B2

)

∈

(1.1)

B1

= {

x

x

and B2

Rn

Rn

∶

x1

x1

≤

1
Φ−
1
Φ−

γn
(
γn
(

A1
(
A2
(

))}

= {
are parallel half-spaces with the same volumes as A1 and A2 respectively.

))}

≤

∈

∶

If

ρ

1

−

<

<

0 then the inequality (1.1) is reversed.

Like many other inequalities about sets, Theorem 1.1 has a functional analogue. To state

it, we deﬁne the function

≤
Theorem 1.2. For any measurable functions f, g

) =

) =

J

x, y; ρ
(

Prρ

X1
(

J

x, y
(

1
Φ−

, Y1
x
(
)
Rn →

0, 1

∶

1
Φ−

y
(

.
))

≤

and any 0

ρ

<

<

1,

EρJ

f

X

, g

Y

; ρ

J

Ef, Eg; ρ
]
[

≤

(1.2)

If

ρ

1

−

<

<

(
0 then the inequality (1.2) is reversed.

)

(

)

)

(

(

)

0, 0

To see that Theorem 1.2 generalizes Theorem 1.1, consider f
X

1A2. Note
that J
1, 1
A2 and
so the left hand side (resp. right hand side) of Theorem 1.2 is the same as the left hand side
)
(resp. right hand side) of Theorem 1.1.

1A1 and g
1X

1. Thus, J

0, while J

=
A1,Y

=
, g

1, 0

0, 1

))

Y

J

J

=

=

=

=

=

f

)

)

(

(

)

(

(

(

)

(

(

∈

∈

In fact, we can also go in the other direction and prove Theorem 1.2 from Theorem 1.1:
g

1
1 to be the epigraphs of Φ−
+

, deﬁne A1, A2

1
f and Φ−

Rn →

0, 1

Rn

○

○

given f, g
respectively. It can be easily checked, then, that
]

⊂

[

∶

EρJ

f

X

, g

Y

; ρ

Prρ

˜X

A1, ˜Y

A2

∈
where ˜X and ˜Y are standard Gaussian vectors on Rn
hand, Ef

and Eg

(
A2

(
γn

A1

γn

=

(

)

1

1

)

)
and so the deﬁnition of J implies that

=

(

)

∈
1 with E ˜Xi ˜Yi
+

=

+

=

+

δijρ. On the other

(

)

J

Ef, Eg; ρ
)
(

Prρ

˜X

B1, ˜Y

∈

B2

∈

=

(

)

(

3

)



<!-- pdf-page: 4 -->
+

where B1 and B2 are parallel half-spaces with the same volumes as A1 and A2. Thus,
1 dimensions implies Theorem 1.2 in n dimensions.
Theorem 1.1 in n

However, we will give a proof of Theorem 1.2 that does not rely on Theorem 1.1. We do
this for two reasons: ﬁrst, we believe that our proof of Theorem 1.2 is simpler than existing
proofs of Theorem 1.1. More importantly, our proof of Theorem 1.2 is a good starting point
for the main results of the paper.
In particular, it allows us to characterize the cases of
equality and near-equality. As we mentioned earlier, it is not known how to get such results
from existing proofs of Theorem 1.1.

1.3 New results: Equality

In our ﬁrst main result, we get a complete characterization of the functions for which equality
in Theorem 1.2 is attained.

Theorem 1.3. For any measurable functions f, g
∶
if equality is attained in (1.2) then there exist a, b, d

0, 1

1
−
Rn such that either

and any

Rn →

ρ

<

<

1 with ρ

0,

≠

or

f

x

g

x
(

=

)

=

Φ

Φ

a, x

a, x

(⟨

−

−

(

)

(⟨

b

d
⟩)

⟩)

]

∈

[
a.s.

a.s.

−
In particular, the second case of Theorem 1.3 implies that if A1 and A2 achieve equality

⟩≥

(

)

f

g

x

x
(

)

1
a,x
⟨
1
a,x
⟨

=

=

b
⟩≥
−
d

0 a.s.
0 a.s.

in Theorem 1.1 then A1 and A2 must be almost surely equal to parallel half-spaces.

1.4 New results: Robustness

f

X

Once we know the cases of equality, the next natural thing to ask is whether they are robust:
if f and g almost achieve equality in (1.2) – in the sense that EρJ
δ
−
– does it follow that f and g must be close to some functions of the form Φ
? In
)
))
the case of the Gaussian isoperimetric inequality, which can be viewed as a limiting form
of Borell’s theorem, the question of robustness was ﬁrst addressed by Cianchi et al. [13],
who showed that the answer was “yes,” and gave a bound that depended on both δ and n.
The authors [35] then proved a similar result which had no dependence on n, but a worse
(logarithmic, instead of polynomial) dependence on δ. The arguments we will apply here are
similar to those used in [35], but with some improvements. In particular, we establish a result
with no dependence on the dimension, and with a polynomial dependence on δ (although we
suspect that the exponent is not optimal).

Ef, Eg
b

J
a, x
(

, g

⟩)

(⟨

−

Y

≥

(

(

)

(

Theorem 1.4. For measurable functions f, g

∶
Ef, Eg

Rn →

0, 1

, deﬁne

EρJ
[

f

X
]

, g

Y

−

(1.3)

δ

f, g

δ

=

J

=

and let

)
m

(
m

=

(

f, g

Ef

=

)
1

−

Ef

))

(
Eg

(
1

(
Eg

.

)

−

(

)

(

)

(

)

4



<!-- pdf-page: 5 -->
For any 0
exist a, b, d

<
∈

1, there exist 0

ρ
Rn such that

<

c

ρ

, C

ρ

<

< ∞

such that for any f, g

Rn →

0, 1

there

∶

E

f

X

E

g
∣

X
(

)

−

−

(
)
a, X

Φ

Φ

(⟨

a, X

)

(
b

d

⟩)∣

−

−

≤

≤

C

ρ

mc

ρ
)δ
(

C

ρ
(

mc
)

ρ
)δ
(

1
4 (

1
4 (

[

]

2

2

)

)

.

ρ

1
3ρ
−

ρ

1
3ρ
−

1

1

−

−

ρ
1
)(
+

ρ
1
)(
+

∣

)

(

We should mention that a more careful tracking of constants in our proof would improve
the exponent of δ slightly. However, this improvement would not bring the exponent above
1
4 and it would not prevent the exponent from approaching zero as ρ → 1.

⟩)∣

(⟨

Although Theorem 1.4 is stated only for 0

0
follows from certain symmetries. Indeed, one can easily check from the deﬁnition of J that
J

1, the same result for

. Taking expectations,

x, y; ρ

y;

−

x

J

<

<

<

<

ρ

ρ

ρ

1

(

)

=

−

x, 1
−
EρJ

(

−
X

f

(

)

Now, suppose that

(

−

(
1

)
ρ
<
<
EρJ

, g

Y

; ρ

)

=

Ef
Ef

−

EρJ
E
ρJ
(
−

f

X

g

Y

, 1
−
, 1

f
(

X
)

−

ρ

;

;
Y
−
)

ρ

.

)

)

=

(
0 and that f, g almost attain equality in Theorem 1.2:

−
)

−

−

)

)

f

X

, g

Y

; ρ

J

≤

(

(
)
Ef, Eg; ρ

g
(

+

(
δ.

Setting ˜g

y

g

1

−

y

−

=

, this implies that
(
Y

)
, ˜g

(
X

(
f

E

ρJ
−

(

)

)
ρ

)
;

−

(
J

≥

Ef, E˜g;

)
ρ

−

δ.

−

(

)
ρ

1, we can apply Theorem 1.4 to f and ˜g to conclude that f and ˜g are close to
Since 0
)
the equality cases of Theorem 1.3, and it follows that f and g are also close to one of these
1.
equality cases. Therefore, we will concentrate for the rest of this article on the case 0

< −

<

ρ

)

(

(

)

(

(

)

<

<

1.5 Optimal dependence on ρ in the case f = g

The dependence on ρ in Theorem 1.4 is particularly interesting as ρ → 1, since it is in
that limit that Borell’s inequality recovers the Gaussian isoperimetric inequality. As it is
stated, however, Theorem 1.4 does not recover a robust version of the Gaussian isoperimetric
inequality because of its poor dependence on ρ as ρ → 1. In particular, as ρ → 1, the constant
C

ρ, ǫ
It turns out that this poor dependence on ρ is necessary in some sense. For example, let

grows to inﬁnity, and the exponent of δ tends to zero.

(

)

f

x

g

x
(

)

=

=

x1

x1

1
{
1
{

0

}
2,x2

<

<

<

0 or x1

1,x2

<

.

0

}

≥

Then

Prρ

f

X

1, g

X

=

(

)

0

=

≤

Prρ

X1

0, Y1

1

≥

≤

exp

<

2

1

1

−

,

ρ2

which tends to zero very quickly as ρ → 1. In particular, this means that as ρ → 1, δ
f, g
tends to zero exponentially fast even though g is a constant distance away from a half-space.
)
Thus, the constant C

must blow up as ρ → 1. Similarly, if we redeﬁne g as

ρ, ǫ

)

(

(

)

(

(

)

(

)

)

(

)

(

1
≤
+
then we see that the exponent of δ in Theorem 1.4 must tend to zero as ρ → 1.
We can, however, avoid examples like the above if we restrict to the case f

,x2
)

,x2
)

0 or x1

δ
(

δ
(

x1

=

(

)

(

)

O

O

−

<

<

≥

}

1

0

g

x

1
{

case, it turns out that δ
rate for recovering the Gaussian isoperimetric inequality.
)

grows only like

f, f

−

ρ

1

(

(

)

−

g. In this
2 as ρ → 1, which is exactly the right
1
/

=

5



<!-- pdf-page: 6 -->
Theorem 1.5. For every ǫ
with Ef
any f

Rn →

0, 1

∶

>
=

0, there is a ρ0
1

<
2, there exists a

Rn such that

∈

1 and a C

ǫ

such that for any ρ0

ρ

<

<

1 and

[

]

E

/
X

f

Φ

a, X

C

ǫ

−

ρ
)
(
2 is there for technical reasons, and we do not believe that it is

⟩)∣

)(

(⟨

≤

)

)

(

1
4

ǫ
−

.

δ

(
)
f, f
1
(
√

−

The requirement Ef

necessary (see Conjecture 6.9).

∣
1

=

/

By applying Ledoux’s result [32] connecting Borell’s inequality with the Gaussian isoperi-
metric inequality, Theorem 1.5 has the following corollary (for the deﬁnition of Gaussian
surface area, see [35]):

2 and A has Gaussian surface area less than 1

0, there is a C

ǫ

< ∞

such that for every set A

Rn such that
δ, there is a half-space B such

⊂

A

Corollary 1.6. For every ǫ
Pr
that
(

=

1

)

/

>

(

)

√2π +

Pr

A∆B

C

ǫ

4
δ1
/

ǫ.
−

≤

This should be compared with the work of Cianchi et al. [14], who gave the best possible

(

)

(

)

dependence on δ, but suﬀered some unspeciﬁed dependence on n:

Theorem 1.7. For every n and every a
Rn such that Pr
every set A
A
there is a half-space B such that
)

⊂

=

(

∈

(

)

0, 1

, there is a constant C

n, a

a and A has Gaussian surface area less than φ

such that for
δ,
a

1
Φ−

+

(

)

Pr

A∆B

C

n, a

2.
δ1
/

≤

(

(

))

)

(

Note that Theorem 1.7 is stronger than Corollary 1.6 in two senses, but weaker in one.
(
Theorem 1.7 is stronger since it applies to sets of all volumes and because it has a better
2 is the best possible dependence on δ).
dependence on δ (in fact, Cianchi et al. show that δ1
/
However, Corollary 1.6 is stronger in the sense that it – like the rest of our robustness results
– has no dependence on the dimension. For the applications we have in mind, this dimension
independence is more important than having optimal rates. Nevertheless, we conjecture that
it is possible to have both at the same time:

)

Conjecture 1.8. There are constants 0
surface area less than φ

Pr

A

c, C

such that for every A

<
⊂
δ, there is a half-space B such that

< ∞

1
Φ−

Rn with Gaussian

(

(

(

Pr

)))

+
A∆B

C Pr

A

2.
cδ1
/

≤

)
1.6 On highly correlated functions

(

(

)

Let us mention one more corollary of Theorem 1.5. We have used EρJ
functional generalization of Prρ
used functional generalization of Prρ
ρ
Since xy
x, y
hand side is replaced by Eρf
(
whereas equality in Theorem 1.2 holds for f

, f
as a
is another commonly
(
(
which appeared, for example, in [32].
(
(
1, we see immediately that Theorem 1.2 holds when the left
<
(
X
. The equality case, however, turns out to be diﬀerent:

, there is equality in

. However, Eρf

A
A, Y
)

A, Y
X

for 0

a, x

∈
∈

))

X

X

X

A

Φ

Y

Y

Y

x

J

≤

<

f

f

f

(

)

)

(

)

)

)

∈

∈

b

(

)
(
Eρf

)
X

=
J

−
Ef, Ef ; ρ

)
≤
only when f is the indicator of a half-space. Moreover, a robustness result for (1.4) follows
)
fairly easily from Theorems 1.4 and 1.5.

⟩)

(⟨

(

(

(

)

(

)

(1.4)

f

Y

6



<!-- pdf-page: 7 -->
Corollary 1.9. For any 0
satisﬁes Ef
1

2 and

=

/

ρ

<

<

1, there is a constant C

ρ

such that if f

Rn →

0, 1

∶

< ∞

Ef

X

f

Y

1
4 +

1
2π

≥

arcsin

)

(
ρ

δ

−

(

)

[

]

then there is a half-space B such that
(

(

)

E

f

X

)

−

1B

X

C

ρ

δc,

≤

where c

>

∣
0 is a universal constant.

(

)

(

)∣

(

)

1.7 Discrete applications

Corollary 1.9 implies a robust version of the “majority is stablest” theorem [36], which con-
cerns functions of low inﬂuence and high noise stability; for a function f
,
we deﬁne the inﬂuence of the ith coordinate by

n →

1, 1

1, 1

−

−

∶

Inf i

f

=

Pr

f

x1, . . . , xn

and the noise stability of f by
(

(

)

(

Sρ

f

f

x1, . . . , xi

xi, xi

1,
−

−

(
Eρf

ξ

f

σ

≠

)

=

}

{

}

{
1, . . . , xn
+

))

∈

)

)

)

}

{

=

−

−

))

((

1, 1

ξ1, . . . , ξn

σ1, . . . , σn
(

n is chosen so that

0 and Eρξiσi
}

n
1, 1
,
ξ, σ
)
(
)
(
×
−
Eσi
2 are independent random variables with Eξi
=
(
}
(
{

where
1, 1
The majority is stablest theorem [36] informally states that low-inﬂuence, balanced func-
{
tions cannot be essentially more noise-stable than the majority function. This was ﬁrst
explicitly conjectured by Khot, Kindler, Mossel, and O’Donnell [28] in a paper studying the
hardness of approximation of Max-Cut. It was used to show that approximating the maxi-
mum cut in a graph to within a factor of about 0.87856 is unique-games hard. This result is
optimal, since the famous eﬃcient algorithm of Goemans and Williamson [19] is guaranteed
to ﬁnd a cut that is within a 0.87856 factor of the maximum cut. A special case of the major-
ity is stablest theorem was conjectured earlier by Kalai [21] in the context of his quantitative
version of Arrow’s theorem.

ξi, σi

ρ.

=

=

(

)

∈

Combining our Gaussian results with the original proof from [36], we obtain a robust

version of the majority is stablest theorem:

Theorem 1.10. For every δ
f

>
is a function with Infi

0, there is a τ
f

n →

0, 1

1, 1

∶

−

>
≤

0 such that the following holds: suppose that
τ for every i. Then for every 0

1,

ρ

<

<

{

}

[

]

Sρ

f

≤

J
(

Ef, Ef ; ρ
)

δ.

+

If, moreover, there is some 0

ρ

<

1 such that

(

)

(

)

<
Sρ

J

Ef, Ef ; ρ

f

≥

δ

−

then there exist a, b

∈

Rn such that

(

)

(

)

E

f

ξ

1
{⟨

a,ξ

−

b
⟩≥
−

0

}

≤

C

ρ

δc,

where c, C

>

)
0 are universal constants.

(

∣

∣

(

)

7

(1.5)

(1.6)



<!-- pdf-page: 8 -->
1
√n

1
Φ−

Ef

{⟨

bn

an,ξ

=
0

If we set an

1, . . . , 1
→ Ef and Sρ
(

an, then the central limit theorem implies
1
that E1
→ J
2 and
)
bn
0, (1.5) says, therefore, that no low-inﬂuence function can be much more noise stable
)
than the simple majority function – this is the content of the majority is stablest theorem
from [36]. Our contribution is (1.6), which says that the only low-inﬂuence functions which
come close to this bound are close to weighted majority functions.

and bn
1
{⟨

In the case Ef

Ef, Ef ; ρ

=
an,ξ

(
⟩≥

bn

=

=

⟩≥

)

(

(

)

−

−

}

}

0

.

We remark that Theorem 1.10 is not the most general possible theorem that we can prove.
In particular, we could state a two-function version of Theorem 1.10 or a version that uses the
functional EρJ
f
. All of these variations, however, are proved
in essentially the same way, namely by combining the ideas from [36] with the appropriate
)
Gaussian robustness result. In order to avoid repetition, therefore, we will only state and
prove one version.

in place of Sρ

; ρ

, f

σ

f

(

(

)

(

)

)

(

ξ

1.8 Spherical noise stability and the Max-Cut problem

The well-known similarity between a Gaussian vector and a uniformly random vector on a
high-dimensional sphere suggests that there might be a spherical analogue of our Gaussian
noise sensitivity result. The correlation structure on the sphere that is most useful is the
is exactly ρ. Under
uniform measure over all pairs of points
this model of noise, we can use robust Gaussian noise sensitivity to show, asymptotically
)
in the dimension, robustness for spherical noise sensitivity. This uses the theory of spher-
ical harmonics and has applications to rounding semideﬁnite programs (in particular, the
Goemans-Williamson algorithm for Max-Cut). Our proof uses and generalizes the work of
Klartag and Regev [30], in which a related problem was studied in the context of one-way
communication complexity.

whose inner product

x, y

x, y

(

⟨

⟩

Y

X

and Y

Our spherical noise stability result mostly follows from Theorem 1.4, by replacing X and
. When n is large, these renormalized Gaussian vectors are uniformly
Y by X
distributed on the sphere and their inner product is tightly concentrated around ρ. The fact
that their inner product is not exactly ρ causes some diﬃculty, particularly because Qρ is
actually orthogonal to the joint distribution of two normalized Gaussians. Working through
this diﬃculty with some properties of spherical harmonics, we obtain the following spherical
analogue of Theorem 1.4:

/∣

/∣

∣

∣

Theorem 1.11. Let 0
where the pair

X, Y

ρ

<

<

is uniformly distributed in

1 and write Qρ for the measure of

X, Y

on the sphere Sn

1

−

(

)

(

)

x, y

Sn

1

−

Sn

1

−

∶

×

∈

x, y

ρ

.

=

For measurable A1, A2

δ

δ

=

⊂
A1, A2

Sn

1, deﬁne
{(
)
−

Qρ

X

B1, Y

∈

B2

∈

−

Qρ

X

∈

A1, Y

∈

A2

,

=

⟨

⟩

}

where B1 and B2 are parallel spherical caps with the same volumes as A1 and A2 respectively.
Deﬁne also

(

)

(

)

(

)

m

A1, A2

p

1

−

=

p

q

1

q

−

where p

Pr

X

=

∈

A1

and q

Pr

Y
(

A2

.
)

∈

=

(

)

(

)

(

)

(

)

8



<!-- pdf-page: 9 -->
For any A1, A2

⊂

Sn

1, there exist parallel spherical caps B1 and B2 such that
−

Q

A1∆B1

Q

(
A2∆B2

)

C

ρ

mc

C

mc
)
(
ρ

≤

≤

1
4 (

ρ
)δ
(
∗
1
ρ
4 (
)δ
(
∗

ρ

1
3ρ
−

ρ

1
3ρ
−

1

−

1

−

ρ
1
)(
+

ρ
1
)(
+

)

2

2

)

.

(

)

.
(

max

where δ

∗ =
The case ρ

2 log n
1
δ, n−
/
0 of the above theorem is related to work by Klartag and Regev [30]. In this
1 and
case one expects that X and Y should behave as independent random variables on Sn
−
that therefore for all A1, A2, Q0
A2
Y
A2
.
Indeed the main technical statement of Klartag and Regev (Theorem 5.2) says that for every
)
two sets,

should be close to Q

A1, Y

A1

(
=

X

X

Q

)

)

(

)

(

)

(

∈

∈

∈

∈

Q0

X

A1, Y

∈

A2

∈

−

Q

X

∈

A1

Q

Y

A2

∈

≤

C
n

.

∣

In other words the results of Klartag and Regev show that in the case ρ
X, Y
orthogonal pair
1, while our results show that for 0
to an error of order n−
)
behave like Gaussians with the same correlation.

0, a uniform
(
on the sphere behaves like a pair of independent random variables up
that are ρ correlated

X, Y

1,

)∣

=

<

<

ρ

(

)

(

)

(

That spherical caps minimize the quantity Qρ

over all sets A1 and A2
with some prescribed volumes is originally due to Baernstein and Taylor [3], while a similar
result for a diﬀerent noise model is due to Beckner [5]. Their results do not follow from ours
because of the dependence on n in Theorem 1.11, and so one could ask for a sharper version
of Theorem 1.11 that does imply these earlier results. One obstacle is that we do not know
a proof of Beckner’s inequality that gives control of the deﬁcit.

A1, Y

X

(

)

∈

∈

(
A2

)

1.8.1 Rounding the Goemans-Williamson algorithm

(

=

V, E

be a graph and recall that the Max-Cut problem is to ﬁnd a set A

V such
Let G
that the number of edges between A and V
It is of course equivalent to
2 is maximal. Goemans’
look for a function f
v
such that
−
and Williamson’s breakthrough was to realize that this combinatorial optimization problem
(
)
∣
1. Let us say, therefore, that an
to Sn
can be eﬃciently solved if we relax the range
−
1 is optimal if
embedding f of a graph G
−

A is maximal.
f

}
V, E

∖
∑(

V →

1, 1

1, 1

u,v

)∣

−

−

u

⊂

{

)∈

f

)

(

E

∶

=

(

)

into the sphere Sn
}
v

{
u

f

f

2

−

∑
)∈

u,v
(

E

) ∣
is maximal. An oblivious rounding procedure is a (possibly random) function R

1 →
−
(we call it “oblivious” because it does not look at the graph G). We will then denote
G, R
the expected value of the cut produced by rounding the worst possible optimal

Sn

)∣

(

)

(

∶

1, 1
−
by Cut
{
}
spherical embedding of G:
)

(

Cut

G, R

1
2

=

E

min
f

R

f

u

R

f

v

,

−

E

∑
u,v
)∈
(

(
where the minimum is over all optimal embeddings f .
cut in G, then Goemans and Williamson [19] showed that when R
standard Gaussian vector X, then for every graph G,

))

(

(

(

)

(

∣

))∣

If MaxCut denotes the maximum
for a

X, x

sgn

x

=

(

)

(⟨

⟩)

Cut

G, R

MaxCut

G

min
θ

αθ,

≥

(

)

(

)

9



<!-- pdf-page: 10 -->
where αθ =
oblivious rounding scheme R and every ǫ

θ
cos θ . In the other direction, Feige and Schechtman [18] showed that for every
−

0, there is a graph G such that

2
π

1

>

Cut

G, R

MaxCut

G

≤

ǫ

min
θ

+

αθ

.

(
In other words, no rounding scheme is better than the half-space rounding scheme. Using
Theorem 1.4, we can go further:

)(

)

)

(

Theorem 1.12. Suppose R is a rounding scheme on Sn
n vertices,

1 such that for every graph G with
−

min
θ
Then there is a hyperplane rounding scheme ˜R such that

MaxCut

Cut

G, R

)(

G

≥

(

)

(

ǫ

.

αθ −

)

E

R

Y

˜R

Y

−

≤

,

Cǫc
⋆

where Y is a uniform (independent of R and ˜R) random vector on Sn
∣
2 log n
1
ǫ, n−
constants, and ǫ
/

max

(
.

)∣

)

(

1, C and c are absolute
−

⋆ =

In other words, any rounding scheme that is almost optimal is essentially the same as

{

}

rounding by a random half-space.

1.9 Testing half-spaces

⊂

We quickly sketch an application of Theorems 1.4 and 1.10 to testing. Suppose we are given
Rn (meaning that we are not given an explicit representation of
oracle access to a set A
the set, but we can query whether points belong to A), and we want to design an algorithm
that (1) will answer “yes” with high probability if A is a half space and (2) will answer “no”
with high probability if Pr

ǫ for all half-spaces B.
An eﬃcient test for this problem was found in [34]. We note that Theorem 1.5 provides
ǫ pairs
and counting the number
−
Xi
. By doing so, we obtain
and so by Theorem 1.5, we can tell
(

4
a simpler and very direct test just by sampling ǫ−
of times that Xi
accurate estimates of Pr
whether A is close to a half-space.

A and the number of times that 1A
A

Xi, Yi
1A

and Pr

A∆B

A, Y

Yi
)

=
(

X

A

>

(

)

(

)

)

∈

∈

∈

(

)

(

By Theorem 1.10, this algorithm also applies to linear threshold functions with low inﬂu-
ences on the discrete cube (such functions are called regular in [34]). (By the more general
arguments in [36], the algorithm also applies to other discrete spaces such as half-spaces in
biased cubes or cubes of the form
3.) Using the arguments of [34] it is then
possible to extend the testing algorithm to general linear threshold functions on the discrete
cube.

n for some q

≥

q

[

]

)

1.10 Proof Techniques

1.10.1 Borell’s theorem

We prove Theorem 1.2 by diﬀerentiating along the Ornstein-Uhlenbeck semigroup. This
technique was used by Bakry and Ledoux [4] in their proof of the Gaussian isoperimetric
inequality and, more generally, a Gaussian version of the L´evy-Gromov comparison theorem.
Recall that the Ornstein-Uhlenbeck semigroup can be speciﬁed by deﬁning, for every t
0,
the operator

≥

Ptf

x

f

tx

e−

= ∫Rn

(

)(

)

(

+

1
√

−

2ty
e
−

dγn

y

.

)

(

)

(1.7)

10



<!-- pdf-page: 11 -->
Note that Ptf → f as t → 0 (pointwise, and also in Lp), while Ptf → Ef as t →

Let ft

=

Ptf , gt

=

Ptg, and consider the quantity

EρJ

ft

X

, gt

Y

.

Rt

∶=

.
∞

(1.8)

As t → 0, Rt converges to the right hand side of (1.2); as t →
∞
hand side of (1.2). We will prove Theorem 1.2 by showing that dRt
dt ≥

))

(

(

)

(

0 for all t

0.

>

, Rt converges to the left

1.10.2 The equality case

The equality case almost comes for free from our proof of Theorem 1.2. Indeed, Lemma 2.2
writes dRt

dt as the expectation of a strictly positive quantity times

1
Φ−

ft

○

∇

X

1
Φ−

gt

○

−

∇

Y

,

⋅

(

∣(

denotes the Euclidean norm. Now, if there is equality in Theorem 1.2 then dRt
where
(
dt
must be zero for all t, which implies that the expression above must be zero almost surely.
∣
This implies that ∇
are almost surely equal to the same constant,
and therefore ft and gt can be written as Φ composed with a linear function. We can then
)
infer the same statement for f and g because Pt is one-to-one.

and ∇

1 ○ ft

1 ○ gt

Φ−

Φ−

))(

))(

)∣

)

(

(

)

(

∣

1.10.3 Robustness

f, g

is small then dRt

Our approach to robustness begins similarly to the approach in our recent work [35].
δ
Lemma 2.2 we ﬁrst concentrate on the main term:
(
)
and wt
=
value of

If
0. Looking at the expression in
1 ○ ft
2 where vt
1 ○ gt. Using an analogue of Poincar´e’s inequality, we argue that if the expected
∣

dt must also be small for most t
∇vt

2 is small then vt and wt are close to linear functions.

Φ−
∇vt

− ∇wt

− ∇wt

Φ−

>
X

X

)∣

Y

Y

=

(

)

(

∣

(

)

(

=

)∣

f, g

x, a

is small then for every t

Considerable eﬀort goes into controlling the “secondary terms” of the expression in
Lemma 2.2. This control is established in a sequence of analytic results, which rely heavily on
the smoothness of the semigroup Pt, concentration of Gaussian vectors and Lp interpolation
δ, t
δ
inequalities. In the end, we show that if δ
close to a linear function. Since Φ is a contraction, this implies that ft must be close to a
)
(
− b
function of the form Φ
1
We would like to then conclude the proof by applying P −
, and saying that f must be close
t
)
1
x, a′
to P −
. The obvious problem here is that
, which also has the form Φ
t Φ
1
P −
is not a bounded operator, but we work around this by arguing that it acts boundedly on
t
(⟨
the functions that we care about. This part of the argument marks a substantial departure
from [35], where our argument used smoothness and spectral information. Here, we will use
a geometric argument to say that if h
can be
bounded in terms of E
. This improved argument is essentially the reason that the rates
in Theorem 1.4 are polynomial, while the rates in [35] were logarithmic.

1A − 1B where B is a half-space, then E

0, vt is ǫ

− b′

Pth

x, a

− b

(⟨

(⟨

h

=

>

)

)

)

(

⟩

⟩

⟩

.

∣

∣

∣

∣

1.11 Subsequent work

A quite diﬀerent study of the functional EρJ
f
turns out to yield yet another
proof of Borell’s inequality: in a subsequent work with De [15], the authors give a proof of
(
Borell’s inequality by ﬁrst proving a four-point inequality for J which tensorizes to the discrete
cube. Applying the central limit theorem then recovers Borell’s inequality. That approach
is similar to Bobkov’s elementary proof of the Gaussian isoperimetric inequality [7]. The

; ρ

, g

X

Y

(

)

(

)

)

11



<!-- pdf-page: 12 -->
proof in [15] has an advantage and a disadvantage compared to the one presented here. The
advantage of the tensorization argument is that it directly yields some interesting inequalities
on the cube (in particular, one obtains a direct proof of the “majority is stablest” theorem),
while the proof we present here has the advantage of giving control over the deﬁcit.
In
particular, we don’t know how to prove Theorem 1.4 using the techniques in [15].

2 Proof of Borell’s theorem

Recall the deﬁnition of Pt and Rt from (1.7) and (1.8). In this section, we will compute dRt
dt
1 ○ ft,
and show that it is non-negative, thereby proving Theorem 1.2. First, deﬁne vt
x, Y
wt

1 ○ gt, and K

. Then

x, y; ρ

Prρ

Φ−

X

=

b

Φ−

=

=

≤

≤
, gt

(

J
)

ft

X
(

Y

=

K
)

vt

X

, wt

Y

.

Lemma 2.1.

(

(

)

(

))

(

(

)

(

))

∂K

x, y

∂x
(
x, y

∂K

∂y
(

=

=

)

)

φ

x

Φ

(
y
φ

)
Φ

(

y − ρx
1 − ρ2
x − ρy
√
1 − ρ2

)
.

Proof. Note that Y can be written as ρX +
X
√
Gaussian vectors. Then
≤

x, Y

X

≤

=

≤

y

)

)

(

√

(
1 − ρ2Z, where X and Z independent standard
x, Z

, and so

y
−
√1

ρX
ρ2

−

≤

{

K

x, y

Diﬀerentiating in x,

(

)

}

{

x

y
−
√1

ρs
ρ2
−

φ

s

φ

t

}
dt ds.

= ∫

−∞

∫

−∞

∂K

x, y

∂x
(

)

y
−
√1

ρx
ρ2
−

−∞
x

Φ

= ∫
φ

=

(

)

(

)

dt

t

φ
x
φ
y − ρx
(
(
)
1 − ρ2

.
)

This proves the ﬁrst claim. The second claim follows because K
y.

(

)

(

√

)

x, y

is symmetric in x and

(

)

Lemma 2.2.

dRt
dt =

2π

ρ
1 − ρ2

Eρ exp

−

t + w2
v2
2

t − 2ρvtwt
1 − ρ2

∇vt − ∇wt

2.

Before we prove Lemma 2.2, note that it immediately implies Theorem 1.2 because the

(

)

√

(

)∣

∣

right hand side in Lemma 2.2 is clearly non-negative.

Proof. Set L
dft
dt =

Lft for all t

=

∆ −

x, ∇

; it is well-known (and easy to check by direct computation) that

0. The integration by parts formula
⟨

⟩

≥

Ef

X

Lg

X

=

−E

∇f

X

, ∇g

X

(

)

(

)

⟨

(

)

(

)⟩

12

(2.1)



<!-- pdf-page: 13 -->
for bounded smooth functions f and g is also standard and easily checked. Thus,

dRt
dt =

Eρ

Kx

vt

X

, wt

Y

dvt

X

+ Eρ

Ky

vt

X

, wt

Y

dt
(

dt
(
(
. Hence, the ﬁrst term of (2.2) is

))

)

(

)

(

)

(

(2.2)

.

)

)

dwt

X

))
(
Lft
Now, the chain rule implies that dvt
vt
φ
dt =
(
Y

(

(

(

)

Kx

)

Eρ

Lft

X

,

(2.3)

vt
φ
(

X
vt
(
(

, wt
X
)
(

Lft

X

wt

EρΦ

=

X

Y

− ρvt
1 − ρ2
)
(
√

)

(

(

(

))

(
(
))
1 − ρ2Z (with X and Z independent);
where we have used Lemma 2.1. Now write Y
=
conditioning on Z and and applying the integration by parts (2.1) with respect to X, we have
wt − ρvt
1 − ρ2
vt − ρwt
√
(
1 − ρ2

ρ
1 − ρ2
ρ
√
1 − ρ2

∇wt − ∇vt, ∇ft

∇vt − ∇wt, ∇vt

(
ρX +

Eρφ

Eρφ

(2.3)

(2.4)

)⟨
φ

√

vt

−

=

=

)

)

)

⟩

.

where we have written, for brevity, vt and wt instead of vt
symmetric in its arguments, there is a similar computation for the second term of (2.2):

. Since K is

X

Y

√

(

√

)

(

)⟨

⟩
and wt

E

Ky

vt

X

, wt

Y

(
(
Note that

(

)

(

))

dwt

X

dt
(

)

)

−

=

ρ
1 − ρ2

Eρφ

wt − ρvt
1 − ρ2

√

(

√

)

(

)⟨

(

)

φ

wt

)

(
∇vt − ∇wt, ∇wt

(2.5)

.

⟩

φ

wt − ρvt
1 − ρ2

φ

vt

φ

=

vt − ρwt
1 − ρ2

φ

wt

1
2π

=

exp

−

t + w2
v2
2

t − 2ρvtwt
1 − ρ2

hence, we can plug (2.4) and (2.5) into (2.2) to obtain

(

√

)

(

)

(

√

)

(

)

(

(

)

;

)

dRt
dt =

2π

ρ
1 − ρ2

E exp

−

v2
t + w2
2

t − 2ρvtwt
1 − ρ2

3 The equality case

√

(

(

)

∇vt − ∇wt

2.

)∣

∣

Lemma 2.2 allows us to analyze the the equality case (Theorem 1.3), with very little additional
eﬀort. Similar ideas were used by Carlen and Kerce [12] to analyze the equality case in the
standard Gaussian isoperimetric problem. Clearly, Lemma 2.2 implies that if for every t, vt
and wt are linear functions with the same slope, then equality is attained in Theorem 1.2.
To prove Theorem 1.3, we will show that the converse also holds (ie. if equality is attained
then vt and wt are linear functions with the same slope). Then we will take t → 0 to obtain
the desired conclusion regarding f and g.
x

0, then a direct computation gives

First of all, if f

1
a,x
⟨

b
⟩≥
−

=

(

)

ft

x

Φ

kt

=

(

)

(

a, x − etb
a

⟨

⟩

)

,

(3.1)

e2t − 1
where kt
for some a, b with
=
decreasing in t, we have the following lemma:

2. Since Pt is injective, it follows that whenever ft
1
∣
/
kt, f must have the form f

Φ
. Since, moreover, kt is
⟩)

a, x − b′

b
⟩≥
−

1
{⟨

(⟨

a,x

x

=

=

=

(

}

0

∣

−
a
)
∣

∣

(

)

13



<!-- pdf-page: 14 -->
Lemma 3.1. If ft
such that if ˜f

x

x
1
=
)
(
{⟨

=
a,x

Φ

a, x − b′
0
b
(⟨
⟩≥
−

then f
⟩)

}

for some a, b′ ∈
Ps ˜f , where s solves
=

Rn with
a

kt, then there exists b

Rn

∈

In order to apply Lemma 3.1, we will use the following pointwise bound on ∇vt, whose
proof can be found in [4]. Note that the bound is sharp because, according to (3.1), equality
is attained when f is the indicator function of a half-space.

(

)

∣

≤
ks

t.
+

a

=
∣

∣
∣

Lemma 3.2. For any function f ∶ Rn →

0, 1

, any t

0, and any x

>

Rn,

∈

∇vt
[

x
]

kt.

≤

∣

(

>

)∣

0 implies that ∇vt

0. In particular, we may ﬁx some t

Proof of Theorem 1.3. Suppose that equality is attained in (1.2). Since dRt
is non-negative,
dt
0 such that dRt
it must be zero for almost every t
0.
Note that everything in Lemma 2.2 is strictly positive, except for the last term, which can be
zero. Therefore, dRt
almost surely. Since the conditional
=
distribution of Y given X is fully supported, ∇vt and ∇wt must be almost surely equal to
1 are
some constant a′ ∈
smooth); hence, vt

dt =
)
(
Rn. Moreover, vt and wt are smooth functions (because ft, gt and Φ−
a, x − d′
x
a, x − b′
⟨
a, x − d′

for some b′, d′ ∈

Rn, and so

a, x − b′

and wt

(
x

dt =

∇wt

ft
gt

Φ
)
Φ

⟩
.

(
=

X

Y

x

>

=

=

)

)

(

⟨

⟩

(⟨

⟩)

x

Now, Lemma 3.2 asserts that

some b such that if ˜f
1
a,x
⟨
takes one of the two forms indicated in Theorem 1.3: if s
On the other hand, s
a, x − b
the form Φ
applying the same argument to g.

)
(
0 implies, by (3.1), that fs
>
by replacing ks

kt. Hence, Lemma 3.1 implies that there is
(⟨
⟩)
≤
Ps ˜f , where s solves
t. In particular, f
=
+
˜f
0 then f
0.
1
a,x
=
=
=
∣
∣
a
, x − esb
⟨
, which we can write in
a
(
)
with a and ksesb with b. We complete the proof by
∣

ks
x

b
⟩≥
−

a
a
∣

ks

⟩)

=
∣

Φ

x

=

=

a

)

(

(

⟨

∣

∣

x
(

=
)
∇vt
a
(
)
=
0 then f
b
∣
∣
⟩≥
−

∣

(⟨

⟩)

4 Robustness: approximation for large t

The proof of Theorem 1.4 follows the same general lines as the one in [35]. Our starting point
is Lemma 2.2, and the observation that if (1.2) is close to an equality then dRt
dt must be small
for most t. For such t, using Lemma 2.2, we will argue that vt must be close to linear for that
t; it then follows that ft must be close to one of the equality cases in Theorem 1.3. Finally,
we use a time-reversal argument to show that f must be close to one of those equality cases
also.

Our proof will be divided into two main parts. In this section, we will show that vt is
close to linear; we will give the time-reversal argument in Section 5. The main result in this
section, therefore, is Proposition 4.1, which says that ft must be close to one of the equality
2.
1
cases of Theorem 1.3. Recall the deﬁnition of δ from (1.3), and recall that kt
/

e2t − 1

=

Proposition 4.1. For any 0
f, g and for any 0

ρ
1, there exist b, d

1, and for any t
R and a

α

<

<

<

<

∈

0, there exists C
Rn with

t, ρ
kt such that

a

(

such that for any

)

≤

(

)

>
∈

E

ft

X

− Φ

a, X

− b

2 + E

gt

X

− Φ

a, X

− d

2

(

(

)

(⟨

⟩

))

(

(

)

C

⟩
t, ρ

))
m

f, g

(⟨

≤

where m

f, g

=

Ef

1 − Ef

Eg

1 − Eg

.

(

)

(

)

(

)

(

)

(

)

14

∣

∣

8k

2
t

(

2

1

ρ
2
−
k
t

1
(
+

2
)
)

1

α

(

+

)

δ
α

1

4k

+

(

)

1

2
t

1

1

α

1

ρ

/(

−

)

+



<!-- pdf-page: 15 -->
Let us observe – and this will be important when we apply Proposition 4.1 – that by
0

kt implies that Φ

s1B for some s
can be written in the form Pt
+

− b

a, ⋅

>

a

The main goal of this section is to prove Proposition 4.1. The proof proceeds according

(⟨

⟩

)

Lemma 3.1,
and some half-space B.
∣

≤

∣

to the following steps:

• First, using a Poincar´e-like inequality (Lemma 4.2) we show that if Eρ

∇v
is small then v and w are close to linear functions (with the same slope).
(

)∣
• In Proposition 4.3, we use the reverse H¨older inequality and some concentration prop-
2p must be small for some

is small, then Eρ

−∇w

Y

2

− ∇wt

∇vt

X

X

Y

)

(

∣

erties to show that if dRt
dt
p

1.

<

• Using Lemma 3.2, we argue that if Eρ

−
2 is also small. Thus, we can apply the Poincar´e inequality mentioned in the
)

∇wt
ﬁrst bullet point, and so we obtain linear approximations for vt and wt.

2p is small then Eρ

∇vt

X

X

)∣

Y

Y

(

(

(

)

∣

∣

∣
∇vt

)
(
− ∇wt

(

)∣

4.1 A Poincar´e-like inequality

Recall that we proved the equality case by arguing that if dRt
is
identically zero, so ∇vt and ∇wt must be constant and thus vt and wt must be linear. The
(
is small, then vt
ﬁrst step towards a robustness result is to show that if
and wt must be almost linear, and with the same slope.
∣
Rn, γn

)∣
E∇v + E∇w

)
, if we set a

− ∇wt

− ∇wt

0 then

dt =

∇vt

∇vt

then

L2

X

X

)∣

Y

Y

)

(

(

(

∣

Lemma 4.2. For any smooth functions v, w
for any 0

1,

ρ

∈

1
2

=

(

)∣

<

<

E

v

X

−

X, a

− Ev

2 + E

w

X

−

X, a

− Ew

(

)
2

≤

Eρ

∇v

∣

X
2
(

(

(
− ∇w

Y

1 − ρ
)

(

)∣

)

2

.

)

We remark that Lemma 4.2 achieves equality when v and w are quadratic polynomials

)

(

(

)

⟨

⟩

(

(

)

⟨

⟩

)

which diﬀer only in the constant term.

Hk
L2

2ex2
1
/

In order to prove Lemma 4.2, we recall the Hermite polynomials:
x
=
R, γ1
(
)
(

N, deﬁne
2 dk
2. It is well-known that the Hk form an orthonormal basis of
k!
dxk e−
/
/
. For a multiindex α
(
)

Nn, let

for k

x2

)

∈

∈

n

−

Hα

x

Hαi

xi

.

=

∏i
1
=

(

)

Then the Hα form an orthonormal basis of L2
α
is linear if and only if
=
αi − 1 and
Siα
by
=
∣
polynomials states that

1, and αi
j

=
αj for j

Siα

=

≠

∣

i

(

)

(
)
Rn, γn

α
i αi; note that Hα
0, deﬁne Siα
0.
∣
i. Then a well-known recurrence for Hermite

. Deﬁne
Hα

0 implies that
)
(

If αi

= ∑

∂
∂xi

=
∣

>

(

)

∂
∂xi

Hα

αiHSiα

if αi
if αi

0
0.

>
=

0
√

= ⎧⎪⎪
⎨
⎪⎪⎩
∂
∂xi

E

2

Hα

αi.

=

(4.1)

In particular,

It will be convenient for us to reparametrize the Ornstein-Uhlenbeck semigroup Pt: for
)
ρ
0
<
Tρv

. It is then easily checked that for any v

1, let Tρ
X
.

Rn, γn

1
ρ
)
/
(

, Eρ

Plog

L1

X

Y

=

<

=

(

v

∈

(

)

(

(

)∣

)

(

)(

)

15



<!-- pdf-page: 16 -->
The ﬁnal piece of background that we need before proving Lemma 4.2 is the fact that Tρ

acts diagonally on the Hermite basis, with

TρHα

=

ρ∣

α
∣Hα.

(4.2)

Proof of Lemma 4.2. First, consider two arbitrary functions b
pose that their expansions in the Hermite basis are b

Eρ

b

X

− c

Y

2

(

(

)

(

))

=

=

x

, c

x
α bαHα and c
)
)
Y

(
c

(

= ∑
Eb2 + Ec2 − 2Eρb
Eb2 + Ec2 − 2Eb
Tρc
X
(
)
(
α + c2
b2
α
α − 2ρ∣
∣bαcα
)(
(

X

,

= ∑α

X

)

)(

)

and sup-

L2

∈
= ∑

Rn, γn
α cαHα. Then
(
)

(
where we have used (4.2) in the last line to compute the Hermite expansion of Tρc. Now,
2bαcα

α and so

α + c2
b2

)

≤

Eρ

b

X

− c

Y

2

(

(

)

(

))

=

≥

≥

b0 − c0

2 +

(
b0 − c0

)
2 +

(
b0 − c0

)
2 +

∣

∑
1
α
∣≥

∣

∑
1
α
∣≥
(
1 − ρ

α + c2
b2

α − 2ρ∣

α
∣bαcα

(
α + c2
b2
α

1 − ρ∣

α
∣

)

)(
b2
α + c2
α

)
.

(4.3)

∑
1
α
∣≥
vαHα and w

(

)

∣

Now write v and w in the Hermite basis as v

(

)

(

= ∑

)
wαHα. Then, by (4.1),

= ∑

∂v
∂xi = ∑αi
1
≥
∂w
∂xi = ∑αi
1
≥

vα

αiHSiα

√

wα

αiHSiα.

√

In particular, if we set b
, then bSiα
≥
(where ei is the multi-index with 1 in position i and 0 elsewhere) and

αivα for any α with αi

=

=

∂v
∂xi

√

1. Speciﬁcally, b0

vei

=

b2
α = ∑
2,αi
α
∣≥
∣

1

≥

b2
Siα = ∑
2,αi
α
∣

∣≥

1

≥

∑
1
α
∣≥

∣

αiv2
α

∂w
(Setting c
∂xi
to (4.3), we have

=

, there is of course an analogous inequality for c and w.) Applying this

Eρ

∂v
∂xi

X

−

∂w
∂xi

Y

2

≥

vei

− wei

2 +

1 − ρ

αi

α + w2
v2
α

.

1

(4.4)

∑
2,αi

α

∣

∣≥

≥

(
Now if we apply (4.4) for each i and sum the resulting inequalities, we obtain

))

(

(

)

(

)

(

)

(

)

Eρ

∇v

X

− ∇w

Y

2

vα − wα

2 + 2

1 − ρ

α + w2
v2
α.

(4.5)

On the other hand, let a

∣

(

)

that

(
1
2

=

≥ ∑
1
α
∣
∣=
)∣
(
E∇v + E∇w

∑
2
α
∣≥

∣

(
)
. Since E ∂v
∂xi =

)
vei and Hei

xi, it follows

x

=

(

)

(
x, a

=

⟨

⟩

)
vα + wα

1
2 ∑
1
α
∣=
∣
(
16

Hα

x

.

)

(

)



<!-- pdf-page: 17 -->
Since Ev

=

v0, we have

E

v

X

−

X, a

− Ev

2

vα − wα
2

2

+

v2
α.

∑
2
α
∣≥

∣

= ∑
1
α
∣=
∣

)
Adding to this the analogous expression for w, we obtain

(

(

(

)

⟨

⟩

)

Noting that 1 − ρ

E

v

X

≤

−

2

1 − ρ

E

v

X

−

X, a

− Ev

2 + E

w

X

−

(

)(

(

(

)

⟨

⟩

)

(

(

)
=

X, a
1 − ρ
⟨

⟩

− Ew

2

∑
1
α
∣=
(

∣

vα − wα
)
)

2 + 2

1 − ρ

α + w2
v2
α.

∑
2
α
∣≥

∣

)
1, we see that this is smaller than (4.5). Hence

(

)

(

)

X, a

− Ev

2 + E

w

X

−

X, a

− Ew

2

(

)
4.2 A lower bound on dRt
dt

(

(

)

⟨

⟩

(

(

)

⟨

⟩

)

)

− ∇w

Y

Eρ

∇v

≤

∣

X
2
(

1 − ρ
)

(

)∣

2

.

(

)

X

− ∇wt

dt given in Lemma 2.2.

Recall the formula for dRt
In this section, we will use the reverse-
H¨older inequality to split this formula into an exponential term and a term depending on
∇vt
. We will then use the smoothness of vt and wt to bound the exponential
X
term, with the following result:
∣
(
Proposition 4.3. For any 0
r

<
and for any f and g,

0 such that for any

0, there is a c

1 and any t

t, ρ

)∣

<

>

>

ρ

(

)

1

1
4k2
t
+

1

/(

−

ρ
)

≤

2
t

k

c

t, ρ

m2

dRt
dt ≥

1
1
(

kt
ρ

+
−

(

)

2

)

E

∇vt

X

− ∇wt

Y

2r

1
r
/

.

There are three main ingredients in the proof of Proposition 4.3. The ﬁrst is the reverse-
0 and

(
)
H¨older inequality, which states that for any functions f
0

(
)∣
0 and g

0 and for any β

− 1

1,

>

≥

>

r

(

)

∣

)

(

1 with 1
r

<

<

β =

Ef g

≥

β
Ef −

1
β
/

−

Egr

1
r
/

.

(4.6)

The second ingredient involves concentration properties of the Gaussian measure. The

(

)

(

)

proof is a standard computation, and we omit it.

Lemma 4.4. If f ∶ Rn → R is 1-Lipschitz with median M then for any λ

1,

<

E exp

λf 2

X

2

2
1 − λ

e

λ
1

λ

2

(

−

)

M 2

.

≤

√
The third and ﬁnal ingredient is a relationship between the mean of f and the median of

)/

(

(

)

vt.

Lemma 4.5. If Nt is a median of vt then

m

f

=

Ef

1 − Ef

(

)

(

≤

)

2 exp

−

N 2
t
1 + kt

2

(

(

.

2

)

)

17



<!-- pdf-page: 18 -->
Proof of Lemma 4.5. Lemma 3.8 of [35] proved that if Mt is a median of ft then

Recall that ft
=
we see that Mt
≤

Φ ○ vt and so Mt
e−

2 and so
/

N 2
t

1

1
kt )
+

2

.

2M (
t

≤
. Suppose ﬁrst that Nt

Ef

Φ

Nt

=

Ef

)
2 exp

(

≤

N 2
t
1 + kt

−

2

.

2

0. Since Φ

−x

≤

x2

e−

2,
/

≤

(

)

(4.7)

On the other hand, if Nt

>

0, we apply the preceding argument to 1 − f and we conclude that

(

)

E

1 − f

2 exp

−

≤

2

(

)
N 2
t
1 + kt

.

2

(4.8)

Of course, max
claim of the lemma.

Ef, 1 − Ef

{

)
1 and so we can combine (4.7) and (4.8) to prove the second

(

(

)

(

)

≤

}

Proof of Proposition 4.3. We begin by applying the reverse-H¨older inequality (4.6) to the
equation in Lemma 2.2:

dRt
dt ≥

2π

ρ
1 − ρ2

Eρ exp

β

t + w2
v2
2

t − 2ρvtwt
1 − ρ2

1
β
/

−

Eρ

∇vt − ∇wt

2r

1
r
/

(4.9)

with β and r yet to be determined. Let us ﬁrst consider the exponential term in (4.9). Since
2

(

)

vtwt

t + w2
v2

))

(

∣

∣

)

√

(

(

≤

∣

∣

t , we have
t + w2
v2
2

Eρ exp

β

t − 2ρvtwt
1 − ρ2

(

(

)

Eρ exp

β

E exp

(

β

)

≤

≤

t + w2
v2
t
1 − ρ
2
v2
t
(
1 − ρ

)
E exp
)

β

w2
t
1 − ρ

2
1
/

,

(4.10)

(

)

(

1 − ρ

; we see that if λ

))
where we used the Cauchy-Schwarz inequality in the last line. Recall from Lemma 3.2 that
vt and wt are both kt-Lipschitz. Thus, we can apply Lemma 4.4 with f
2βk2
t

≤
v2
)
t
1 − ρ
where Mt is a median of vt. Applying the same argument to wt and plugging the result
into (4.10), we have

CeλM 2
t ,

1
2 , then

kt and λ

/(
E exp

2βk2
t

1 − ρ

/(

vt

β

≤

=

=

=

(

)

(

)

/

Eρ exp

β

t + w2
v2
2

t − 2ρvtwt
1 − ρ2

M 2
Ceλ
t
(

N 2
t
+

),

≤

where Nt is a median of wt. Going back to (4.9), we have

)

(

with (recall) λ
that (4.11) holds for any r

2βk2
t

=

1 − ρ

Eρ

∇vt − ∇wt

2r

)

1
r
/

,

dRt
dt ≥

)
N 2
t
+

≤

(
λ
β

e−

M 2
t
(

cρ
1 − ρ2
√
1
2 ; hence, β
≤
1
4k2
t
+
M 2
t

− 2k2

exp

ρ
)

1
)

<

/(

−

1

=

/(

exp

−

λ
β

(
∣
1 − ρ

1
4

)
t . Recalling that 1
k2
r

∣

− 1

β =

. Finally, we invoke Lemma 4.5 to show that

(

)/

t M 2
t
1 − ρ

cEf

1 − Ef

≥

2
t

k

2

1
1
(

2

)

kt
ρ

+
−

(4.11)

1, we see

(
(and similarly for g and Nt). Plugging this into (4.11) completes the proof.

))

(

)

)

(

(

18



<!-- pdf-page: 19 -->
4.3 Proof of Proposition 4.1

We are now prepared to prove Proposition 4.1 by combining Proposition 4.3 with Lemmas 3.2
and 4.2. Besides combining these three results, there is a small technical obstacle: we know
only that the integral of dRt
dt at speciﬁc values of
dt
t. So instead of showing that vt is close to linear for every t, we will show that for every t,
there is a nearby t∗ such that vt
is close to linear. By ensuring that t∗ is close to t, we will
then be able to argue that vt is also close to linear.

is small; we don’t know anything about dRt

∗

Proof of Proposition 4.1. For any 0

r

<

<

1, Lemma 3.2 implies that

E∇vt + E∇wt) and we deﬁne ǫ

Eρ

∇vt − ∇wt

2r

1
r
/

≥

E

2

∇vt − ∇wt
1
2k2
r
)/
(
∣
t

r
−

∣

1
r
/

.

)

(

(
By Lemma 4.2 applied to vt and wt, if we set a
E

2 (and similarly for ǫ

− Ev

X, a

X

−

)

∣

∣

wt

vt

1
2
=
), then
(

(

(

)

⟨

⟩

)
ǫ

vt

+ ǫ

wt

1
r
/

≤

1
k2
r
r
(
)
)/
(
−
t
1 − ρ

(
Now we plug this into Proposition 4.3 to obtain

))

(

)

(

Eρ

∇vt − ∇wt

2r

1
r
/

.

(

∣

∣

)

ǫ

vt

+ ǫ

wt

C

t, ρ

m

2k

2
t

1
r
/

≤

Recall that δ

f, g

(
(
∞0
= ∫

)
))
dRs
ds ds. In particular,

(

(

)

ρ
kt

1
1
−
+

(

2 dRt
dt

)

.

vt

=

(

)

(4.12)

and so there is some s
∈
replaced by s and with r

(

)

t
≤

αt min
1
t
s
α
≤
(
+
)
1 + α
1
4k2
(
t
+

t, t

=
[

/(

1

1

dRt
dt

s ≤ ∫

t

1
t
(

α
)

+

dRs
ds

δ

f, g

ds

≤

∣

such that dRt
dt
1
4k2
s

1

1

+

/(

−

ρ
)

ρ
) ≤
)]
−

s ≤
, we obtain
∣

ǫ

vs

+ ǫ

ws

r

C

t, ρ

m

≤

2k

2
t

1

ρ

1
−

k

(

+

2
t

)

r

.

δ
α

(

)

δ
αt . If we apply this to (4.12) with t

(
Since Φ is Lipschitz, if we denote E
then we have

(

)

)
fs − Φ

(

)
X, a

− Evs

)
(
2 by ǫ

fs

(and similarly for gs),

ǫ

fs

+ ǫ

(
gs

(⟨
t, ρ

C

r
⟩
m

≤

1

ρ

1
−

(

+

))
2
k
t
)

Note that r

=

1
ρ
4k2
−
ρ
+

1

−

t ≥

1
1
4
(

ρ
(
k2
−
t
+

)

)
(
and so

)

(

)

ǫ

fs

+ ǫ

gs

C

t, ρ

2
8k
m (
t

≤

2k

2
t

1

2

ρ

1
−

)
k

(

+

2

2
t

)

r

(
.

)

δ
α

(

)

r

.

δ
α

(4.13)

Now we will need a lemma to show that ǫ

(

)

(

)

(

)
ft

and ǫ

(
ft

)
are small. We will prove the

lemma after this proof is complete.

Lemma 4.6. For any t

s and any h

L2

∈

<

)
(
Rn, γn

,

(

)

E

Pth

2

≤

E

(
Psh

2

s
t
)
/

Eh2

1

s
t
/
−

.

(

)

(

(

)

(

)

)
19



<!-- pdf-page: 20 -->
To complete the proof of Proposition 4.1, apply Lemma 4.6 with h

exists by Lemma 3.1, because

a

1
(note that P −
s Φ
1 + α
and s

X, a

− Evs
t, we see that

≤

(⟨

⟩

(

)

ǫ

ft

)

=

E

Pth

2

≤

E

Psh

2

s
t
/

ǫ

fs

=

=

1
f −P −
s Φ
ks). Since Eh2
≤
(⟨

X, a
sup
⟩

−Evs
h

≤

1
)

∣

∣

≤

∣

1

∣
1

α
).

/(

+

Applying this (and the equivalent inequality for g) to (4.13), we have

(

)

(

)

)

(

)

(

)

(

ǫ

ft

+ ǫ

gt

C

t, ρ

≤

1

1
1
8k
α m (
+
(
+

2
t

2

1

ρ
2
−
k
t

2
)
)

1

α

(

+

)

r

1

α ,

+

δ
α

ft

means E
where ǫ
and so we can absorb the power
(⟨
Proof of Lemma 4.6. Expand Psh in the Hermite basis as Psh
)

)
X, a
1
α into the constant C
⟩
+

(
2 and similarly for ǫ
.

)
(
1
ft−P −
tΦ
s
−

(
−Evs

t, ρ

))

(

(

)

)

(

(

1

(

)
gt

. Since α

1, 1

2 ≤

<

1

1
α ≤
+

1

)
bαHα. Then

= ∑

E

Psh

2

E
(

2
Pth
)
Eh2
)

(

b2
α
αe2
b2
s
(
b2
αe2s

∣

t
−
)∣
α
∣.

α
∣

= ∑

= ∑

= ∑

By H¨older’s inequality applied with the exponents s

t and s

s − t

,

E

Pth

2

s
b(
α

s
t
)/
−

= ∑

e2
s
(

(

)

≤

=

∣

α
∣

αe2s
b2
s
t
s
)
)/
−
(

∑
Eh2
(

t
s
∣bt
α
/
α
)∣
−
/
s
t
s
)/
−
(

∑
2

E

Psh
(

)

s
t
/

/(

b2
α

s
t
/

.
)

)
5 Robustness: time-reversal

(

(

(

)

)

The ﬁnal step in proving Theorem 1.4 is to show that the conclusion of Proposition 4.1
implies that f and g are close to one of the equality cases.
In [35], the authors used a
spectral argument. However, that spectral argument was responsible for the logarithmically
slow rates (in δ) that [35] showed. Here, we use a better time-reversal argument that gives
polynomial rates. The argument here will need the function f to take values only in
.
Thus, we will ﬁrst establish Theorem 1.4 for sets; having done so, it is not diﬃcult to extend
}
it to functions using the equivalence, described in Section 1.4, between the set and functional
forms of Borell’s theorem.

0, 1

{

=

h

h

1; on the other, E

from above in terms of E

The main goal of a time-reversal argument is to bound E

Pth
,
for some function h. The diﬃculty is that such bounds are not possible for general h. An
∣
∣
illuminating example is the function h ∶ R → R given by h
: on the one
hand, E
can be made arbitrarily small by taking k large.
(

The example above is problematic because there is a lot of cancellation in Pth. The
essence of this section is that for the functions h we are interested in, there is a geometric
reason which disallows too much cancellation. Indeed, we are interested in functions h of the
form 1A − 1B where B is a half-space. The negative part of such a function is supported on
B, while the positive part is supported on Bc. As we will see, this fact allows us to bound
the amount of cancellation that occurs, and thus obtain a time-reversal result:

Pth

sgn

sin

kx

))

∣
x

=

)

(

(

∣

∣

∣

∣

∣

20



<!-- pdf-page: 21 -->
Proposition 5.1. Let B be a half-space and A be any other set. There is an absolute constant
C such that for any t

0,

>

γ

A∆B

≤

C max

E

Pt1A − Pt1B

,

e2t − 1

4
1
/

E

Pt1A − Pt1B

,

√

(

∣
The main idea in Proposition 5.1 is in the following lemma, which states that if a non-
negative function is supported on a half-space then Pt will push strictly less than half of its
mass onto the complementary half-space.

∣}

{

)

(

)

∣

∣

0 such that for any b

∈

>

R, if f ∶ Rn →

0, 1

is supported

Lemma 5.2. There is a constant c
on

then for any t

0,

b

x1

≤

>

{

}

E

Ptf

X1

1
{

e

≥

tb
−

} ≤

max

Proof. Because Pt is self-adjoint,

(

)

[

]

Ef − c

1
2

{

,

3
8

2

Ef
e2t − 1
(
)
√

Ef

.

}

E

Ptf

X1

1
{

e

≥

tb
−

} =

Ef Pt1
{

X1

e

≥

tb
−

} =

Ef Φ

X1 − b
e2t − 1

.

b − Ef

(
≤

x1

)
≤

b

has measure at most φ

0

(

√

)

Ef . In particular, Ef 1
b
−
{

Ef

}
and B

b − Ef

x1

b

≤

≤

=

(

)

and recall that f is supported on

x1

b
} ≤

≤

≤

b

,

x1

≤

{
x1 − b
e2t − 1

(

√

)

Φ
1
≤ ⎧⎪⎪
2
⎨
⎪⎪⎩

(

}
− Ef
√e2t

1

−

)

A

B

x

x

∈

∈

{

}

0

Now, the set
Ef
φ
≤
Let A
)
so that f

1
2

(

=
=

f
{

Ef .
{
x1
≤
1A + 1B

b − Ef

. Now,
}

(

)

Φ

and so

Ef Φ

X1 − b
e2t − 1

(

√

)

=

≤

=

E1Af Φ

X1 − b
e2t − 1

+ E1Bf Φ

X1 − b
e2t − 1

)
E1Af + 1
2

(
E1Bf

√

)

Φ

−

(
√
Ef −

1
2

Ef
√
(
e2t − 1
1
2

)
− Φ

−

Ef
e2t − 1

Ef 1A.

− cx, 1
4

(5.1)

. Applying this with

There is a constant c
x

, we have

Ef
√e2t

=

1

−

(
0 such that for all x

(
0, Φ

√
−x

≥

max

≤

>

(

)

))
1
2

{

(5.1)

1
2

≤

Ef − Ef 1A min

c

Ef
e2t − 1

,

1
4

max

≤

Ef − c

1
2

}
where in the last inequality, we recalled that Ef 1A

√

{

{
Ef .

1
2

≥

2

}
Ef
e2t − 1
(
)
√

,

3
8

Ef

}

Proof of Proposition 5.1. Without loss of generality, B is the half-space
the positive part of 1A − 1B and let g be the negative part, so that γ
that f is supported on Bc and g is supported on B.

A∆B
{

x1

. Let f be
b
≤
Ef + Eg. Note

=

}

(

)

21



<!-- pdf-page: 22 -->
Without loss of generality, Ef

≥

Eg; Lemma 5.2 implies that if Ef

2E

1BPtf + 1Bc Ptg

Ef + Eg − c

≤

2

Ef + Eg
e2t − 1
)

(

√

≤

C

e2t − 1 then

√

.

(5.2)

On the other hand, if Ef

(

≥

C

)
e2t − 1 then

√

2E

1BPtf + 1Bc Ptg

3
4

≤

Ef + Eg

7
8

≤

Ef + Eg

.

(5.3)

Thus,

(

)

(

)

}

E

Ptf − Ptg

∣

=

∣

=

≥

≥

EPtf + EPtg − 2E min
Ef + Eg − 2E min
Ef + Eg − 2E

Ptf, Ptg

Ptf, Ptg
{
1BPtf + 1Bc Ptg
}
Ef + Eg
8

{
2

,

,

)

min

c

Ef + Eg
(
e2t − 1
)

(

√
Where we have applied (5.2) and (5.3) in the last inequality. Now there are two cases,
depending on which term in the minimum is smaller: if the ﬁrst term is smaller then

}

{

otherwise, the second term in the minimum is smaller and

)

(

∣

∣

Ef + Eg

≤

C

e2t − 1

4
1
/

E

Ptf − Ptg

;

√

In either case,

Ef + Eg

≤

8E

Ptf − Ptg

.

∣

∣

γ

A∆B

as claimed.

(

Ef + Eg

≤

=

)

C max

E

Ptf − Ptg

,

e2t − 1

4
1
/

E

Ptf − Ptg

,

{

∣

∣

(

√

∣

)

∣}

5.1 Synchronizing the time-reversal

(

)

)

=

>

0.

Proposition 5.1 would be enough if we knew that E
Pt1A − Pt1B
sition 4.1 and Lemma 3.1 imply that E
Pt1A − Pt
s1B
(
t
+
section, we will show that if e−
case for arbitrary sets A; in fact, for any s
is arbitrarily small. Fortunately, we have some extra information on A: we know that it is
)
ρ then E1APt1A is
t
almost optimally noise stable with parameter ρ. In particular, if e−
close to E1BPt1B.

2 were small. Now, Propo-
In this
ρ then s must be small. Now, this is not necessarily the
2

≥
Pt1A − Pt
s1B
+

0 one can ﬁnd A such that E

2 is small, for some s

Using this extra information, the proof of robustness proceeds as follows: since E1APt1A
s1B, we will show that E1BPt
is close to E1BPt1B and Pt1A is close to Pt
s1B is close to
E1BPt1B. But we know all about B: it is a half-space. Therefore, we can ﬁnd explicit and
+
+
accurate estimates for E1BPt
s1B and E1BPt1B in terms of t, s and γn
; using them, we can
+
conclude that s is small. Now, if s is small then we can show (again, using explicit estimates)
that E
2 is small (this was our starting point,
Pt1A −Pt
s1B
remember), we can apply the triangle inequality to conclude that E
2 is small.
+
Finally, we can apply Proposition 5.1 to show that E

(
Pt1A − Pt1B

Pt1B −Pt
s1B
+

2 is small. Since E

is small.

)
1A − 1B

B

=

(

)

(

)

(

(

)

22

∣

∣



<!-- pdf-page: 23 -->
Proposition 5.3. For every t, there is a C
Rn, suppose that B, B′ ⊂
there exist s, ǫ1, ǫ2

Rn are parallel half-spaces with γ
(

0 such that

)

t

such that the following holds. For sets A, A′ ⊂
B
. If

, γ

A

γ

γ

A′

=

B′

=

(

)

(

)

(

)

(

)

>

E

Pt1A − Pt
s1B
+

2

ǫ2
1

≤

(
E1APt1A

)

E1BPt1B

− ǫ2

′

′ ≥

and

then

where I

x

E

Pt1A − Pt1B

2

2
1
/

C

t

≤

φ

1
Φ−

(
x

(

.

)

)

(

)

ǫ1 + ǫ2

I

γ

A

I

γ

A
′

,

C

t
)
(

(

(

(

))

(

(

)))

=

Rather than prove Proposition 5.3 all at once, we have split the part relating E
Pt
s1B
+

into a separate lemma.

(
2 and E1B

− Pt
s1B
+

(
))
Pt1B

)

(

′

′

Pt1B −

(

t

such that for any parallel half-spaces B and B′,

Lemma 5.4. For every t there is a C
(
)
and for every s
0,

)

>

E

Pt1B − Pt
s1B
+

2

)
(
2
1
/

C

t

≤

E1B

Pt1B

′

− Pt
s1B
′
+
C

I

γ

B
(

I

γ

B

′

.

t
)
(
)

(
Proof. First of all, one can easily check through integration by parts that for a smooth
function f ∶ R → R,

)))

))

(

(

)

)

(

(

(

(

)

(

∞

φ

x

Lf

x

dx

−f ′

b

φ

b

.

By rotating B and B′, we can assume that B
)
tx
E1BPt1B
b
e
−
−
2t
√1
e
−
−

∞a φ

′ = ∫

)(

Φ

x

(

=
x1
x1
dx and consider its derivative: by (5.4),
{

and B′ =
(
)

a
(

)(

=

≤

{

)

b

∫

(5.4)

b

. Let Fab

t

≤

=

}

(

)

(

)

(

)
F ′ab

t

(

)

}
tx − b
e−
1 − e
2t
−

dx

)

ta − b
e−
(
√
1 − e
2t
−
a2 + b2 − 2e−
√
(
)
−
1 − e
2t
−

tab

2
a2 + b2
(
1 − e
2t
−

)

.

)

∞

φ

x

LΦ

= ∫
a

−ktφ

(
a

)
φ

=

=

≤

−

kt
2π
kt
2π
−x

−

(
)
exp

(

−

exp

(
2t
1 − e−

F ′ab

(
τ

/(
−

kt
s
+
2π

≤

))

exp

−

a2 + b2
1 − e
2t
−

.

Now, kt is decreasing in t and exp
τ

t, t + s

,

is increasing in t. In particular, for any

)

[

]

Hence,

∈

≥

)
a2 + b2
−s max
1 − e
2t
t
s
−
≤
≤
s decreases exponentially in s. However, when
If s is large, this is a poor bound because skt
)
+
s

1 we can instead use

skt
s
+
2π

− Fab

t + s

(5.5)

F ′ab

exp

Fab

−

≥

≥

(

)

(

)

(

(

(

)

(

)

τ

t

.

τ

Fab

t

− Fab

t + s

Fab

t

− Fab

t + 1

≥

kt
1
+
2π

≥

exp

−

a2 + b2
1 − e−
2t

(

)

(

)

(

)

(
23

)

(

.

)

(5.6)



<!-- pdf-page: 24 -->
Equations (5.5) and (5.6) show that if E1B

The next step, therefore, is to control E

E

Pt1B − Pt
s1B
+

2

E

=

Pt1B

)

(

E1B
((
Faa
(
F ′aa
s
(
(
where the inequality follows because
(

≤

=

=

(

is small then s must be small.

′

− Pt
Pt1B
s1B
′
2 in terms of s. Now,
+
Pt1B − Pt
s1B
(
+
2 − 2
2 +
Pt
s1B
)
(
+
1B − 2P2t
P2t1B + P2
s1B
s
t
)(
(
)
)
(
+
(
+
)
2t + s
− Faa
2t + s
−
Faa
2t
)
2t + 2s
− F ′aa
))
(

Pt
s1B
+

))
− Faa

)
Pt1B

2t
)

,
(

(

)

(

2t + 2s

(5.7)

))

)

(
a2
t
1 − e−
1 − e
2t
−
)
(
and so F ′aa is an increasing function. To control the right hand side of (5.7), we go to the
second derivative of F :

a2
1 + e
t
−

kt
2π

kt
2π

F ′aa

exp

exp

−

−

−

−

=

=

(

)

(

)

))

)

(

t

t

F ′′

2 exp
3
/
This is decreasing in t; hence

2π

=

(

)

e2t
e2t − 1

)

(
E

Pt1B − Pt
s1B
+

−

a2
1 + e
t
−

+

2π

1
e2t − 1

a2e−
t
1 + e
t
−

2 exp

−

(

2

≤

)

√

s

F ′

2t

− F ′

(
2t + 2s

)
2s2F ′′

≤

(

2t

.

a2
1 + e
t
−

)

(5.8)

We will now complete the proof by combining our upper bound on E
Pt1B − Pt
s1B
(
)
(
)
+
− Pt
kt
1. Then kt
s1B
1
s
≥
)
+
+
+

with our lower bounds on E1B
and so (5.5) plus (5.8) implies that

))
(
. First, assume that s

)
Pt1B

≤

(

(

(

2

′

′

E

Pt1B − Pt
s1B
+

2

(

(

)

)

(
2
1
/

2π exp

2π1
−

(
2
e

1

−

−

≤

=

)
a2 + b2
1 − e−
2t
2F
kt
+

√

2t

2t

2F ′′
kt
1
(
)
+
E1B

√

2t

)
′′

1
(

I

γ

)

B
(

E1B

Pt1B

− Pt
s1B
+

′

′

(
Pt1B
′
γ

I

− Pt
s1B
+

)

.

B′

1

′
2
2t
e
)
−

−

If we take C
the other hand, if s

≥

t

max

(

)

>

′′

2t

2F

2t
1 − e−
1, 2
kt
+
1 then (5.6) implies that
√
)/
{
2
e

2t

/(
E1B

Pt1B

1

(
2π1
−
kt
+

−

−
1

I

γ

B
(

I

)}
− Pt
s1B
+

′
γ

B

′

1.

1

′
2
2t ≥
e
)
−

−

then the Lemma holds in this case. On
)))

))

(

(

(

(

(

Since E

Pt1B − Pt
s1B
+

2

≤

(

)

(

(

1 trivially, the Lemma holds in this case provided that
)))
2t
1 − e−

max

))

C

1

(

(

(

t

.

≥

1, 2
kt
+

Proof of Proposition 5.3. By the Cauchy-Schwarz inequality,
)}

E1APt1A

{
E

)
(
/
/(
E1APt
Pt1A − Pt
s1B +
s1B
≤
+
+
E1BPt
s1B since B is a super-level set of Pt
s1B with the same
+
+

E1APt
s1B + ǫ1.
+

√

≤

(

)

2

≤

Moreover, E1APt
s1B
+
volume as A. Thus,

E1BPt1B − ǫ2

E1APt1A
E1APt
s1B + ǫ1
+
E1BPt
s1B + ǫ1.
+

≤

≤

≤

24



<!-- pdf-page: 25 -->
By Lemma 5.4,

E

Pt1B − Pt
s1B
+

2

2
1
/

≤

C

t

E1B

Pt1B − Pt
s1B
+

≤

C

t

ǫ1 + ǫ2

Finally, the triangle inequality gives

(

(

)

)

(

)

(

)

(

)(

E

Pt1A − Pt1B

2

2
1
/

(

(

)

)

≤

≤

2

2 +
1
/

E

Pt1B − Pt
s1B
+

E

ǫ1 + C
(
(

Pt1A − Pt
s1B
+
ǫ1 + ǫ2
.
t
)
t
)

)(

(

(

(

)

.

Of course, 1 can be absorbed into the constant C

)

2

2
1
/

)

)

5.2 Proof of robustness

(

)

t
Proof of Theorem 1.4. First, deﬁne t by e−
of δ in Proposition 4.1 becomes

=

ρ. We then have k2

t =

ρ2
ρ2 and so the exponent
−

1

1

ρ2

ρ2

1

ρ
)

1 + 4

1
(

⋅

1
1 + α =

1 − ρ2
1 − ρ
1 − ρ + 3ρ2 + ρ3
(
)
)(

−

)(

−
0 (depending on ρ) so that (5.9) is

⋅

1
1 + α

.

(5.9)

Of course, we can deﬁne α

>

1 − ρ2

1 − ρ

1 + 3ρ
)(

.

)

for some A, A′ ⊂
kt and

η ∶
=

(
1A
=
a

′
≤
− Φ
∣
∣

a, X

− b

2

≤

C

ρ

mc

)δη.
ρ
(

Rn. Proposition 4.1 implies that

Now suppose that f

there are a

Rn and b

∈

1A and g
=
R such that

∈
E

Pt1A

X

((
x

)(
; then

Since
Φ

a
a, x
∣

≤
− b

∣
⟩

(⟨

Pt
s1B
+

=

)

(

)(

)

E

kt, Lemma 3.1 implies that we can ﬁnd some s
(

))

(⟨

)

⟩

0 and a half-space B such that
)
>

Pt1A − Pt
s1B
+
γ

B

A

C

ρ

mc

)δη.
ρ
(

2

≤

(5.10)

; however, we can ensure this by modifying B
)

)

(

At this point, it isn’t clear that γ
slightly:

(

Pt1A − Pt
s1B
+
Therefore let ˜B be a translation of B so that γ

≥

E

)

2
(

(

)

(

=
)
EPt1A − EPt
s1B
+
˜B

(

E

Pt1A − Pt
s1 ˜B
+

2

2
1
/

(

(

)

)

≤

≤

≤

E

E
(

2
(

Pt1A − Pt
(
)
s1B
+
Pt1A − Pt
s1B
(
+
E
Pt1A − Pt
s1B
)
(
+

2
)

2

γ

A

− γ

B

2.

=
. By the triangle inequality,
(
))

(

)

(

E

γ
(

s1B − Pt
Pt
s1 ˜B
+
+
2
1
˜B
− γ
/

B
(

2

2
1
/

)

)

∣

(

)

(

)∣

=
2

γ

A
)
2 +
1
(
)
/
2 +
1
/
)
2
1
2
/
)

.

By replacing B with ˜B, we can assume in (5.10) that γ
)
C

by a factor of 2).

ρ
Now we apply Proposition 5.3 with ǫ2
)

Proposition 5.3 leaves us with

C

ρ

mc

1 =

(

(

)

(

A

γ

B

=
(
)
)δη and ǫ2
ρ
(

(

)

(at the cost of increasing

δ. The conclusion of

=

E

Pt1A − Pt1B

2

2
1
/

(

(

)

)

(
C

C

)
ρ

mc
mc
ρ
)
(

≤

≤

ρ
)
(
)δη
ρ
(
(

ǫ1 + ǫ2
2.
/

)

(

)

25



<!-- pdf-page: 26 -->
where we have absorbed the constant C
E

ρ
2 for any random variable X, we may apply Proposition 5.1:
1
/
)

from Proposition 5.1 into C

EX 2

X

≤

(

t

and c

ρ

. Since

(

)

∣

∣

(

)

γ

A∆B

E

Pt1A − Pt1B

(
)
ρ

C

≤

√
E
Pt1A − Pt1B
ρ
∣
)
(
4.
)δη
ρ
mc
ρ
/
(
)(
(
(
By applying the same argument to A′ and B′, this establishes Theorem 1.4 in the case that
f and g are indicator functions.

4
1
/

2
∣

C

C

≤

≤

)

(

)

)

)

(

To extend the result to other functions, note that EJ
where ˜X and ˜Y are ρ-correlated Gaussian vectors in Rn

A
=
A′ =
{(
and Eg
{(

x, xn
x, xn

1

+

∈

1

)

+
γn

∈
A′

Rn

Rn

1 ∶ xn
+
1 ∶ xn
+

1

+

1

+

≥

≥

Moreover, Ef
in dimension n + 1, we ﬁnd a half-space B so that
)

1
)
+

γn

A

=

=

(

)

+

1

(
A∆B

γn

1

+

C

ρ

mc

)δη
ρ
(

4.
/

≤

X
f
1, and
+
)
(
(
1
x
f
Φ−
1
Φ−

g
(

x
(

, g

Y

EJ

1A

=

˜X

, 1A

′

˜Y

(

))

(

(

)

(

))

.
))}

. Applying Theorem 1.4 for indicator functions

(

(

))}

By slightly perturbing B, we can assume that it does not take the form
(
n; in particular, this means that we can write B in the form
1

)

(

)

i

≤

≤

(5.11)

xi

≥

b

for any

{

}

for some a

Rn and b

∈

∈

B

x, xn

=
R. But then

{(
A∆B

γn

1

+

Rn ∶ xn

1

+

≥

a, x

− b

.

f

X

− Φ

⟩

⟨
a, X

}

− b

;

1

+

∈

)
E

=

combined with (5.11), this completes the proof.

(

)

∣

(

)

(⟨

⟩

)∣

6 Optimal dependence on ρ

In this section, we will prove Theorem 1.5. To do so we need to improve the dependence on ρ
that appeared in Theorem 1.4. Before we begin, let us list the places where the dependence
on ρ can be improved:

1. In Proposition 4.3, we needed to control

Eρ exp

β

v2
t

X

+ w2
t

− 2ρvt

X

wt

Y

.

Y
2
(

1 − ρ2
)

(

)

(

)

(

)

Of course, the denominator of the exponent blows up as ρ → 1. However, if vt
wt then
(
the numerator goes to zero (in law, at least) at the same rate. In this case, therefore,
we are able to bound the above expectation by an expression not depending on ρ.

=

(

)

)

2. In the proof of Proposition 4.1, we used an L

bound on

∇vt

and

∇wt

to show that

∞

for some r

1,

<
Eρ

∇vt

X

− ∇wt

Y

2

1
r
/

≤

C

t

Eρ

∇vt

X

∣
∣
− ∇wt

Y

∣

2r

∣
1
r
/

.

This inequality is not sharp in its ρ-dependence because when vt
(∣
)∣
(
side shrinks like
get the right ρ-dependence by using an Lp bound on
(
H¨older’s inequality, instead of an L

wt, the left hand
)
)
(
1
r as ρ → 1, while the right hand side shrinks like 1 − ρ. We can
/
∇vt
when applying

(
1 − ρ

bound.

− ∇vt

)∣
=

X

(∣

Y

)

)

(

(

)

)

∞

26

∣

(

)

(

)∣



<!-- pdf-page: 27 -->
t
3. In applying Proposition 5.3, we were forced to take e−

ρ. Since most of our bounds
have a (necessary) dependence on t, this causes a dependence on ρ which is not optimal.
To get around this, we will use the subadditivity property of Kane [24], Kindler and
t is
O’Donnell [29] to show that we can actually choose certain values of t such that e−
much smaller than ρ. In particular, we can take t to be quite large even when ρ is close
to 1.

=

Once we have incorporated the ﬁrst two improvements, we will obtain a better version of

Proposition 4.1:

Proposition 6.1. For any α, t
0, 1

, there exist a

Rn, b

>
R with

0, there is a constant C
kt such that

a

∈

∈

≤

[

]

E

ft

X

− Φ

X, a

∣
∣
− b

2

C

t, α

≤

1
1
m (

+
+

kt
8k

(
α

2

2
)
t −

)

δ
1 − ρ

ρ

1
8k

1

+

α

2
t −

.

t, α

such that for any f ∶ Rn →

where kt

=

(
−

(⟨
f

(
e2t − 1

)
2, δ
1
, f
/
Moreover, this statement holds with a C

(
Y
t, α
))
(
Once we have incorporated the third improvement above, we will use the arguments of
)
(

)
√
)
− J
f
, and m
which, for any ﬁxed α, is decreasing in t.
(

(
Ef, Ef

1 − Ef

⟩
EρJ

))
f

Ef

X

=

=

(

)

(

)

)

(

(

)

)

(

)

(

.

Section 5 to prove Theorem 1.5.

6.1 A better bound on the auxiliary term

First, we will tackle item 1 above. Our improved bound leads to a version of Proposition 4.3
with the correct dependence on ρ.
e2t − 1

∞ such that for any

2. There are constants 0
1
/

c, C

−

<

<

Proposition 6.2. Let kt
t

0, if r

then

=

1

1
8k2
t
+

≤

>

dRt
dt ≥

where m

f

=

Ef

1 − Ef

√
.

(
ρ
1 − ρ2

)

cm

f

kt

1
(

+

2

)

E

∇vt

X

− ∇vt

Y

2r

1
r
/

(

(

))

(

∣

(

)

(

)∣

)

To obtain this improvement, we note that for a Lipschitz function v,

(

)

(

)

satisﬁes a Gaussian tail bound that does not depend on ρ:
Lemma 6.3. If v ∶ Rn → R is L-Lipschitz then

v

X

−v

Y

1 − ρ

(

(

)

(

√

))/

In particular, if 4βL2

<

Prρ

v

X

− v

Y

Ls

≥

(
(
1 then

)

(

)

2
√

1 − ρ

1 − Φ

s

.

≤

))

(

)

(

2

Eρ exp

v

β

Y

X

− v
1 − ρ
(
(
)
))
(
, so that EZ 2
X
Y
)
(
−
2
Z1 − Z2

(

.

≤

1
1 − 4βL2
2 and EZ 2

√

)
1
+

ρ

ρ
2 . Now we condition on
−
is 2L-Lipschitz in Z2 and has conditional median

2 =

1 =

1

X

Proof. Let Z1
+
2
Z1: the function v
zero (because it is odd in Z2); thus

Y
and Z2
Z1 + Z2

=
− v

=

(
Prρ

)
Z1 + Z2

(
− v

)
Z1 − Z2

v

≥
Now integrate out Z1 to prove the ﬁrst claim.
)
(

(
Proving the second claim from the ﬁrst one is a standard calculation.

)∣

(

)

)

(

(

)

Ls

2
√

1 − ρ

Z1

1 − Φ

s

.

≤

27



<!-- pdf-page: 28 -->
Next, we use the estimate of Lemma 6.3 to prove a bound on

)
that is better than the one from (4.10) which was used to derive Proposition 4.3.

(

)

(

(

)

(

)

Eρ exp

β

v2
t

X

+ v2
t

− 2ρvt

X

wt

Y

Y
2
(

(

1 − ρ2
)

)

Lemma 6.4. There is a constant C such that for any t

0, and for any β

0 with 6βk2

t ≤

>

1,

Eρ exp

β

v2
t

X

+ v2
t

(
where Mt is a median of vt.

(

)

Y
2
(

>
vt

Y

− 2ρvt

X

1 − ρ2
)

(

)

(

)

(

)

CeM 2

t

2,
/

≤

)

Proof. We begin with the Cauchy-Schwarz inequality:

Eρ exp

β

v2
t

X

+ v2
t

(
Eρ exp

β

(

vt

(
Eρ exp

(

2β

)
X
2

(
vt

=

≤

X

vt

Y

(
)
exp

(
vt
β

2

)

2
1
(
/

− 2ρvt

1 − ρ2
)
2
Y
)

Y
2
(
− vt
(
1 − ρ2
(
)
− vt
X
)
(
1 − ρ2
2
(
)
)
(

))
Y

(

Y

)
vt
X
)
1 + ρ
)
(
)
)
X
vt
1 + ρ
(
)

2β

exp

2

2
1
/

.

(6.1)

))
Now, recall from Lemma 3.2 that vt is kt-Lipschitz. In particular, Lemma 6.3 implies that
if 8βk2
2. Finally, Lemma 4.4 implies that the
second term of (6.1) is bounded by CeM 2

1 then the ﬁrst term of (6.1) is at most

t ≤

))

))

(

(

(

(

(

(

t

√

2.
/

Proof of Proposition 6.2. First, follow the proof of Proposition 4.3 up until (4.9). At this
point, we can apply Lemma 6.4 to obtain

dRt
dt ≥

c

ρ
1 − ρ2

eM 2

t

2
/

Eρ

∇vt

X

− ∇vt

Y

2r

1
r
/

,

(
√
and we conclude by applying Lemma 4.5, which implies that

(

(

)

∣

)∣

)

eM 2

t

2
/

≥

cm

f

kt

1
(

+

2

)

.

))
6.2 Higher moments of ∣∇vt(X) − ∇vt(Y )∣

(

(

Here, we will carry out the second step of the plan outlined at the beginning of Section 6.
The main result is an upper bound on arbitrary moments of

X

Y

− ∇vt

∇vt

.

Proposition 6.5. There is a constant C such that for any t

∣
>

Eρ

∇vt

X

− ∇vt

Y

q

1
q
/

Ck2
t

≤

1 − ρ

1 + kt

q
√

(

∣

(

If we ﬁx q and t, then the bound of Proposition 6.5 has the right dependence on ρ. In
kt, which does not improve as

)((
(
particular, we will use it instead of the uniform bound
ρ → 1.

))

)∣

≤

)

(

)

(

(

/

)

There are two main tools in the proof of Proposition 6.5. The ﬁrst is a moment bound
F denotes the Frobenius

on the Hessian of vt, which was proved in [35]. In what follows,
norm of a matrix.

⋅

√
)
∇vt

∣

∣

(

0 and any 1
(
)
≤
+

m

f

1

log

∞,

q
)∣
<

qkt

.

√

∥

∥

28



<!-- pdf-page: 29 -->
Proposition 6.6. Let Hvt denote the Hessian matrix of vt. There is a constant C such that
for all t

0 and all 1

∞,

q

>

≤

<

E

Hvt

1
q
/

q
F

Ck2
t

1 + kt

≤

log

1
f

m

+

qkt

√

)

√
)

(

)
Hvt

F .

The other tool in the proof of Proposition 6.5 is a result of Pinelis [38], which will allow

us to relate moments of

X

− ∇vt

Y

to moments of

∥

)

(

∥
∇vt

((

Proposition 6.7. Let h ∶ Rn → Rk be a C 1 function and let Dh be the n × k matrix of its
partial derivatives. If Z1 and Z2 are independent, standard Gaussian vectors in Rn then

)∣

(

)

∥

(

∥

∣

E

h

Z1

− h

Z2

q

1
q
/

C

E

q

Dh

1
q
/

q
F

≤

for every 1

q

√
∞, where C is a universal constant.

)∣

)

(

)

(

(

∣

(

∥

∥

)

≤

<
Proof. Deﬁne f ∶ R2n → Rk by f
Z1
that if Ψ ∶ Rk → R is a convex function then for any function f ∶ R2n → Rk with Ef
(

where Z

Z1, Z2

− h

Z2

Z

h

=

=

(

)

0,

=

. Pinelis [38] showed

(
EΨ

)
f

)
EΨ

)
Df

(
π
2

Z

≤

Z

⋅ ˜Z

,

where ˜Z is an independent copy of Z. Applying this with Ψ
Df

⊗ Dh, we obtain

(

(

))

(

)

(

)

x

=

x

q, and noting that

(

)

∣

∣

E

f

Z

q

≤

C qE

Dh

Z1

⋅ Z2

q.

q

q

2
/

A

F for any ﬁxed matrix A; if we apply this fact conditionally on

)∣

(

)

(

∣

∣

∣

1 0
1
0

−

=

(

)

Now, E
C
AZ2
Z1, then we obtain

≤

q

∣

∣

(

√

)

∥

∥

E

f

Z

q

C

qE

q

Dh

q
F .

≤

√
Proof of Proposition 6.5. Let Z, Z1 and Z2 be independent standard Gaussians on Rn; set
)∣
1 − ρZ2 so that X and Y are standard Gaussians with
X
correlation ρ. Conditioned on Z, deﬁne the function

1 − ρZ1 and Y

∣
(
ρZ +

ρZ +

=

=

(

)

∥

∥

√

√

√

√

h

x

so that h

Z1

=

∇vt

X

and h

Z2

(

)
=

=
∇vt

∇vt

Z +

1 − ρx

,

√
√
Y
. Note that
(

)

(

)

(

)

Dh

x

(

1 − ρ
(

Hvt
)

ρZ +

1 − ρx

;

√
thus Proposition 6.7 (conditioned on Z) implies that
(

)(

)(

(

)

)
=

√

√

qE

)

Hvt

X

q
F

Z

.

E

∇vt

X

− ∇vt

Y

q

Z

C

≤

1 − ρ

q
√

Integrating out Z and raising both sides to the power 1

)∣

∣

(∣

)

(

(

(

)

(

))

q, we have
(∥
(

)∥

∣

)

E

∇vt

X

− ∇vt

Y

q

1
p
/

C

≤

1 − ρ
/

E

Hvt

1
q
/

.

q
F

q
√

We conclude by applying Proposition 6.6 to the right hand side.

)(

∥

)∣

)

(

∣

(

)

(

(

∥

)

With the ﬁrst two steps of our outline complete, we are ready to prove Proposition 6.1.
This proof is much like the proof of Proposition 4.1, except that it uses Propositions 6.2
and 6.5 in the appropriate places.

29



<!-- pdf-page: 30 -->
α

<

<

2, 0

r

<

<

(6.2)

2. Lemma 4.2

)

2
γ
/

Proof of Proposition 6.1. For any non-negative random variable Z and any 0
1, H¨older’s inequality applied with p

γ implies that

2r

EZ 2

=

EZ γZ 2
−

γ

≤
2 − γ

In particular, if we set q

2r

=

=
EZ 2r

γ

/

2r

/(

EZ 2r

)

γ

2
(

−

2r

)/(

γ

−

)

2r
(

γ

−

2r

)/(

).

(

2r − γ
)

then we obtain

(

)

(

)/(
1
r
EZ 2r
/

)

(

≥

EZ q

⎛
)
⎜
E∇vt and ǫ
⎝

(

2
γ
/

.

EZ 2
2
(

γ

q
)/

−

⎞
⎟
⎠
vt

(
2
γ
/

Now, set Z
and Proposition 6.5 then imply that the right-hand side of (6.2) is at least

X, a

, a

X

X

Y

=

=

=

− ∇vt

∇vt

)
vt

−

E

− Evt

∣

(

)

(

)∣

(

)

(

)

⟨

⟩

2

1 − ρ

ǫ

vt

1 − ρ

1 + kt
(

log
)
(

1

m
)

f

+

qkt

2

γ

−

(

)((

√
)

(

√

))

ck2
t

q
√

⎛
⎜
⎜
⎝

(

⎞
⎟
⎟
⎠

ǫ

vt

(
))
1 − ρ

/
c
√

=

k2
t

⎛
⎜
⎜
(
⎝
and choose r
=
2 −
2r − αη

q

1 + kt

log
(

1

m
)

f

+

qkt

2

γ

−

√
)

(
1 − η (so as to satisfy the hypothesis of Propo-
α
1, we will ﬁnd that

η for some 0

((
2 + α

))

))

(

/

√

⎞
⎟
⎟
⎠

8k2
t

Now deﬁne η
=
sition 4.3). If we then deﬁne γ
q

1 + 8k2
t

)

6

2r 2
α
+
α ≤

=

<
=
α. In particular, the last displayed quantity is at least

/(

=

<

/

1 − ρ

cα

γ

2
(

−

(

)(

)

γ

)/

k3
t

+ 1

)
vt

ǫ

log
(

1
)

2
γ
/
m

f

γ

2
(

−

γ

)/

√

(

√
)

k3
t + 1

2
(

γ

−

)/

γ depends only on t, we can put this all together (going back to (6.2)) to
/

)))

((

(

(

Since
obtain
(

)

E

∇vt

X

− ∇vt

Y

2r

1
r
/

(

∣

(

)

(

)∣

)

≥

=

Combined with Proposition 6.2, this implies

c

t, α

1 − ρ

logC

(

)(

)

c

t, α

1 − ρ

(

)(

)

ǫ
t
)
(
(

2
γ
vt
/
m
1
)
2
8k
1
t
2
(
/
+
4αk
t
−
1

m

(

1

f

f

vt
ǫ
t
logC
)
(
(

)

))

.

(

/

(

))

m
logC

f
t
)
(
(

kt

+
m

1
(
1
)

2

)
f

ǫ

vt

1

1

2
8k
t
2
+
4αk
t

−

ρ

1 − ρm

1
/
(
+
(

2
kt
(
)

αǫ
))
+

f

(
vt

1

)
1

2
8k
t
2
+
4αk
t ,

−

(6.3)

0 and every C, there is a C ′
where the last line follows because for every α
)
)
)
such that for
α. Now, with (6.3) as an analogue of (4.12), we complete
every x
the proof by following that of Proposition 6.1. Let us reiterate the main steps: recalling that

4 , logC

(
x−

C ′

(
>

α

α

x

≤

≤

1

(

(

)

1

dRt
dt ≥

≥

c

t

ρ

1 − ρ

√

(
)
t, α
c

√

(

/

)

(

)

30



<!-- pdf-page: 31 -->
dRs
ds ds, we see that for any α, t

δ
By (6.3) applied with t

= ∫

s, we have

∞0

=

ǫ

vs

≤

C

t, α

m (

0, there is some s

>

t, t

1 + α

so that dRt
dt

∈

2

1

kt

+

)
1

4αk
1
2
−
(
8k
t

+

2
t

)

α

−

ρ

[

δ
1 − ρ

)]

1

(
2
4αk
t
2
8k
t .

+

−
1

δ
αt .

s ≤

∣

Now, note that Φ is a contraction, and so Lemma 4.6 implies that

(

)

(

)

(

√

)

E

ft

X

1
− P −
tΦ
s
−

X, E∇vs

− Evs

2

(

(

)

(⟨

⟩

))

C

t, α

m (

≤

2

1

kt

+

)
1

4αk
1
2
−
(
8k
t

+

2
t

)

α

−

δ
1 − ρ

ρ

2
4αk
t
2
8k
t −

α

1

−
1

+

.

By changing α and adjusting C
t, α
that was claimed in the proposition.

accordingly, we can put this inequality into the form

(

)

(

√

)

Finally, recall that
written in the form Φ

E∇vs
X, a
∣

≤
− b
∣

)

(
1
ks by Lemma 3.2, and so P −
tΦ
s
Rn, b
−
a
for some a

R with

∈

∈

kt.
(⟨

≤

⟩
6.3 On the monitonicity of δ with respect to ρ

(⟨

)

∣

∣

X, E∇vs

− Evs

can be

⟩

)

=

The ﬁnal step in the proof of Theorem 1.5 is to improve the application of Lemma 5.4.
Assuming, for now, that f is the indicator function of a set A, the hypothesis of Theorem 1.5
ρ then E1APt1A is almost as large as possible; that is, it is almost as large as
t
tells us if e−
E1BPt1B where B is a half-space of probability Pr
A
. This assumption allows us to apply
Lemma 5.4, but only with t
. In particular, this means that we will need to use
this value of t in Proposition 6.1, which implies a poor dependence on ρ in our ﬁnal answer.
To avoid all these diﬃculties, we will follow Kane [24] and Kindler and O’Donnell [29] to
, then it is also large for certain

show if E1APt1A is almost as large as possible for t
values of t that are larger.

log

log

=

=

ρ

ρ

1

1

)

(

(

)

/

Proposition 6.8. Suppose A
and

⊂

Rn has Pr

A

1

=

/
(
2. If θ

)

=

cos

k cos−

1 ρ

for some k

N,

∈

J

1

2, 1

2; ρ

(
− EρJ

)
1A

/
X

, 1A

Y

; ρ

(
δ
≤

)

then

(
1

/
2, 1

/
2; θ

)
− EθJ

(
1A

(
X

)
, 1A

(
Y

)
; θ

J

)

≤

kδ

Proof. Let Z1 and Z2 be independent standard Gaussians on Rn and deﬁne Z
)
Z2 sin γ. Note that for any γ and any j
In particular, if γ

)
)
(
N, Z
and Z
, then the union bound implies that

Z1 cos γ +
=
have correlation cos γ.
)

)
j + 1

(
γ

jγ

γ

ρ

(

(

(

∈

/

/

1
cos−

=

Prθ

A, Y
)

X
(
∈

(

A

)

∈

/

=

≤

=

Pr

Z

0

k

1
(
(
−
Pr
∑j
0
=
k Prρ

((

A, Z

∈

)
)
kγ

A

∈

(

)

)
Z

jγ

∈

(
A, Z

) /

j + 1
)

γ

A

∈

(
X

)
A, Y

(
∈

∈

A

((
.

)

) /

)

(6.4)

The remarkable thing about this inequality is that it becomes equality when A is a half-space
of measure 1

2, because in this case, Prρ

A, Y

X

A

ρ

(

/

.

)
1
1
2π cos−

∈

∈

=

/

(

/

)

(

)

31



<!-- pdf-page: 32 -->
A

. Thus, the hypothesis of the

X

1A

Recall that EρJ

, 1A
proposition can be rewritten as
(
1
cos−

)

(
1
2

(
− 1
2π

Y

; ρ

=

Prρ

X

A, Y

∈

)
ρ

)
−

(
A

Pr

− Prρ

X

∈

∈

)
A, Y

which rearranges to read

(

(

))

(

(

)

By (6.4), this implies that

(

Prρ

X

A, Y

∈

A

δ +

≤

)

∈

/

(

1
2π

cos−

1 ρ.

A

δ,

≤

))

∈

/

Prθ

X

A, Y

∈

A

∈

kδ + 1
2π

≤

cos−

1 θ,

which can then be rearranged to yield the conclusion of the proposition.

/

)

(

Let us point out two deﬁciencies in Proposition 6.8: the requirement that Pr

2 and
1
that k be an integer. The ﬁrst of these deﬁciencies is responsible for the assumption Ef
2
/
in Theorem 1.5, and the second one prevents us from obtaining a better constant in the
exponent of δ. Both of these restrictions come from the subadditivity condition (6.4), which
only makes sense for an integer k, and only achieves equality for a half-space of volume 1
2 .
But beyond the fact that our proof fails, we have no reason not to believe that some version
of Proposition 6.8 is true without these restrictions. In particular, we make the following
conjecture:

=

=

1

(

)

A

Conjecture 6.9. There is a function k

ρ, a

such that

• for any ﬁxed a

∈
• for any ﬁxed a ∈

• for any a ∈

0, 1

0, 1

, k

ρ, a

∼

1 − ρ as ρ → 1;
(
√

)
∼ ρ as ρ → 0; and

ρ, a
(
)

, k
0, 1
(
)
and any A ⊂ Rn the quantity
(

)

(

)

(

)

J

a, a; ρ

(

)

is increasing in ρ.

− EρJ
k

X

1A
ρ, a
(
(

(

)

, 1A

Y

; ρ

)

(

)

))

If this conjecture were true, it would tell us that sets which are almost optimal for some
quantiﬁes the almost

ρ are also almost optimal for smaller ρ, where the function k
optimality.

ρ, a

In any case, let us move on to the proof of Theorem 1.5. If the conjecture is true, then

(

)

the following proof will directly beneﬁt from the improvement.

Proof of Theorem 1.5. We will prove the theorem when f is the indicator function of a set
A. The extension to general f follows from the same argument that was made in the proof
of Theorem 1.4.

Fix ǫ > 0. If ρ0 is close enough to 1 then for every ρ0 < ρ < 1, there is a k ∈ N such that
, where

−ǫ, π
∈
2
converge to zero as ǫ → 0. Moreover, this k must satisfy

. In particular, this means that cos

1
k cos−

− ǫ
2

, c2

π
2
ǫ

c1

ρ

ǫ

ǫ

1
k cos−
ǫ
c1

]

(

(

))

[

(

)

(

)]

∈
ρ
and c2
(
)

[
(

(

)

)

k ≤

C
ǫ
1
cos−
(

ρ
)
(

)
32

≤

.

C
ǫ
1 − ρ
)
(

√



<!-- pdf-page: 33 -->
Now let θ

cos

1
k cos−

=

ρ

. By Proposition 6.8, A satisﬁes

(

(
1

))
2, 1

J

2; θ

− EθJ

1A

X

, 1A

Y

; θ

C

ǫ

≤

δ
1 − ρ

.

/

/

(

(
)
Now we will apply Proposition 6.1 with ρ replaced by θ and t
it follows that kt
Proposition 6.1 gives us a
√
/

R such that
(

(where c3

≤
Rn, b

1 − θ2

c3

=

θ

(

(

)

(

)

)

)

(

)

∈

∈

ǫ

ǫ

)
√
=

log

θ
,
→ 0 with ǫ). Thus, the conclusion of
)
/
)

. Since θ

c2

≤

1

(

(

ǫ

E

Pt1A

X

− Φ

X, a

− b

2

((

)(

)

(⟨

⟩

))

C

θ

(
ǫ

C

≤

≤

√
(

δ
1 − θ
δ
)(
1 − ρ

1 − ρ
)
1
ǫ
c4
).
(
)

−

1

c4

−

ǫ
(

)

(6.5)

Now we apply the same time-reversal argument as in Theorem 1.4: Lemma 3.1 implies

(

)(

√

)

that there is some s

>

0 and a half-space B such that

E

Pt1A − Pt
s1B
+

2

≤
and we can assume, at the cost of increasing C
implies that

(

)

C

ǫ

δ

1 − ρ

1

c4

−

ǫ
(

)

√

)(
/
, that Pr

ǫ
(

B

)

=

Pr

A

. Then Proposition 5.3

E

Pt1A − Pt1B

2

(
C

)
ǫ

δ

(
1 − ρ

c4

1
)
−

ǫ
(

(
),

)

≤

√

and we apply Proposition 5.1 (recalling that t is bounded above and below by constants
(
depending on ǫ) to conclude that

)(

(

)

)

/

Pr

A∆B

≤

C

ǫ

δ

1 − ρ

c4

4
1
/

−

ǫ
(

4.

)/

√

is some quantity tending to zero with ǫ. Therefore, we can derive the claim
Recall that c4
)
of the theorem from the equation above by modifying C

)(

(

(

)

/

ǫ

ǫ

.

(

)

Finally, we will prove Corollary 1.9.

(

)

Proof of Corollary 1.9. Since xy

≤

J

x, y

, the hypothesis of Corollary 1.9 implies that

EJ

f

X

(
, f

)

Y

1
4

+ 1
2π

≥

arcsin

ρ

− δ.

Now, consider Theorem 1.5 with ǫ
In either case, the conclusion is that there is some a

>

1

(
))
8. If ρ

(

(

)
=

(

)
Rn such that

ρ0 then apply it; if not, apply Theorem 1.4.

E

f

X

/
− Φ

∈

X, a

C

ρ

δc.

≤

Setting g

X

Φ

X, a

=

)
, H¨older’s inequality implies that

⟩)∣

(⟨

(

)

(

∣

Eg
(

X
)

g

Y
(⟨

− Ef
⟩)

X

f

Y

∣

(

)

(

)

(

)

(

)∣

=

≤

E

2E
∣
(

X
g
f − g
(
)

− f

X

g

Y

+ Ef

X

g

Y

− f

Y

.

(

))

(

)

(

)(

(

)

(

))∣

In particular,

Eg

X

g

Y

∣
+ 1
2π

1
4

≥

∣

arcsin

ρ

− δ − C

ρ

δc.

(6.6)

(

)

(

)

(

)

(

)

33



<!-- pdf-page: 34 -->
But the left hand side can be computed exactly: if
then

a

e2t − 1

2 and A
1
/

−

x

∈

=

Rn ∶ x1

0

≤

(

)

{

}

=

∣

Y

∣
Pt1A

Eg

X

g

Y

=

(

)

(

)

=

=

≤

EPt1A
X
E1A
P2t
X
(
)
−
+ 1
1
arcsin
(
)
2π
4
1
+ 1
2π
4

arcsin

X

log

1A
ρ
)
(
)
(
2tρ
e−

(
− 1
)
2π

)

ρ

2t
1 − e−

,

(

)

(
ρ

(

)

where the last line used the fact that the derivative of arcsin is at least 1. Combining this
with (6.6), we have

2t
1 − e−

C

ρ

δc

≤

1
2

On the other hand,

E

g − 1A

=

2

1

2 − Eg1A

=

(
− 1
π

)

arcsin

t
e−

≤

)
∣
which combines with (6.7) to prove that E
g − 1A
we conclude that

(

/

∣

E

f − 1A

E

≤

∣
f − g

∣
+ E

C

ρ

≤
(
g − 1A

C

ρ

δc.

)

≤

∣
7 The robust “majority is stablest” theorem

(

)

∣

∣

∣

∣

∣

(6.7)

1 − e
2t,
−

√

(
δc. Applying the triangle inequality,

)

In this section, we prove Theorem 1.10. For the rest of this section, we set ξ and σ to be
n satisfying Eξiσi
uniformly random elements in
We begin the proof of Theorem 1.10 by recalling some Fourier-theoretic properties of
−1, 1

ρ for all i.

n. For S

−1, 1

χS ∶ S

by χS

S xi. Then

n

n

x

=

i
= ∏
. We will write ˆfS for the coeﬃcients of f in this
∈
]}

⊂

{

{

(

)

[

{
, deﬁne χS ∶
−1, 1
⊂
form an orthonormal basis of L2
{
}
basis; that is,

]

[

n →
n

}
−1, 1
−1, 1
}
}
x

f

{
({

}
ˆfSχS

)
= ∑S⊂[n]

x

.

(

)

(7.1)

Recall the Bonami-Beckner semigroup Qt deﬁned by

(

)

and denote Qtf by ft; then

(

)(

)

(

(

) ∣

)

Qtf

ξ

Ee

t
−

=

f

σ

ξ

,

Sρ

f

=

Eρf

ξ

f

σ

=

Ef flog(1/ρ).

)
7.1 The invariance principle

(

(

)

(

)

−1, 1

Note that any function f ∶
Rn through the Fourier expansion (7.1): since χS
ˆfSχS
}
{
g
S
= ∑
−1, 1
note that g and f agree on
(

n → R can be extended to a multilinear function from on
Rn, we may deﬁne
is deﬁned for all x
. We will say that g is the multilinear extension of f ;

x
n, thereby justifying the term “extension.”
(

Rn by g

for x

x

x

x

(

)

(

)

)

)

∈

∈

{

}

34



<!-- pdf-page: 35 -->
Let us remark on some well-known and important properties of multlinear polynomials.
1, it is trivial to check that for multlinear

0 and Eξ2

EX 2

EXi

=

i =

i =

First of all, since Eξi
functions f and g,

=

Ef
Ef 2
g
ξ

ξ

ξ
(
σ
(

=

=

)

)

=

Eρf

X

Ef
Ef 2
(
Ef
X
(

X
)
g
)

Y

.

0, Qtf and Ptf
It is also easy to check that if f is a multilinear polynomial then for any t
(
are the same polynomial. In particular, there is no ambiguity in using the notation ft for
both Ptf and Qtf .

>

)

)

(

(

(

)

)

ξ

>

X

and g

Despite these similarities, g

can have very diﬀerent distributions in general
x1). The main technical result of [36] is that when f has low inﬂuence
(for example, if g
x
=
(
and t
and ft
0, then ft
X
have similar distributions. We will quote a much less general
)
statement then the one proved in [36], which will nevertheless be suﬃcient for our purposes.
)
In particular, we will only need to know that if g
mostly
takes values in
. Before stating the theorem from [36], let us introduce some notation:
for a function f taking values in R, let ¯f be its truncation which takes values in

takes values in

(
(
0, 1

, then g

)
0, 1

0, 1

X

)

(

)

(

(

)

)

(

ξ

ξ

[

]

:

[

]

1

[

]

x

0
f

x
f
)
f

if f
if 0
if 1

0
<
x
x
(
(
τ then for any η

≤
(
<

1
⎨

= ⎧⎪⎪⎪⎪
⎪⎪⎪⎪⎩

≤
.
)
)
0,

(

X

− fη

X

2

≤

>
Cτ cη

¯f

x

≤
fη
)

1,

(
ρ′ <
fη
X

)
Theorem 7.1. Suppose f is a multilinear polynomial such that f
−1, 1
f

n. If f satisﬁes maxi Inf i

(

)

{

}

E
(

ξ

∈

0, 1

for all ξ

∈

(

)

[

]

(7.2)

We will now use Theorem 7.1 to prove Theorem 1.10. First, (7.2) and the triangle in-

(

)

(

))

equality imply that for any 0

<
fη

Eρ

′

Y

Eρ

′

≤

fη

X

fη

Y

+ Cτ cη.

Now,

)
Eρ
ξ
e2ηρ (assuming that η is small enough so that e2ηρ
)

)
2η ρ
′
−

If we set ρ′ =
(
the assumption (1.6) of Theorem 1.10 imply that

(
fη

(
Ee

(
fη

)
Y

Eρ

fη

fη

X

σ

=

=

f

)

)

(

(

)

(

(

)

)

(

ξ

′

′

f

(7.3)

(7.4)

σ

.

1) then (7.3), (7.4), and
(

)

<

Eρ

′

fη

X

fη

Y

(

)

(

)

J

J

J

≥

≥

≥

Ef, Eg; ρ
Efη, Efη; ρ
(
)
Efη, Efη; ρ′
)
(

− Cτ cη − δ

− Cτ cη − δ
− C

ρ

η − Cτ cη − δ,

where the second inequality follows because (by (7.2))
∂x
bounded. Applying Corollary 1.9 (with ρ′ in place of ρ) to fη, we see that there are a, b
such that

≤

∈

)

(

Ef − Efη
)

Cτ cη

and ∂J(x,y;ρ)

(

is
Rn

E

fη

X

− 1

a,X

≥0
b
⟩
−

}

{⟨

2

C

ρ

≤

∣
η + τ cη + δ

∣
c.

By (7.2) and the triangle inequality, we may replace fη by fη:
)

)(

(

(

(

)
2

E

fη

X

− 1

a,X

≥0
b
⟩
−

}

{⟨

C

ρ

η + τ cη + δ

≤

(

(

)

)
35

(

)(

)
c.

)

(7.5)



<!-- pdf-page: 36 -->
The next step is to pull (7.5) back to the discrete cube by replacing X by ξ. We will
has small

do this using Theorem 7.1. As a prerequisite, we need to show that 1
inﬂuences; this is essentially the same as saying that a is well-spread:

≥0
b
⟩
−

a,x

{⟨

}

Lemma 7.2. There is an a

Rn satisfying (7.5) with

∈

a2
i =

∑

1 and maxi

ai

Cτ c.

≤

Once we have shown that 1

≥0
b
⟩
−
show that the multilinear extension of 1

a,x

{⟨

}

has small inﬂuences, we can use Theorem 7.1 to

∣

∣

a,x

≥0
b
⟩
−

}

{⟨

is close to 1

a,x

:

≥0
b
⟩
−

}

{⟨

Lemma 7.3. Let ga,b be the multilinear extension of the function x ↦ 1
0,
and maxi

τ then for any η

ai

{⟨

a,x

. If

≥0
b
⟩
−

}

i a2

i =

∑

1

≤

>
ga,b
η

∣

∣

E

X

− 1

2

C

η + τ cη

.

a,X

≥0
b
⟩
−

≤

{⟨
From Lemma 7.3 and the triangle inequality, we conclude from (7.5) that

(

(

)

)

(

)

}

Since fη − ga,b
η
replaced by ξ:

E

fη

X

− ga,b
η

X

2

≤

C

ρ

η + τ cη + δ

c.

)(
is a multilinear polynomial, its second moment remains unchanged when X is

))

(

)

(

(

)

(

E

fη

ξ

− ga,b
η

ξ

2

≤

C

ρ

η + τ cη + δ

c.

Now, ga,b is the indicator of a half-space on the cube; thus, E
ξ
(
)
for example, [6]). Applying this and the triangle inequality, we have
(

))

)(

(

(

(

ga,b
)
η

− ga,b

ξ

2

Cηc (see,

≤

)

(

))

E

fη

ξ

− ga,b

ξ

2

C

ρ

(
η + τ cη + δ

c.

≤
The last piece is to replace fη by f . We do this with a simple lemma which shows that for any
function f , if fη is close to some indicator function then f is also close to the same indicator
function.

)(

))

(

(

)

(

(

)

(7.6)

Lemma 7.4. For any functions f ∶

−1, 1

n →

0, 1

and g ∶

−1, 1

n →

0, 1

and any η

0,

>

E

f

ξ

− g
{

ξ

2
}

≤

CE
[

fη
]

ξ

− g

ξ
{

2.

}

{

}

Applying Lemma 7.4 to (7.6), we obtain

))

(

(

)

(

(

(

)

(

))

E

f

ξ

− ga,b

ξ

2

C

ρ

η + τ cη + δ

c.

≤
By choosing τ and η small enough compared to δ, the proof of Theorem 1.10 is complete,
modulo the proofs of Lemmas 7.2, 7.3 and 7.4. We will prove them in the coming section.

)(

))

(

(

)

(

)

(

7.2 Gaussian and boolean half-spaces

Here we will prove the lemmas of the previous section. Before doing so, let us observe that
EXi1
is proportional to ai, a fact which has already been noted by Matulef et
{⟨
al. [34]:

≥0
b
⟩
−

a,X

}

Lemma 7.5.

EXi1

a,X

{⟨

aiφ

a, b

.

≥0
b
⟩
−

} =

(⟨

⟩)

36



<!-- pdf-page: 37 -->
∈

X, a

X, a⊥

and so E

Proof. Let ei
aia + a⊥, where a⊥ is some element of Rn which is orthogonal to a. Note that
independent of

Rn be the vector with 1 in position i and 0 elsewhere. We may write ei
X, a⊥

≥0
b
−
⟩
1
{⟨
where the second inequality follows because, by the rotational invariance of the Gaussian
has the same distribution as X1. Finally, integration by parts implies that
measure,
EX11
φ
{

aiEX11
{

1
{⟨
a, X

⟨
≥0
b
} =
⟩
−

0. Hence,

EXi1
⟩

≥0
b
⟩
−

aiE
⟩

a,b
⟨

a, X

} =

} =

a, b

X1≥

=
is

a,X

a,X

a,X

{⟨

⟩}

⟩

⟨

⟨

⟨

⟩

.

,

a,b
X1≥
⟨
⟨

⟩} =
⟩

Next, we prove Lemma 7.2. The point is that if a half-space is close to a low-inﬂuence
function f then that half-space must also have low inﬂuences. We can then perturb the
half-space to have even lower inﬂuences without increasing its distance to f by much.

⟩)

(⟨

Proof of Lemma 7.2. Suppose that f has inﬂuences bounded by τ , and that

E

f

X

− 1

a,X

{⟨

≥0
b
⟩
−

}

2

γ,

≤

c. We will show that there is some ¯a such that
)

(

(

)

where γ
¯ai
maxi

η + τ cη + ǫ

C
ρ
=
Cτ c, and
≤
(

)(

∣

∣

)

E

f

X

− 1

¯a,X

≥0
b
⟩
−

}

{⟨

γc.

2

≤

When applied to the function fη, this will imply the claim of Lemma 7.2.
(
)
Since the inﬂuences of f are bounded by τ , it follows in particular that

)

(

i. On the other hand, Xi form an orthonormal sequence and so

(7.7)

i ¯a2

i =

∑

1,

(7.8)

τ for every

E

f

X

− 1

a,X

{⟨

(

(

)

≥0
b
⟩
−

}

2

)

≥ ∑i

EXif

X

− EXi1

a,X

≥0
b
⟩
−

}

)

(7.9)

{⟨
2

,

(
ˆf
i
{

}

= ∑i

(
)
− aiφ

a, b

where the equality used Lemma 7.5. Deﬁning κa,b =
ai

Cτ , we have

− aiκa,b

ca2

2

i κ2

(

(⟨
a, b

⟩))
, it follows that for any i with

φ

ˆf
i
{

(
γ

≥

≥
− 1
)

a,X

{⟨

}
E

f

X

(

(

)

a,b. Combining this with (7.7) and (7.9),

(⟨

⟩)

≥0
b
⟩
−

}

2

≥

)

cκ2

a,b ∑i
ai

κa,b≥Cτ

∶∣

∣

a2
i .

(7.10)

κa,b ≥
∣

∣

for every i.

We consider two cases, depending on whether κa,b is large or small. First, suppose that

Ef

(
≤
0, 1

κa,b ≤

γ1
/

3. Now, κa,b ≥

c Pr

X1

a, b

E1

=

a,X

{⟨

, while (7.7) implies that

≥
γ + E1
⟨

⟩)
a,X
{⟨

≥0
b
⟩
−

} ≤

≥0
b
⟩
−
}
3
γ + Cγ1
/

3.
Cγ1
/

≤

Since f takes values in
half-space with small enough measure will satisfy (7.8).
]
3); then (7.10) implies that
3 (which is in turn larger than τ 1
γ1
Now suppose that κa,b ≥
/
/

√
, it follows that f is close to the zero function; in particular,any

√

[

a2
i ≤

3.
Cγ1
/

∑i
ai
∣
∶∣

≥Cτ 2
/

3

If we deﬁne ¯a to be the truncated version of a (i.e. ¯ai
=
2
a − ¯a
¯a
then this implies that
≥

3. Moreover,
Cγ1
/

≤

2

3 and ¯ai
Cτ 2
ai if
ai
0 otherwise),
/
<
=
3, which implies that we can
1 − Cγ1
/
∣
∣

∣

∣

∣

∣

37

ˆf
i
{

}

≤

∣

∣
2



<!-- pdf-page: 38 -->
1, while preserving the fact that

a − ¯a

2

≤

3 and maxi ¯ai
Cγ1
/

3.
Cγ1
/

≤

normalize ¯a so that
Finally,

a − ¯a

2

¯a
=
3 implies that
Cγ1
/
∣
∣

≤

∣

∣

b
−
⟩}
By the triangle inequality and (7.7), (7.8) follows.

b
⟩}
−

a,X

¯a,X

{⟨

(

E

1
{⟨

− 1

∣
Cγc.

2

∣

≤

)

Next, we will prove Lemma 7.3: if ga,b is the linear extension of a low-inﬂuence half-space,
then ga,b is close to a half-space. Observe that this is very much not the case for general
half-spaces: the linear extension of 1x1≥0 is x1, which is not close, in L2
, to any
half-space.

Rn, γn

(

)

Proof of Lemma 7.3. The proof rests on the invariance principle (Theorem 7.1). Let g be the
linear extension of 1
. First of all, the Berry-Esseen theorem
implies that for any M

and let h

a, x − b

a,x

x

=

{⟨

}

≥0
b
⟩
−
0,
>

Eg

ξ

h

ξ

Eh

ξ

=

(

)

(

)

∞
Pr
)
(
= ∫
a,b
⟩
⟨
M

(
)
1h

ξ
(

≥0
)
a, x

(⟨

Pr

a, x

⟨

⟩

t

dt

)

t

dt

≥

≥

⟩

≥ ∫
a,b
⟩
⟨
M

≥ ∫
a,b
⟩
⟨
∞
≥ ∫
a,b
⟩
⟨

log

1

τ

, we have

)
dt − CM τ

dt − CM τ − Ce−

M 2

2.
/

(⟨
X1

Pr

(
X1
Pr

(

t

⟩
≥

≥

)

t

)

Choosing M

=

√
Eg

Now, h is linear and so ht

(

)

(

)

(
h

/
ξ

ξ

)
≥ ∫

t

dt − Cτ c

X1

Pr

∞
a,b
⟩
⟨
th; since Qη is self-adjoint, we have
e−

≥0
b
⟩
−

a,X

E1

≥

=

{⟨

(

)

}

h

X

− Cτ c.

(7.11)

=
Eg

ξ

h

ξ

=

(

)

(

)

=

≤

≤

h

ξ

ξ

eηEgη
eηEgη
X
(
)
eηEgη
X
(
Egη
X
(

X
h
)
(
X
h
(
)
X
h
(
)

+ Ceη

)
+ C
)

η + τ cη
(

η + τ cη
,

(

)

)

where the last inequality assumes that η
(
Combining this with (7.11),

)
<

(
1 (if not then the lemma is trivial anyway).

(

)

)

X

Now, let m

a,X
have the same sign. Let A
)
(
we must have E
E
m
of m and h agree,

1Ac

=

≥

1
{⟨

∣

∣

E1

a,X

≥0
b
⟩
−

{⟨

h

X

Egη

X

h

X

+ C

η + τ cη

.

}
− gη
X
)
(
a, X − b
)
(
ǫ
A
⟩
/

)
2, ǫ

≤
E
; note when m
and take ǫ
)
(
(
(
=
−ǫ
A
. Then Pr
2
∈
∣
2. But on Ac we have
h
(
]}
∣

x
)
(

≥
/

m

≤

≥

)

)

(

/

/

ǫ

[

∣

≥0
b
x ∶
}
−
⟩
=
− Pr
m
⟨
{
∣

∣

(7.12)

≠

0 then m and h
1
2; since the signs

2, and since
ǫ

m

≤

∣

∣

Em

X

h

X

Em

X

h

X

≥

1
X∈Ac
{

} ≥

ǫ
2

E

m

1Ac

≥

(

)

(

)

(

)

(

)
38

∣

∣

/

)∣
ǫ2
4

.



<!-- pdf-page: 39 -->
Applying this to (7.12) yields ǫ
that

≤

C

η + τ cη

c. So if we recall the deﬁnition of ǫ, then we see

E

1
{⟨

a,X

(
≥0
b
⟩
−

}

)
− gη

X

C

ηe2η + τ cη

c.

≤
with E
(

By changing the constant c, we may replace E
2; by (7.2), we may replace gη by
gη. This completes the proof of the lemma. Note that the only reason for proving this lemma
∣
with gη instead of g was for extra convenience when applying it; the statement of the lemma
is also true with g instead of gη.

⋅
)∣

(

)

(

)

∣

∣

⋅

The only remaining piece is Lemma 7.4.

Proof of Lemma 7.4. Suppose f ∶
. This does
not exactly correspond to the statement of the lemma, but it will be more convenient for the
proof; we can recover the statement of the lemma by replacing f by 1
[
{
+
, we have Eg2

2. Since g takes values in

1; then the triangle

]
−1, 1

and g ∶

−1, 1

−1, 1

−1, 1

−1, 1

Let ǫ

g
2 .
+

}

{

}

{

}

ξ

n →

n →

f

2 and g by 1
=

fη

E
−g
ξ
inequality implies that
(

=

(

(

)

Since Ef 2

1, we have

≤

))

Ef 2

η ≥

Eg2 − 2ǫ

{
}
1 − 2ǫ.
=

E

f − fη

2

(

)

= ∑S⊂[n]

≤ ∑S⊂[n]

ˆf 2
S

1 − e−

η∣S∣

2

ˆf 2
S

(
1 − e−

η∣S∣

)

)

Ef 2 − Ef 2
η

(

2ǫ.

=

≤

It then follows by the triangle inequality that E

f − g

2

Cǫ.

≤

8 Spherical noise stability

(

)

We now use Theorem 1.4 to prove Theorem 1.11. For a subset A
to be the radial extension of A:

⊂

Sn

1, we deﬁne ¯A
−

Rn

⊂

¯A

=

x

∈

Rn ∶ x

≠

0 and

x
x

A

∈

From the spherical symmetry of the Gaussian distribution it immediately follows that Pr
Q
A
Prρ
(

. The proof of Theorem 1.11 crucially relies on the fact that Qρ
¯A1, ¯A2
)

in high dimensions. More explicitly it uses the following lemmas:

A1, A2

=
is close to
(

)

)

∣

∣

¯A

{

}

(
there is a spherical cap B

Lemma 8.1. For any half-space H
Sn

such that Pr

a, x

¯B

)

(
1 ∶
−

b′

≤

⟨

⟩

}

(

)
Pr

Lemma 8.2. For any two sets A1, A2
(

=
Pr

∈

x
H
{
¯B∆H
(
)

=

Rn ∶
and

a, x

b

≤

⟨
Cn−

}
⟩
1/2 log n.

≤
1 and any ρ
Sn
)
−

x

∈

=

{

Qρ

A1, A2

⊂
− Prρ

¯A1, ¯A2

C

ǫ

≤

−1 + ǫ, 1 − ǫ

∈
n−
[

1/2 log n.

it holds that

]

Given Lemmas 8.2 and 8.1, the proof of Theorem 1.11 is an easy corollary of Theorem 1.4:

)∣

(

)

(

(

)

∣

39



<!-- pdf-page: 40 -->
Hi
, and let B1, B2 be the corresponding caps whose existence is guaranteed by Lemma 8.1.
)

. Let H1, H2 be parallel half-spaces with Pr

Proof of Theorem 1.11. Deﬁne δ
¯Ai
Pr
Then
(

∗ =

)

(

(

)

δ

=

¯A1, ¯A2

δ
∗ =
=

≤

≤

=

¯A1, ¯A2
X

δ

Prρ
(
Prρ

Qρ

X
(
X
(

∈
A1, A2
(

δ

∈

H1, Y
)
¯B1, Y
∈
B1, Y
+ O

∈

− Prρ
H2
¯B2
− Prρ
)
∈
− Qρ
B2
)
1/2 log n
(
)

∈
n−

X

X
(
X
(
,

∈

∈

¯A1, Y
¯A1, Y
∈
A1, Y

∈

∈

¯A2
¯A2
∈
A2

+ O

)
+ O
)

1/2 log n
n−
1/2 log n
n−
(

)

)

(

)

where the ﬁrst inequality follows from Lemma 8.1 and the second follows from Lemma 8.2.
)
From Theorem 1.4 it follows that there are parallel half-spaces H1 and H2 with Pr
¯Ai

satisfying

Hi

Pr

(

(

)

=

(

)

(

)

Pr

¯Ai∆Hi

C

ρ

≤

mc(ρ)δ
∗

By Lemma 8.1, there are parallel caps B1 and B2 such that
(

)

(

)

2

ρ

1

1
4 (

−

1
3ρ
−

ρ
1
)(
+

)

.

Q

Ai∆Bi

Pr

¯Ai∆ ¯Bi

=

C

ρ

≤

1
4 (

mc(ρ)δ
∗

ρ

1
3ρ
−

1

−

ρ
1
)(
+

2

)

.

The proof of Lemma 8.1 is quite simple, so we present it ﬁrst:

(

)

(

)

(

)

Proof of Lemma 8.1. Let H
0. For any ǫ
that b

≥

>

x

∈

=
0, deﬁne
{
H +ǫ =
H −ǫ =

Rn ∶

a, x

≤

b

, and suppose without loss of generality

⟨
Rn ∶
Rn ∶

⟩
a, x

a, x
⟨

}

≤

⟩

≤

x

x
{

∈

∈

b

1 + ǫ
1 − ǫ
b
(

.
)}

Note that Pr

Now deﬁne B

H +ǫ ∖ H −ǫ
x

(

=

{

x, a

Cǫ.
1 ∶
−
¯B ∖ H +ǫ
⟨

≤
Sn

∈
)
Pr

{

≤

)}

∈
b

X

(
⟩
⟨
. Then ¯B

b

n

x

Rn ∶

x, a

√
Pr
/
Pr

1 + ǫ
}
X
≥
((
cǫ2n,
Ce−
(∣
∣

)

(

⟩

=

)

≤

≤

b
≤
1 + ǫ
⟨

{
≤
n
⟩

n
⟨
√

)

∣

∣/

=
X, a

√
)

)

(

b

x

n

, and so

√

∣/

∣

}

≤

⟩

where the last line follows from standard concentration inequalities (Bernstein’s inequalities,
for example). Similarly,

Since H −ǫ ⊂

H

⊂

H +ǫ and Pr
(

Pr

H −ǫ ∖ ¯B

≤
H +ǫ ∖ H −ǫ
)

(

Pr

Pr

X

≤

1 − ǫ

n

√
)

∣

(

Cǫ, it follows that
)
(∣
cǫ2n.

Cǫ + Ce−

≤
H∆ ¯B
)

≤

cǫ2n.

Ce−

≤

By choosing ǫ

=

Cn−

1/2 log n, we have
(

)

Pr

H∆ ¯B

Cn−

1/2 log n.

≤

(8.1)

Now, the lemma claimed that we could ensure Pr

. Since the volume of the
=
is continuous and strictly increasing in b′, we may deﬁne b′ to be

Pr

(

)

H

¯B

cap B′

∶
=

a, x

b′

x

≤

{⟨

⟩

∣

∣}

(

)

(

)

40



<!-- pdf-page: 41 -->
the unique real number such that Pr
¯B
Pr

. Now, either B
H
. On the other hand, (8.1) implies that

− Pr

Pr

Pr

=

⊂

B′ or B′ ⊂

B; hence

¯B∆ ¯B′

=

¯B′
¯B
(

¯B′

(

=

)
Pr

¯B

(
)
− Pr

H

(

)

∣

(

)

Pr

− Pr
)∣

¯B′

and so the triangle inequality leaves us with
(
∣

)∣

)

(

(

∣

)

(

)∣

Pr

H∆ ¯B′

≤

Pr

H∆ ¯B

+ Pr

B∆ ¯B′

Cn−

1/2 log n,

Cn−

1/2 log n.

≤

≤

We defer the proof of Lemma 8.2 until the next section, since this proof requires an

)

(

)

(
introduction to spherical harmonics.

(

)

8.1 Spherical harmonics and Lemma 8.2

We will try to give an introduction to spherical harmonics which is as brief as possible, while
still containing enough material for us to explain the proof of Lemma 8.2 adequately. A
slightly less brief introduction is contained in [30]; for a full treatment, see [37].

Let Sk be the linear space consisting of harmonic, homogeneous, degree-k polynomials.
. One
n
.
; combined with
)

1, Q
We will think of Sk as a subspace of L2
−
can easily check that Sk is invariant under rotations. Hence it is a representation of SO
It turns out, moreover, that Sk is an irreducible representation of SO
Schur’s lemma, this leads to the following important property:

spans L2

1, Q
−

Sk ∶ k

; then

Sn

Sn

n

≥

{

}

0

(

)

(

(

)

Lemma 8.3. If T ∶ L2
eigenspaces of T .

Sn

1

−

→ L2

Sn

1

−

(
commutes with rotations then

)
Sk ∶ k

0

are the

≥

(

)

(

)
In particular, we will apply Lemma 8.3 to the operators Tρ deﬁned by
E
X
Y
f
, where
1 ∶
y ∈ Sn
x, y
set
−
)
)∣
(
(
Sk ∶ k
are the eigenspaces of Tρ. In particular, there exist
0
that
{
ρ
Tρf
µk
=
{
Sk. For this task, the Gegenbauer polynomials provide good candidates: deﬁne
single f
)

=
is the average of f over the
x
. Clearly, Tρ commutes with rotations; hence Lemma 8.3 implies
)(
)
such that
, it is enough to compute Tρf for a
)

(
}
Sk. Moreover, to compute µk

(
≥
⟨
⟩
f for all f
}

In other words,

X, Y
ρ

∼ Qρ.

}
Tρf

Tρf

∶ k

µk

)(

X

∈
(

≥

=

ρ

ρ

{

}

{

0

(

)

)

(

∈

Gk

t

=

E

t + iW1

)
(
1 − t2

k,

√
distributed uniformly on the sphere Sn

2.
−
Sk; on the other hand, one can easily check that

)

−

1

. From the discussion above, it then follows that

)

x

where the expectation is over W
Gk
Deﬁne fk
e1
fk
1, while
(
)

W1, . . . , Wn
(
(
=
; it turns out that fk ∈
x1
(
ρ
Gk
Tρfk
(
)
(

(

)

e1

)(

E

=

=

=

)

)

)
ρ

(
µk

With this explicit formula, we can show that µk

(

)

(

ρ + iW1

1 − ρ2

k.

=

√
ρ

is continuous in ρ:

)

Lemma 8.4. For any ǫ

0 there exists C

ǫ

>

such that if ρ, η

(

)

∈
1/2

−1 + ǫ, 1 − ǫ

then

.
[

]

We will leave the proof of Lemma 8.4 to the end. Instead, let us show how it can be used

(

)∣

(

)(∣

)

∣

∣

µk

ρ

− µk

η

C
)

ǫ

(
≤

ρ − η

+ n−

is continuous in ρ.

to prove that Qρ

X

A1, Y

∈

∈

Lemma 8.5. For any ǫ

(

Qρ

X

A1, Y

∈

A2

∈

>
− Qη

)

(
A2

)

0 there exists C

ǫ

such that if ρ, η

−1 + ǫ, 1 − ǫ

then

A1, Y

X

∈

A2
(
)

∈

≤

C

ǫ

Q1/2

A1

A2

ρ − η
]

1/2

+ n−

.

∈
Q1/2
[

∣

(

)

(

)∣
41

(

)

(

)

(

)(∣

∣

)



<!-- pdf-page: 42 -->
Proof. Take f, g

L2

Sn

1, Q
−

∈

and write f

(

EgTρf − EgTηf
)

0 fk where fk ∈
= ∑∞k
=
Tρf − Tηf
g

2

2

≤

Sk. Then

(where

f

2 denotes

Ef 2) and
∣

∣

∥

∥

∥

∥

∥

∥

√

Tρf − Tηf

By Lemma 8.4, we have

∥

2
2 =
∥

µk

∞
∑k
0
=
(

ρ

− µk

η

2

fk

2
2

(

)

(

))

∥

∥

Tρf − Tηf

C

ǫ

2

≤

ρ − η

1/2

+ n−

f

2,

and therefore

Note that if f

1A1 and g

∣

=

=

∥

∥
EgTρf − EgTηf

C
1A2 then EgTρf

≤

∣

(
ǫ

)(∣
f

∣

g

2

2

ρ − η

1/2

.

)∥
∥
+ n−
A2
∣

Qρ
)∥

(
=

X
∥
∥

∥
∈

A1, Y
(∣

∈

, while
)

f

2

=

Q

A1

1/2.

The proof of Lemma 8.2 is straightforward once we know Lemma 8.5. As we have already
(
mentioned, normalized Gaussian vectors from Prρ have a joint distribution that is similar to
Qρ, except that their inner products are close to ρ instead of being exactly ρ. But Lemma 8.5
implies that a small diﬀerence in ρ doesn’t aﬀect the noise sensitivity by much.

∥

)

∥

(

)

Proof of Lemma 8.2. Let X, Y be distributed according to Prρ. Then

Prρ

X

¯A1, Y

∈

¯A2

∈

Prρ

=

X
X

A1,

∈

Y
Y

A2

,

∈

Note that conditioned on
cording to Qr, where r

Y

(
,
X
and
Y
X
X, Y
∣
⟨
∣
∣
⟩
∣
n ± Cn1/2 log n,
∣)
∣∣
⟩/(∣

2

∈

=
2,

⟨
Y

X

(

, the variables X
∣

)
)
X, Y
, Y
. Now with probability 1 − 1
n2 it holds that
/∣

X

/∣

Y

∣

∣

∣

are distributed ac-

∣
∣
ρn ± Cn1/2 log n.

X, Y

∈

∣
On this event, we have

∣

∣

∣

r

=

X
X

,

Y
Y

∈

⟨
ρ ± Cn−

⟩
1/2 log n.

Using Lemma 8.5 we get that

Prρ

X

¯A1, Y

∈

∈

⟨

∣
¯A2

⟩

∣

∣

∣

Qρ

X

A1, Y

∈

∈

≤

A2

+ C

ǫ

1/2 log n.

n−

(
A similar argument yields a bound in the other direction and concludes the proof.

)

(

)

(

)

Our ﬁnal task is the proof of Lemma 8.4:

Proof of Lemma 8.4. Deﬁne Zρ
=
2) so that µk
formly distributed on Sn
−
probability at least 1 − exp
) then
(
)
1 − ρ2

ρ + iW1
ρ

−cn

Zρ

(
)
ρ2 + W1
=

√
=

∣

∣

(

)

1 − ρ2 (recalling that W
EZ k
W1
ρ . Note that if

W1, . . . , Wn
is uni-
1
2 (which happens with
(

)

−

1

=
≤

1 + ρ2
2

≤

1 −

≤

ǫ
2 ≤

∣

∣

exp

−cǫ

.

(

)

42



<!-- pdf-page: 43 -->
Now,

If

W1

≤

∣

∣

1
2 then

ρZ k
Z j
η

∣

1

j
−

−

≤

∣

Applying this to (8.2), we have

∣

µk

ρ

− µk

η

(

)

(

)

E

ρ − Z k
Z k
η

E

(
Zρ − Zη

=

=

exp

−cǫk

(
and so

)

k
)

1

−
∑j
1
=

(
ρZ k
Z j
η

)
1
−

j
−

∑j

k exp

−cǫk

C

ǫ

≤

(

)

(

)

≤

∣

Z j
ρZ k
η

1

j
−

−

.

(8.2)

µk

ρ

− µk

η

∣

(

)

(

)∣

=

≤

E

Z k
ρ − Z k
η

1{∣W1∣

1/2} + E1{∣W1∣

1/2}

<
Zρ − Zη

E

(
2 Pr

exp

≤
ρ − η

W1
−cn
(∣

∣

)
1
≥
+ C
/

(
)
because

≥
+ C
ǫ
2
ρ − η
ǫ
,
)
(
)
)∣
∣
1 − ρ2 −

(

where E

Zρ − Zη

C

ǫ

≤

√
∣
(
8.2 Spherical noise and Max-Cut

)∣

∣

∣

∣

∣

1 − η2

√

∣

≤

C

ǫ

ρ − η

.

∣

(

)∣

∣

Zρ − Zη

(

)

k

1

−
∑j
1
=

Z j
ρZ k
η

1

j
−

−

In this section, we will outline how robust noise sensitivity on the sphere (Theorem 1.11)
implies that half-space rounding for the Goemans-Williamson algorithm is robustly optimal
(Theorem 1.12). The key for making this connection is Karloﬀ’s family of graphs [?]: for any
n, d
balanced elements

N, let Gn,d =
∈
1/2, n−
−n−
)
24 then the optimal cut of Gn,d has value
n

n, and with an edge between u and v if
En,d

u, v
of
1 − d
if d
{
⟩
⟨
embedding (and any rotation of it) is an optimal embedding of Gn,d into Sn
/
∣(
embeddings, every angle between two connected vertices is d
the expected value of a rounding scheme:

n
n/2
n. Karloﬀ showed that
d
(
. Moreover, the identity
/
In these
n; hence, it is easy to calculate

be the graph whose vertices are the

Vn,d, En,d

1.
−

=
n

1/2

≤

}

)

(

)

/

∣

/

Lemma 8.6. Let

X, Y

be distributed according to Qd/n. For any rounding scheme R,

(

)

Cut

Gn,d, R

≤

En,d
2

∣

∣

E

R

X

− R

Y

,

(
where the expectation is with respect to X, Y and R.

(

)

∣

)

(

)∣

Proof. Recall that

Cut

G, R

1
2

=

ER

min
f

∑(u,v)
∈

R

f

u

− R

f

v

E

∣
R

(
f

(
u

))
− R

(
f

(
v

))∣
,

(

)

1
2

≤

EREf

∑(u,v)
∈
where the expectation is taken over all rotations f . But if f is a uniformly random rotation
v
f
then for every
(and both pairs are independent of R).
(
)

is equal in distribution to the pair

En,d, the pair

X, Y

u, v

))∣

, f

))

))

u

(

(

(

(

(

(

)

(

(

∈

E

)

∣

43



<!-- pdf-page: 44 -->
Theorem 1.12 follows fairly easily from Lemma 8.6, Theorem 1.11, and the fact that
1,

1 θ∗
2.33 minimizes αθ, and suppose there is a rounding scheme R such that

Indeed, choose n and d such that

n − cos−

1 − d

Gn,d

En,d

n−

n

=

≤

d

.

MaxCut
where θ∗ ≈
(

)

∣

∣(

/
Cut

)
Gn,d, R

≥
; since αθ is continuous in θ, it follows that
)

)(

∗

αθ − αθ
)

MaxCut

Gn,d

αθ

− ǫ

.

∣

/

∣

Let θ
max

=
ǫ, n−

d
n
cos
1/2 log n
)
/

(

, we have

(
αθ − αθ

Cǫ

⋆

∗

≤

(
and so

C
n . Taking ǫ

⋆ =

∗

≤

∣

{

}

∣
Cut

Gn,d, R
∣

≥

(

)

=

=

MaxCut
En,d
2
∣
π

En,d
∣(

θ

Gn,d
1 − cos θ

(

)(
1 − Cǫ
)(
⋆

∣
αθ − Cǫ
⋆
αθ − Cǫ

)
⋆

.

)

By Lemma 8.6, 1
2
x
by AR

x ∶ R

=

E

{

(

)

R
1
(
}

Y

− R
X
, and set ρ
)∣
− Sρ

AR

≥
=

Pr

(

)

=
∣

∣
2
1 − Cǫ
π θ
cos θ then

(

AR

1
2

=

)
E

R

X

− R

Y

R

∣(
. If we deﬁne the (random) subset AR

)

Sn

1

−

⊂

⋆

Taking expectations,

(

)

(

)

(∣

(

)

(

)∣∣

)

E

Pr

AR

− Sρ

AR

1
2

=

E

R

X

− R

Y

2
π

≥

arccos ρ − Cǫ

.

⋆

(8.3)

∣

⋆

(

(

)

=

)
Pr

(
AR

))
(
2
π arccos ρ −
. Take ηR to be the distance from AR to the nearest hemisphere: ηR

(
Let δR be the random deﬁcit δR
Cǫ
B is a hemisphere
because the set of hemispheres is compact with respect to the distance d
Recall that θ
Theorem 1.4, Theorem 1.11 applies for ρ
ηR

≤
∶
and let BR be a hemisphere that achieves the minimum (which is attained
)
).
0; by the same symmetries discussed following
<
0, but with the deﬁcit inequality reversed. Hence,

, so that (8.3) implies EδR
AR∆B
min

c. Taking expectations,

2.33 and so ρ

}
θ∗ ≈
δR, n−

1/2 log n

C max

)∣
− Sρ

A∆B

cos θ

A, B

AR

(
Pr

{
=

Pr

))

≈

<

=

=

(

(

(

)

)

(

)

(

≤

{

EηR

≤

CE max
}

δR, n−

1/2 log n

c

C max

≤

EδR, n−

Consider the rounding scheme ˜R
R

which is 1 when y
}
2ηR, and so the displayed equation above implies that

− ˜R

R

Y

Y

{

{

y

∈

E

=

c

1/2 log n

C ′ǫc
⋆
BR and −1 otherwise. Then

=

}

.

(∣

(

)

(

)∣∣

)

E

(
R

)
Y

− ˜R

Y

.

Cǫc
⋆

≤

Since ˜R is a hyperplane rounding scheme, this completes the proof of Theorem 1.12.
)

)∣

(

(

∣

Acknowledgements

Part of the work on this paper was done while the second author was visiting the Universit´e
de Paul Sabatier. He would like to thank Michel Ledoux and Franck Barthe for hosting him,
and for fruitful discussions.

44



<!-- pdf-page: 45 -->
References

[1] K. Arrow. A diﬃculty in the theory of social welfare. J. of Political Economy, 58:328–

346, 1950.

[2] Per Austrin. Towards Sharp Inapproximability For Any 2-CSP. In IEEE Symposium on

Foundations of Computer Science (FOCS), pages 307–317, 2007.

[3] Albert Baernstein and B.A. Taylor. Spherical rearrangements, subharmonic functions,

and ∗-functions in n-space. Duke Math. J., 43:245–268, 1976.

[4] D. Bakry and M. Ledoux. L´evy–Gromov’s isoperimetric inequality for an inﬁnite dimen-

sional diﬀusion generator. Inventiones mathematicae, 123(2):259–281, 1996.

[5] William Beckner. Sobolev inequalities, the Poisson semigroup, and analysis on the sphere

Sn. Proc. Natl. Acad. Sci. USA, 89(11):4816–4819, 1992.

[6] I. Benjamini, G. Kalai, and O. Schramm. Noise sensitivity of boolean functions and

applications to percolation. Inst. Hautes ´Etudes Sci. Publ. Math., 90:5–43, 1999.

[7] S. Bobkov. A functional form of the isoperimetric inequality for the Gaussian measure.

J. Funct. Anal., 135(1):39–49, 1996.

[8] C. Borell. The Brunn-Minkowski inequality in Gauss space. Inventiones Mathematicae,

30(2):207–216, 1975.

[9] C. Borell. Geometric bounds on the Ornstein-Uhlenbeck velocity process. Z. Wahrsch.

Verw. Gebiete, 70(1):1–13, 1985.

[10] A. Burchard and M. Schmuckenschl¨ager. Comparison theorems for exit times. Geom.

Funct. Anal., 11(4):651–692, 2001.

[11] E. A. Carlen and C. Kerce. On the cases of equality in Bobkov’s inequality and Gaussian
rearrangement. Calculus of Variations and Partial Diﬀerential Equations, 13(1):1–18,
2001.

[12] E. A. Carlen and C. Kerce. On the cases of equality in Bobkov’s inequality and Gaussian
rearrangement. Calculus of Variations and Partial Diﬀerential Equations, 13(1):1–18,
2001.

[13] A. Cianchi, N. Fusco, F. Maggi, and A. Pratelli. On the isoperimetric deﬁcit in Gauss

space. American Journal of Mathematics, 133(1):131–186, 2011.

[14] A. Cianchi, N. Fusco, F. Maggi, and A. Pratelli. On the isoperimetric deﬁcit in Gauss

space. American Journal of Mathematics, 133(1):131–186, 2011.

[15] A. De, E. Mossel, and J. Neeman. Majority is stablest: Discrete and SoS. In Proceedings

of the 45th Annual ACM Symposium on Theory of Computing (STOC), 2013.

[16] I. Dinur, E. Mossel, and O. Regev. Conditional hardness for approximate coloring. In
Proceedings of the thirty-eighth annual ACM symposium on Theory of computing (STOC
2006), pages 344–353, 2006.

45



<!-- pdf-page: 46 -->
[17] A. Ehrhard. ´El´ements extremaux pour les in´egalit`es de Brunn-Minkowski Gaussiennes.

Ann. Inst. H. Poincar`e Anal. non lin`eaire, pages 149–168, 1986.

[18] U. Feige and G. Schechtman. On the optimality of the random hyperplane rounding
technique for MAX-CUT. Random Structures and Algorithms, 20:403–440, 2002.

[19] M. X. Goemans and D. P. Williamson. Improved approximation algorithms for maximum
cut and satisﬁability problems using semideﬁnite programming. Jour. of the ACM, pages
1115–1145, 1995.

[20] Marcus Isaksson and Elchanan Mossel. Maximally stable gaussian partitions with dis-

crete applications. Israel Journal of Mathematics, 189:347–396, 2012.

[21] G. Kalai. A Fourier-theoretic perspective on the Concordet paradox and Arrow’s theo-

rem. Adv. in Appl. Math., 29(3):412–426, 2002.

[22] G. Kalai. Social Indeterminacy. Econometrica, 72:1565–1581, 2004.

[23] G. Kalai and E. Friedgut. It ain’t over till it’s over. Private communication, 2001.

[24] D. M. Kane. The gaussian surface area and noise sensitivity of degree-d polynomial

threshold functions. Computational Complexity, 20(2):389–412, 2011.

[25] R. Karp. Reducibility among combinatorial problems. In R. Miller and J. Thatcher,
editors, Complexity of Computer Computations, pages 85–103. Plenum Press, 1972.

[26] S. Khot. On the power of unique 2-prover 1-round games. In Proc. 34th Ann. STOC,

pages 767–775, 2002.

[27] S. Khot, G. Kindler, E. Mossel, and R. O’Donnell. Optimal inapproximability results
In Proceedings of the 45th Annual IEEE

for MAX-CUT and other 2-variable CSPs?
Symposium on Foundations of Computer Science, pages 146–154. IEEE, 2004.

[28] S. Khot, G. Kindler, E. Mossel, and R. O’Donnell. Optimal inapproximability results

for max-cut and other 2-variable csps? SIAM J. Comput., 37:319–357, 2007.

[29] G. Kindler and R. O’Donnell. Gaussian noise sensitivity and fourier tails.

In IEEE

Conference on Computational Complexity, pages 137–147, 2012.

[30] B. Klartag and O. Regev. Quantum one-way communication can be exponentially

stronger than classical communication. In STOC, pages 31–40, 2011.

[31] M. Ledoux. Semigroup proofs of the isoperimetric inequality in Euclidean and Gauss

space. Bulletin des sciences math´ematiques, 118(6):485–510, 1994.

[32] M. Ledoux.

Isoperimetry and gaussian analysis. Lectures on probability theory and

statistics, pages 165–294, 1996.

[33] M. Ledoux. The concentration of measure phenomenon, volume 89. Amer Mathematical

Society, 2001.

[34] K. Matulef, R. O’Donnell, R. Rubinfeld, and R. A. Servedio. Testing halfspaces.

In

SODA 2009, pages 256–264. 2009.

46



<!-- pdf-page: 47 -->
[35] E. Mossel and J. Neeman. Robust dimension free isoperimetry in Gaussian space.

(preprint http://arxiv.org/abs/1202.4124), 2012.

[36] E. Mossel, R. O’Donnell, and K. Oleszkiewicz. Noise stability of functions with low
inﬂuences: invariance and optimality. Annals of Mathematics, 171(1):295–341, 2010.

[37] C. M¨uller. Spherical harmonics, volume 17 of Lecture notes in mathematics. Springer,

1966.

[38] I. Pinelis. Optimal tail comparison based on comparison of moments.

In High
Dimensional Probability, Progress in Probability, pages 297–314. Oberwolfach, 1996,
Birkhauser, Basel, 1998.

[39] Prasad Raghavendra. Optimal Algorithms and Inapproximability Results For Every
CSP? In Proceedings of the 40th Annual Symposium on Theory of Computing (STOC),
pages 245–254, 2008.

[40] V.N. Sudakov and B.S. Tsirel’son. Extremal properties of half-spaces for spherically

invariant measures. Journal of Mathematical Sciences, 9(1):9–18, 1978.

47


