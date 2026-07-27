<!-- generated-by: proofmatch local extraction -->
<!-- source-pdf-sha256: cdca27e1b5fd476248b00c800b13ba2b3a166b02bdeeabe815ee2ebf9d3cf3fd -->
<!-- extractor: pdfminer.six v20260107 -->

<!-- pdf-page: 1 -->
Chapter 1

Boolean functions and
the Fourier expansion

In this chapter we describe the basics of analysis of Boolean functions. We
emphasize viewing the Fourier expansion of a Boolean function as its repre-
sentation as a real multilinear polynomial. The viewpoint based on harmonic
analysis over Fn
2 is mostly deferred to Chapter 3. We illustrate the use of basic
Fourier formulas through the analysis of the Blum–Luby–Rubinfeld linearity
test.

1.1. On analysis of Boolean functions

This is a book about Boolean functions,

f : {0, 1}n → {0, 1}.

Here f maps each length-n binary vector, or string, into a single binary value,
or bit. Boolean functions arise in many areas of computer science and mathe-
matics. Here are some examples:

• In circuit design, a Boolean function may represent the desired behavior

of a circuit with n inputs and one output.

• In graph theory, one can identify v-vertex graphs G with length-

v
2
strings indicating which edges are present. Then f may represent a
¢
property of such graphs; e.g., f (G) = 1 if and only if G is connected.

¡

• In extremal combinatorics, a Boolean function f can be identiﬁed with
a “set system” F on [n] = {1, 2, . . . , n}, where sets X ⊆ [n] are identiﬁed
with their 0-1 indicators and X ∈ F if and only if f (X ) = 1.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.

19



<!-- pdf-page: 2 -->
20

1. Boolean functions and the Fourier expansion

• In coding theory, a Boolean function might be the indicator function for

the set of messages in a binary error-correcting code of length n.

• In learning theory, a Boolean function may represent a “concept” with n

binary attributes.

• In social choice theory, a Boolean function can be identiﬁed with a “vot-

ing rule” for an election with two candidates named 0 and 1.

We will be quite ﬂexible about how bits are represented. Sometimes we
will use True and False; sometimes we will use −1 and 1, thought of as real
numbers. Other times we will use 0 and 1, and these might be thought of as
real numbers, as elements of the ﬁeld F2 of size 2, or just as symbols. Most
frequently we will use −1 and 1, so a Boolean function will look like

f : {−1, 1}n → {−1, 1}.

But we won’t be dogmatic about the issue.

We refer to the domain of a Boolean function, {−1, 1}n, as the Hamming
cube (or hypercube, n-cube, Boolean cube, or discrete cube). The name “Ham-
ming cube” emphasizes that we are often interested in the Hamming distance
between strings x, y ∈ {−1, 1}n, deﬁned by

∆(x, y) = #{i : xi 6= yi}.

Here we’ve used notation that will arise constantly: x denotes a bit string,
and xi denotes its ith coordinate.

Suppose you have a problem involving Boolean functions with the follow-

ing two characteristics:

• the Hamming distance is relevant;

• you are counting strings, or the uniform probability distribution on

{−1, 1}n is involved.

These are the hallmarks of a problem for which analysis of Boolean functions
may help. Roughly speaking, this means deriving information about Boolean
functions by analyzing their Fourier expansion.

1.2. The “Fourier expansion”: functions as multilinear

polynomials

The Fourier expansion of a Boolean function f : {−1, 1}n → {−1, 1} is simply
its representation as a real, multilinear polynomial. (Multilinear means that
no variable xi appears squared, cubed, etc.) For example, suppose n = 2 and

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 3 -->
1.2. The “Fourier expansion”: functions as multilinear polynomials

21

f = max2, the “maximum” function on 2 bits:

max2(+1, +1) = +1,
max2(−1, +1) = +1,
max2(+1, −1) = +1,
max2(−1, −1) = −1.

Then max2 can be expressed as a multilinear polynomial,
max2(x1, x2) = 1
2

2 x2 − 1

2 x1 + 1

2 x1x2;

+ 1

(1.1)

this is the “Fourier expansion” of max2. As another example, consider the
majority function on 3 bits, Maj3 : {−1, 1}3 → {−1, 1}, which outputs the ±1 bit
occurring more frequently in its input. Then it’s easy to verify the Fourier
expansion

2 x2 + 1

2 x3 − 1

2 x1x2x3.

Maj3(x1, x2, x3) = 1

2 x1 + 1
The functions max2 and Maj3 will serve as running examples in this chapter.
Let’s see how to obtain such multilinear polynomial representations in
general. Given an arbitrary Boolean function f : {−1, 1}n → {−1, 1} there is a
familiar method for ﬁnding a polynomial that interpolates the 2n values that
f assigns to the points {−1, 1}n ⊂ Rn. For each point a = (a1, . . . , an) ∈ {−1, 1}n
the indicator polynomial

(1.2)

1{a}(x) =

1+a1 x1
2

1+a2 x2
2

· · ·

1+an xn
2

´ ³
takes value 1 when x = a and value 0 when x ∈ {−1, 1}n \ {a}. Thus f has the
polynomial representation

³

´

³

´

Illustrating with the f = max2 example again, we have

a∈{−1,1}n
X

f (x) =

f (a)1{a}(x).

max2(x) = (+1)

+ (+1)

+ (+1)

+ (−1)

1+x1
2
1−x1
2
1+x1
2
1−x1
2

³

³

³

1+x2
2
1+x2
2
1−x2
2
1−x2
2

´

´

´

´ ³

´ ³

´ ³

= 1
2

(1.3)

+ 1

2 x1 + 1

2 x2 − 1

2 x1x2.

´

³

´ ³
Let us make two remarks about this interpolation procedure. First, it works
equally well in the more general case of real-valued Boolean functions, f :
{−1, 1}n → R. Second, since the indicator polynomials are multilinear when
expanded out, the interpolation always produces a multilinear polynomial.
Indeed, it makes sense that we can represent functions f : {−1, 1}n → R with
multilinear polynomials: since we only care about inputs x where xi = ±1, any
factor of x2

i can be replaced by 1.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 4 -->
22

1. Boolean functions and the Fourier expansion

We have illustrated that every f : {−1, 1}n → R can be represented by a
real multilinear polynomial; as we will see in Section 1.3, this representation
is unique. The multilinear polynomial for f may have up to 2n terms, corre-
sponding to the subsets S ⊆ [n]. We write the monomial corresponding to S
as

xS =

xi

(with x; = 1 by convention),

and we use the following notation for its coefﬁcient:

i∈S
Y

f (S) = coefﬁcient on monomial xS in the multilinear representation of f .

This discussion is summarized by the Fourier expansion theorem:

b

Theorem 1.1. Every function f : {−1, 1}n → R can be uniquely expressed as a
multilinear polynomial,

f (x) =

f (S) xS.

(1.4)

This expression is called the Fourier expansion of f , and the real number
f (S)
is called the Fourier coefﬁcient of f on S. Collectively, the coefﬁcients are
called the Fourier spectrum of f .

b

S⊆[n]
X

b

As examples, from (1.1) and (1.2) we obtain:

max2({1}) = 1
2 ,
Maj3({3}) = 1
2 ,
ƒ

max2(;) = 1
2 ,

max2({2}) = 1
2 ,

max2({1, 2}) = − 1
2 ;

Maj3({2}),

Maj3({1}),
ƒ

Maj3({1, 2, 3}) = − 1
2 ,
ƒ
ƒ
We ﬁnish this section with some notation. It is convenient to think of the
(cid:129)

(cid:129)
monomial xS as a function on x = (x1, . . . , xn) ∈ Rn; we write it as

Maj3(S) = 0 else.

(cid:129)

(cid:129)

(cid:129)

Thus we sometimes write the Fourier expansion of f : {−1, 1}n → R as

i∈S
Y

χS(x) =

xi.

f (x) =

f (S) χS(x).

S⊆[n]
X

b
So far our notation makes sense only when representing the Hamming cube
by {−1, 1}n ⊆ Rn. The other frequent representation we will use for the cube
is Fn
→ R by
“encoding” input bits 0, 1 ∈ F2 by the real numbers −1, 1 ∈ R. We choose the
encoding χ : F2 → R deﬁned by

2 . We can deﬁne the Fourier expansion for functions f : Fn

2

χ(0F2) = +1, χ(1F2) = −1.

This encoding is not so natural from the perspective of Boolean logic; e.g., it
means the function max2 we have discussed represents logical AND. But it’s
mathematically natural because for b ∈ F2 we have the formula χ(b) = (−1)b.
We now extend the χS notation:

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 5 -->
1.3. The orthonormal basis of parity functions

23

Deﬁnition 1.2. For S ⊆ [n] we deﬁne χS : Fn
2

→ R by

which satisﬁes

χS(x) =

χ(xi) = (−1)

i∈S xi ,

i∈S
Y

P

χS(x + y) = χS(x)χS(y).

(1.5)

In this way, given any function f : Fn
2

→ R it makes sense to write its

Fourier expansion as

f (x) =

f (S) χS(x).

In fact, if we are really thinking of Fn
b
2 the n-dimensional vector space over
2 . This will

F2, it makes sense to identify subsets S ⊆ [n] with vectors γ ∈ Fn
be discussed in Chapter 3.2.

S⊆[n]
X

1.3. The orthonormal basis of parity functions

For x ∈ {−1, 1}n, the number χS(x) =
i∈S xi is in {−1, 1}. Thus χS : {−1, 1}n →
{−1, 1} is a Boolean function; it computes the logical parity, or exclusive-or
Q
(XOR), of the bits (xi)i∈S. The parity functions play a special role in the
analysis of Boolean functions: the Fourier expansion

f =

f (S) χS

(1.6)

shows that any f can be represented as a linear combination of parity func-
tions (over the reals).

S⊆[n]
X

b

It’s useful to explore this idea further from the perspective of linear alge-
bra. The set of all functions f : {−1, 1}n → R forms a vector space V , since we
can add two functions (pointwise) and we can multiply a function by a real
scalar. The vector space V is 2n-dimensional: if we like we can think of the
functions in this vector space as vectors in R2n
, where we stack the 2n values
f (x) into a tall column vector (in some ﬁxed order). Here we illustrate the
Fourier expansion (1.1) of the max2 function from this perspective:

+1
+1
−1
−1



+1
+1
+1
−1



+1
+1
+1
+1



+1
−1
+1
−1



+ (1/2) 





= (1/2) 





max2 = 



















More generally, the Fourier expansion (1.6) shows that every function
f : {−1, 1}n → R in V is a linear combination of the parity functions; i.e., the
parity functions are a spanning set for V . Since the number of parity functions
is 2n = dim V , we can deduce that they are in fact a linearly independent basis
for V . In particular this justiﬁes the uniqueness of the Fourier expansion
stated in Theorem 1.1.











+ (−1/2) 





+ (1/2) 





+1
−1
−1
+1



.

(1.7)

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 6 -->
24

1. Boolean functions and the Fourier expansion

We can also introduce an inner product on pairs of function f , g : {−1, 1}n →
R in V . The usual inner product on R2n
x∈{−1,1}n f (x)g(x),
but it’s more convenient to scale this by a factor of 2−n, making it an average
rather than a sum. In this way, a Boolean function f : {−1, 1}n → {−1, 1} will
have 〈 f , f 〉 = 1, i.e., be a “unit vector”.

would correspond to

P

Deﬁnition 1.3. We deﬁne an inner product 〈·, ·〉 on pairs of function f , g :
{−1, 1}n → R by

〈 f , g〉 = 2−n

x∈{−1,1}n
X
We also use the notation k f k2 =

f (x)g(x) =

E
x∼{−1,1}n

[ f (x)g(x)] .

(1.8)

〈 f , f 〉, and more generally,

k f kp = E[| f (x)|p]1/p.

p

Here we have introduced probabilistic notation that will be used heavily

throughout the book:

Notation 1.4. We write x ∼ {−1, 1}n to denote that x is a uniformly chosen ran-
dom string from {−1, 1}n. Equivalently, the n coordinates xi are independently
chosen to be +1 with probability 1/2 and −1 with probability 1/2. We always
write random variables in boldface. Probabilities Pr and expectations E will
always be with respect to a uniformly random x ∼ {−1, 1}n unless otherwise
speciﬁed. Thus we might write the expectation in (1.8) as Ex[ f (x)g(x)] or
E[ f (x)g(x)] or even E[ f g].

Returning to the basis of parity functions for V , the crucial fact underlying

all analysis of Boolean functions is that this is an orthonormal basis.

Theorem 1.5. The 2n parity functions χS : {−1, 1}n → {−1, 1} form an orthonor-
mal basis for the vector space V of functions {−1, 1}n → R; i.e.,

〈χS, χT 〉 =

1 if S = T,

0 if S 6= T.

(

Recalling the deﬁnition 〈χS, χT 〉 = E[χS(x)χT (x)], Theorem 1.5 follows imme-
diately from two facts:

Fact 1.6. For x ∈ {−1, 1}n it holds that χS(x)χT (x) = χS4T (x), where S4T
denotes symmetric difference.

Proof. χS(x)χT (x) =

xi

xi =

xi

i∈S
Y

i∈T
Y

Fact 1.7. E[χS(x)] = E

xi

=

i∈S
hY

i

i∈S4T
Y

i∈S∩T
Y
1 if S = ;,

0 if S 6= ;.

(

xi = χS4T (x).

(cid:3)

x2
i =

i∈S4T
Y

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 7 -->
1.4. Basic Fourier formulas

25

Proof. If S = ; then E[χS(x)] = E[1] = 1. Otherwise,

E

xi

=

E[xi]

because the random bits x1, . . . , xn are independent. But each of the factors
(cid:3)
E[xi] in the above (nonempty) product is (1/2)(+1) + (1/2)(−1) = 0.

i∈S
hY

i

i∈S
Y

1.4. Basic Fourier formulas

As we have seen, the Fourier expansion of f : {−1, 1}n → R can be thought
of as the representation of f over the orthonormal basis of parity functions
(χS)S⊆[n]. In this basis, f has 2n “coordinates”, and these are precisely the
Fourier coefﬁcients of f . The “coordinate” of f in the χS “direction” is 〈 f , χS〉;
i.e., we have the following formula for Fourier coefﬁcients:

Proposition 1.8. For f : {−1, 1}n → R and S ⊆ [n], the Fourier coefﬁcient of f
on S is given by

f (S) = 〈 f , χS〉 =

E
x∼{−1,1}n

[ f (x)χS(x)].

We can verify this formula explicitly:

b

〈 f , χS〉 =

*

f (T) χT , χS

=

+

T⊆[n]
X

T⊆[n]
X

f (T)〈χT , χS〉 =

f (S),

(1.9)

b

where we used the Fourier expansion of f , the linearity of 〈·, ·〉, and ﬁnally
Theorem 1.5. This formula is the simplest way to calculate the Fourier coef-
ﬁcients of a given function; it can also be viewed as a streamlined version of
the interpolation method illustrated in (1.3). Alternatively, this formula can
be taken as the deﬁnition of Fourier coefﬁcients.

b

b

The orthonormal basis of parities also lets us measure the squared “length”
(2-norm) of f : {−1, 1}n → R efﬁciently: it’s just the sum of the squares of f ’s
“coordinates” – i.e., Fourier coefﬁcients. This simple but crucial fact is called
Parseval’s Theorem.

Parseval’s Theorem. For any f : {−1, 1}n → R,

〈 f , f 〉 =

E
x∼{−1,1}n

[ f (x)2] =

f (S)2.

S⊆[n]
X

In particular, if f : {−1, 1}n → {−1, 1} is Boolean-valued then

b

b
As examples we can recall the Fourier expansions of max2 and Maj3:

S⊆[n]
X

f (S)2 = 1.

max2(x) = 1
2

+ 1

2 x1 + 1

2 x2 − 1

2 x1x2,

Maj3(x) = 1

2 x1 + 1

2 x2 + 1

2 x3 − 1

2 x1x2x3.

In both cases the sum of squares of Fourier coefﬁcients is 4 × (1/4) = 1.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 8 -->
26

1. Boolean functions and the Fourier expansion

More generally, given two functions f , g : {−1, 1}n → R, we can compute
〈 f , g〉 by taking the “dot product” of their coordinates in the orthonormal basis
of parities. The resulting formula is called Plancherel’s Theorem.
Plancherel’s Theorem. For any f , g : {−1, 1}n → R,

〈 f , g〉 =

E
x∼{−1,1}n

[ f (x)g(x)] =

f (S)

g(S).

S⊆[n]
X

b

b

We can verify this formula explicitly as we did in (1.9):

〈 f , g〉 =

f (S) χS,

g(T) χT

=

f (S)

g(T)〈χS, χT 〉 =

f (S)

g(S).

b

T⊆[n]
X

S⊆[n]
D X

S,T⊆[n]
X
Now is a good time to remark that for Boolean-valued functions f , g :
{−1, 1}n → {−1, 1}, the inner product 〈 f , g〉 can be interpreted as a kind of “cor-
relation” between f and g, measuring how similar they are. Since f (x)g(x) = 1
if f (x) = g(x) and f (x)g(x) = −1 if f (x) 6= g(x), we have:

S⊆[n]
X

E

b

b

b

b

b

Proposition 1.9. If f , g : {−1, 1}n → {−1, 1},

〈 f , g〉 = Pr[ f (x) = g(x)] − Pr[ f (x) 6= g(x)] = 1 − 2dist( f , g).

Here we are using the following deﬁnition:

Deﬁnition 1.10. Given f , g : {−1, 1}n → {−1, 1}, we deﬁne their (relative Ham-
ming) distance to be

the fraction of inputs on which they disagree.

dist( f , g) = Pr
x

[ f (x) 6= g(x)],

With a number of Fourier formulas now in hand we can begin to illustrate
a basic theme in the analysis of Boolean functions: interesting combinatorial
properties of a Boolean function f can be “read off” from its Fourier coefﬁ-
cients. Let’s start by looking at one way to measure the “bias” of f :
Deﬁnition 1.11. The mean of f : {−1, 1}n → R is E[ f ]. When f has mean 0 we
say that it is unbiased, or balanced. In the particular case that f : {−1, 1}n →
{−1, 1} is Boolean-valued, its mean is

E[ f ] = Pr[ f = 1] − Pr[ f = −1];

thus f is unbiased if and only if it takes value 1 on exactly half of the points
of the Hamming cube.
Fact 1.12. If f : {−1, 1}n → R then E[ f ] =

f (;).

This formula holds simply because E[ f ] = 〈 f , 1〉 =

f (;) (taking S = ; in
Proposition 1.8). In particular, a Boolean function is unbiased if and only if
its empty-set Fourier coefﬁcient is 0.

b

b

Next we obtain a formula for the variance of a real-valued Boolean func-

tion (thinking of f (x) as a real-valued random variable):

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 9 -->
1.4. Basic Fourier formulas

27

Proposition 1.13. The variance of f : {−1, 1}n → R is

Var[ f ] = 〈 f − E[ f ], f − E[ f ]〉 = E[ f 2] − E[ f ]2 =

f (S)2.

The above Fourier formula follows immediately from Parseval’s Theorem and
Fact 1.12. We also have:

S6=;
X

b

Fact 1.14. For f : {−1, 1}n → {−1, 1},

Var[ f ] = 1 − E[ f ]2 = 4 Pr[ f (x) = 1] Pr[ f (x) = −1] ∈ [0, 1].

In particular, a Boolean-valued function f has variance 1 if it’s unbiased
and variance 0 if it’s constant. More generally, the variance of a Boolean-
valued function is proportional to its “distance from being constant”.

Proposition 1.15. Let f : {−1, 1}n → {−1, 1}. Then 2² ≤ Var[ f ] ≤ 4², where

² = min{dist( f , 1), dist( f , −1)}.

The proof of Proposition 1.15 is an exercise. See also Exercise 1.17.

By using Plancherel in place of Parseval, we get a generalization of Propo-

sition 1.13 for covariance:

Proposition 1.16. The covariance of f , g : {−1, 1}n → R is

Cov[ f , g] = 〈 f − E[ f ], g − E[g]〉 = E[ f g] − E[ f ] E[g] =

f (S)

g(S).

We end this section by discussing the Fourier weight distribution of Boolean

S6=;
X

b

b

functions.

Deﬁnition 1.17. The (Fourier) weight of f : {−1, 1}n → R on set S is deﬁned
to be the squared Fourier coefﬁcient,

f (S)2.

Although we lose some information about the Fourier coefﬁcients when
b
we square them, many Fourier formulas only depend on the weights of f .
For example, Proposition 1.13 says that the variance of f equals its Fourier
weight on nonempty sets. Studying Fourier weights is particularly pleasant
for Boolean-valued functions f : {−1, 1}n → {−1, 1} since Parseval’s Theorem
says that they always have total weight 1. In particular, they deﬁne a proba-
bility distribution on subsets of [n].

Deﬁnition 1.18. Given f : {−1, 1}n → {−1, 1}, the spectral sample for f , de-
noted S f , is the probability distribution on subsets of [n] in which the set S
has probability

f (S)2. We write S ∼ S f for a draw from this distribution.

For example, the spectral sample for the max2 function is the uniform
distribution on all four subsets of [2]; the spectral sample for Maj3 is the
uniform distribution on the four subsets of [3] with odd cardinality.

b

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 10 -->
28

1. Boolean functions and the Fourier expansion

Given a Boolean function it can be helpful to try to keep a mental picture
of its weight distribution on the subsets of [n], partially ordered by inclu-
sion. Figure 1.1 is an example for the Maj3 function, with the white circles
indicating weight 0 and the shaded circles indicating weight 1/4.

Figure 1.1. Fourier weight distribution of the Maj3 function

Finally, as suggested by the diagram we often stratify the subsets S ⊆ [n]
according to their cardinality (also called “height” or “level”). Equivalently,
this is the degree of the associated monomial xS.

Deﬁnition 1.19. For f : {−1, 1}n → R and 0 ≤ k ≤ n, the (Fourier) weight of f
at degree k is

Wk[ f ] =

f (S)2.

If f : {−1, 1}n → {−1, 1} is Boolean-valued, an equivalent deﬁnition is
Wk[ f ] = Pr
S∼S f

[|S| = k].

S⊆[n]
X
|S|=k

b

By Parseval’s Theorem, Wk[ f ] = k f =kk2

2 where

f =k =

f (S) χS

|S|=k
X
is called the degree k part of f . We will also sometimes use notation like
W>k[ f ] =

f (S)2 and f ≤k =

b

f (S) χS.

|S|>k

|S|≤k

1.5. Probability densities and convolution

b

b

P

P

For variety’s sake, in this section we write the Hamming cube as Fn
2 rather
than {−1, 1}n. In developing the Fourier expansion, we have generalized from
Boolean-valued Boolean functions f : Fn
→ {−1, 1} to real-valued Boolean func-
2
tions f : Fn
→ R. Boolean-valued functions arise more often in combinatorial
2
problems, but there are important classes of real-valued Boolean functions.
One example is probability densities.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.

[3]{1,3}{2,3}{1,2}{1}{2}{3}

<!-- pdf-page: 11 -->
1.5. Probability densities and convolution

29

Deﬁnition 1.20. A (probability) density function on the Hamming cube Fn
2
is any nonnegative function ϕ : Fn
2

→ R≥0 satisfying

[ϕ(x)] = 1.

E
x∼Fn
2

We write y ∼ ϕ to denote that y is a random string drawn from the associated
probability distribution, deﬁned by

[y = y] = ϕ(y)

Pr
y∼ϕ

1
2n

∀y ∈ Fn
2 .

Here you should think of ϕ(y) as being the relative density of y with

respect to the uniform distribution on Fn

Fact 1.21. If ϕ is a density function and g : Fn
2

2 . For example, we have:
→ R, then

[g(y)] = 〈ϕ, g〉 = E

[ϕ(x)g(x)].

E
y∼ϕ

x∼Fn
2

The simplest example of a probability density is just the constant func-
tion 1, which corresponds to the uniform probability distribution on Fn
2 . The
most common case arises from the uniform distribution over some subset
A ⊆ Fn
2 .

Deﬁnition 1.22. If A ⊆ Fn
function of A; i.e.,

2 we write 1A : Fn

2

→ {0, 1} for the 0-1 indicator

1A(x) =

1 if x ∈ A,

0 if x ∉ A.

(

Assuming A 6= ; we write ϕA for the density function associated to the uni-
form distribution on A; i.e.,

E[1A] 1A.
We typically write y ∼ A rather than y ∼ ϕA.

ϕA = 1

A simple but useful example is when A is the singleton set A = {0}. (Here 0
2 .) In this case the function ϕ{0} takes
2 . In Exercise 1.1 you will

is denoting the vector (0, 0, . . . , 0) ∈ Fn
value 2n on input 0 ∈ Fn
verify the Fourier expansion of ϕ{0}:

2 and is zero elsewhere on Fn

Fact 1.23. Every Fourier coefﬁcient of ϕ{0} is 1; i.e., its Fourier expansion is

ϕ{0}(y) =

χS(y).

S⊆[n]
X
We now introduce an operation on functions that interacts particularly

nicely with density functions, namely, convolution.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 12 -->
30

1. Boolean functions and the Fourier expansion

Deﬁnition 1.24. Let f , g : Fn
2
Fn
2

→ R deﬁned by

→ R. Their convolution is the function f ∗ g :

( f ∗ g)(x) = E

[ f (y)g(x − y)] = E

[ f (x − y)g(y)].

y∼Fn
2
Since subtraction is equivalent to addition in Fn

y∼Fn
2

( f ∗ g)(x) = E

y∼Fn
2

[ f (y)g(x + y)] = E

y∼Fn
2

2 we may also write
[ f (x + y)g(y)].

If we were representing the Hamming cube by {−1, 1}n rather than Fn
would replace x + y with x ◦ y, where ◦ denotes entry-wise multiplication.

2 we

Exercise 1.25 asks you to verify that convolution is associative and com-

mutative:

f ∗ (g ∗ h) = ( f ∗ g) ∗ h,

f ∗ g = g ∗ f .

Using Fact 1.21 we can deduce the following two simple results:

Proposition 1.25. If ϕ is a density function on Fn

2 and g : Fn

2

→ R then

ϕ ∗ g(x) = E
y∼ϕ

[g(x − y)] = E
y∼ϕ

[g(x + y)].

In particular, Ey∼ϕ[g(y)] = ϕ ∗ g(0).

Proposition 1.26. If g = ψ is itself a probability density function then so is
ϕ ∗ ψ; it represents the distribution on x ∈ Fn
2 given by choosing y ∼ ϕ and
z ∼ ψ independently and setting x = y + z.

The most important theorem about convolution is that it corresponds to

multiplication of Fourier coefﬁcients:

Theorem 1.27. Let f , g : Fn
2

→ R. Then for all S ⊆ [n],

f ∗ g(S) =

f (S)

g(S).

Proof. We have

(cid:129)

b

b

f ∗ g(S) = E

x∼Fn
2

[( f ∗ g)(x)χS(x)]

(cid:129)

= E

x∼Fn

E
y∼Fn
2

2 ·
E
y,z∼Fn
2
independently

=

[ f (y)g(x − y)]χS(x)
¸
[ f (y)g(z)χS(y + z)]

(the Fourier formula)

(by deﬁnition)

(as x − y is uniform on Fn
2

∀x)

= E

y,z∼Fn
2

[ f (y)χS(y)g(z)χS(z)]

(by identity (1.5))

=

f (S)

g(S)

(Fourier formula, independence),

as claimed.

b

b

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.

(cid:3)



<!-- pdf-page: 13 -->
1.6. Highlight: Almost linear functions and the BLR Test

31

1.6. Highlight: Almost linear functions and the BLR Test

In linear algebra there are two equivalent deﬁnitions of what it means for a
function to be linear:

Deﬁnition 1.28. A function f : Fn
2
equivalent conditions hold:

→ F2 is linear if either of the following

(1) f (x + y) = f (x) + f (y) for all x, y ∈ Fn
2 ;
(2) f (x) = a · x for some a ∈ Fn
2 ; i.e., f (x) =

i∈S xi for some S ⊆ [n].

Exercise 1.26 asks you to verify that the conditions are indeed equivalent.
If we encode the output of f by ±1 ∈ R in the usual way then the “linear”
functions f : Fn
2

→ {−1, 1} are precisely the 2n parity functions (χS)S⊆[n].

P

Let’s think of what it might mean for a function f : Fn
2
imately linear. Deﬁnition 1.28 suggests two possibilities:

→ F2 to be approx-

(10) f (x + y) = f (x) + f (y) for almost all pairs x, y ∈ Fn
2 ;
(20) there is some S ⊆ [n] such that f (x) =

i∈S xi for almost all x ∈ Fn
2 .

Are these equivalent? The proof of (2) =⇒ (1) in Deﬁnition 1.28 is “robust”: it
easily extends to show (20) =⇒ (10) (see Exercise 1.26). But the natural proof
of (1) =⇒ (2) in Deﬁnition 1.28 does not have this robustness property. The
goal of this section is to show that (10) =⇒ (20) nevertheless holds.

P

Motivation for this problem comes from an area of theoretical computer
science called property testing, which we will discuss in more detail in Chap-
ter 7. Imagine that you have “black-box” access to a function f : Fn
→ F2,
2
meaning that the function f is unknown to you but you can “query” its value
on inputs x ∈ Fn
2 of your choosing. The function f is “supposed” to be a linear
function, and you would like to try to verify this.

The only way you can be certain f is indeed a linear function is to query
its value on all 2n inputs; unfortunately, this is very expensive. The idea
behind “property testing” is to try to verify that f has a certain property – in
this case, linearity – by querying its value on just a few random inputs. In
exchange for efﬁciency, we need to be willing to only approximately verify the
property.

Deﬁnition 1.29. If f and g are Boolean-valued functions we say they are
²-close if dist( f , g) ≤ ²; otherwise we say they are ²-far. If P is a (nonempty)
property of n-bit Boolean functions we deﬁne dist( f , P ) = ming∈P {dist( f , g)}.
We say that f is ²-close to P if dist( f , P ) ≤ ²; i.e., f is ²-close to some g
satisfying P .

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 14 -->
32

1. Boolean functions and the Fourier expansion

In particular, in property testing we take property (20) above to be the no-
tion of “approximately linear”: we say f is ²-close to being linear if dist( f , g) ≤ ²
for some truly linear g(x) =

i∈S xi.

In 1990 Blum, Luby, and Rubinfeld [BLR90] showed that indeed (10) =⇒
(20) holds, giving the following “test” for the property of linearity that makes
just 3 queries:

P

BLR Test. Given query access to f : Fn
2
2 independently.

2 and y ∼ Fn
• Choose x ∼ Fn
• Query f at x, y, and x + y.

→ F2:

• “Accept” if f (x) + f (y) = f (x + y).

We now show that if the BLR Test accepts f with high probability then
f is close to being linear. The proof works by directly relating the acceptance
probability to the quantity

f (S)3; see equation (1.10) below.

S

Theorem 1.30. Suppose the BLR Test accepts f : Fn
P
2
1 − ². Then f is ²-close to being linear.

b

→ F2 with probability

Proof. In order to use the Fourier transform we encode f ’s output by ±1 ∈ R;
thus the acceptance condition of the BLR Test becomes f (x) f (y) = f (x + y).
Since

1
2

+ 1

2 f (x) f (y) f (x + y) =

1 if f (x) f (y) = f (x + y),

0 if f (x) f (y) 6= f (x + y),

(

we conclude

1 − ² = Pr[BLR accepts f ] = E
x,y

[ 1
2

+ 1

2 f (x) f (y) f (x + y)]

= 1
2

= 1
2
= 1
2

+ 1
2

= 1
2

+ 1
2

+ 1

2 E
x

[ f (x) · E
y

[ f (y) f (x + y)]]

+ 1

2 E
x

[ f (x) · ( f ∗ f )(x)]

(by deﬁnition)

f (S)

f ∗ f (S)

(Plancherel)

S⊆[n]
X

f (S)3
b

(cid:129)

(Theorem 1.27).

b
We rearrange this equality and then continue:

S⊆[n]
X

1 − 2² =

f (S)3

(1.10)

b
f (S)} ·
{

f (S)2

S⊆[n]
X
≤ max
S⊆[n]

= max
S⊆[n]

b
f (S)}

{

S⊆[n]
X

b

(Parseval).

b
Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 15 -->
1.7. Exercises and notes

33

f (S) = 〈 f , χS〉 = 1 − 2dist( f , χS) (Proposition 1.9). Hence there exists some
But
S∗ ⊆ [n] such that 1−2² ≤ 1−2dist( f , χS∗); i.e., f is ²-close to the linear function
(cid:3)
χS∗.

b

In fact, for small ² one can show that f is more like (²/3)-close to linear,

and this is sharp. See Exercise 1.28.

The BLR Test shows that given black-box access to f : Fn
2

→ {−1, 1}, we can
“test” whether f is close to some linear function χS using just 3 queries. The
test does not reveal which linear function χS is close to (indeed, determining
this takes at least n queries; see Exercise 1.27). Nevertheless, we can still
determine the value of χS(x) with high probability for every x ∈ Fn
2 of our
choosing using just 2 queries. This property is called local correctability of
linear functions.

Proposition 1.31. Suppose f : Fn
2
Then for every x ∈ Fn
at least 1 − 2²:

→ {−1, 1} is ²-close to the linear function χS.
2 , the following algorithm outputs χS(x) with probability

• Choose y ∼ Fn
2 .
• Query f at y and x + y.

• Output f (y) f (x + y).

We emphasize the order of quantiﬁers here: if we just output f (x) then this
will equal χS(x) for most x; however, the above “local correcting” algorithm
determines χS(x) (with high probability) for every x.

Proof. Since y and x + y are both uniformly distributed on Fn
2 (though not
independently) we have Pr[ f (y) 6= χS(y)] ≤ ² and Pr[ f (x + y) 6= χS(x + y)] ≤ ²
by assumption. By the union bound, the probability of either event occurring
is at most 2²; when neither occurs,

f (y) f (x + y) = χS(y)χS(x + y) = χS(x)

as desired.

1.7. Exercises and notes

(cid:3)

1.1 Compute the Fourier expansions of the following functions:

(a) min2 : {−1, 1}2 → {−1, 1}, the minimum function on 2 bits (also known

as the logical OR function);

(b) min3 : {−1, 1}3 → {−1, 1} and max3 : {−1, 1}3 → {−1, 1};
(c) the indicator function 1{a} : Fn
→ {0, 1}, where a ∈ Fn
2 ;
2
(d) the density function ϕ{a} : Fn
→ R≥0, where a ∈ Fn
2 ;
2
(e) the density function ϕ{a,a+e i} : Fn
2

→ R≥0, where a ∈ Fn

2 and e i =

(0, . . . , 0, 1, 0, . . . , 0) with the 1 in the ith coordinate;

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 16 -->
34

1. Boolean functions and the Fourier expansion

(f ) the density function corresponding to the product probability distri-
bution on {−1, 1}n in which each coordinate has mean ρ ∈ [−1, 1];

(g) the inner product mod 2 function, IP2n : F2n
2

IP2n(x1, . . . , xn, y1, . . . , yn) = (−1)x·y;

→ {−1, 1} deﬁned by

(h) the equality function Equn : {−1, 1}n → {0, 1}, deﬁned by Equn(x) = 1 if

and only if x1 = x2 = · · · = xn;

(i) the not-all-equal function NAEn : {−1, 1}n → {0, 1}, deﬁned by NAEn(x) =

1 if and only if the bits x1, . . . , xn are not all equal;

(j) the selection function, Sel : {−1, 1}3 → {−1, 1}, which outputs x2 if x1 =

→ {0, 1}, which is 1 if and only if the number of 1’s in the

−1 and outputs x3 if x1 = 1;

(k) mod3 : F3
2

(l) OXR : F3
2

input is divisible by 3;

→ {0, 1} deﬁned by OXR(x1, x2, x3) = x1 ∨ (x2 ⊕ x3). Here ∨ de-

notes logical OR, ⊕ denotes logical XOR;

(m) the sortedness function Sort4 : {−1, 1}4 → {−1, 1}, deﬁned by Sort4(x) =

−1 if and only if x1 ≤ x2 ≤ x3 ≤ x4 or x1 ≥ x2 ≥ x3 ≥ x4;

(n) the hemi-icosahedron function HI : {−1, 1}6 → {−1, 1} (also known as
the Kushilevitz function), deﬁned to be the number of facets labeled
(+1, +1, +1) in Figure 1.2, minus the number of facets labeled (−1, −1, −1),
modulo 3.

Figure 1.2. The hemi-icosahedron

(Hint: First compute the real multilinear interpolation of the ana-
logue HI : {0, 1}6 → {0, 1}.)

(o) the majority functions Maj5 : {−1, 1}5 → {−1, 1} and Maj7 : {−1, 1}7 →

{−1, 1};

(p) the complete quadratic function CQn : Fn
2

→ {−1, 1} deﬁned by CQn(x) =
1≤i< j≤n xi x j). (Hint: Determine CQn(x) as a function of the num-
χ(
ber of 1’s in the input modulo 4. You’ll want to distinguish whether n
is even or odd.)

P

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 17 -->
1.7. Exercises and notes

35

1.2 How many Boolean functions f : {−1, 1}n → {−1, 1} have exactly 1 nonzero

Fourier coefﬁcient?

1.3 Let f : Fn
2

→ {0, 1}, n > 1, and suppose #{x : f (x) = 1} is odd. Prove that all

of f ’s Fourier coefﬁcients are nonzero.

1.4 Let f : {−1, 1}n → R have Fourier expansion f (x) =

Rn → R be the extension of f which is also deﬁned by F(x) =
Show that if µ = (µ1, . . . , µn) ∈ [−1, 1]n then
b

P

S⊆[n]

f (S) xS. Let F :
f (S) xS.

S⊆[n]

P

b

F(µ) = E
y

[ f (y)],

where y is the random string in {−1, 1}n deﬁned by having E[yi] = µi
independently for all i ∈ [n].

1.5 Prove that any f : {−1, 1}n → {−1, 1} has at most one Fourier coefﬁcient
with magnitude exceeding 1/2. Is this also true for any f : {−1, 1}n → R
with k f k2 = 1?

1.6 Use Parseval’s Theorem to prove uniqueness of the Fourier expansion.
1.7 Let f : {−1, 1}n → {−1, 1} be a random function (i.e., each f (x) is ±1 with
probability 1/2, independently for all x ∈ {−1, 1}n). Show that for each
f (S) has mean 0 and variance 2−n. (Hint:
S ⊆ [n], the random variable
Parseval.)

b

1.8 The (Boolean) dual of f : {−1, 1}n → R is the function f † deﬁned by f †(x) =
− f (−x). The function f is said to be odd if it equals its dual; equivalently,
if f (−x) = − f (x) for all x. The function f is said to be even if f (−x) = f (x)
for all x. Given any function f : {−1, 1}n → R, its odd part is the function
f odd : {−1, 1}n → R deﬁned by f odd(x) = ( f (x) − f (−x))/2, and its even part
is the function f even : {−1, 1}n → R deﬁned by f even(x) = ( f (x) + f (−x))/2.
(a) Express
(b) Verify that f = f odd + f even and that f is odd (respectively, even) if and

f †(S) in terms of

f (S).

only if f = f odd (respectively, f = f even).

b

c

(c) Show that

f odd =

f (S) χS,

f even =

f (S) χS.

S⊆[n]
X
|S| odd

b

S⊆[n]
X
|S| even

b

1.9 In this problem we consider representing False,True as 0, 1 ∈ R.

(a) Using the interpolation method from Section 1.2, show that every f :
{False,True}n → {False,True} can be represented as a real multilinear
polynomial

q(x) =

cS

xi,

(1.11)

“over {0, 1}”, meaning mapping {0, 1}n → {0, 1}.

S⊆[n]
X

i∈S
Y

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 18 -->
36

1. Boolean functions and the Fourier expansion

(b) Show that this representation is unique. (Hint: If q as in (1.11) has
at least one nonzero coefﬁcient, consider q(a) where a ∈ {0, 1}n is the
indicator vector of a minimal S with cS 6= 0.)

(c) Show that all coefﬁcients cS in the representation (1.11) will be inte-

gers in the range [−2n, 2n].

(d) Let f : {False,True}n → {False,True}. Let p(x) be f ’s multilinear rep-
resentation when False,True are 1, −1 ∈ R (i.e., p is the Fourier ex-
pansion of f ) and let q(x) be f ’s multilinear representation when
False,True are 0, 1 ∈ R. Show that q(x) = 1
2

2 p(1 − 2x1, . . . , 1 − 2xn).

− 1

1.10 Let f : {−1, 1}n → R be not identically 0. The (real) degree of f , denoted
deg( f ), is deﬁned to be the degree of its multilinear (Fourier) expansion;
i.e., max{|S| :
(a) Show that deg( f ) = deg(a + b f ) for any a, b ∈ R (assuming b 6= 0, a +

f (S) 6= 0}.

b f 6= 0).

b

(b) Show that deg( f ) ≤ k if and only if f is a real linear combination of
functions g1, . . . , gs, each of which depends on at most k input coordi-
nates.

(c) Which functions in Exercise 1.1 have “nontrivial” degree? (Here f :

{−1, 1}n → R has “nontrivial” degree if deg( f ) < n.)

1.11 Suppose that f : {−1, 1}n → {−1, 1} has deg( f ) = k ≥ 1.

(a) Show that f ’s real multilinear representation over {0, 1} (see Exer-

cise 1.9), call it q(x), also has deg(q) = k.

(b) Using Exercise 1.9(c),(d), deduce that f ’s Fourier spectrum is “21−k-

granular”, meaning each

f (S) is an integer multiple of 21−k.

(c) Show that

S⊆[n] |

f (S)| ≤ 2k−1.

b

b

P

1.12 A Hadamard Matrix is any N × N real matrix with ±1 entries and orthog-
onal rows. Particular examples are the Walsh–Hadamard Matrices HN ,
inductively deﬁned for N = 2n as follows: H1 =
.
¸
(a) Let’s index the rows and columns of H2n by the integers {0, 1, 2, . . . , 2n−
1} rather than [2n]. Further, let’s identify such an integer i with its
binary expansion (i0, i1, . . . , i n−1) ∈ Fn
2 , where i0 is the least signiﬁcant
bit and i n−1 the most. For example, if n = 3, we identify the index
i = 6 with (0, 1, 1). Now show that the (γ, x) entry of H2n is (−1)γ·x.
→ R is represented as a column vector in R2n

H2n H2n
H2n −H2n

, H2n+1 =

(b) Show that if f : Fn
2

1

·

£

¤

cording to the indexing scheme from part (a)) then 2−nH2n f =
we think of
S ⊆ {0, 1, . . . , n − 1} with their indicator vectors.

f as also being a function Fn
2

b

(ac-
f . Here
→ R, identifying subsets

b

(c) Show how to compute H2n f using just n2n additions and subtractions
(rather than 22n additions and subtractions as the usual matrix-vector
multiplication algorithm would require). This computation is called

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 19 -->
1.7. Exercises and notes

37

the Fast Walsh–Hadamard Transform and is the method of choice
for computing the Fourier expansion of a generic function f : Fn
→ R
2
when n is large.

(d) Show that taking the Fourier transform is essentially an “involution”:

f = 2−n f (using the notations from part (b)).

1.13 Let f : {−1, 1}n → R and let 0 < p ≤ q < ∞. Show that k f kp ≤ k f kq. (Hint:
Use Jensen’s inequality with the convex function t 7→ tq/p.) Extend the in-
equality to the case q = ∞, where k f k∞ is deﬁned to be maxx∈{−1,1}n {| f (x)|}.

bb

1.14 Compute the mean and variance of each function from Exercise 1.1.
1.15 Let f : {−1, 1}n → R. Let K ⊆ [n] and let z ∈ {−1, 1}K . Suppose g : {−1, 1}[n]\K →
R is the subfunction of f gotten by restricting the K-coordinates to be z.
Show that E[g] =

f (T) zT .

T⊆K

1.16 If f : {−1, 1}n → {−1, 1}, show that Var[ f ] = 4·dist( f , 1)·dist( f , −1). Deduce

Proposition 1.15.

P

b

1.17 Extend Fact 1.14 by proving the following: If F is a {−1, 1}-valued random

variable with mean µ then
Var[F] = E[(F − µ)2] = 1

2 E[(F − F0)2] = 2 Pr[F 6= F0] = E[|F − µ|],

where F0 is an independent copy of F. (The ﬁrst two equalities do not
require F to be {−1, 1}-valued.)
1.18 For any f : {−1, 1}n → R, show that

〈 f =k, f =`〉 =

Wk[ f ]
0

(

if k = `,
if k 6= `.

1.19 Let f : {−1, 1}n → {−1, 1}.

(a) Suppose W1[ f ] = 1. Show that f (x) = ±χS for some |S| = 1.
(b) Suppose W≤1[ f ] = 1. Show that f depends on at most 1 input coordi-

nate.

(c) Suppose W≤2[ f ] = 1. Must f depend on at most 2 input coordinates?

At most 3 input coordinates? What if we assume W2[ f ] = 1?

1.20 Let f : {−1, 1}n → R satisfy f = f =1. Show that Var[ f 2] = 2
f ( j)2.
1.21 Prove that there are no functions f : {−1, 1}n → {−1, 1} with exactly 2
nonzero Fourier coefﬁcients. What about exactly 3 nonzero Fourier coefﬁ-
cients?

f (i)2

i6= j

P

b

b

1.22 Verify Propositions 1.25 and 1.26.

1.23 In this exercise you will prove some basic facts about “distances” between
probability distributions. Let ϕ and ψ be probability densities on Fn
2 .
(a) Show that the total variation distance between ϕ and ψ, deﬁned by

dTV(ϕ, ψ) = max
A⊆Fn

Pr
y∼ϕ

[y ∈ A] − Pr
y∼ψ

[y ∈ A]

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.

,

o

¯
¯
¯

2 n¯
¯
¯



<!-- pdf-page: 20 -->
38

1. Boolean functions and the Fourier expansion

is equal to 1
2

kϕ − ψk1.

(b) Show that the collision probability of ϕ, deﬁned to be

[y = y0],

Pr
y,y0∼ϕ
independently

is equal to kϕk2

2/2n.

(c) The χ2-distance of ϕ from ψ is deﬁned by

dχ2(ϕ, ψ) = E
y∼ψ

ϕ(y)
ψ(y)
assuming ψ has full support. Show that the χ2-distance of ϕ from
uniform is equal to Var[ϕ].

− 1

h³

i

´

2

,

(d) Show that the total variation distance of ϕ from uniform is at most

1
2

Var[ϕ].

p

1.24 Let A ⊆ {−1, 1}n have “volume” δ, meaning E[1A] = δ. Suppose ϕ is a
probability density supported on A, meaning ϕ(x) = 0 when x ∉ A. Show
that kϕk2
2 ≥ 1/δ with equality if ϕ = ϕA, the uniform density on A.

1.25 Show directly from the deﬁnition that the convolution operator is associa-

tive and commutative.

1.26 Verify that (1) ⇐⇒ (2) in Deﬁnition 1.28.
1.27 Suppose an algorithm is given query access to a linear function f : Fn
2

→
F2 and its task is to determine which linear function f is. Show that
querying f on n inputs is necessary and sufﬁcient.
1.28 (a) Generalize Exercise 1.5 as follows: Let f : Fn
2

→ {−1, 1} and suppose
f (S)| ≤ 2δ for all S 6= S∗. (Hint: Use

that dist( f , χS∗) = δ. Show that |
the union bound.)

b
(b) Deduce that the BLR Test rejects f with probability at least 3δ −

10δ2 + 8δ3.

(c) Show that this lower bound cannot be improved to cδ − O(δ2) for any

c > 3.
1.29 (a) We call f : Fn
2

→ F2 an afﬁne function if f (x) = a · x + b for some a ∈ Fn
2 ,
b ∈ F2. Show that f is afﬁne if and only if f (x)+ f (y)+ f (z) = f (x+ y+ z)
for all x, y, z, ∈ Fn
2

(b) Let f : Fn
2

→ R. Suppose we choose x, y, z ∼ Fn

uniformly. Show that E[ f (x) f (y) f (z) f (x + y + z)] =

(c) Give a 4-query test for a function f : Fn
2

S
→ F2 with the following prop-
b
erty: if the test accepts with probability 1 − ² then f is ²-close to being
afﬁne. All four query inputs should have the uniform distribution
on Fn

2 (but of course need not be independent).

P

(d) Give an alternate 4-query test for being afﬁne in which three of the
query inputs are uniformly distributed and the fourth is not random.

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.

2 independently and
f (S)4.



<!-- pdf-page: 21 -->
1.7. Exercises and notes

39

(Hint: Show that f is afﬁne if and only if f (x) + f (y) + f (0) = f (x + y)
for all x, y ∈ Fn

2 .)

1.30 Permutations π ∈ Sn act on strings x ∈ {−1, 1}n in the natural way: (xπ)i =
xπ(i). They also act on functions f : {−1, 1}n → R via f π(x) = f (xπ) for all x ∈
{−1, 1}n. We say that functions g, h : {−1, 1}n → {−1, 1} are (permutation-
)isomorphic if g = hπ for some π ∈ Sn. We call Aut( f ) = {π ∈ Sn : f π = f }
the (permutation-)automorphism group of f .

(a) Show that

f π(S) =

f (π−1(S)) for all S ⊆ [n].

For future reference, when we write (

f (S))|S|=k, we mean the sequence
of degree-k Fourier coefﬁcients of f , listed in lexicographic order of the
k-sets S.

c

b

b

Given complete truth tables of some g and h we might wish to deter-
mine whether they are isomorphic. One way to do this would be to deﬁne
a canonical form can( f ) : {−1, 1}n → {−1, 1} for each f : {−1, 1}n → {−1, 1},
meaning that: (i) can( f ) is isomorphic to f ; (ii) if g is isomorphic to h then
can(g) = can(h). Then we can determine whether g is isomorphic to h by
checking whether can(g) = can(h). Here is one possible way to deﬁne a
canonical form for f :
1. Set P0 = Sn.
2. For each k = 1, 2, 3, . . . , n,
3.

Deﬁne Pk to be the set of all π ∈ Pk−1 that make the sequence
f π(S))|S|=k maximal in lexicographic order on R(n
k).
(

4. Let can( f ) = f π for (any) π ∈ Pn.

(b) Show that this is well-deﬁned, meaning that can( f ) is the same func-

c

tion for any choice of π ∈ Pn.

(c) Show that can( f ) is indeed a canonical form; i.e., it satisﬁes (i) and (ii)

f ({n}) are distinct numbers then can( f ) can be

above.
(d) Show that if
computed in

f ({1}), . . . ,
O(2n) time.
b
b
e

(e) We could more generally consider g, h : {−1, 1}n → {−1, 1} to be isomor-
phic if g(x) = h(±xπ(1), . . . , ±xπ(n)) for some permutation π on [n] and
some choice of signs. Extend the results of this exercise to handle this
deﬁnition.

Notes. The Fourier expansion for real-valued Boolean functions dates back
to Walsh [Wal23] who introduced a complete orthonormal basis for L2([0, 1])
consisting of ±1-valued functions, constant on dyadic intervals. Using the or-
dering introduced by Paley [Pal32], the nth Walsh basis function wn : [0, 1] →
i=0 ni2i and r i(x) (the
{−1, 1} is deﬁned by wn(x) =
i=0 xi2−(i+1)
“ith Rademacher function at x”) is deﬁned to be (−1)xi , with x =
for non-dyadic x ∈ [0, 1]. Walsh’s interest was in comparing and contrasting

i=0 r i(x)ni , where n =

Q

P

∞

∞

∞

P

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 22 -->
40

1. Boolean functions and the Fourier expansion

the properties of this basis with the usual basis of trigonometric polynomials
and also Haar’s basis [Haa10].

The ﬁrst major study of the Walsh functions came in the remarkable paper
of Paley [Pal32], which included strong results on the L p-norms of truncations
of Walsh series. Sadly, Paley died in an avalanche one year later (at age 26)
while skiing near Banff. The next major development in the study of Walsh
series was conceptual, with Vilenkin [Vil47] and Fine [Fin49] independently
suggesting the more natural viewpoint of the Walsh functions as characters
of the discrete group Zn
2 . There was signiﬁcant subsequent work in the 1950s
and 1960s, but it’s somewhat unnatural from our point of view because it
relies fundamentally on ordering the Rademacher and Walsh functions ac-
cording to binary expansions. Bonami [Bon68] and Kiener [Kie69] seem to
have been the ﬁrst authors to take our viewpoint, treating bits x1, x2, x3, . . .
symmetrically and ordering Fourier characters χS according to |S| rather
than max(S). Bonami also obtained the ﬁrst hypercontractivity result for the
Boolean cube. This proved to be a crucial tool for analysis of Boolean func-
tions; see Chapter 9. For an early survey on Walsh series, see Balashov and
Rubinshtein [BR73].

Turning to Boolean functions and computer science, the idea of using
Boolean logic to study “switching functions” (as engineers originally called
Boolean functions) dates to the late 1930s and is usually credited to Naka-
shima [Nak35], Shannon [Sha37], and Shestakov [She38]. Muller [Mul54b]
seems to be the ﬁrst to have used Fourier coefﬁcients in the study of Boolean
functions; he mentions computing them while classifying all functions f :
{0, 1}4 → {0, 1} up to certain equivalences. The ﬁrst publication devoted to
Boolean Fourier coefﬁcients was by Ninomiya [Nin58], who expanded on
Muller’s use of Fourier coefﬁcients for the classiﬁcation of Boolean functions
up to various isomorphisms. Golomb [Gol59] independently pursued the
same project (his work is the content of Exercise 1.30); he was also the ﬁrst to
recognize the connection to Walsh series. The use of “Fourier–Walsh analysis”
in the study of Boolean functions quickly became well known in the early
1960s. Several symposia on applications of Walsh functions took place in the
early 1970s, with Lechner’s 1971 monograph [Lec71] and Karpovsky’s 1976
book [Kar76] becoming the standard references. However, the use of Boolean
analysis in theoretical computer science seemed to wane until 1988, when the
outstanding work of Kahn, Kalai, and Linial [KKL88] ushered in a new area
of sophistication.

The original analysis by Blum, Luby, and Rubinfeld [BLR90] for their
linearity test was combinatorial; our proof of Theorem 1.30 is the elegant an-
alytic one due to Bellare, Coppersmith, Håstad, Kiwi, and Sudan [BCH+96].
In fact, the essence of this analysis appears already in the 1953 work of

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 23 -->
1.7. Exercises and notes

41

Roth [Rot53] (in the context of the cyclic group ZN rather than Fn
2 ). The
work of Bellare et al. also gives additional analysis improving the results of
Theorem 1.30 and Exercise 1.28. See also the work of Kaufman, Litsyn, and
Xie [KLX10] for further slight improvement.

In Exercise 1.1, the sortedness function was introduced by Ambainis [Amb03,

LLS06]; the hemi-icosahedron function was introduced by Kushilevitz [NW95].
The fast algorithm for computing the Fourier transform mentioned in Exer-
cise 1.12 is due to Lechner [Lec63].

Copyright © Ryan O’Donnell, 2014, 2015, 2016, 2017, 2018, 2019, 2020, 2021.



<!-- pdf-page: 24 -->

