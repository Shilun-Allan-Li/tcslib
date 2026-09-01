<!-- generated-by: proofmatch local extraction -->
<!-- source-pdf-sha256: 6bd33ae73ade77ad4a393e92243ca508478906f32de19880904153123c7e900d -->
<!-- extractor: pdfminer.six v20260107 -->

<!-- pdf-page: 1 -->
GURUSWAMI, H ˚ASTAD, SUDAN, AND ZUCKERMAN

1

Combinatorial Bounds for List Decoding

Venkatesan Guruswami Johan H˚astad Madhu Sudan David Zuckerman

Abstract—Informally, an error-correcting code has “nice” list-
decodability properties if every Hamming ball of “large” radius
has a “small” number of codewords in it. Here, we report linear
codes with non-trivial list-decodability: i.e., codes of large rate
that are nicely list-decodable, and codes of large distance that
are not nicely list-decodable. Speciﬁcally, on the positive side,
we show that there exist codes of rate R and block length n
that have at most c codewords in every Hamming ball of radius
H −1(1 − R − 1/c) · n. This answers the main open question
from the work of Elias [8]. This result also has consequences
for the construction of concatenated codes of good rate that are
list decodable from a large fraction of errors, improving previous
results of [13] in this vein. Speciﬁcally, for every ε > 0, we present
a polynomial time constructible asymptotically good family of
binary codes of rate Ω(ε4) that can be list decoded in polynomial
time from up to a fraction (1/2 − ε) of errors, using lists of size
O(ε−2).

On the negative side, we show that for every δ and c, there
exists τ < δ, c1 > 0 and an inﬁnite family of linear codes
{Ci}i such that if ni denotes the block length of Ci, then Ci has
minimum distance at least δ · ni and contains more than c1 · nc
i
codewords in some Hamming ball of radius τ ·ni. While this result
is still far from known bounds on the list-decodability of linear
codes, it is the ﬁrst to bound the “radius for list-decodability by
a polynomial-sized list” away from the minimum distance of the
code.

Index Terms—Error-correcting codes, List decoding, Concate-

nated codes, Reed-Solomon code.

I. INTRODUCTION

L IST decoding was introduced independently by Elias [7]

and Wozencraft [24] as a relaxation of the “classical”
notion of decoding by allowing the decoder to output a list of
codewords as answers. The decoding is considered successful
as long as the correct message is included in the list. Early
work by Elias and Wozencraft [7], [24] analyzed the probabil-
ity of error in this model and used random coding arguments to

A preliminary version of this paper appears in the Proceedings of the Annual
Allerton Conference on Communication, Control and Computing, Monticello,
Illinois, October 2000, pp. 603-612.

address

Venkatesan Guruswami’s

at
Berkeley, Computer Science Division, Berkeley, CA 94720. Email:
venkat@lcs.mit.edu. The work was done while the author was at
MIT and was supported in part by an IBM Graduate Fellowship and NSF
CCR-9875511.

of California

is University

Johan H˚astad’s address is Department of Numerical Analysis and Computer
Science, Royal Institute of Technology, SE-100 44 Stockholm, Sweden.
Email: johanh@nada.kth.se. Supported in part by the G¨oran Gustafsson
foundation and NSF grant CCR-9987077.

Madhu Sudan’s address is Laboratory for Computer Science, 200 Tech-
nology Square, Cambridge, MA 02139, USA. Email: madhu@mit.edu.
Supported in part by a Sloan Foundation Fellowship, NSF Career Award
CCR-9875511, NSF Grant CCR-9912342, and NTT Award MIT2001-04.

David Zuckerman’s address is Department of Computer Science, University
of Texas, Austin, TX 78712, USA. Email: diz@cs.utexas.edu. Most
of this work was done while this author was on leave at the University of
California, Berkeley. Supported in part by NSF Grant CCR-9912428, NSF
NYI Grant CCR-9457799, and a David and Lucile Packard Fellowship for
Science and Engineering.

explore the average decoding error probability of block codes
at low rates for the binary symmetric channel. List decoding
was also used by Shannon, Gallager and Berlekamp [17] in
exploring low rate average error bounds for general discrete
memoryless channels, and Ahlswede [1] showed that it enables
one to determine capacity of a wide class of communication
channels.

Research in the eighties applied this notion in a more
adversarial setting and investigated what happens if the error
is effected by an adversary or a “jammer”, as opposed to
a probabilistic channel. Works of Zyablov and Pinsker [25],
Blinovsky [3], [4], and Elias [8] applied in this setting. (The
paper by Elias [8] also gives a very good summary of the prior
work and history.) The basic question raised in this setting was:
How many errors could still be recovered from, with lists of
small size? Two basic parameters thus are the number of errors
and the allowed size of the output list. These parameters are
usually studied as a function of some of the more classical
parameters of error-correcting codes. How large can the rate
of a code be if we want small list sizes for a certain number of
errors? And how do codes of large minimum distance perform
with respect to list decoding? Recently there has been rejuve-
nated interest in this line of work thanks to the development of
some efﬁcient algorithms for list decoding in [19], [12], [18],
[13]. These algorithms decode with polynomial sized lists (and
sometimes with constant sized lists) for much more than half
the minimum distance of the code, and investigations of the
tightness of the algorithms have led Høholdt and Justesen [16]
to re-initiate the investigation of the combinatorial bounds on
list decoding.

In this paper we continue the investigation of bounds on
list decoding. In particular, we investigate codes that exhibit
non-trivial list decoding performance. Speciﬁcally, we report
the existence of linear codes of large rate that are nicely list-
decodable, and codes of large minimum distance which are
not nicely list-decodable (the precise quantitative versions of
these results are stated in the next section). To motivate this
study we ﬁrst ﬁx some standard notation and then deﬁne two
fundamental questions (parameters) to study in the context of
list decoding.

Our results also has consequences for the construction
of concatenated codes of good rate that are list decodable
from a large fraction of errors, improving previous results of
[13] in this vein. Speciﬁcally, for every ε > 0, we present
a polynomial time constructible asymptotically good family
of binary codes of rate Ω(ε4) that can be list decoded in
polynomial time from up to a fraction (1/2 − ε) of errors,
using lists of size O(ε−2).



<!-- pdf-page: 2 -->
2

GURUSWAMI, H ˚ASTAD, SUDAN, AND ZUCKERMAN

II. DEFINITIONS AND MAIN RESULTS

For a prime power q,

let Fq denote a ﬁnite ﬁeld of
cardinality q. An [n, k]q (linear) code C is a k-dimensional
vector space in Fn
2 . We refer to n as the blocklength of the
code and to k as the dimension of the code. Unless explicitly
mentioned otherwise, we will only be interested in linear codes
in this paper and will moreover restrict ourselves to the binary
case (when q = 2).

For two strings x, y of length n over an arbitrary alphabet
Σ, let ∆(x, y) denote the Hamming distance between them,
i.e., the number of coordinates where x and y differ. Denote
by δ(x, y) = ∆(x,y)
the relative (fractional) distance between
x and y. The minimum distance of a code C, denoted dist(C),
is the quantity minx,y∈C,x(cid:54)=y{∆(x, y)}. The relative distance
of the code C, denoted δ(C), is analogously deﬁned.

n

Since the main thrust of this paper is the asymptotic
performance of the codes, we deﬁne analogs of the quantities
above for inﬁnite families of codes. An inﬁnite family of
(binary) codes is a family C = {Ci|i ∈ Z+} where Ci is
an [ni, ki]2 code with ni > ni−1. We deﬁne the rate of an
inﬁnite family of codes C to be

rate(C) = lim inf
i

(cid:27)

.

(cid:26) ki
ni

We deﬁne the (relative) distance of an inﬁnite family of codes
C to be

∆(C) = lim inf
i

(cid:26) dist(Ci)
ni

(cid:27)

.

We now deﬁne the list decoding radius of a code. For non-
negative integer r and x ∈ Fn
2 , let B(x, r) denote the ball of
radius r around x, i.e., B(x, r) = {y ∈ Fn
2 |∆(x, y) ≤ r}. For
integers e, (cid:96), a code C ⊆ Fn
2 is said to be (e, (cid:96))-list decodable
if every ball of radius e has at most (cid:96) codewords, i.e. ∀ x ∈ Fn
2 ,
|B(x, e) ∩ C| ≤ (cid:96).

Deﬁnition 1 (List Decoding Radius): For an [n, k] binary
code C, and list size (cid:96), the list of (cid:96) decoding radius of C,
denoted radius(C, (cid:96)) is deﬁned to be the maximum value of e
for which C is (e, (cid:96))-list decodable.

Deﬁnition 2: (List Decoding Radius for code and function
families) For an inﬁnite family of codes C and a function
(cid:96) : Z+ → Z+, deﬁne the list of (cid:96) decoding radius of C,
denoted Rad(C, (cid:96)), to be

Rad(C, (cid:96)) = lim inf
i

(cid:26) radius(Ci, (cid:96)(ni))
ni

(cid:27)

.

list decoding radius for a given function (cid:96)? Note that the other
two questions are uninteresting: speciﬁcally, it is possible to
construct codes of small rate that have small list decoding
radius (for example, the linear code that is spanned by a
small number of standard basis vectors has small rate, but
the entire code is contained in a small ball around the all
zeroes codeword); and it is possible to construct codes of
small distance that have large list decoding radius even for
lists of size 2 (for example by taking a code of large minimum
distance and adding one codeword at a small distance to some
existing codeword). In what follows we introduce some formal
parameters to study the above questions.

A. List decoding radius vs. Rate of the code

Deﬁnition 3 (Upper bound on list decoding radius): For
real rate 0 ≤ R ≤ 1 and list size (cid:96) : Z+ → Z+, the upper
bound on list of (cid:96) decoding radius for (binary) codes of rate
R, denoted U(cid:96)(R), is deﬁned to be

U(cid:96)(R) =

sup
C | rate(C)≥R

Rad(C, (cid:96)).

Similarly, for a family of integer-valued functions F, one
deﬁnes the quantity

UF (R) = sup
(cid:96)∈F

U(cid:96)(R) .

Note that the reason for the term “upper bound” is that
U(cid:96)(R) is the list decoding radius of the best code (i.e. one
with largest possible list decoding radius) among all codes
that have at least a certain rate. The case where the list size
function is a constant, or growing polynomially is of special
interest to us, and we consider the following deﬁnitions.

c

c

Deﬁnition 4: For real rate 0 ≤ R ≤ 1 and constant
the quantity U const
(R) is deﬁned to be U(cid:96)(R) where
c,
(cid:96)(n) = c. The quantity U poly
(R) is deﬁned to be UFc(R)
: Z+ →
functions {(cid:96)c1
where Fc
is the family of
Z+ where (cid:96)c1(n) = c1nc}. The quantity U const(R) (resp.
U poly(R)) will denote the quantity lim supc→∞{U const
(R)}
(resp. lim supc→∞{U poly
(R)}).

Thus the quantities U const(R) and U poly(R) denote the
maximum possible value of the (relative) list decoding radius
for lists of constant and polynomial size, respectively. These
quantities are actually surprisingly well-understood. The ﬁrst
to pin this quantity down were Zyablov and Pinsker [25].
Zyablov and Pinsker showed that

c

c

For an inﬁnite family of codes C and a family of integer-valued
functions F, the list decoding radius of C w.r.t F, also denoted
Rad(C, F) by abuse of notation, is deﬁned as

U const(R) = U poly(R) = H −1(1 − R).

Here H(·) is the binary entropy function and H −1(·) is its
inverse. Speciﬁcally,

Rad(C, F) = sup
(cid:96)∈F

Rad(C, (cid:96))

H(x) = −x lg x − (1 − x) lg(1 − x)

It is interesting to study the list decoding radius of inﬁnite
families of codes as a function of their distance and rate, when
the list size is either bounded by a constant or a polynomial
in the length of the code. Within this scope the broad nature
of the two main questions are: (1) Do there exist codes of
large rate with large list decoding radius for a ﬁxed function
(cid:96)? and (2) Do there exist codes of large distance with small

where lg x denotes the logarithm of x to base 2. Further, for
0 ≤ y ≤ 1, H −1(y) denotes the unique z in the range 0 ≤
z ≤ 1/2 such that H(z) = y.

The behavior of the upper bound on list decoding radius for
lists of size c, for speciﬁc constants c, however, was not known
completely. This quantity has been investigated signiﬁcantly in
[25], [3], [4], [8], [23], [5] and below we attempt to describe



<!-- pdf-page: 3 -->
COMBINATORIAL BOUNDS FOR LIST DECODING

3

their results and how it motivates our study. We start by noting
that U const
(R) is monotonic in c, and is thus always at least
c
H −1(1 − R)/2 which is the Gilbert-Varshamov bound. The
results of Zyablov and Pinsker [25], stated in our notation,
showed that

U const
c

(R) ≥ H −1(cid:16)

1 −

1
lg(c + 1)

(cid:17)

,

− R

(1)

(this result implies the above-mentioned result U const(R) =
H −1(1−R)). The dependence on c above is weaker than what
what one can hope for and so the question merited further
study. Blinovsky [3] (see also [4]) initiated a systematic study
of this quantity for speciﬁc choices of c. His focus however
was on small values of c and the lower bounds in his result
were obtained using non-linear codes. In more recent work [5]
shows how the techniques from his prior work may be used to
get lower bounds on U const
(R) for linear codes as well. Other
researchers to focus on U const
(R) for small c include Wei and
Feng [23]. The results of [3], [4], [5], [23] have a complex
dependence on c and so it is hard to extract the asymptotic
behavior of U const
(R) as a function of c. The only other result
with a nice asymptotic relationship between U const
(R) and R
and c is that of Elias [8] who shows:

c

c

c

c

U const
c

(R) ≥

(cid:114)

1 −

1 −

(cid:16)

1
2

2(c − 1)
c

H −1(1 − R)

(cid:17)

.

(2)

c

The two results with analytic forms, speciﬁcally (1) and (2),
are incomparable to one another. Note that we are interested
in relating three parameters: the rate R, the list-size c, and
the list-decoding radius U const
(R). The bound (2) has a
better dependence on the list-size, but a weaker dependence
on the rate than the bound (1). A setting which brings this
incomparability out very well and also motivates our result
(Theorem 5 below) is the following. Consider binary linear
codes which have a list-of-c decoding radius (1/2−ε) for some
constant c (that may depend on ε). The bound (1) guarantees
the existence of such codes of rate Ω(ε2) with a list size
c = 2O(ε−2). While the rate is good (in fact, optimal up to
constant factors), the list size is very high. On the other hand,
the bound (2) guarantees the existence of such codes of rate
Ω(ε4) with a list size c = O(1/ε2). Here we strengthen the
bounds and show the following result which, for the case for
a list decoding radius of (1/2 − ε), combines the optimal rate
Ω(ε2) with a list size of O(1/ε2). In particular, our result
answers the main open question posed by Elias [8] on whether
the bound (1), speciﬁcally its dependence on the list size c,
can be improved.

c

Theorem 5: For each ﬁxed integer c ≥ 1, and rate 0 < R <
(cid:1).

(R) ≥ H −1(cid:0)1 − R − 1

1, U const
c

1) Upper bounds on U const

To see why this is the right form for the bound U const
(R),
we survey some of the known upper bounds on this quantity.
the above results
(including ours from Theorem 5) provide lower bounds on
U const
(·) (except for the simple upper bound U const
(R) ≤
c
U poly(R) ≤ H −1(1 − R)). Blinovsky [3] also gave non-trivial
upper bounds on U const
(·) for ﬁxed constants c. Speciﬁcally,

(R): All

c

c

c

c

he obtains the following result:

(cid:19)

(cid:18)2c(cid:48)
c(cid:48)

U const
c

(R) ≤ λ−

c(cid:48) + 2
c(cid:48) + 1

(λ(1 − λ))c(cid:48)+1
(c(cid:48) + 2) − 2(2c(cid:48) + 1)λ(1 − λ)
(3)
where c(cid:48) = (cid:100)c/2(cid:101) and λ = H −1(1 − R). (For the special
case of c = 2, the exact upper bound was later improved in
[2].) The above bound applies to non-linear codes as well.
While this form of the result is hard to parse, it does imply
the following theorem:

,

Theorem 6: [Follows from [3]] For every c ≥ 1 and 0 <

R < 1, we have U const

c

(R) < H −1(1 − R).

A careful interpretation of the bound (3) above gives a hint
that Theorem 5 has the right behavior as a function of c. To get
this perspective, let us again focus on the case of a family of
binary codes C with Rad(C, (cid:96)) ≥ (1/2 − ε) for some constant
ε > 0 and where (cid:96) is the constant function (cid:96)(n) = c ∀n. Then
Theorem 5 tells us that such code families with rate Ω(ε2)
exist for a list size of c = O(ε−2). On the other hand, the
bound (3) implies that in order to have rate(C) > 0, we must
have c = Ω(ε−2). Indeed if we want Rad(C, c) ≥ 1/2 − ε,
then Equation (3) implies λ ≥ (1/2 − ε) and thus λ(1 − λ) ≥
1/4 − ε2. Therefore the second term in the right hand side of
Equation (3) is at least

Ω

(cid:16) (1 − 4ε2)c(cid:48)+1
c(cid:48)(2 + 4c(cid:48)ε2)

√

(cid:17)

using Stirling’s approximation (cid:0)2c(cid:48)
c(cid:48) ). On the
c(cid:48)
other hand, this term must be at most O(ε), since we want
(R) ≥ 1/2 − ε. Together these facts imply that c(cid:48) =
U const
c
Ω(ε−2), as desired.

(cid:1) = Θ( 4c(cid:48)

√

In this sense, the result of Theorem 5 is (nearly) the best
possible, and in particular the 1/c loss term in the bound for
U const
(R) cannot be improved asymptotically (for instance,
c
it cannot be improved to 1/c1+γ for a positive γ). In fact,
since the upper bound of Equation (3) holds even for general
codes, Theorem 5 cannot be improved substantially even if
one allows general, non-linear codes.

We remark that an account of the results discussed above in
a slightly different notation which studies the rate as a function
of list decoding radius (instead of studying the list decoding
radius as a function of the rate) appears in [10, Chap. 5]. The
presentation there also gives more detailed descriptions of the
various results in the literature and their interconnections.

B. List decoding radius vs. Distance of the code

Next we move on to lower bounds on the list decoding
radius. As mentioned earlier, it makes sense to study this as
a function of the minimum distance of the code. A large
minimum distance implies a large list decoding radius by
existing combinatorial bounds (see for example [9]), and we
want to ﬁnd the smallest possible list decoding radius for a
code of (at least) a certain minimum distance. This motivates
the next deﬁnition.

Deﬁnition 7 (Lower bound on list decoding radius): For a
distance 0 ≤ δ ≤ 1, and list size (cid:96) : Z+ → Z+, the



<!-- pdf-page: 4 -->
4

GURUSWAMI, H ˚ASTAD, SUDAN, AND ZUCKERMAN

lower bound on list-of-(cid:96) decoding radius for (binary) codes
of relative distance δ, denoted L(cid:96)(δ), is deﬁned to be

L(cid:96)(δ) =

inf
C | ∆(C)≥δ

Rad(C, (cid:96)).

Note that both in the case of the upper bound function
U(cid:96) and the lower bound function L(cid:96) one could allow the
arguments, i.e., rate and distance to be functions of n, in which
case the supremum would be taken over codes C that satisfy
dim(Ci) ≥ R(ni) · ni (or in the case of the lower bound
function, we would take the inﬁmum over codes that satisfy
dist(Ci) ≥ δ(ni) · ni).

As in the case of the upper bound function, we introduce
notation to study the special cases when the list size is a
constant or grows as a polynomial.

c

c

c

Deﬁnition 8: For real distance 0 ≤ δ < 1/2 and con-
(δ) is deﬁned to be L(cid:96)(δ) where
(δ)
(δ) is deﬁned to be supc1 L(cid:96)c1
(resp.
(δ)}

stant c, the quantity Lconst
(cid:96)(n) = c. The quantity Lpoly
where (cid:96)c1(n) = c1nc. The quantity Lconst(δ)
Lpoly(δ)) will denote the quantity lim supc→∞{Lconst
c
(resp. lim supc→∞{Lpoly
(δ)}).

Note that we restrict δ < 1/2 since binary codes with
relative distance δ ≥ 1/2 have at most a linear number of
codewords and are thus not very interesting. It is clear that
L1(δ) = δ/2. It is also easy to see that Lpoly(δ) ≤ δ (since
there exist codes of relative distance δ with super-polynomially
many codewords in ball of radius close to the minimum
distance.) Thus all lower bounds of interest lie in the range
[δ/2, δ]. The exact values are, however, mostly unknown. The
main motivation for our work is the following conjecture.

Conjecture 9: For every 0 < δ < 1/2, Lconst(δ) =

Lpoly(δ) = 1

2 · (cid:0)1 −

√

1 − 2δ(cid:1).

Evidence in support of the conjecture comes piecemeal.

Firstly, it is known that

and

Lpoly(δ) ≥ Lpoly

1

(δ) ≥

√

(cid:16)

·

1 −

1 − 2δ

(cid:17)

1
2

Lconst
c

(δ) ≥

1
2

(cid:16)

(cid:17)
1 − (cid:112)1 − 2δ + 2δ/c

·

(see, for example, [9], [14] for a proof of these facts). Upper
bounds on Lpoly and Lconst are not as well studied. Justesen
and Høholdt [16] demonstrate some MDS code families C of
1 − δ) for every constant c
distance δ with Rad(C, c) ≤ (1−
for certain values of δ, but this does not apply for codes over
any ﬁxed size alphabet, and in particular for binary codes.

√

The quantity Lpoly(δ) is even less well understood. When
δ is either very large (of the form 1/2 − o(1)) or very small
(of the form o(1)), there is some evidence conﬁrming this
bound. In particular, Dumer et al. [6] construct a family of
linear codes C, for any ε > 0, for which δ(n) = nε−1 and
Lpoly(δ) ≤ δ/(2 − ε) which matches the conjecture above
reasonably closely. We give a simple probabilistic argument
to show the following:

Theorem 10: For every ε > 0, there exists an inﬁnite family
of binary codes C and a function (cid:96) : Z+ → Z+ that grows
faster than any polynomial such that every member of C ∈ C
with block length n satisﬁes

(n/2 − ∆(C))
(n/2 − radius(C, (cid:96)(n)))

≤ 3ε.

This seems to show that the tangent of the curve Lpoly(δ)
has inﬁnite slope as δ → 1/2, which is consistent with
the conjecture above (and thus mild evidence in favor of
the conjecture). One additional reason for believing in the
conjecture is that if the deﬁnition of codes is extended to allow
non-linear codes, then indeed it is known that the conjecture
is true (see for example [9]). All this evidence adds support
to the conjecture, however remains far from proving it. In fact
until this paper it was not even known if Lpoly
(δ) < δ. The
following theorem resolves this question.

c

Theorem 11: For every integer c ≥ 1 and every δ, 0 < δ <

c

1/2, we have Lpoly
(δ) < δ.
Further, for the case δ = 1
2 · (1 − o(1)), we actually get close
to proving the above conjecture. This is done in the theorem
below which informally states that if

then

δ(n) =

1
2

(cid:0)1 − Θ((log n)ε−1)(cid:1),

Lpoly(δ) ≤

1
2

[1 − (1 − 2δ)1/2+ε],

for arbitrarily small ε. (Of course, the above does not make
sense formally since Lpoly(δ) was deﬁned as a limit of a series
and not a function of n. The following theorem makes the
assertion formally, in slightly more cumbersome detail.) The
theorem below follows from Lemma 14 which is stated and
proved in Section III-C.

Theorem 12: For every ε, 0 < ε < 1/2, for some δ :
(cid:0)1 − Θ((log n)ε−1)(cid:1) and some
Z+ → Z+ satisfying δ(n) = 1
2
superpolynomial function (cid:96) : Z+ → Z+, there exists an inﬁnite
family of codes C such that for every C ∈ C of block length n,
the relative minimum distance of C is at least δ(n) and the list
of (cid:96)(n) decoding radius of C is at most 1
2 [1 − (1 − 2δ)1/2+ε].
In a recent result, Guruswami [11] has made signiﬁcant
progress towards resolving Conjecture 9 — he resolves this
conjecture assuming a well-known number-theoretic conjec-
ture. We discuss this result further in Section VI.

Remark: For codes over an alphabet of size q for large enough
q, it turns out that Lpoly(q, δ) < δ for certain values of δ can
be easily deduced from existing results on codes that beat
the Gilbert-Varshamov bound (here Lpoly(q, δ) denotes the
quantity analogous to Lpoly(δ) for the case of q-ary codes).
Indeed, it is easy to show that for any code that lies above the
GV bound, the expected number of codewords at a Hamming
distance of at most d from a random received word, where
d is the minimum distance of the code, is exponential. Since
q-ary codes that beat the GV bound are known for all square
prime powers q ≥ 49 (speciﬁcally certain algebraic-geometric
codes achieve this [21]), it follows that for certain q ≥ 49 and
certain values of δ, we indeed have Lpoly(q, δ) < δ. However,
our focus is on binary codes, and since the GV bound is the
best current asymptotic trade-off between rate and distance
known for binary codes, the above approach does not give
anything for binary codes.

C. Organization of the Paper

We study the lower bound functions Lpoly(δ) and Lpoly
(δ)
in Section III and prove Theorems 10, 11, and 12. In Sec-

c



<!-- pdf-page: 5 -->
COMBINATORIAL BOUNDS FOR LIST DECODING

5

tion IV, we study the function U const
(R) and prove Theo-
rem 5. We then prove an adaptation of Theorem 5 (Lemma 22)
in Section V, and then use it to construct binary linear codes
with very high (algorithmic) list decodability.

c

III. LIST DECODING RADIUS AND MINIMUM DISTANCE
We now prove upper bounds on the function Lpoly(δ)
claimed in Theorems 11 and 12. We will ﬁrst prove Theo-
rem 12 which shows that when δ = 1
2 ·(1−o(1)), one “almost”
has a proof of Conjecture 9. A modiﬁcation of this proof will
also yield the proof of Theorem 11. We ﬁrst review the basic
deﬁnitions and concepts from (Discrete) Fourier analysis that
will be used in some of our proofs.

A. Fourier analysis and Group characters

For this section, it will be convenient to represent Boolean
values by {1, −1} with 1 standing for FALSE and −1 for
TRUE. This has the nice feature that XOR just becomes multi-
plication. Thus a binary code of blocklength m will be a subset
of {1, −1}m. There are 2t functions χα : {0, 1}t → {1, −1}
on t-variables, one for each α ∈ {0, 1}t. The function χα
P αixi. Fixing some
is deﬁned by χα(x) = (−1)α·x = (−1)
representation of the ﬁeld GF(2t) as elements of {0, 1}t, the
functions χα are the additive characters of the ﬁeld GF(2t),
and can also be indexed by elements α ∈ GF(2t). We will do
so in the rest of the paper. We also have, for each y ∈ GF(2t),
(cid:80)
α χα(y) equals 0 if y (cid:54)= 0 and 2t if y = 0, where the
summation is over all α ∈ GF(2t).

We can deﬁne an inner product (cid:104)f, g(cid:105) for functions f, g :

GF(2t) → R as

(cid:104)f, g(cid:105) = 2−t (cid:88)

f (x)g(x).

x

We call this inner product the normalized inner product, in
contrast to the unnormalized inner product (cid:80)
x f (x)g(x). The
functions χα form an orthonormal basis for the space of real-
valued functions on GF(2t) with respect to the normalized
inner product. Thus every real-valued function on GF(2t), and
in particular every Boolean function f : GF(2t) → {1, −1}
can be written in terms of the χα’s as:

f (x) =

(cid:88)

ˆfαχα(x) .

α∈GF(2t)

(4)

The coefﬁcient fα is called the Fourier coefﬁcient of f with
respect to α and satisﬁes

ˆfα = (cid:104)f, χα(cid:105) = 2−t (cid:88)

f (x)χα(x).

x

If we deﬁne the distance between functions f, g as

∆(f, g) = Pr
x

(cid:2)f (x) (cid:54)= g(x)(cid:3),

then

ˆfα = 1 − 2∆(f, χα).
The Fourier coefﬁcients of a Boolean function also satisfy
Plancherel’s identity (cid:80)
ˆf 2
α = 1.
α
Hadamard code: For any integer t,
the Hadamard code
Hadt of dimension t maps t bits (or equivalently elements
of GF(2t)) into {1, −1}2t
as follows: For any x ∈ GF(2t),
Hadt(x) = (cid:104)χα(x)(cid:105)α∈GF(2t).

B. Idea behind the Construction

Since our aim is to prove lower bounds on the list de-
coding radius we must construct codes with large minimum
distance with a large number of codewords in a ball of
desired radius. The speciﬁc codes we construct are obtained
by concatenating an outer extended Reed-Solomon code over
a ﬁnite ﬁeld F = GF(2t) with the Hadamard code Hadt
of blocklength 2t and dimension t. Thus the messages of
this code will be degree (cid:96) polynomials over GF(2t) for
some (cid:96), and such a polynomial P is mapped into the code-
word (cid:104)Hadt(P (z1)), . . . , Hadt(P (z2t))(cid:105) where z1, z2, . . . , z2t
is some enumeration of the elements in GF(2t).

Let n = 2t. It is easy to see that this code has blocklength
(cid:1)22t. If (cid:96) = (1−2δ)n, then
(cid:0)1− (cid:96)
22t and minimum distance 1
2
the relative minimum distance is δ, and for future reference
we denote this code by RS-HADt(δ).

n

To construct the received word (which will be the center
of the Hamming ball with a lot of codewords), consider the
following. Suppose we could pick an appropriate subset S
of GF(2t) and construct a Boolean function f : GF(2t) →
{1, −1} that has large Fourier coefﬁcient ˆfα with respect to
α for α ∈ S. Let v ∈ {1, −1}2t
be the 2t-dimensional vector
consisting of the values of f on GF(2t). The word v|F |, i.e.,
v repeated |F | times will be the “received word” (the center
of the Hamming ball which we want to show has several
codewords). Since f has large Fourier support on S, v|F | will
have good agreement with all codewords that correspond to
messages (polynomials) P that satisfy P (zi) ∈ S for many
ﬁeld elements zi. By picking for the set S a multiplicative
subgroup of GF(2t) of suitable size, we can ensure that there
are several such polynomials, and hence several codewords in
the concatenated code with good agreement with v|F |.

The main technical component of our construction and
analysis is the following Theorem which asserts the existence
of Boolean functions f with large support on subgroups
S of GF(2t). We will defer the proof of the theorem to
Section III-E, and ﬁrst use it to prove Theorems 12 and 11.

Theorem 13: There exist inﬁnitely many integers s with the
following property: For inﬁnitely many integers t, there exists
a multiplicative subgroup S of GF(2t) of size s such that the
following holds: For every β (cid:54)= 0 in GF(2t) there exists a
function f : GF(2t) → {1, −1} with
(cid:114) s
3

ˆfα ≥

(cid:88)

.

α∈β·S

Here β · S denotes the coset {βx : x ∈ S} of S.
Remarks: Our proof of the above theorem in fact gives the
following additional features which we make use of in our
applications of the theorem.

1) The integers s exists with good density; in particular for
any integer k ≥ 4, there exists an s, with k ≤ s < 3k,
that satisﬁes the requirements of Theorem 13.

2) We can also add the condition that there exist inﬁnitely
many t including one that lies in the range s/2 ≤ t ≤ s,
and the theorem still holds.

For any subset S ⊆ GF(2t), one can show that (cid:80)

ˆfα
is at most |S|1/2 using Plancherel’s identity and Cauchy-

α∈S



<!-- pdf-page: 6 -->
6

GURUSWAMI, H ˚ASTAD, SUDAN, AND ZUCKERMAN

Schwartz, and Theorem 13 shows that we can achieve a
sum of Ω(|S|1/2) inﬁnitely often for appropriate multiplicative
subgroups S.

i, 1 ≤ i ≤ n, the expected value of ˆfbi satisﬁes
p
1
s
n

(n − 1)
ns

ˆf0 ≥

ˆfα +

ˆfα −

(cid:88)

(cid:88)

1
n

1
n

≥

α∈S

C. Proof of Theorem 12

≥

1
√
3s

−

α∈S
2
n

,

(cid:88)

α∈S

ˆfα −

2
n

(6)

We now employ Theorem 13 to prove Theorem 12. We
in fact prove the following Lemma which clearly establishes
Theorem 12.

Lemma 14: For every ε, 0 < ε < 1/2,

there exist
inﬁnitely many integers t such that
the following holds:
Let N = 22t. There exists a vector r ∈ {1, −1}N and
(cid:0)1−Θ((log N )ε−1)(cid:1), such that the number of codewords
δ = 1
2
C of the code RS-HADt(δ) with

where the last inequality follows from Equation (5). Let X
denote the random variable which is the unnormalized inner
product of the codeword (encoding the message R(x)p for a
random polynomial R of degree at most m) with the received
vector r = vn. By linearity of expectation and using (6), we
have

E[X] =

n
(cid:88)

i=1

E[n ˆfbi] ≥

√

− 2

N ≥

N
√
3s

1.1N
√
4s

(7)

∆(r, C) ≤

N
2

(cid:0)1 − (1 − 2δ)1/2+ε(cid:1)

is at least N Ω(logε N ).

Proof: Let s, t be any pair of integers guaranteed by
Theorem 13 with t ≤ s ≤ 2t (we are using one of the
remarks following Theorem 13 here). Let S be a multiplicative
subgroup of GF(2t) of size s and f : GF(2t) → {1, −1} a
function such that

for large enough N (since s = Θ(log N )). Now, for each i,
1 ≤ i ≤ n,

E[ ˆf 2
bi

] ≤

p
n

(cid:88)

ˆf 2
α ≤

1
s

.

α∈S∪{0}

Since the bi’s are evaluations of the polynomial R(x)p at the n
ﬁeld elements for a random R, they are pairwise independent.
Thus the variance of the random variable X is bounded from
above by

ˆfα ≥

(cid:88)

α∈S

(cid:114) s
3

.

(5)

E[X 2] =

n
(cid:88)

i=1

E[(n ˆfbi)2] ≤

N 3/2
s

.

(8)

Let n = 2t, N = 22t and p = (n − 1)/s. Note that s =
Θ(log N ) since we have t ≤ s ≤ 2t. Then S ∪ {0} consists of
all elements in GF(2t) which are p’th powers of some element
of GF(2t).

We ﬁrst ﬁx the “received word” r. Let v ∈ {1, −1}n be the
vector (cid:104)f (x)(cid:105)x∈GF(2t) of all values of f . Then r = vn, i.e.
the vector v repeated n = 2t times, one for each position of
the outer Reed-Solomon code.

Let δ be a parameter to be speciﬁed later and (cid:96) = (1−2δ)n.
Consider the binary code C = RS-HADt(δ) obtained by
concatenating an extended Reed-Solomon code of dimension
(cid:96) + 1 = (1 − 2δ)n + 1 over GF(2t) with Hadt. C has
blocklength N and minimum distance δN . We now want to
demonstrate several codewords in C that are “close” to r.
We prove this picking codewords in C at random from some
distribution and showing that the agreement with r is “large”
with good probability.

Let m = (cid:98)(cid:96)/p(cid:99) and consider a message (degree (cid:96) polyno-
mial over GF(2t)) P of C which is of the form P (x) = R(x)p
for a random polynomial R of degree at most m over GF(2t).
The Reed-Solomon encoding (b1, b2, . . . , bn) of P satisﬁes
bi ∈ S ∪ {0} for every i, 1 ≤ i ≤ n. It is easy to see that
for each i and each a ∈ S, we have Pr[bi = a] = p/n, and
Pr[bi = 0] = 1/n. Moreover, the choices of bi are pairwise
independent.

Now, by deﬁnition of the Fourier coefﬁcient, for each i, the
Hadamard codeword Hadt(bi) and the vector v we constructed
above have an unnormalized inner product equal to n · ˆfbi (or
equivalently, agree on a fraction
of positions). For any

1+ ˆfbi
2

We now use Chebyshev’s inequality to prove that the inner
product X is greater than N/
4s with probability at least
1/2. Indeed

√

Pr[X ≤

N
√
4s

] ≤ Pr[X − E[X] ≤ −

N
√

10

]

4s

≤ Pr[|X − E[X]| ≥

N
√

10

]

4s

≤

<

400s E[X 2]
N 2

≤

400
√
N

1
2

(for large enough N ),

where we have used the lower bound on E[X] from Equation
(7) and the upper bound on E[X 2] from Equation (8).

Hence the codewords encoding at

2 · nm of the
polynomials of the form R(x)p where R is a polynomial of
degree at most m, differ from r in at most ( 1
)N
codeword positions.

2 − 1

least 1

4s

√

2

We now pick parameters (namely m, δ) suitably to conclude
the result. Recall that s = Θ(log N ). Picking m = sε, we have

(1 − 2δ) =

(cid:96)
n

= Θ(

(cid:96)
ps

) = Θ(

m
s

) = Θ(cid:0)(log N )ε−1(cid:1) .

Thus the minimum distance δ (for our choice of m) satisﬁes
δ = 1
2

(cid:0)1 − Θ((log N )ε−1)(cid:1).

Also we have

(1 − 2δ)1/2+ε (cid:39) s(ε−1)(1/2+ε) ≤ (4s)−1/2

for large enough N (since ε < 1/2). Thus there exist
Ω(nm) = N Ω(logε N ) codewords of RS-HADt(δ) all of which



<!-- pdf-page: 7 -->
COMBINATORIAL BOUNDS FOR LIST DECODING

7

lie in a Hamming ball of radius N
2 (1 − (1 − 2δ)1/2+ε). Since
Theorem 13 implies that there are inﬁnitely many choices for
t that we could use, we also have inﬁnitely many choices of
blocklengths N available for the above construction, and the
proof is thus complete.

D. Proof of Theorem 11

c

We now turn to obtaining upper bounds on Lpoly

(δ) for a
ﬁxed constant c. One way to achieve this would be to pick
m (cid:39) 2c in the above proof, and then pick s (cid:39) 2c/(1 − 2δ)
(cid:17)1/2(cid:1).
and this would give (roughly) Lpoly
However this upper bound is better than δ only for δ large
2 − 1
enough, speciﬁcally for δ > 1
12c . We thus have to modify
the construction of Lemma 14 in order to prove Theorem 11.
We prove the following lemma which will
in turn imply
Theorem 11. Since our goal was only to establish Theorem 11,
we have not attempted to optimize the exact bounds in the
lemma below.

(cid:16) 1−2δ
6c

(δ) ≤ 1
2

(cid:0)1 −

c

Lemma 15: For every c and every δ, we have
(cid:110)
(δ + α)(cid:0)1 − (

(δ) ≤ min

Lpoly
c

0≤α≤1/2−δ

α
12(2c + 1)

)1/2(cid:1)(cid:111)
.

Proof: To prove the claimed upper bound on Lpoly
(δ),
we will closely follow the construction from the proof of
Lemma 14. Let 0 < δ < 1/2, 0 ≤ α ≤ (1/2 − δ), and c
be given. Deﬁne α(cid:48) = 2α and pick an integer s,

c

2(2c + 1)/α(cid:48) ≤ s < 6(2c + 1)/α(cid:48)

such that the conditions of Theorem 13 are met (we know
such an s exists by the remarks following Theorem 13). Let
t be any integer for which a subgroup S of GF(2t) exists
as guaranteed by Theorem 13 (there are once again inﬁnitely
many such values of t).

Now we describe the actual construction for a particular
δ, α(cid:48), s, t. Let n = 2t, N = n2 and p = (n − 1)/s. As in the
proof of Lemma 14, the code will again be RS-HADt(δ) (the
messages of the code will thus be polynomials over GF(2t) of
degree at most (cid:96) = (1−2δ)n and the code has blocklength N ).
The only change will be in the construction of the received
word r. Now, instead of using as received word the vector vn
(recall that v was the table of values of the Boolean function
f with large Fourier support on a multiplicative subgroup S of
GF(2t)), we will set the ﬁrst B = ((cid:96) − α(cid:48)n) = (1 − 2δ − α(cid:48))n
blocks of r to be all zeroes. The last (n − B) blocks of r will
be vectors v(i), B < i ≤ n, which will be speciﬁed shortly.

Let m = 2c + 1. We will consider the messages corre-
sponding to polynomials of the form P (x) = (x − z1) · · · (x −
zB)R(x)p where z1, . . . , zB of GF(2t) are the B elements of
GF(n) that correspond to the ﬁrst B positions of the Reed-
Solomon code and R is a random degree m polynomial. Note
that

degree(P ) = B + pm = (cid:96) − α(cid:48)n +

n − 1
s

(2c + 1) ≤ (cid:96)

since we picked s ≥ 2(2c + 1)/α(cid:48). By the choice of P , the
codeword (b1, b2, . . . , bn) corresponding to P (which we abuse
notation and also denote by P ) will agree with r in the ﬁrst nB
positions (as both begin with a string of nB zeroes). At each

of the remaining (n − B) blocks, we will have bi ∈ Si ∪ {0}
where Si is a coset S (recall that S is s-element multiplicative
subgroup of GF(2t) consisting of all the p’th powers). Specif-
ically Si = βiS where βi = (zi − z1) · · · (zi − zB). Now, for
B < i ≤ n, deﬁne v(i) ∈ {1, −1}2t
to the value of the
functions f (i) where f (i) : GF(2t) → {1, −1} is a function
with (cid:80)

α ≥ (cid:112)s/3 as guaranteed by Theorem 13.
ˆf (i)

Using arguments similar to those in the proof of Lemma 14,
one can show that with probability at least 1/2, the codeword
corresponding to the polynomial P differs from r in at most
(cid:1)n positions. Thus there are at least
E = (n − B)(cid:0) 1
1
2 nm codewords of RS-HADt(δ) that lie within a ball of radius
E around r. Since N = n2, m = 2c+1 and s < 6(2c+1)/α(cid:48),
we have ω(N c) codewords in a Hamming ball of radius

2 − 1

4s

√

2

α∈Si

N (δ + α(cid:48)/2)(cid:0)1 −

(cid:115)

α(cid:48)
24(2c + 1)

(cid:1),

and recalling that α(cid:48) = 2α, the claimed result follows. To
conclude, we just reiterate that by Theorem 13, for the picked
value of s, there are inﬁnitely many values of t (and therefore
the blocklength N ) for which the code RS-HADt(δ) has the
claimed properties. Thus we get an inﬁnite family of codes
with the requisite property, and the proof is complete.

We now turn to the proof of of Theorem 11.

Proof: (of Theorem 11) We want to prove Lpoly
1

(δ) < δ.
48(2c+1) , setting α = 1/2 − δ gives

Note that when δ > 1

c

2 −
1
2

Lpoly
c

(δ) ≤

(cid:0)1 − (

1 − 2δ
24(2c + 1)

)1/2(cid:1) < δ .

When δ ≤ 1
valid setting since it is less than 1/2 − δ), we have

48(2c+1) , setting α = δ2/48(2c + 1) (this is a

2 −

1

Lpoly
c

(δ) ≤ δ + α − δ(

α
12(2c + 1)

)1/2 < δ.

Thus we have Lpoly

c

(δ) < δ in either case.

E. Proof of Theorem 13

The proof proceeds in several steps. We ﬁrst prove the
following Lemma which shows that if a subset S of GF(2t)
satisﬁes a certain property, then there exists a Boolean function
f : GF(2t) → {1, −1} such that (cid:80) ˆfα is large when summed
over α ∈ S.

Lemma 16: For any integer t, let S be an arbitrary subset
of elements of the ﬁeld GF(2t) such that no four (distinct)
elements of S sum up to 0. Then there exists a function f :
GF(2t) → {1, −1} with (cid:80)

ˆfα ≥
Proof: For any set S, the following simple claim identiﬁes

(cid:113) |S|
3 .

α∈S

the “best” function f for our purposes.
Claim: Deﬁne the function g : GF(2t) → R by g(x) =
(cid:80)
α∈S χα(x). Then the maximum value of (cid:80)
ˆfα achieved
by a boolean function f is exactly 2−t · (cid:80)

α∈S
x |g(x)|.

Proof: Indeed
ˆfα =

2t (cid:88)

(cid:88)

f (x)χα(x) =

α∈S

x,α∈S
(cid:88)

f (x)g(x) ≤

=

x

|g(x)|

(cid:88)

x

f (x)

(cid:88)

x

(cid:88)

α∈S

χα(x)



<!-- pdf-page: 8 -->
8

GURUSWAMI, H ˚ASTAD, SUDAN, AND ZUCKERMAN

with equality holding when f is deﬁned as f (x) = sign(g(x)).

Thus the above claim “removes” the issue of searching for an
f by presenting the “best” choice of f , and one only needs to
analyze the behavior of the above character sum function g,
and speciﬁcally prove a lower bound on (cid:80)
To get a lower bound on (cid:80)
inequality which states that

x |g(x)|, we employ H¨older’s

x |g(x)|.1

(cid:88)

x

|h1(x)h2(x)| ≤

(cid:32)

(cid:88)

x

(cid:33)1/p (cid:32)

(cid:88)

(cid:33)1/q

|h2(x)|q

,

|h1(x)|p

x

for every positive p and q that satisfy 1
q = 1. Applying
this with h1(x) = |g(x)|2/3, h2(x) = |g(x)|4/3, p = 3/2 and
q = 3 gives

p + 1

(cid:32)

(cid:88)

x

(cid:33)2/3 (cid:32)

(cid:88)

(cid:33)1/3

g(x)4

(cid:88)

≥

g2(x).

(9)

|g(x)|

x

x

This inequality is also a consequence of log convexity of the
power means (see Hardy, Littlewood, Polya [15]; Theorem
18).

Now (cid:80)

x g2(x) = (cid:80)

x χα1+α2(x) which equals
|S| · 2t (the inner sum equals 2t whenever α1 = α2 and 0
otherwise, and there are |S| pairs (α1, α2) with α1 = α2).
Note that this also follows from Plancherel’s identity.

α1,α2

(cid:80)

Similarly
(cid:88)

g4(x) =

(cid:88)

(cid:88)

χα1+α2+α3+α4(x)

x

α1,α2,α3,α4∈S

x

equals N4,S · 2t where N4,S is the number of 4-tuples in
(α1, α2, α3, α4) ∈ S4 that sum up to 0. But the property
satisﬁed by S, no four distinct elements of S sum up to 0,
and hence the only such 4-tuples which sum up to 0 are those
which have two of the α’s equal. There are at most 3|S|2 such
4-tuples (α1, α2, α3, α4) with two of the α’s equal. Hence
N4,S ≤ 3|S|2, and hence (cid:80)
x g4(x) ≤ 3|S|22t. Plugging this
into Equation (9) we get, when f (x) = sign(g(x)),

ˆfα =

(cid:88)

α∈S

1
2t

(cid:88)

x

|g(x)| ≥

(cid:115)

|S|3
3|S|2 =

(cid:114)

|S|
3

.

Given the statement of Lemma 16, we next turn to con-
structing subgroups of GF(2t) with the property that no four
(or fewer) distinct elements of the subgroup sum up to 0.
To construct such subgroups, we make use of the following
simple lemma about the existence of certain kinds of cyclic
codes. For completeness sake, we quickly review the necessary
facts about cyclic codes. A binary cyclic code of blocklength
n is an ideal in the ring

R = F2[X]/(X n − 1).

1It can be shown that the representation of the ﬁeld (as a vector space of
dimension t over GF(2)) does not affect the value distribution of g, and thus
we can pick an arbitrary representation of the ﬁeld, and the result will be the
same.

It is characterized by its generator polynomial g(X) where
g(X)|(X n − 1). The codewords correspond to polynomials in
R that are multiples of g(X) (the n coefﬁcients of each such
polynomial form the codeword symbols). A (binary) cyclic
code is said to be maximal if its generator polynomial is
irreducible over GF(2). A BCH code is a special kind of
cyclic code whose generator polynomial is deﬁned to be the
minimal polynomial that has roots β, β2, . . . , βd−1. Here β
is a primitive n’th root of unity over GF(2), and d is the
“designed distance” of the code.

Lemma 17: Let k ≥ 4 be any integer. Then there exists an
integer s in the interval [k, 3k) such that a maximal binary
BCH code of blocklength s and minimum distance at least 5
exists.

Proof: Let s be an integer of the form 2f − 3 in the
range [k, 3k) (such an integer clearly exists). Let β be the
primitive s’th root of unity over GF(2) and let h be the
minimal polynomial of β over GF(2). Clearly, h(β2i
) = 0
for all i ≥ 1, and hence h(β2) = h(β4) = 0. Since β2f
= β3,
we also have h(β3) = 0. Now the consider the cyclic code
Ch of blocklength s with generator polynomial h. It is clearly
maximal since h, being the minimal polynomial of β,
is
irreducible over GF(2). Also h(βi) = 0 for i = 1, 2, 3, 4.
Using the BCH bound on designed distance (see, for example,
Section 6.6 of [22]), this implies that the minimum distance
of Ch is at least 5, as desired.

Lemma 18: Let k ≥ 4 be any integer. Then there exists an
integer s in the interval [k, 3k) with the following property.
For inﬁnitely many integers t, including some integer which
lies in the range s/2 ≤ t ≤ s, there exists a multiplicative
subgroup S of GF(2t) of size s such that no four or fewer
distinct elements of S sum up to 0 (in GF(2t)). Moreover, for
any non-zero β ∈ GF(2t) this property holds for the coset βS
as well.

Proof: Given k, let k ≤ s < 3k be an integer for
which there exists a binary BCH code C of blocklength s
as guaranteed by Lemma 17 exists. Such a code is generated
by an irreducible polynomial h where h(x)|(xs − 1). Let
t = degree(h); clearly t ≤ s. Consider the ﬁnite ﬁeld
F = F2[X]/(h(X)) which is isomorphic to GF(2t), and
consider the subgroup S of size s of F comprising of
{1, X, X 2, X 3, . . . , X s−1}. The fact that C has distance at
least 5 implies that (cid:80)
i∈G X i is not divisible by h(X) for any
set G of size at most 4, and thus no four or fewer distinct
elements of S sum up to 0 in the ﬁeld F . This gives us one
value of t ≤ s for which the conditions of Lemma 18 are met,
but it is easy to see that any multiple of t also works, since
the same S is also a (multiplicative) subgroup of GF(2kt) for
all k ≥ 1. In particular we can repeatedly double t until it
lies in the range s/2 ≤ t ≤ s (note that we had t ≤ s to
begin with). The claim about the cosets also follows easily,
since if a1 + a2 + a3 + a4 = 0 where each ai ∈ βS, then
β−1a1 + β−1a2 + β−1a3 + β−1a4 = 0 as well, and since
β−1ai ∈ S, this contradicts the property of S.

We now have all the ingredients necessary to easily deduce

Theorem 13.



<!-- pdf-page: 9 -->
COMBINATORIAL BOUNDS FOR LIST DECODING

9

Proof: (of Theorem 13) Theorem 13 now follows from
Lemma 16 and Lemma 18. Note also that the statement of
Lemma 18 implies the remarks made after the statement of
Theorem 13.

F. Proof of Theorem 10

We begin by bounding the expected number of codewords
in a random ball of an MDS code. Recall that an MDS code is
an [n, k] code whose minimum distance equals (the optimum
value of) (n − k + 1).

Lemma 19: For any MDS [n, k]q code C and a ≥ k,

(cid:19)

(cid:18)n
a

1
e

qk−a ≤ E
x

[|B(x, n − a) ∩ C|] ≤

(cid:19)

qk−a.

(cid:18)n
a

Proof: The upper bound follows from the claim that for
any set Sa of a positions, the expected number of codewords
which agree with x on Sa is at most qk−a. To show this claim,
ﬁrst ﬁx a subset Sk ⊆ Sa of k of these positions. For each
x, there is a unique codeword wx that agrees with x on Sk.
The probability that wx agrees with x on Sa therefore equals
qk−a.

The lower bound follows from a similar claim: that for any
set Sa of a positions, the probability that a codeword agrees
with x on Sa and disagrees with x outside of Sa is at least
qk−a/e. This claim is true because the probability that wx
above agrees with x on Sa and disagrees with x outside of Sa
equals qk−a(1 − 1/q)n−a. For an MDS code, n < q + k − 1,
so n − a ≤ n − k < q − 1 so (1 − 1/q)n−a > 1/e.

Corollary 20: For any constants ε, γ > 0, for large enough
(1 − nε−1) ≤ 1 − (1 − γ)nε−1/ε, where Lpoly
denotes

n, Lpoly
n
the analog of Lpoly for q-ary codes.

q

Proof: Use an MDS [n, k]q code with n = q and k = nε,

such as a Reed-Solomon code. Then

(cid:19)

(cid:18)n
a

qk−a ≥

(cid:17)a

(cid:16) n
a

nk−a =

nk
aa .

Letting a = (1 − γ)nε/ε, for large enough n we have aa ≤
n(1−γ/2)nε
, and the expected number of codewords in a ball
of radius n − a is Ω(n

), yielding the corollary.

2 nε

γ

Proof: (of Theorem 10) We show that the family of codes
C that we construct satisﬁes the property that every member
C ∈ C with block length n satisﬁes

1) The relative minimum distance of C is at

least

2) The list-of-(cid:96)(n) decoding radius of C is at most

(cid:0)1 − nε−1/2(cid:1).

1
2

1
2

(cid:0)1 − 1

3ε nε−1/2(cid:1).
This sufﬁces to prove the theorem.

√

The codes C in our family are concatenations of Reed-
Solomon codes with Hadamard codes. For such a concatenated
code C to have block length n, the RS code must have block
n, and the relative minimum distance of C is half the
length
relative minimum distance of the RS code. The theorem then
follows from Corollary 20 for (cid:96)(n) growing exponentially in
n.

IV. LIST DECODING RADIUS VS. RATE

We now prove Theorem 5.

Proof: (of Theorem 5) For each ﬁxed integer c ≥ 1 and
0 < p < 1/2, we use the probabilistic method to guarantee
the existence of a binary linear code C of blocklength n, with
at most c codewords in any ball of radius e = pn, and whose
dimension is k = (cid:98)(1 − H(p) − 1/c)n(cid:99), for all large enough
n. This clearly implies the lower bound on U const
claimed in
the statement of the Theorem.

c

The code C = Ck will be built iteratively in k steps by
randomly picking the k basis vectors in turn. Initially the code
C0 will just consist of the all-zeroes codeword b0 = 0n. The
code Ci, 1 ≤ i ≤ k, will be successively built by picking a
random (non-zero) basis vector bi that is linearly independent
of b1, . . . , bi−1, and setting Ci = span(b1, . . . , bi). Thus C =
Ck is an [n, k]2 linear code. We will now analyze the list of c
decoding radius of the codes Ci, and the goal is to prove that
the list of c decoding radius of C is at least e.

The key to analyzing the list of c decoding radius is the
following potential function SC deﬁned for a code C of
blocklength n:

SC =

1
2n

(cid:88)

n

c ·|B(x,e)∩C| .

2

(10)

x∈{0,1}n

x 2nT i

x the quantity |B(x, e)∩Ci|, so that Si = 2−n (cid:80)

For notational convenience, we denote SCi be Si. Also denote
by T i
x/c.
Let B = |B(0, e)| = |B(0, pn)|; then B ≤ 2H(p)n where
H(p) is the binary entropy function of p (see for example
Theorem (1.4.5) in [22, Chapter 1]). Clearly
S0 = 1 − B/2n + B2n/c/2n ≤ 1 + 2n(cid:0)H(p)−1+1/c(cid:1)
Now once Ci has been picked with the potential function
Si taking on some value, say ˆSi, the potential function Si+1
for Ci+1 = span(Ci ∪ {bi+1}) is a random variable depend-
ing upon the choice of bi+1. We consider the expectation
E[Si+1|Si = ˆSi] taken over the random choice of bi+1 chosen
uniformly from outside span(b1, . . . , bi).
E[Si+1] = 2−n (cid:88)

(11)

.

x

]

E[2n/c ·T i+1
E[2n/c·(cid:0)|B(x,e)∩Ci|+|B(x,e)∩(Ci+bi+1)|(cid:1)
(cid:18)

(cid:19)

]

[2n/c ·T i

x+bi+1 ]

(12)

2n/c ·T i

x E
bi+1

x

= 2−n (cid:88)

x

= 2−n (cid:88)

x

where in the second and third steps we used the fact that
if z ∈ B(x, e) ∩ Ci+1, then either z ∈ B(x, e) ∩ Ci, or
z+bi+1 ∈ B(x, e)∩Ci. To estimate the quantity (12), ﬁrst note
that if we did not have the condition that bi+1 was chosen from
outside span(b1, . . . , bi) (12) would simply equal ˆS2
i . This
follows from the fact that x and x + bi+1 are independent
and the deﬁnition of ˆSi. Now we use the simple fact that
the expectation of a positive random variable taken over bi+1
chosen randomly from outside span(b1, . . . , bi) is at most
(1 − 2i−n)−1 times the expectation taken over bi+1 chosen
uniformly at random from {0, 1}n. Hence, we get that

E[Si+1] ≤

ˆS2
i
(1 − 2i−n)

.

(13)



<!-- pdf-page: 10 -->
10

GURUSWAMI, H ˚ASTAD, SUDAN, AND ZUCKERMAN

Applying (13) repeatedly for i = 0, 1, . . . , k − 1, we conclude
that there exists an [n, k] binary linear code C with

SC = Sk ≤

S2k
0
i=0 (1 − 2i−n)2k−i

(cid:81)k−1

≤

S2k
0
(1 − 2k−n)k ≤

S2k
0
1 − k2k−n

(14)

since (1 − x)a ≥ 1 − ax for x, a ≥ 0. Combining (14) with
(11), we have

Sk ≤ (1 − k2k−n)−1(cid:0)1 + 2n(H(R)−1+1/c)(cid:1)2k

and using (1 + x)a ≤ (1 + 2ax) for ax (cid:28) 1, this gives

Sk ≤ 2(1 + 2 · 2k+(H(p)−1+1/c)n) ≤ 6,

(15)

where the last inequality follows since k = (cid:98)(1 − H(p) −
1/c)n(cid:99). By the deﬁnition of the potential Sk (10), this implies
that

2n/c·|B(x,e)∩C| ≤ 6 · 2n < 2n+3,

or

|B(x, e) ∩ C| ≤ (1 +

3
n

)c

for every x ∈ {0, 1}n. If n > 3c, this implies |B(x, e) ∩ C| <
c + 1 for every x, implying that the list of c decoding radius
of C is at least e, as desired.

Remark: One can also prove Theorem 5 with the additional
property that the relative minimum distance ∆(R) of the code
(in addition to its list decoding radius for list size c) also
satisﬁes ∆(R) ≥ H −1(1 − R − 1/c). This can be done, for
example, by conditioning the choice of the random basis vector
bi+1 in the above proof so that span(b1, b2, . . . , bi+1) does not
contain any vector of weight less than pn. It is easy to see
that with this modiﬁcation, Equation (13) becomes

E[Si+1] ≤

ˆS2
i
(1 − 2i+H(p)n−n)

.

Using exactly similar calculations as in the above proof, we
can then guarantee a code C of dimension k = (cid:98)(1 − H(p) −
1/c)n(cid:99) and minimum distance at least pn such that SC =
O(1).

V. APPLICATION TO HIGHLY LIST DECODABLE CODES

We now apply the proof technique from the previous
section to give constructions of concatenated codes that are
list decodable from very high noise and yet have good rate.
We ﬁrst describe the setting that we are interested in, which
is the same as the one that was considered in [13].

Given ε > 0, we are interested in asymptotically good
family of binary linear codes Cε that can be list decoded
efﬁciently for up to a fraction (1/2 − ε) of errors. The goal is
to give explicit (polynomial time) constructions of such code
families with a reasonable rate. Such codes have a variety
of applications some of which are discussed in [13], [20].
The best earlier result, due to [13], gives constructions with a
rate of Ω(ε6) (the construction is an algebraic-geometric code
concatenated with any inner code like the Hadamard code that

has large minimum distance). Note that if we did not care
about efﬁcient constructibility or efﬁcient list decoding, then
Theorem 5 guarantees that such code families exist with rate
Ω(ε2), and this is the best possible asymptotically.

Using the codes guaranteed by Theorem 5 as inner codes
in a concatenation scheme with outer Reed-Solomon code,
we can show that a rate of Ω(ε6) can be achieved without
relying on algebraic-geometric codes, thus “simplifying” the
construction in [13]. This does not, however, improve the
quantitative aspects of the earlier result. Instead we prove
an adaptation of Theorem 5 that guarantees the existence
of codes that have certain properties tailor-made for the
weighted list decoding algorithm for Reed-Solomon codes
from [12] to work well. Using such codes as inner codes in a
concatenation scheme with outer Reed-Solomon code, gives us
code families of rate Ω(ε4) that are efﬁciently list decodable
from a (1/2 − ε) fraction of errors. This is summarized in the
following theorem, which is the main result of this section.

Theorem 21: There exist absolute constants b, d > 0 such
that for each ﬁxed ε > 0, there exists a polynomial time
constructible code family C with the following properties:

1) rate(C) ≥ ε4
b
2) Rad(C, dε−2) ≥ 1
3) ∆(C) ≥ ( 1
4) There is a polynomial time list decoding algorithm for
C that corrects up to a fraction (1/2 − ε) of errors.

2 − ε)

2 − ε

The above theorem will follow from Theorem 24, which is
stated and proved in Section V-B.

A. An “inner code” construction

1) Existence of a good code: We now prove the existence
of codes that will serve as excellent inner codes in our later
concatenated code construction. The proof is an adaptation of
that of Theorem 5. We will then show how such a code can be
constructed in 2O(n) time (where n is the blocklength) using
an iterative greedy procedure.

Lemma 22: There exist absolute constants σ, A > 0 such
that for any ε > 0 there exists a binary linear code family C
with the following properties:

1) rate(C) = σε2
2) For every code C ∈ C and every x ∈ {0, 1}n where n

is the blocklength of C, we have

(cid:88)

(cid:0)1 − 2δ(x, c)(cid:1)2

≤ A .

(16)

c∈C
δ(x,c)≤(1/2−ε)

Proof: For every large enough n, we will prove the
existence of a binary linear code Ck of blocklength n and
dimension k ≥ σε2n which satisﬁes Condition (16) for every
x ∈ {0, 1}n.

The proof will follow very closely the proof of Theorem 5
and in particular we will again build the code Ck iteratively in
k steps by randomly picking the k basis vectors b1, b2, . . . , bk
in turn. Deﬁne Ci = span(b1, . . . , bi) for 0 ≤ i ≤ k. The key
to our proof is the following potential function WC deﬁned
for a code C of blocklength n (compare with the potential



<!-- pdf-page: 11 -->
COMBINATORIAL BOUNDS FOR LIST DECODING

11

function (10) from the proof of Theorem 5):

Therefore

WC =

1
2n

(cid:88)

n
A

2

x∈{0,1}n

P

c∈C:δ(x,c)≤(1/2−ε)(1−2δ(x,c))2

.

(17)

u ≤

(The constant A will be ﬁxed later in the proof, and we
assume that A > ln 4.) Denote the random variable WCi by
the shorthand Wi, and for x ∈ {0, 1}n, deﬁne

Ri

x =

(cid:88)

c∈Ci
δ(x,c)≤(1/2−ε)

(1 − 2δ(x, c))2 ,

(18)

so that Wi = 2−n (cid:80)

x 2 n

A ·Ri
x.

x+bi+1

Now, exactly as in the proof of Theorem 5, we have Ri+1
x =
x +Ri
Ri
, and using this it is straightforward to show that
i over the choice of bi+1 uniformly
E
bi+1
at random from {0, 1}n, and it is therefore easy to argue that

[Wi+1|Wi = ˆWi] = ˆW 2

E[Wi+1|Wi = ˆWi] ≤

ˆW 2
i
1 − 2i−n .

(19)

when the expectation is taken over a random choice of bi+1
outside span(b1, . . . , bi). Applying (19) repeatedly for i =
0, 1, . . . , k − 1, we conclude that there exists an [n, k] binary
linear code C = Ck with

−

2
ln 2

(cid:17)(cid:16) 1
2

(cid:17)2

− y

(cid:16) 4
A
(cid:17)

max
0≤y≤(1/2−ε)
(cid:16) 1
ln 4

−

ε2 ,

= −4

1
A
since A > ln 4. Combining (20), (21) and (22), it is now
easy to argue that we have WC = Wk = O(1) as long as
k < −un, which will be satisﬁed if k < 4( 1
A )ε2n. Thus
the statement of the lemma holds, for example, with A = 2
and σ = 0.85.

ln 4 − 1

(22)

Remark: Arguing exactly as in the remark following the
proof of Theorem 5, one can also add the condition ∆(C) ≥
(1/2 − ε) to the claim of Lemma 22. The proof will
then pick bi+1 randomly from among all choices such that
span(b1, b2, . . . , bi+1) ∩ B(0, ( 1

2 − ε)n) = ∅.

2) A greedy construction of the “inner” code: We now
discuss how a code guaranteed by Lemma 22 can be con-
structed in a greedy fashion. We will refer to some notation
that was used in the proof of Lemma 22. The algorithm works
as follows:

Algorithm GREEDY-INNER:

WC = Wk ≤

W 2k
0
1 − k2k−n .

(20)

Parameters: Dimension k; ε, A > 0 (where A is the absolute
constant from Lemma 22)

If we could prove, for example, that WC = O(1), then this
x ≤ A for every x ∈ {0, 1}n
would imply, using (17), that Rk
and thus C would satisfy Condition (16), as desired. To show
this, we need an estimate (upper bound) on W0, to which we
turn next.

Deﬁne A = (1/2 − ε)n. Since C0 consists of only the all-
x = (1 − 2wt(x)/n)2 if wt(x) ≤
zeroes codeword, we have R0
a and R0
x = 0 otherwise (here we use wt(x) = ∆(x, 0)
to denote the Hamming weight of x). Let us denote 2x by
exp2(x). We now have
W0 = 2−n (cid:88)

(cid:1)

exp2

R0
x

(cid:0) n
A

x∈{0,1}n

≤ 1 + 2−n

A
(cid:88)

i=0

(cid:19)

(cid:18)n
i

exp2

(cid:16)

≤ 1 + n2−n exp2
≤ 1 + n2un

max
0≤i≤A

(cid:0)1 −

(cid:0) n
A
(cid:110)
H(cid:0) i
n

(cid:1)2(cid:1)

2i
n

(cid:1)n +

4n
A

(cid:0) 1
2

−

i
n

(cid:1)2(cid:111) (cid:17)

(21)

where

u def=

max
0≤y≤(1/2−ε)

(cid:110)

H(y) − 1 +

4
A

(cid:16) 1
2

(cid:17)2(cid:111)

.

− y

ln 2 ( 1

We now claim that for every y, 0 ≤ y ≤ 1/2, we have H(y) ≤
1 − 2
2 − y)2. One way to prove this is to consider the
Taylor expansion around 1/2 of H(y), which is valid for the
range 0 ≤ y ≤ 1/2. We have H (cid:48)(1/2) = 0 and H (cid:48)(cid:48)(1/2) =
−4/ ln 2. Also it is easy to check that all odd derivatives of
H(y) at y = 1/2 are zero while the even derivatives are non-
positive. Thus

H(y) ≤ H(1/2) − H (cid:48)(cid:48)(1/2)

(1/2 − y)2
2

= 1 −

2
ln 2

(cid:0) 1
2

− y(cid:1)2

.

Output: A binary linear code C = GREEDY(k, ε) with
dimension k, blocklength n = O(k/ε2) and minimum distance
(1/2 − ε)n such that for every x ∈ {0, 1}n, Condition (16)
holds.

1) Start with b0 = 0.
2) For i = 1, 2, . . . , k:

• Let Ui = {x ∈ {0, 1}n : span(b1, b2, . . . , bi−1, x) ∩

B(0, (1/2 − ε)n) = ∅ }.

• Pick bi ∈ Ui that minimizes the potential function
x is as deﬁned in

A ·Ri

x 2 n
x , where Ri
(break ties arbitrarily)

Wi = 2−n (cid:80)
Equation (18)

3) Output C = span(b1, b2, . . . , bk).

The following result easily follows from the proof of
Lemma 22 and since each of the k iterations of the for loop
above can be implemented to run in 2O(n) time.

Lemma 23: Algorithm GREEDY-INNER constructs a code

GREEDY(k, ε) with the desired properties in k · 2O(n) time.

B. A concatenated code construction

The statement of Theorem 21 follows immediately from the
concatenated code construction guaranteed by the following
theorem.

Theorem 24: There exist absolute constants b, d > 0 such
that for every integer K and every ε > 0, there exists a
def= RS⊕ GREEDY(m, ε/2) (for a
concatenated code CK
suitable parameter m) that has the following properties:

1) CK is a linear code of dimension K, blocklength N ≤

bK

ε4 , and minimum distance at least ( 1

2 − ε)N .

2) The generator matrix of CK can be constructed in

N O(ε−2) time.



<!-- pdf-page: 12 -->
12

GURUSWAMI, H ˚ASTAD, SUDAN, AND ZUCKERMAN

3) CK is (( 1

2 −ε)N, d/ε2)-list decodable; i.e. any Hamming
ball of radius (1/2−ε)N has at most O(ε−2) codewords
of CK.

4) There exists a polynomial time list decoding algorithm
for CK that can correct up to (1/2 − ε)N errors.
Proof: The code CK is constructed by concatenating an
outer Reed-Solomon code over GF(2m) of blocklength n0 =
2m and dimension k0 = K/m (for some integer m which will
be speciﬁed later in the proof) with an inner code Cinner =
GREEDY(m, ε/2) (as guaranteed by Lemma 23). Since the
blocklength of Cinner is n1 = O( m
ε2 ), the concatenated code
CK has dimension K and blocklength
(cid:17)

(23)

N = O

(cid:16) n0m
ε2

and minimum distance D at least

.

(cid:16)

(cid:17)

−

ε
2

1 −

(24)

D ≥

(cid:17)(cid:16) 1
2

K
mn0
For ease of notation, we often hide constants using the big-
Oh notation in what follows, but in all these cases the hidden
constants will be absolute constants that do not depend upon ε.
Note that since Cinner is constructible in 2O(n1) = 2O(m/ε2)
time, and m = log n0, the generator matrix for CK can be
constructed in N O(ε−2) time. This proves Property 2 claimed
in the theorem.

We will now present a polynomial

time list decoding
algorithm for CK to recover from a fraction (1/2−ε) of errors
with a small (O(ε−2)) list size. This will clearly establish both
Properties 3 and 4 claimed in the theorem.

Let y ∈ {0, 1}N be any received word. We wish to ﬁnd a
list of all codewords c ∈ CK such that ∆(y, c) ≤ 1/2 − ε.
For 1 ≤ i ≤ n0, denote by yi (resp. ci) the portion of y (resp.
c) that corresponds to the ith codeword position of the outer
Reed-Solomon code. For 1 ≤ i ≤ n0 and α ∈ GF(2m), deﬁne

wi,α = max

(cid:110)(cid:16) 1
2

−

ε
2

− ∆(yi, Cinner[α])

(cid:17)

(cid:111)

, 0

(25)

(here Cinner[α] denotes the inner encoding of α interpreted
as an m-bit string). By the property of Cinner guaranteed by
Lemmas 22 and 23, we have, for each i, 1 ≤ i ≤ n0,

(cid:88)

w2

i,α ≤ B(cid:48) ,

α∈GF(2m)

(26)

for some absolute constant B(cid:48).

Now, consider the following decoding algorithm for CK.
First, the inner codes are decoded by a brute force procedure
that goes over all codewords. Speciﬁcally, for each position i
of the outer Reed-Solomon code, the inner decoder passes a
list of all ﬁeld elements α with the respective weights wi,α
deﬁned in Equation (25). The weight wi,α may be interpreted
as the reliability information for the possibility that the i’th
symbol of the outer codeword was the ﬁeld element α. The
inner decoding takes O(2m) = O(n0) time for each of the n0
inner codes, and thus the total time required to perform this
step is poly(N ). We now have to perform decoding of the
outer Reed-Solomon code taking into account these weights.
For this we use a weighted (or “soft-decision”) list decoding
algorithm for Reed-Solomon codes from [12], similar to its

use in [13] for decoding the Reed-Solomon concatenated with
the Hadamard code. This algorithm guarantees to ﬁnd, in time
polynomial in n0 and 1/γ, a list of all codewords c ∈ CK
that satisfy

(cid:118)
(cid:117)
(cid:117)
(cid:116)

(cid:16)

n0 −

wi,ci ≥

n0(cid:88)

i=1

n0 − K/m + 1
1 + γ

(cid:17)

·

(cid:88)

i,α

w2

i,α

(27)

where γ > 0 is a parameter to be set later, and by abuse
of notation wi,ci = wi,αi where αi ∈ GF(2m) is such that
Cinner[αi] = ci. Moreover, it is also known that there will be
at most (1 + 1/γ) codewords c that satisfy Condition (27) for
any choice of weights wi,α, and thus the algorithm will output
a list of at most O(1/γ) codewords.

Using (25) and (26), we have that Condition (27) will be

satisﬁed if
n0(cid:88)

i=1

(cid:16) 1
2

−

ε
2

−

(cid:17)

∆(yi, ci)
n1

≥

(cid:114)(cid:16)

γn0 +

(cid:17)

K
m

· n0B(cid:48)

which is equivalent to
(cid:18) 1
2

∆(y, c) ≤ N

−

ε
2

−

(cid:114)

(cid:16)

B(cid:48)

γ +

(cid:17)(cid:19)

K
mn0

(28)

and, as long as we pick γ ≤ ε2
m2m ≤ ε2
K
satisﬁed provided

=
8B(cid:48) , we can hence conclude that Condition (27) is

8B(cid:48) and m such that K
mn0

∆(y, c) ≤

(cid:17)

N.

− ε

(cid:16) 1
2

Thus we have a decoding algorithm that outputs a list of
all O(1/γ) = O(ε−2) codewords that differ from y in at most
(1/2 − ε)N positions. Finally, by our choice of m, we have
mn0 = O(K/ε2), and plugging this into (23) and (24), we
have that the blocklength N of CK satisﬁes N = O(K/ε4)
and the distance D satisﬁes D ≥ (1/2 − ε)N , as desired.

Discussion: The time required to construct a code with the
properties claimed in Theorem 24,
though polynomial for
every ﬁxed ε, grows as N O(ε−2). Thus these codes are not
uniformly constructive (i.e. are constructible in O(f (ε)nc)
time for a ﬁxed constant c, independent of ε, for some arbitrary
function f ). If one uses the best known algebraic-geometric
codes (which in particular beat the Gilbert-Varshamov bound)
as the outer code instead of Reed-Solomon codes, one
can carry out
the code construction of Theorem 24 in
2O(ε−2 log(1/ε))N c time for a ﬁxed constant c (the constant
c will depend upon the time required to construct the outer
algebraic-geometric code). This is not entirely satisfying since
the construction complexity of such algebraic-geometric codes
that beat the Gilbert-Varshamov bound is still quite high. It
is an interesting open question to ﬁnd an alternative, simpler
construction of uniformly constructive codes which meet the
requirements of Theorem 24.

VI. CONCLUDING REMARKS

In this paper, we reported codes with non-trivial list decod-
ing properties. One of our results was to show the existence of



<!-- pdf-page: 13 -->
COMBINATORIAL BOUNDS FOR LIST DECODING

13

[10] V. Guruswami. List Decoding of Error-Correcting Codes. Ph.D thesis,

Massachusetts Institute of Technology, August 2001.

[11] V. Guruswami. Limits to list decodability of linear codes. Manuscript,

November 2001.

[12] V. Guruswami and M. Sudan. Improved decoding of Reed-Solomon
and Algebraic-geometric codes. IEEE Trans. on Information Theory,
45 (1999), pp. 1757-1767.

[13] V. Guruswami and M. Sudan. List decoding algorithms for certain
concatenated codes. Proceedings of the 32nd ACM Symposium on the
Theory of Computing (STOC), Portland, OR, May 2000, pp. 181-190.
[14] V. Guruswami and M. Sudan. Extensions to the Johnson Bound.

Manuscript, February 2001.

[15] G. H. Hardy, J. E. Littlewood, G. P´olya. Inequalities, 2nd Edition,

Cambridge University Press, 1952.

[16] J. Justesen and T. Høholdt. Bounds on list decoding of MDS codes. IEEE
Transactions on Information Theory, 47(4):1604–1609, May 2001.
[17] C. E. Shannon, R. G. Gallager and E. R. Berlekamp. Lower bounds to
error probability for coding on discrete memoryless channels. Informa-
tion and Control, 10, pp. 65-103 (Part I), pp. 522-552 (Part II), 1967.
[18] M. A. Shokrollahi and H. Wasserman. List decoding of algebraic-
geometric codes. IEEE Trans. on Information Theory, 45(2):432–437,
March 1999.

[19] M. Sudan. Decoding of Reed-Solomon codes beyond the error-
correction bound. Journal of Complexity, 13(1):180–193, March 1997.
[20] M. Sudan. List Decoding: Algorithms and Applications. SIGACT News,

Vol. 31, March 2000, pp. 16–27.

[21] M. A. Tsfasman, S. G. Vl˘adut and T. Zink. Modular curves, Shimura
curves, and codes better than the Varshamov-Gilbert bound. Math.
Nachrichten, 109:21–28, 1982.

[22] J. H. van Lint. Introduction to Coding Theory, Graduate Texts in
Mathematics 86, (Third Edition) Springer-Verlag, Berlin, 1999.
[23] V. K. Wei and G. L. Feng. Improved lower bounds on the sizes of
error-correcting codes for list decoding. IEEE Trans on Info Theory,
40(2):559–563, 1994.

[24] J. M. Wozencraft. List Decoding. Quarterly Progress Report, Research

Laboratory of Electronics, MIT, Vol. 48 (1958), pp. 90-95.

[25] V. V. Zyablov and M. S. Pinsker. List cascade decoding. In Prob.
Information Transmission, 17(4):29–34 (in Russian), 1981; pp. 236–240
(in English), 1982.

linear codes that have an arbitrarily large polynomial number
of codewords in a Hamming ball of relative radius strictly
less than the relative distance. While it is easy to show that
non-linear codes with this property exist (by a simple random
coding argument), the situation for linear codes is more tricky.
Recently, the techniques used in Section III of this paper
were used together with some new ideas to prove that, under
a widely believed number-theoretic conjecture, the result of
Conjecture 9 holds [11] (see also [10, Chap. 4]). However,
this does not subsume the result of Theorem 11 in this paper,
since our result holds unconditionally without the need for any
unproven number-theoretic conjecture.

We also demonstrated the existence of codes of good rate
with a small number of codewords in a Hamming ball of
large radius (Theorem 5). Our proof, however, was highly non-
constructive and does not even give a high probability result.
It is an open question whether a random linear code satisﬁes
the property claimed in Theorem 5 with high probability.

We then showed that the statement of Theorem 5 can be
adapted to guarantee the existence of certain linear codes
which serve as good (for purposes of list decoding) inner
codes in a concatenation scheme with an outer Reed-Solomon
code. This in turn gave us an efﬁciently constructible family
of binary linear codes of rate Ω(ε4) and relative distance at
least (1/2 − ε), which can be efﬁciently list decoded from
up to a ( 1
2 − ε) fraction of errors, using lists of size O(ε−2).
This improves upon the results claimed in [13] (the best rate
achieved by [13] for such families of codes was Ω(ε6)). The
time required to construct such a code, though polynomial
for every ﬁxed ε, grows exponentially in 1/ε, and it will be
desirable to, if possible, bring this down to polynomial in both
N and 1/ε.

ACKNOWLEDGEMENTS

We thank Amnon Ta-Shma and Alex Russell for helpful

discussions about Theorem 10.

REFERENCES

[1] R. Ahlswede. Channel capacities for list codes. J. Appl. Probability, 10

(1973), pp. 824-836.

[2] A. Ashikhmin, A. Barg, and S. Litsyn. A new upper bound on
In Ingo Althofer et al., editor,
codes decodable into size-2 lists.
Numbers, Information and Complexity, pages 239–244. Boston: Kluwer
Publishers, 2000.

[3] V. M. Blinovsky. Bounds for codes in the case of list decoding of ﬁnite
volume. Prob. Information Transmission, 22(1):11–25 (in Russian),
1986; pp. 7–19 (in English), 1986.

[4] V. M. Blinovsky. Asymptotic Combinatorial Coding Theory. Kluwer

Academic Publishers, Boston, 1997.

[5] V. M. Blinovsky. Lower Bound for the Linear Multiple Packing of the
Binary Hamming Space. Journal of Combinatorial Theory, Series A,
Vol. 92, No. 1, October 2000, pp. 95-101.

[6] I. Dumer, D. Micciancio and M. Sudan. Hardness of approximating
the minimum distance of a linear code. Proceedings of the 40th IEEE
Symposium on Foundations of Computer Science (FOCS), New York,
NY, October 1999, pp. 475-484.

[7] P. Elias. List decoding for noisy channels. Wescon Convention Record,
Part 2, Institute of Radio Engineers (now IEEE), pp. 94-104, 1957.
[8] P. Elias. Error-correcting codes for List decoding. IEEE Transactions on

Information Theory, 37(1):5–12, 1991.

[9] O. Goldreich, R. Rubinfeld and M. Sudan. Learning polynomials with
queries: the highly noisy case. SIAM Journal on Discrete Mathematics,
13(4):535–570, November 2000.



<!-- pdf-page: 14 -->
14

GURUSWAMI, H ˚ASTAD, SUDAN, AND ZUCKERMAN

BIOGRAPHIES

Venkatesan Guruswami is a Miller Postdoctoral Fellow at
the Computer Science Division of the University of California
at Berkeley. He received his Bachelor’s degree from the
Indian Institute of Technology at Madras in 1997 and his
Ph.D. from the Massachusetts Institute of Technology in 2001.
His research interests fall mainly in the areas relating to
Theoretical Computer Science and include approximability of
combinatorial optimization problems, complexity theory and
error-correcting codes.

Johan H˚astad is a Professor in the Department of Numerical
Analysis and Computer Science at
the Royal Institute of
Technology in Stockholm, Sweden. He received his Bachelor’s
degree from Stockholm University in 1981, a licentiate degree
from Uppsala University in 1984 and a Ph.D. from MIT in
1986. He held a post-doc position at MIT until he joined the
Royal Institute of Technology in 1988. He is a member of
the Royal Swedish Academy of Sciences. Professor H˚astad’s
research interests include computational complexity theory,
algorithms, cryptography, and coding theory.

Madhu Sudan is an Associate Professor in the Department
of Electrical Engineering and Computer Science at the Mas-
sachusetts Institute of Technology. He recieved his Bachelor’s
degree from the Indian Institute of Technology at New Delhi
in 1987 and his Ph.D. from the University of California at
Berkeley in 1992. He was a Research Staff Member at IBM’s
Thomas J. Watson Research Center in Yorktown Heights, NY
from 1992 to 1997 and has been at his current position since
then. His research interests include computational complexity
theory, algorithms and coding theory.

David Zuckerman is an Associate Professor in the Depart-
ment of Computer Science at the University of Texas at Austin.
He recieved his A.B. in Mathematics from Harvard University
in 1987 abd his Ph.D. from the University of California at
Berkeley in 1991. He was a postdoctoral fellow at MIT from
1991-1993, and at Hebrew University in the Fall of 1993.
He has been with the University of Texas since then, visiting
the Computer Science Division of U.C. Berkeley as a visit-
ing MacKay Lecturer from 1999-2000. His research include
the role of randomness in computation, pseudorandomness,
complexity theory, constructive combinatorics, coding theory,
fault tolerance, random walks on graphs, approximability, and
cryptography.


