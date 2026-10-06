<!-- generated-by: proofmatch local extraction -->
<!-- source-pdf-sha256: 5ada2eaf45a82e0deea73bcd5180a5dd3c8e1d125c5f65c4d4cce6458deea54a -->
<!-- extractor: pdfminer.six v20260107 -->

<!-- pdf-page: 1 -->
The Annals of Statistics
2000, Vol. 28, No. 5, 1302–1338

ADAPTIVE ESTIMATION OF A QUADRATIC FUNCTIONAL
BY MODEL SELECTION

By B. Laurent and P. Massart

Universit´e Paris Sud

(cid:1)

We consider the problem of estimating (cid:1)s(cid:1)2 when s belongs to some
separable Hilbert space and one observes the Gaussian process Y(cid:2)t(cid:3) =
(cid:5)s(cid:4) t(cid:6) + σL(cid:2)t(cid:3), for all t ∈ (cid:1), where L is some Gaussian isonormal process.
This framework allows us in particular to consider the classical “Gaussian
sequence model” for which (cid:1) = l2(cid:2)(cid:2)∗(cid:3) and L(cid:2)t(cid:3) =
λ≥1 tλελ, where (cid:2)ελ(cid:3)λ≥1
is a sequence of i.i.d. standard normal variables. Our approach consists in
considering some at most countable families of ﬁnite-dimensional linear
subspaces of (cid:1) (the models) and then using model selection via some con-
veniently penalized least squares criterion to build new estimators of (cid:1)s(cid:1)2.
We prove a general nonasymptotic risk bound which allows us to show that
such penalized estimators are adaptive on a variety of collections of sets for
the parameter s, depending on the family of models from which they are
built. In particular, in the context of the Gaussian sequence model, a con-
venient choice of the family of models allows deﬁning estimators which are
adaptive over collections of hyperrectangles, ellipsoids, lp-bodies or Besov
bodies. We take special care to describe the conditions under which the
penalized estimator is efﬁcient when the level of noise σ tends to zero.
Our construction is an alternative to the one by Efro¨ımovich and Low for
hyperrectangles and provides new results otherwise.

1. Introduction.
The framework. We consider the following extension of the standard linear
Gaussian model to a possibly inﬁnite-dimensional setting. Given some sepa-
rable Hilbert space (cid:1), one observes

Y(cid:2)t(cid:3) = (cid:5)s(cid:4) t(cid:6) + σL(cid:2)t(cid:3)

for all t ∈ (cid:1)(cid:4)

where L is some centered Gaussian isonormal process; that is, L maps (cid:1)
isometrically onto some Gaussian subspace of (cid:3)2(cid:2)(cid:11)(cid:3). We shall say that Y is
a Gaussian linear process with mean s and variance σ 2. Our purpose is to
propose new adaptive estimators of (cid:1)s(cid:1)2. The Gaussian framework that we
introduce here could appear useless or at least unusual to the reader. In fact,
it will turn out to be convenient for covering both the inﬁnite-dimensional
“white noise model” introduced by Ibragimov and Khasminskii for which (cid:1) =
(cid:3)2(cid:2)(cid:11)0(cid:4) 1(cid:12)(cid:3) and L(cid:2)t(cid:3) =
t(cid:2)x(cid:3) dW(cid:2)x(cid:3), where W is a standard Brownian motion,
and the ﬁnite-dimensional linear model for which (cid:1) = (cid:4)N and L(cid:2)t(cid:3) = (cid:5)ζ(cid:4) t(cid:6),
where ζ is a standard N-dimensional Gaussian vector. Given some Hilbertian
basis (cid:13)ϕλ(cid:14)λ∈(cid:18) of (cid:1), where (cid:18) is a ﬁnite or countable set, one can equivalently

(cid:2)

Received December 1998; revised April 2000.
AMS 1991 subject classiﬁcations. Primary 62G05; secondary 62G20, 62J02.
Key words and phrases. Adaptive estimation, quadratic functionals, model selection, Besov

bodies, lp-bodies, Gaussian sequence model, efﬁcient estimation.

1302



<!-- pdf-page: 2 -->
ESTIMATION OF A QUADRATIC FUNCTIONAL

1303

describe the observation Y by

Yλ = βλ + σελ(cid:4)

λ ∈ (cid:18)(cid:4)

where (cid:13)ελ(cid:14)λ∈(cid:18) is a family of i.i.d. standard normal random variables and
(cid:13)βλ(cid:14)λ∈(cid:18) is the family of coordinates of s. When (cid:18) = (cid:2)∗, this model is known
as the Gaussian sequence model. The white noise model (or its equivalent
discrete version, the Gaussian sequence model) has been considered by many
authors since it represents in some sense an “ideal laboratory” for nonpara-
metric inference. One can indeed hope to transpose the estimation methods
developed within this framework, which is especially simple from a proba-
bilistic point of view, to other more complicated situations such as density or
regression estimation. It is exactly in this spirit that we will deal with the
statistical framework described above, choosing to write the level of noise σ
as σ = n−1/2 in order to allow easy comparisons of the results obtained within
this framework and other ones, such as density estimation on the basis of
n i.i.d. observations. Let us now recall what is known about the problem of
estimating (cid:1)s(cid:1)2 in the white noise, Gaussian sequence or density frameworks.
Estimating (cid:1)s(cid:1)2 with prior information on s. First it is important to say
that, even from a purely minimax point of view when s belongs to some given
set (cid:5) , there is at this time no complete answer to the following question:

(Q) Taking the usual distance on (cid:4) as a loss function, what is the order of the

minimax risk over (cid:5) when estimating (cid:1)s(cid:1)2?

This problem is really puzzling since two related questions have been solved
for quite a long time. Indeed, when estimating the function itself with vari-
ous loss functions, one can identify the order of the minimax risk in terms of
the metric dimension of (cid:5) [see the landmark paper by Birg´e (1983) on this
topic]. Concerning the problem of estimating a linear functional, the order of
the risk is entirely determined by the modulus of continuity of the functional
over (cid:5) with respect to Hellinger distance [see Donoho and Liu (1991) where
one will also ﬁnd some results for nonlinear functionals which are not, how-
ever satisfactory for quadratic functionals]. Let us now turn to the estimation
of a quadratic functional. Bickel and Ritov (1988) were the ﬁrst to point out
the following remarkable phenomenon for the estimation rates of θ = (cid:1)s(cid:1)2
in the density estimation context (more precisely if one observes n i.i.d. vari-
ables with common density s with respect to the Lebesgue measure on the
real line). Assume that s belongs to some H¨olderian ball (cid:5) with radius R
and index of smoothness α; then it is possible to construct some estimator ˆθn
(depending on (cid:5) ) such that, if α > 1/4, ˆθn is an asymptotically
n-efﬁcient
estimator of θ, while it achieves the rate of convergence n−4α/(cid:2)1+4α(cid:3) whenever
α ≤ 1/4, this rate being the order of the minimax risk over (cid:5) . Corresponding
results for the Gaussian sequence model have been obtained by Donoho and
Nussbaum (1990), the smoothness assumptions being in this context replaced
λ ≤ R2,
by geometric assumptions for the sequence (cid:2)βλ(cid:3)λ≥1 such as
which means that (cid:2)βλ(cid:3)λ≥1 belongs to some ellipsoid. It is worth noticing that

λ≥1 λ2αβ2

(cid:1)

√



<!-- pdf-page: 3 -->
1304

B. LAURENT AND P. MASSART

estimating (cid:1)s(cid:1)2 is a key step to constructing estimators of more general inte-
gral functionals of s. The interested reader will ﬁnd some details about the
density framework in Laurent (1996), where simpler estimators of (cid:1)s(cid:1)2 than
those used by Bickel and Ritov are also introduced [see also Birg´e and Massart
(1995) for minimax lower bounds concerning smooth functionals of the den-
sity]. These results solve question (Q) for some particular sets (cid:5) such as ellip-
soids (similar results hold for hyperrectangles) when (cid:5) is a set of sequences
or H¨olderian balls when (cid:5) is a set of functions. This suggests that a general
answer to question (Q) should take into account not only the modulus of conti-
nuity of the functional as in Donoho and Liu’s theory (the quadratic functional
(cid:1)s(cid:1)2 is indeed Lipschitz over any of the sets (cid:5) described above) but also the
“size” of (cid:5) in a sense that we do not know. Our feeling is that the metric
dimension successfully used by Birg´e for the estimation of s itself might not
be appropriate as suggested by the new results established in this paper con-
cerning lp-bodies, for p < 2. Indeed, for the Gaussian sequence model, under
λ≥1 λp(cid:2)1/2+α−1/p(cid:3)(cid:19)βλ(cid:19)p ≤ Rp with α > 1/p − 1/2, we shall
the assumption
√
n-convergent estimator provided that
show in Section 3 the existence of a
α > 1/p − 1/4 when p ≥ 4/3 and α > 1/2 when p ≤ 4/3. The striking fact
here is that our result depends on p while the metric dimension of the lp-body
is known to depend only on α [see for instance Birg´e and Massart (2000a)].
Unfortunately we do not know whether our result is optimal or not.

(cid:1)

Adaptive estimation of (cid:1)s(cid:1)2. All the estimators of (cid:1)s(cid:1)2 that one can ﬁnd
in the literature cited above suffer from the same drawback: they depend on
the a priori knowledge that s belongs to some set (cid:5) (such as some given
H¨olderian ball or some given ellipsoid for instance). From this point of view,
Efro¨ımovitch and Low (1996) have obtained an important improvement of the
previous results. In the context of the Gaussian sequence model, by using a
procedure which is close to Lepskii’s method [as introduced in Lepskii (1990,
1992)] they propose an estimator ˆθn of θ with the following adaptive properties.
For any positive R and α, provided that the sequence (cid:2)βλ(cid:3)λ≥1 satisﬁes the
condition β2
λλ2α+1 ≤ R2 for all λ [which means that (cid:2)βλ(cid:3)λ≥1 belongs to some
hyperrectangle] one has:

ˆθn is asymptotically efﬁcient if α > 1/4;
(cid:3)(cid:4)

(cid:5)2(cid:6)

1.
2. Ɛ

ˆθn − θ

≤ bn/n, where bn tends to inﬁnity when n goes to inﬁnity as

slowly as desired, if α = 1/4.
Note that they also consider an estimator ˆθn which is
whole range α ≥ 1/4. For both estimates one has

√

n-consistent in the

(cid:3)(cid:4)

Ɛ

ˆθn − θ

(cid:5)2(cid:6)

≤ C(cid:2)R(cid:4) α(cid:3)(cid:2)n−2 log(cid:2)n(cid:3)(cid:3)4α/(cid:2)1+4α(cid:3)

if α < 1/4(cid:29)

Since the minimax quadratic risk for estimating θ on a given hyperrectangle
is of order n−8α/(cid:2)1+4α(cid:3) whenever α < 1/4, the estimator ˆθn misses the optimal
rate within the factor (cid:2)log(cid:2)n(cid:3)(cid:3)4α/(cid:2)1+4α(cid:3). Efro¨ımovitch and Low (1996) actually
show that this is really the price to pay for adaptation, which means that
this logarithmic factor is unavoidable if you do not know in advance to what
hyperrectangle s belongs. The reader should take note of the fact that the index



<!-- pdf-page: 4 -->
ESTIMATION OF A QUADRATIC FUNCTIONAL

1305

α that we use here is different from the one used in Efro¨ımovitch and Low
(1996). This choice will turnout to be convenient when connecting smoothness
assumptions on functions with geometrical constraints on the coefﬁcients of
functions in a proper basis.

Description of our method and results. Our approach to building adaptive
estimators is based on model selection via penalization. This method has been
successfully developed to estimate adaptively a function s in various contexts
[see Birg´e and Massart (1997), Barron, Birg´e and Massart (1999), Baraud
(1997) or Birge and Massart (2000b)]. Although we shall deal with a general
Gaussian framework, we are presenting our approach in the context of the
Gaussian sequence model by sake of simplicity. We consider some collection
(cid:7) of subsets of (cid:2)∗ and a penalty function pen: (cid:7) → (cid:4)+. Our penalized
estimator of θ =

λ is then simply deﬁned by

λ≥1 β2

(cid:1)

(1.1)

ˆθ = sup
m∈(cid:7)

(cid:7)

(cid:8)

λ∈m

(cid:9)

Y2

λ − pen(cid:2)m(cid:3)

(cid:29)

(cid:4)

n

(cid:3)(cid:4)

√

2/

(cid:5)2(cid:6)

(cid:5) (cid:1)

ˆθ − θ −

λ≥1 βλελ

Our main theorem (see Theorem 1 in Section 2 below) provides a nonasymp-
totic bound for Ɛ
when the penalty function is
conveniently chosen (an explicit expression for the penalty function is given
in the statement of Theorem 1). Such a bound can also be used for asymp-
totic purposes and is especially useful for specifying under which condition on
the sequence (cid:2)βλ(cid:3)λ≥1(cid:4) ˆθ is asymptotically efﬁcient. The choice of the penalty
function is very important and inﬂuences the order of magnitude of the risk
bound. The penalty pen(cid:2)m(cid:3) depends, of course, on the cardinality of m but
also on the complexity of the whole collection (cid:7) . It should be noticed that
such a dependency also appears in Birg´e and Massart (2000b) in the same
context of the Gaussian sequence model, but with a very different expression
for the penalty. This means that an appropriate penalty function to estimate
s is not necessarily convenient to estimate (cid:1)s(cid:1)2 and vice versa.

Our general risk bound can be used to analyze the adaptivity property of
the penalized estimator over various families of sets of parameters (cid:2)Sa(cid:3)a∈A. Of
course the geometric nature of the sets Sa, a ∈ A will heavily depend on the
collection (cid:7) and more precisely of its approximation properties. For instance,
taking ﬁrst (cid:7) as the nested family (cid:7)nest of sets (cid:13)1(cid:4) (cid:29) (cid:29) (cid:29) (cid:4) D(cid:14), D ∈ (cid:2)∗, let us
deﬁne the penalized estimator as

(1.2)

(cid:10)

(cid:8)

λ≤D

Y2

λ −

(cid:11)

1
n

ˆθ = sup
D∈(cid:2)∗

(cid:12)

(cid:13)(cid:14)

D + 1 + 2

(cid:2)D + 1(cid:3)xD + 2xD

(cid:4)

where xD = C log D for any positive integer D, for some given constant
C > 2. Then ˆθ will have the same adaptivity properties over the set of
hyperrectangles as the estimator of Efro¨ımovitch and Low. Note that we even
get some modest but objective gain with respect to Efro¨ımovitch and Low’s
result since our estimator is
n-convergent when the
index α of the hyperrectangle is not too small, that is, α > 1/4. It also has

n-efﬁcient instead of

√

√



<!-- pdf-page: 5 -->
1306

B. LAURENT AND P. MASSART

analogous adaptivity properties with respect to the collection of lp-bodies
(cid:1)

λ∈(cid:2)∗ λp(cid:2)α−1/p+1/2(cid:3)(cid:19)βλ(cid:19)p ≤ Rp for p > 2.
We can, moreover, proﬁt by the ﬂexibility of the model selection via penal-
ization method and produce other estimators with new adaptivity properties
by simply enlarging the collection (cid:7)nest. If, for instance, we take (cid:7) as the col-
lection (cid:7)all of all the ﬁnite subsets of (cid:2)∗ and choose the penalty adequately,
we shall show that the penalized estimator still has the adaptivity proper-
ties of the preceding one with respect to the collection of hyperrectangles or
ellipsoids but furthermore has new adaptivity properties with respect to lp-
bodies for p < 2. In particular we shall prove that under the assumption
(cid:1)
n-efﬁcient
provided that α > 1/p − 1/4 when p ≥ 4/3 and α > 1/2 when p ≤ 4/3.
Otherwise some nonparametric rates of convergence arise but, as previously
mentioned, we do not know if our results are optimal or not, simply because
of the lack of lower bounds for the minimax risk on a given lp-body when
p < 2. We shall also construct penalized estimators with improved adaptive
convergence properties (the gain is a logarithmic factor), by considering some
specially designed collection of sets (cid:7) such that (cid:7)nest ⊂ (cid:7) ⊂ (cid:7)all(cid:29)

λ≥1 λp(cid:2)1/2+α−1/p(cid:3)(cid:19)βλ(cid:19)p ≤ Rp with α > 1/p − 1/2, the estimator is

In each example that we shall consider, we shall indicate an easy way to
compute the corresponding penalized estimator. Indeed, since deﬁnition (1.1)
involves some optimization over the collection (cid:7) , one could have legitimate
doubts about the computability of the penalized estimator, especially in sit-
uations where (cid:7) is taken to be a very large collection of sets like (cid:7)all. For-
tunately, we shall show that for all the examples that we shall consider, the
computation reduces to some optimization over the set of integers, exactly as
in (1.2), which this time can be expected to be performed with the help of a
computer.

√

2. Estimation via model selection.

2.1. Description of the framework. Assume that one observes a Gaussian
linear process Y with mean s and variance 1/n on some Hilbert space (cid:1),
endowed with the scalar product (cid:5)·(cid:4) ·(cid:6). We recall that this means

(2.1)

Y(cid:2)t(cid:3) = (cid:5)s(cid:4) t(cid:6) +

1
√
n

L(cid:2)t(cid:3)(cid:4)

t ∈ (cid:1)(cid:4)

where s ∈ (cid:1) is unknown, L is some isonormal Gaussian process on (cid:1) [see
Dudley (1973)], and L is a linear isometry from (cid:1) to some Gaussian sub-
space of (cid:3)2(cid:2)(cid:11)(cid:4) (cid:8)(cid:3). In particular, the covariance of the process is deﬁned by
Cov(cid:2)L(cid:2)t(cid:3)(cid:4) L(cid:2)t(cid:23)(cid:3)(cid:3) = (cid:5)t(cid:4) t(cid:23)(cid:6).
The following frameworks are easily seen to be of type (2.1).
Finite-dimensional Gaussian regression. One observes

(2.2)

Yi = si + εi(cid:4)

i = 1(cid:4) (cid:29) (cid:29) (cid:29) (cid:4) n(cid:4)

where (cid:2)ε1(cid:4) (cid:29) (cid:29) (cid:29) (cid:4) εn(cid:3) are independent standard normal variables. We consider
(cid:1) = (cid:4)n endowed with the scalar product (cid:5)x(cid:4) y(cid:6) = (cid:2)1/n(cid:3)
i=1 xiyi and set

(cid:1)n



<!-- pdf-page: 6 -->
ESTIMATION OF A QUADRATIC FUNCTIONAL

1307

(cid:1)n

s = (cid:2)s1(cid:4) (cid:29) (cid:29) (cid:29) (cid:4) sn(cid:3). Model (2.1) is obtained by setting, for all t = (cid:2)t1(cid:4) (cid:29) (cid:29) (cid:29) (cid:4) tn(cid:3) ∈ (cid:4)n,
√
Y(cid:2)t(cid:3) = (cid:2)1/n(cid:3)

n(cid:3)
Conversely, if model (2.1) is observed, then we recover the Gaussian regres-
sion model with ﬁxed design by considering an orthonormal basis of (cid:4), say
(cid:2)e1(cid:4) (cid:29) (cid:29) (cid:29) (cid:4) en(cid:3), and by setting Yi = Y(cid:2)nei(cid:3), si = n(cid:5)s(cid:4) ei(cid:6) and εi =

i=1 tiYi and L(cid:2)t(cid:3) = (cid:2)1/

i=1 tiεi.

nL(cid:2)ei(cid:3).

(cid:1)n

√

The Gaussian sequence model.

In the Gaussian sequence model, one

observes

(2.3)

Yλ = βλ +

1
√
n

ελ(cid:4)

λ ∈ (cid:2)∗(cid:4)

where (cid:2)ελ(cid:3)λ∈(cid:2)∗ is a sequence of independent standard normal variables.
(cid:1)
(cid:1)

Setting (cid:1) = l2(cid:2)(cid:2)∗(cid:3) endowed with the usual scalar product (cid:5)β(cid:4) γ(cid:6) =
λ∈(cid:2)∗ βλγλ and s = (cid:2)βλ(cid:3)λ∈(cid:2)∗, we deﬁne for any t = (cid:2)αλ(cid:3)λ∈(cid:2)∗ ∈ (cid:1), Y(cid:2)t(cid:3) =
λ∈(cid:2)∗ αλYλ and L(cid:2)t(cid:3) =
Conversely, if one observes (cid:13)Y(cid:2)t(cid:3)(cid:4) t ∈ l2(cid:2)(cid:2)∗(cid:3)(cid:14) according to model (2.1), then
we recover the Gaussian sequence model by setting for all λ ∈ (cid:2)∗, Yλ = Y(cid:2)φλ(cid:3),
βλ = (cid:5)s(cid:4) φλ(cid:6) and ελ = L(cid:2)φλ(cid:3) where (cid:2)φλ(cid:3)λ∈(cid:2)∗ is the canonical basis of l2(cid:2)(cid:2)∗(cid:3).

λ∈(cid:2)∗ αλελ and we see that (2.3) implies (2.1).

(cid:1)

The multivariate white noise model. One observes

(cid:15)

Z(cid:2)x(cid:3) =

(cid:11)0(cid:4)1(cid:12)d

(cid:1)(cid:11)0(cid:4)x1(cid:12)×···×(cid:11)0(cid:4)xd(cid:12)(cid:2)u(cid:3)s(cid:2)u(cid:3) du +

1
√
n

W(cid:2)x(cid:3)

for all x = (cid:2)x1(cid:4) (cid:29) (cid:29) (cid:29) (cid:4) xd(cid:3) ∈ (cid:11)0(cid:4) 1(cid:12)d, where W is the standard Wiener process on
(cid:11)0(cid:4) 1(cid:12)d. We consider (cid:1) = (cid:3)2(cid:2)(cid:11)0(cid:4) 1(cid:12)d(cid:3) endowed with its usual scalar product. We
set Y(cid:2)t(cid:3) =

(cid:11)0(cid:4)1(cid:12)d t(cid:2)u(cid:3) dZ(cid:2)u(cid:3) and L(cid:2)t(cid:3) =

(cid:11)0(cid:4)1(cid:12)d t(cid:2)u(cid:3) dW(cid:2)u(cid:3).

(cid:2)

(cid:2)

Conversely, if one observes (cid:13)Y(cid:2)t(cid:3)(cid:4) t ∈ (cid:3)2(cid:2)(cid:11)0(cid:4) 1(cid:12)d(cid:3)(cid:14), according to model (2.1)
then one a fortiori observes Z(cid:2)x(cid:3) = Y(cid:2)(cid:1)(cid:11)0(cid:4)x1(cid:12)×···×(cid:11)0(cid:4)xd(cid:12)(cid:3) for all x = (cid:2)x1(cid:4) (cid:29) (cid:29) (cid:29) (cid:4) xd(cid:3) ∈
(cid:11)0(cid:4) 1(cid:12)d. Since W(cid:2)x(cid:3) = L(cid:2)(cid:1)(cid:11)0(cid:4)x1(cid:12)×···×(cid:11)0(cid:4)xd(cid:12)(cid:3) is a standard Wiener process, Z is
indeed deﬁned from a white noise model.

2.2. The estimation procedure. Our aim is to estimate (cid:1)s(cid:1)2 = (cid:5)s(cid:4) s(cid:6) from
observation (2.1). We want to present an adaptive estimation method based on
model selection. To better understand its interest and the way it works, it is
useful to recall ﬁrst the minimax approach for which one can use an estimator
deﬁned from a single ﬁnite-dimensional linear model.

The minimax approach. Let us take some D-dimensional linear subspace
S of (cid:1). Given some orthonormal basis (cid:2)φλ(cid:4) λ ∈ (cid:18)(cid:3) of S, since the orthogonal
(cid:1)
λ∈(cid:18)(cid:5)s(cid:4) φλ(cid:6)φλ, it is natural to consider
projection of s on S can be written as
the projection estimator ˆs =

λ∈(cid:18) Y(cid:2)φλ(cid:3)φλ. It is easy to verify that

(cid:1)

ˆs = arg min

(cid:2)(cid:1)v(cid:1)2 − 2Y(cid:2)v(cid:3)(cid:3)(cid:4)

v∈S

which shows that ˆs does not depend on the particular choice of the basis
(cid:2)φλ(cid:4) λ ∈ (cid:18)(cid:3). It is instructive to study the behavior of the statistics (cid:1) ˆs(cid:1)2. Since

ˆs =

(cid:8)

λ∈(cid:18)

(cid:5)s(cid:4) φλ(cid:6)φλ +

1
√
n

(cid:8)

λ∈(cid:18)

L(cid:2)φλ(cid:3)φλ(cid:4)



<!-- pdf-page: 7 -->
1308

we obtain

B. LAURENT AND P. MASSART

(cid:1) ˆs(cid:1)2 =

(cid:8)

λ∈(cid:18)

(cid:5)s(cid:4) φλ(cid:6)2 +

2
√
n

(cid:8)

λ∈(cid:18)

(cid:5)s(cid:4) φλ(cid:6)L(cid:2)φλ(cid:3) +

1
n

(cid:8)

λ∈(cid:18)

L2(cid:2)φλ(cid:3)(cid:29)

From this identity, we derive that ˆθ = (cid:1) ˆs(cid:1)2 − D/n is an unbiased estimator
of (cid:1)πS(cid:2)s(cid:3)(cid:1)2 where πS(cid:2)s(cid:3) =
λ∈(cid:18)(cid:5)s(cid:4) φλ(cid:6)φλ denotes the orthogonal projection of
s onto S. We can easily compute the quadratic risk of ˜θ as an estimator of
θ = (cid:1)s(cid:1)2. Indeed, we notice that

(cid:1)

˜θ − θ −

2L(cid:2)s(cid:3)
√
n

= −(cid:1)s − πS(cid:2)s(cid:3)(cid:1)2 +

2
√
n

L(cid:2)πS(cid:2)s(cid:3) − s(cid:3) +

1
n

(cid:8)

λ∈(cid:18)

(cid:2)L2(cid:2)φλ(cid:3) − 1(cid:3)(cid:29)

Since the variables L(cid:2)πS(cid:2)s(cid:3)−s(cid:3) and
tive distributions (cid:9) (cid:2)0(cid:4) (cid:1)s − πS(cid:2)s(cid:3)(cid:1)2(cid:3) and χ2(cid:2)D(cid:3), we derive that

λ∈(cid:18) L2(cid:2)φλ(cid:3) are independent with respec-

(cid:1)

(cid:10)(cid:11)

Ɛ

˜θ − θ −

(2.4)

(cid:14)

(cid:13)2

2L(cid:2)s(cid:3)
√
n

= (cid:1)s − πS(cid:2)s(cid:3)(cid:1)4 +

4
n

(cid:1)s − πS(cid:2)s(cid:3)(cid:1)2 +

2D
n2

≤ 3(cid:1)s − πS(cid:2)s(cid:3)(cid:1)4 +

2(cid:2)D + 1(cid:3)
n2

(cid:29)

From this inequality, we see that an ideal choice of S would be to make the
trade-off between the squared bias term (cid:1)s − πS(cid:2)s(cid:3)(cid:1)4 and the variance term
D/n2. To be more concrete, let us take (cid:1) = (cid:3)2(cid:2)(cid:11)0(cid:4) 1(cid:12)(cid:3). Then, some prior smooth-
ness assumption on s such as s belongs to the class of H¨olderian functions

(cid:10)α(cid:2)L(cid:3) = (cid:13)t ∈ (cid:3)2(cid:2)(cid:11)0(cid:4) 1(cid:12)(cid:3)(cid:4) (cid:19)t(cid:2)x(cid:3) − t(cid:2)y(cid:3)(cid:19) ≤ L(cid:19)x − y(cid:19)α(cid:4) ∀x(cid:4) y ∈ (cid:11)0(cid:4) 1(cid:12)(cid:14)(cid:4)

leads to the existence of some subspace S (such as histograms with D regular
pieces) such that

sup
s∈(cid:10)α(cid:2)L(cid:3)

(cid:1)s − πS(cid:2)s(cid:3)(cid:1)2 ≤ CL2D−2α(cid:29)

Therefore, choosing D in a way that D/n2 ∼ L4D−4α ensures that, for some
universal constant C(cid:23),
(cid:10)(cid:11)

(cid:14)

Ɛ

sup
s∈(cid:10)α(cid:2)L(cid:3)

˜θ − θ −

(cid:13)2

2L(cid:2)s(cid:3)
√
n

≤ C(cid:23)L4/(cid:2)1+4α(cid:3)n−8α/(cid:2)1+4α(cid:3)(cid:29)

In that case, ˜θ is an asymptotically efﬁcient estimator of θ with asymptotic
variance 4(cid:1)s(cid:1)2 whenever α > 1/4.

The main drawback of this minimax approach is that the choice of the
subspace S and of its dimension D depends on the prior smoothness class
(cid:10)α(cid:2)L(cid:3). Our strategy to overcome this difﬁculty consists of considering some
preliminary collection of models (cid:2)Sm(cid:3)m∈(cid:7) where (cid:7) is some ﬁnite or countable
set that may depend on n and deﬁning our estimator from the corresponding
collection of projection estimators (cid:2) ˆsm(cid:3)m∈(cid:7) via some model selection criterion.
This criterion relies upon the following idea.



<!-- pdf-page: 8 -->
ESTIMATION OF A QUADRATIC FUNCTIONAL

1309

Heuristics of the model selection method. For any m ∈ (cid:7) , let Sm be some
Dm-dimensional linear subspace of (cid:1), sm denote the orthogonal projection
of s onto Sm and ˜θm be the unbiased estimator of (cid:1)sm(cid:1)2 deﬁned by ˜θm =
(cid:1) ˆsm(cid:1)2 − Dm/n. From inequality (2.4), we derive that “the best” model from
the point of view of minimizing the quadratic risk of ˜θm as an estimator of
θ should minimize (cid:1)s − sm(cid:1)2 + C
Dm/n.
Since (cid:1)sm(cid:1)2 is unknown, it is natural to replace it by the unbiased estimator
˜θm. This leads to the idea of minimizing −(cid:1) ˆsm(cid:1)2 + Dm/n + C
Dm/n to get a
proper data-driven model choice. Our selection criterion will indeed be close
to the latter since we shall consider some penalty function pen: (cid:7) → (cid:4)+ and
deﬁne

Dm/n or equivalently −(cid:1)sm(cid:1)2 + C

(cid:16)

(cid:16)

(cid:16)

ˆm = arg min

m∈(cid:7)

(cid:2)−(cid:1) ˆsm(cid:1)2 + pen(cid:2)m(cid:3)(cid:3)(cid:29)

The main issue is that pen(cid:2)m(cid:3) will be taken greater than the heuristically
determined penalty term Dm/n + C
Dm/n in order to take into account the
“complexity” of the collection of models. We ﬁnally deﬁne our penalized esti-
mator of θ as

(cid:16)

ˆθ = (cid:1) ˆs ˆm(cid:1)2 − pen(cid:2) ˆm(cid:3) = sup

m∈(cid:7)

(cid:2)(cid:1) ˆsm(cid:1)2 − pen(cid:2)m(cid:3)(cid:3)(cid:29)

We turn now to the main result of the paper, which we shall illustrate in the
next sections.

2.3. The main theorem. We address the problem of constructing risk bounds
for penalized estimators which depend on a proper choice of the penalty func-
tion. In the statement of Theorem 1 below, the parameter n which appears in
(2.1) is ﬁxed and our bounds involve numerical constants that do not depend
on n. Hence the Hilbert space involved in (2.1) as well as the collection of
models (cid:2)Sm(cid:3)m∈(cid:7) or the penalty function pen(·) are allowed to depend on n.

Theorem 1. Let (cid:1) be some Hilbert space endowed with scalar product (cid:5)·(cid:4) ·(cid:6).
One observes the Gaussian process (cid:13)Y(cid:2)t(cid:3)(cid:4) t ∈ (cid:1)(cid:14), where Y(cid:2)t(cid:3) is given by (2.1).
Let (cid:7) ∗ be some ﬁnite or countable set and for any m ∈ (cid:7) ∗, let Sm denote some
linear subspace of (cid:1) with ﬁnite dimension Dm > 0. We consider (cid:2)xm(cid:3)m∈(cid:7) ∗ to be
some family of nonnegative real numbers. Let, for any m ∈ (cid:7) ∗, pen(cid:2)m(cid:3) satisfy

(2.5)

n pen(cid:2)m(cid:3) ≥ (cid:2)Dm + 1(cid:3) + 2

(cid:2)Dm + 1(cid:3)xm + 2xm(cid:29)

(cid:12)

Let (cid:7) be either (cid:7) ∗ or (cid:7) ∗ ∪ (cid:13)0(cid:14), with S0 = (cid:13)0(cid:14) and pen(cid:2)0(cid:3) = 0. Let ˆsm be the
projection estimator of s over Sm.

We consider the collection of estimators (cid:2) ˆθm(cid:3)m∈(cid:7) of θ = (cid:1)s(cid:1)2, given by

and deﬁne

(2.6)

ˆθm = (cid:1) ˆsm(cid:1)2 − pen(cid:2)m(cid:3)

ˆθ = sup
m∈(cid:7)

ˆθm(cid:29)



<!-- pdf-page: 9 -->
1310

B. LAURENT AND P. MASSART

Let r be some positive real number. Then, whenever
m e−xm < +∞(cid:4)

.r =

Dr/2

(2.7)

(cid:8)

ˆθ is almost surely ﬁnite and

(2.8)

Ɛs

(cid:7)(cid:17)
(cid:17)
(cid:17)
(cid:17)

ˆθ − θ −

2L(cid:2)s(cid:3)
√
n

(cid:17)
r(cid:9)
(cid:17)
(cid:17)
(cid:17)

≤ inf
m∈(cid:7)

Ɛs

− ˆθm + θ +

2L(cid:2)s(cid:3)
√
n

(cid:13)r

(cid:9)

+

+ C1(cid:2)r(cid:3)

(cid:2).r + 1(cid:3)
nr

(cid:4)

m∈(cid:7)

(cid:7)(cid:11)

where C1(cid:2)r(cid:3) is some numerical constant depending only on r. Moreover, for
any m ∈ (cid:7) ,

(cid:7)(cid:11)

Ɛs

− ˆθm + θ +

2L(cid:2)s(cid:3)
√
n

(cid:13)r

(cid:9)

+

(cid:7)

≤ C2(cid:2)r(cid:3)

(cid:1)s − sm(cid:1)2r +
(cid:11)

(2.9)

(cid:2)Dr/2
m + 1(cid:3)
nr

(cid:13)r (cid:9)

(cid:4)

Dm
n

+

pen(cid:2)m(cid:3) −

where sm is the orthogonal projection of s over Sm and C2(cid:2)r(cid:3) is a numerical
constant depending only on r.

Comments.

(i) There is some ambiguity in the deﬁnition of (cid:13)Y(cid:2)t(cid:3)(cid:4) t ∈ (cid:1)(cid:14)
since the isonormal process (cid:13)L(cid:2)t(cid:3)(cid:4) t ∈ (cid:1)(cid:14) is deﬁned up to some negligible event
that may change for each t ∈ (cid:1). In other words, if (cid:1) is inﬁnite dimensional,
one cannot guarantee that there exists a given version of (cid:13)L(cid:2)t(cid:3)(cid:4) t ∈ (cid:1)(cid:14) such
that L(cid:2)t(cid:3)(cid:2)ω(cid:3) is linear with respect to t for almost all ω ∈ (cid:11). Nevertheless, the
deﬁnition of our estimator only involves some given countable collection of
ﬁnite-dimensional linear subspaces (cid:2)Sm(cid:3)m∈(cid:7) and (cid:13)Y(cid:2)t(cid:3)(cid:4) t ∈
m∈(cid:7) Sm(cid:14). It is
easy to see that there exists some version of L which is linear on the algebraic
linear span S of
m∈(cid:7) Sm and such a version is implicitly used to deﬁne a
linear version of Y on S.

(cid:18)

(cid:18)

(ii) If (cid:7) is ﬁnite, then any possible ˆm which minimizes −(cid:1) ˆsm(cid:1)2 + pen(cid:2)m(cid:3)
leads to the same value for ˆθ ˆm which is precisely our estimator ˆθ = supm∈(cid:7)
ˆθm.
If (cid:7) is inﬁnite, there is no guarantee that the minimum of −(cid:1) ˆsm(cid:1)2 +pen(cid:2)m(cid:3) is
achieved. Nevertheless, it always makes sense to consider ˆθ = supm∈(cid:7)
ˆθm; this
is the reason why we use such a deﬁnition of ˆθ in the statement of Theorem 1
rather than ˆθ = ˆθ ˆm. Moreover, Theorem 1 ensures that ˆθ is fortunately almost
surely ﬁnite.

(iii) When applying Theorem 1, we shall generally take pen(cid:2)m(cid:3) as small as

permitted; that is,

pen(cid:2)m(cid:3) =

(cid:2)Dm + 1(cid:3)
n

+ 2

(cid:16)

(cid:2)Dm + 1(cid:3)xm
n

+ 2

xm
n

(cid:29)

The role of the weights (cid:2)xm(cid:3)m∈(cid:7) is therefore essential but might seem myste-
rious at a ﬁrst glance. We have indeed several possible choices for (cid:2)xm(cid:3)m∈(cid:7) .
One possibility is to choose (cid:2)xm(cid:3)m∈(cid:7) in such a way that
(2.10)

Dr/2

(cid:8)

m e−xm ≤ C(cid:23)(cid:2)r(cid:3)(cid:4)

m∈(cid:7)



<!-- pdf-page: 10 -->
ESTIMATION OF A QUADRATIC FUNCTIONAL

1311

where C(cid:23)(cid:2)r(cid:3) is some numerical constant depending only on r. Combining (2.8)
and (2.9) leads, under this assumption, to

(cid:7)(cid:17)
(cid:17)
(cid:17)
(cid:17)

Ɛs

ˆθ − θ −

r(cid:9)

(cid:17)
(cid:17)
(cid:17)
(cid:17)

2L(cid:2)s(cid:3)
√
n

(cid:7)

≤ C(cid:23)(cid:23)(cid:2)r(cid:3) inf
m∈(cid:7)

(cid:1)s − sm(cid:1)2r +
(cid:11)

(2.11)

(cid:2)Dr/2
m + 1(cid:3)
nr

(cid:13)r(cid:9)

(cid:29)

Dm
n

+

pen(cid:2)m(cid:3) −

(iv) One can derive from (2.11) two kinds of information about the behavior

of ˆθ. One possibility is to analyze the risk of ˆθ. We readily get from (2.11),
(cid:7)

(cid:21)

(cid:19)(cid:17)
(cid:17) ˆθ − θ

(cid:17)
(cid:17)r

(cid:20)

Ɛs

(2.12)

≤ 2(cid:2)r−1(cid:3)+

C(cid:23)(cid:23)(cid:2)r(cid:3) inf
m∈(cid:7)

(cid:1)s − sm(cid:1)2r +

(cid:11)

+

pen(cid:2)m(cid:3) −

(cid:2)Dr/2
m + 1(cid:3)
nr
(cid:13)
r

(cid:9)

Dm
n

+

(cid:22)

Ɛ(cid:2)(cid:19)ξ(cid:19)r(cid:3)

2r(cid:1)s(cid:1)r
nr/2

where ξ is a standard normal variable. We shall study in the next section
several examples for which (2.12) leads to upper bounds for the maximal risk
of ˆθ over various sets of parameters.

Another possibility is to use (2.11) for asymptotic analysis, which means
that n goes to inﬁnity. Taking r = 1, if we have chosen the weights (cid:2)xm(cid:3)m∈(cid:7)
such that (2.10) holds, then inequality (2.11) shows that whenever

(cid:7)

inf
m∈(cid:7)

(cid:1)s − sm(cid:1)2 +

D1/2
m
n

(cid:11)

+

pen(cid:2)m(cid:3) −

(cid:13)(cid:9)

Dm
n

= o(cid:2)1/

√

n(cid:3)(cid:4)

√

n(cid:2) ˆθ − θ(cid:3) − 2L(cid:2)s(cid:3) converges towards 0 in probability. Recalling that L(cid:2)s(cid:3)
then
is a centered Gaussian variable with variance θ, we see that, if the Hilbert
space (cid:1) does not depend on n, θ = (cid:1)s(cid:1)2 is also independent of n, and therefore
√

n(cid:2) ˆθ − θ(cid:3) is asymptotically centered normal with variance 4θ.
We intend to apply Theorem 1 to show that our estimator is adaptive in var-
ious classes of parameter sets. Since we have in view to prove that in many
situations our estimator is asymptotically efﬁcient, it is convenient to deal
from now on with the case where (cid:1) is a given inﬁnite-dimensional Hilbert
space, although our theorem clearly also applies when (cid:1) is ﬁnite-dimensional
with dimension depending on n, as in the example of the ﬁxed design regres-
sion model. We recall below the correspondence between classes of functions
in (cid:3)2(cid:2)(cid:11)0(cid:4) 1(cid:12)(cid:3) like H¨olderian, Sobolev or Besov balls and classes of sequences
in l2(cid:2)(cid:2)∗(cid:3) like hyperrectangles, ellipsoids, lp or Besov bodies via some proper
choice of a basis. This will motivate the study of the properties of our penalized
estimator within the framework of the Gaussian sequence model. This study
will be performed in Section 3 where the adaptive properties of the penalized
estimator over various bodies in l2(cid:2)(cid:2)∗(cid:3) will be exhibited.

2.4. Smoothness classes and bodies in l2(cid:2)(cid:2)∗(cid:3). We want to make precise the
correspondence between classes of functions included in (cid:3)2(cid:2)(cid:11)0(cid:4) 1(cid:12)(cid:3) and sets of



<!-- pdf-page: 11 -->
1312

B. LAURENT AND P. MASSART

coefﬁcients. Many classes of functions can indeed be described by the proper-
ties of their expansions on a suitable basis. For the sake of simplicity, we shall
content ourselves with dealing with the Haar basis and control the variations
of a function with the help of moduli of continuity. However, more general
wavelet expansions and moduli of smoothness could be considered as well [we
refer to Donoho and Johnstone (1998) for more details].

Following DeVore and Lorentz (1993), the (cid:3)p-modulus of continuity ω(cid:2)s(cid:4) y(cid:3)p

is deﬁned by

(cid:2)ω(cid:2)s(cid:4) y(cid:3)p(cid:3)p = sup
0<h≤y

(cid:15) 1−h

0

and for p = ∞,

(cid:19)s(cid:2)x + h(cid:3) − s(cid:2)x(cid:3)(cid:19)p dx for 0 < y(cid:4) if 0 < p < ∞(cid:4)

ω(cid:2)s(cid:4) y(cid:3)∞ = sup
0<h≤y

sup
x∈(cid:11)0(cid:4) 1−h(cid:12)

(cid:19)s(cid:2)x + h(cid:3) − s(cid:2)x(cid:3)(cid:19)(cid:29)

Let 0 < α < 1, 0 < p(cid:4) q ≤ ∞, the function s belongs to the Besov space
(cid:11)α

p(cid:4) q(cid:2)(cid:11)0(cid:4) 1(cid:12)(cid:3), if and only if s ∈ (cid:3)p(cid:2)(cid:11)0(cid:4) 1(cid:12)(cid:3) and
(cid:8)

(cid:19)s(cid:19)q

α(cid:4) p(cid:4) q =

2jαqωq(cid:2)s(cid:4) 2−j(cid:3)p < +∞ when 0 < q < +∞(cid:4)

j≥0

(cid:19)s(cid:19)α(cid:4) p(cid:4) ∞ = sup
j≥0

2jαω(cid:2)s(cid:4) 2−j(cid:3)p < +∞ when q = +∞(cid:29)

We recall that α > (cid:2)1/p − 1/2(cid:3)+ warrants that (cid:11)α

p(cid:4) q(cid:2)(cid:11)0(cid:4) 1(cid:12)(cid:3) ⊂ (cid:3)2(cid:2)(cid:11)0(cid:4) 1(cid:12)(cid:3).

We turn now to the correspondence between Besov balls and bodies in a
sequence space via Haar expansions. Let ψ = (cid:1)(cid:11)0(cid:4) 1/2(cid:11) − (cid:1)(cid:11)1/2(cid:4) 1(cid:11), and for any
integers j and k, ψj(cid:4) k(cid:2)·(cid:3) = 2j/2ψ(cid:2)2j(cid:29) − k(cid:3). Any function s ∈ (cid:3)2(cid:2)(cid:11)0(cid:4) 1(cid:12)(cid:3) can be
expanded as

s =

(cid:15) 1

0

s(cid:2)x(cid:3) dx +

(cid:8)

2j(cid:8)

j≥0

k=1

βj(cid:4) kψj(cid:4) k(cid:4)

(cid:2) 1
0 s(cid:2)x(cid:3)ψj(cid:4) k(cid:2)x(cid:3) dx. Let (cid:18) = (cid:13)(cid:2)j(cid:4) k(cid:3) ∈ (cid:2)2(cid:4) k ∈ (cid:13)1(cid:4) (cid:29) (cid:29) (cid:29) (cid:4) 2j(cid:14)(cid:14),
where βj(cid:4) k =
(cid:4) (cid:1)2j
(cid:5)1/p if p < ∞ and (cid:19)β(cid:19)j(cid:4) ∞ =
for any integer j. We set (cid:19)β(cid:19)j(cid:4) p =
supk∈(cid:13)1(cid:4)(cid:29)(cid:29)(cid:29)(cid:4)2j(cid:14) (cid:19)βj(cid:4) k(cid:19). The size of the coefﬁcients of s depends on the modulus of
continuity. This can be seen by using the following classical inequality [see
Devore, Jawerth and Popov (1992)], for all j ≥ 0 and p ≥ 1:

k=1 (cid:19)βj(cid:4) k(cid:19)p

(2.13)

2j(cid:2)1/2−1/p(cid:3)(cid:19)β(cid:19)j(cid:4) p ≤ Cp ω(cid:2)s(cid:4) 2−j(cid:3)p(cid:4)

where Cp is a constant depending only on p.

Assume ﬁrst that p ≥ 1. It follows from (2.13) that if s belongs to some

Besov ball with respect to the seminorm (cid:19) · (cid:19)α(cid:4) p(cid:4) q, that is,
(cid:8)

2jαqωq(cid:2)s(cid:4) 2−j(cid:3)p ≤ Qq

j≥0



<!-- pdf-page: 12 -->
ESTIMATION OF A QUADRATIC FUNCTIONAL

1313

for some Q > 0, then

(2.14)

(cid:8)

j≥0

2qj(cid:2)1/2+(cid:2)α−1/p(cid:3)(cid:3)(cid:19)β(cid:19)q

j(cid:4) p ≤ Rq(cid:4)

where R = CpQ. Similarly, if s belongs to some Besov ball with respect to the
seminorm (cid:19) · (cid:19)α(cid:4) p(cid:4) ∞, that is,

2jαω(cid:2)s(cid:4) 2−j(cid:3)p ≤ Q

sup
j≥0

for some Q > 0, then

(2.15)

∀ j ∈ (cid:2)(cid:4)

(cid:19)β(cid:19)j(cid:4) p ≤ R2−j(cid:2)1/2+(cid:2)α−1/p(cid:3)(cid:3)(cid:29)

We can more generally consider the class of functions s satisfying

(cid:8)

j≥0

ωp(cid:2)s(cid:4) 2−j(cid:3)p
wp(cid:2)2−j(cid:3)

< +∞

if p < ∞ where w is a given positive function on [0,1]. Note that the Besov
p(cid:4) p(cid:2)(cid:11)0(cid:4) 1(cid:12)(cid:3) corresponds to the situation where w(cid:2)x(cid:3) = xα. Assume that
space (cid:11)α

(cid:8)

j≥0

ωp(cid:2)s(cid:4) 2−j(cid:3)p
wp(cid:2)2−j(cid:3)

< +∞(cid:29)

It follows from inequality (2.13) that β ∈ l2(cid:2)(cid:18)(cid:3) provided that x (cid:30)→ w(cid:2)x(cid:3)x1/2−1/p
is nondecreasing (and therefore bounded) if p ≤ 2 and provided that
(cid:1)

j≥0(cid:2)w(cid:2)2−j(cid:3)(cid:3)(cid:2)1/2−1/p(cid:3)−1 < +∞ if p > 2. Moreover if

then

(2.16)

(cid:8)

j≥0

ωp(cid:2)s(cid:4) 2−j(cid:3)p
wp(cid:2)2−j(cid:3)

≤ Qp(cid:4)

(cid:19)β(cid:19)p
Rp2pj(cid:2)1/p−1/2(cid:3)wp(cid:2)2−j(cid:3)

j(cid:4) p

≤ 1(cid:29)

(cid:8)

j≥0

Similarly, if supj≥0(cid:2)ω(cid:2)s(cid:4) 2−j(cid:3)∞/w(cid:2)2−j(cid:3)(cid:3) ≤ Q, then

(2.17)

(cid:19)β(cid:19)j(cid:4) ∞
R2−1/2w(cid:2)2−j(cid:3)

sup
j≥0

≤ 1(cid:29)

The case 0 < p < 1 is more involved since in this case (2.13) is not available.
However, it is still true that the Besov ball with respect to the seminorm
(cid:19) · (cid:19)α(cid:4) p(cid:4) q is included in a Besov body deﬁned by (2.14) if q < ∞ or (2.15) if
q = ∞, for an appropriate value of R. See Devore, Kyriasis, Leviatan and
Tikhomirov (1993).

If we order the countable set (cid:18) with the lexicographical ordering, we can
identify (cid:18) with (cid:2)∗. As shown by the computations above, conditions on the
moduli of continuity of s can be transferred to conditions on the sequence β of



<!-- pdf-page: 13 -->
1314

B. LAURENT AND P. MASSART

coefﬁcients of s. This motivates the following formal deﬁnitions of bodies in
l2(cid:2)(cid:2)∗(cid:3), that we shall use below. We begin with lp-bodies.

Definition 1. Let 0 < p ≤ ∞ and c be some positive and nonincreasing

sequence. We deﬁne the lp-body :p(cid:4) c as
(cid:17)
(cid:17)
(cid:17)
(cid:17)

β ∈ lp(cid:2)(cid:2)∗(cid:3)(cid:4)

:p(cid:4) c =

(cid:8)

(cid:23)

(cid:23)

λ∈(cid:2)∗

:∞(cid:4) c =

β ∈ l∞(cid:2)(cid:2)∗(cid:3)(cid:4) sup
λ∈(cid:2)∗

(cid:17)
p
(cid:17)
(cid:17)
(cid:17)

(cid:24)

≤ 1

if p < ∞(cid:4)

(cid:24)

(cid:17)
(cid:17)
(cid:17)
(cid:17) ≤ 1

if p = ∞(cid:29)

βλ
cλ

(cid:17)
(cid:17)
(cid:17)
(cid:17)

βλ
cλ

Note that an lp-body is always included in l2(cid:2)(cid:2)∗(cid:3) for p ≤ 2. If p > 2, H¨older’s
inequality warrants that :p(cid:4) c ⊂ l2(cid:2)(cid:2)∗(cid:3) whenever

(2.18)

(cid:8)

λ∈(cid:2)∗

c(cid:2)1/2−1/p(cid:3)−1
λ

< ∞(cid:29)

Moreover, :p(cid:4) c is an ellipsoid when p = 2 and an hyperrectangle when p = ∞.
We shall also deal with the scale of Besov bodies as introduced in Donoho

and Johnstone (1998).

Definition 2. Let 0 < p(cid:4) q ≤ ∞(cid:4) α > 0, and R > 0. Assume that α(cid:23) =
j≥0 (cid:18)(cid:2)j(cid:3), where (cid:18)(cid:2)j(cid:3) =

1/2 + α − 1/p > 0. Given the partition of (cid:2)∗(cid:4) (cid:2)∗ =
(cid:13)2j(cid:4) (cid:29) (cid:29) (cid:29) (cid:4) 2j+1 − 1(cid:14), we deﬁne the Besov body (cid:11)α(cid:4) p(cid:4) q(cid:2)R(cid:3) as

(cid:1)

(cid:11)α(cid:4) p(cid:4) q(cid:2)R(cid:3) =

(cid:25)

(cid:11)α(cid:4) p(cid:4) ∞(cid:2)R(cid:3) =

(cid:25)

β ∈ l2(cid:2)(cid:2)∗(cid:3)(cid:4)

(cid:8)

j≥0

(cid:19)β(cid:19)q

j(cid:4) p2qjα(cid:23) ≤ Rq

(cid:26)

if q < ∞(cid:4)

β ∈ l2(cid:2)(cid:2)∗(cid:3)(cid:4) sup
j≥0

(cid:19)β(cid:19)j(cid:4) p2jα(cid:23) ≤ R

(cid:26)

if q = ∞(cid:4)

where (cid:19)β(cid:19)p

j(cid:4) p =

(cid:1)

λ∈(cid:18)(cid:2)j(cid:3) (cid:19)βλ(cid:19)p

if p < ∞ and (cid:19)β(cid:19)j(cid:4) ∞ = supλ∈(cid:18)(cid:2)j(cid:3) (cid:19)βλ(cid:19).

(cid:11)α(cid:4) p(cid:4) p(cid:2)R(cid:3) is essentially an lp-body and does not bring anything new. This is
not the case for (cid:11)α(cid:4) p(cid:4) ∞(cid:2)R(cid:3) which contains (cid:11)α(cid:4) p(cid:4) p(cid:2)R(cid:3) and that we shall use
in the sequel.

All these bodies play a role when expressing smoothness constraints on
the function s through constraints on its sequence of coefﬁcients β. Indeed,
inequalities (2.14) and (2.15) ensure that whenever s belongs to some Besov
ball with respect to the seminorm (cid:19) · (cid:19)α(cid:4) p(cid:4) q then β belongs to some Besov body
(cid:11)α(cid:4) p(cid:4) q(cid:2)R(cid:3), while (2.16) and (2.17) express that more general conditions on the
modulus of continuity of s imply that β belongs to some adequate lp-body.

3. The Gaussian sequence model. A reasonable strategy to estimate
(cid:1)s(cid:1)2 when s belongs to some inﬁnite-dimensional separable Hilbert space and
one observes (2.1) can be described as follows. Let (cid:2)φλ(cid:3)λ∈(cid:18) be some orthonormal
basis of (cid:1). One can always assume that (cid:18) = (cid:18)0 ∪(cid:2)∗ where (cid:18)0 is a ﬁnite subset



<!-- pdf-page: 14 -->
ESTIMATION OF A QUADRATIC FUNCTIONAL

1315

of (cid:12)− which does not depend on n. Think here that this is typically what one
gets when considering the Haar basis in (cid:3)2(cid:2)(cid:11)0(cid:4) 1(cid:12)(cid:3), taking φ0 = (cid:1)(cid:11)0(cid:4) 1(cid:12), and
(cid:2)φλ(cid:3)λ∈(cid:2)∗ as the ordered (cid:2)ψj(cid:4) k(cid:3)j≥0(cid:4) 1≤k≤2j. Then
(cid:8)

(cid:1)s(cid:1)2 = (cid:1)s0(cid:1)2 +

β2
λ(cid:4)

λ∈(cid:2)∗

where s0 is the orthogonal projection of s onto the linear span of (cid:2)φλ(cid:3)λ∈(cid:18)0
.
One can estimate (cid:1)s0(cid:1)2 by (cid:1) ˆs0(cid:1)2 − (cid:19)(cid:18)0(cid:19)/n, where ˆs0 stands for the projection
estimator on the linear span of (cid:2)φλ(cid:3)λ∈(cid:18)0
. This estimator has a quadratic risk
of order 1/n and is moreover efﬁcient which means that

(cid:11)

√

n

(cid:1) ˆs0(cid:1)2 −

(cid:19)(cid:18)0(cid:19)
n

(cid:13)

− (cid:1)s0(cid:1)2

(cid:13)
−→ (cid:9) (cid:2)0(cid:4) 4(cid:1)s0(cid:1)2(cid:3)(cid:29)

λ∈(cid:2)∗ β2

The problem of estimating properly (cid:1)s(cid:1)2 reduces to that of estimating (cid:19)β(cid:19)2 =
(cid:1)
λ. This can be done on the basis of the observation of the Gaussian
sequence model (2.3) where the errors ελ are deﬁned by ελ = L(cid:2)φλ(cid:3). Any
estimator Tn of (cid:19)β(cid:19)2 built from the sequence (cid:2)Yλ(cid:3)λ∈(cid:2)∗ leads to the deﬁnition of
n = (cid:1) ˆs0(cid:1)2 − (cid:19)(cid:18)0(cid:19)/n + Tn. Since (cid:19)(cid:18)0(cid:19) does not
an estimator of (cid:1)s(cid:1)2 by taking T(cid:23)
depend on n, the quadratic risk of T(cid:23)
n will stay of the same order as that of
Tn and, moreover, if Tn is efﬁcient which means that
n(cid:2)Tn − (cid:19)β(cid:19)2(cid:3) (cid:13)−→ (cid:9) (cid:2)0(cid:4) 4(cid:19)β(cid:19)2(cid:3)(cid:4)

√

√

then since ˆs0 is independent of Tn(cid:4) T(cid:23)

n is also efﬁcient; that is,

n(cid:2)Tn − (cid:19)β(cid:19)2(cid:3) (cid:13)−→ (cid:9) (cid:2)0(cid:4) 4(cid:1)s(cid:1)2(cid:3)(cid:29)
Hence, all through this section, we shall focus on the problem of estimating
(cid:19)β(cid:19)2 when one observes the Gaussian sequence model (2.3), and produce esti-
mators which are adaptive on a variety of bodies of l2(cid:2)(cid:2)∗(cid:3). To do so, we shall
consider several examples of collections of subsets (cid:13)(cid:18)m(cid:4) m ∈ (cid:7) (cid:14) of (cid:2)∗ and the
corresponding collection of models (cid:13)Sm(cid:4) m ∈ (cid:7) (cid:14), where for any m ∈ (cid:7) ,

Sm = (cid:13)β ∈ l2(cid:2)(cid:2)∗(cid:3)(cid:4) βλ = 0 ∀λ /∈ (cid:18)m(cid:14)(cid:29)
Then we shall deﬁne appropriate penalty functions and consider the corre-
sponding penalized estimators of (cid:19)β(cid:19)2 as given by (2.6).

3.1. lp-bodies for p ≥ 2. The deﬁnition of the penalized estimator that we

shall consider throughout this section is as follows.

Definition 3. Let (cid:7) = (cid:2)∗ and K be some given real number, K > 1. For

all m ∈ (cid:7) , we set xm = K log(cid:2)m + 1(cid:3) and
(cid:12)

n pen(cid:2)m(cid:3) = m + 1 + 2

(cid:2)m + 1(cid:3)xm + 2xm(cid:29)

We deﬁne ˆθ by

ˆθ = sup
m∈(cid:7)

(cid:11) m(cid:8)

λ=1

(cid:13)

Y2

λ − pen(cid:2)m(cid:3)

(cid:29)



<!-- pdf-page: 15 -->
1316

B. LAURENT AND P. MASSART

We introduce a new body which will turn out to be convenient since it contains
in some sense lp-bodies for p ≥ 2. Let γ = (cid:2)γm(cid:3)m∈(cid:2)∗ be some nonincreasing
and nonnegative sequence and (cid:5)γ be the subset of l2(cid:2)(cid:2)∗(cid:3) deﬁned by

(cid:23)

(cid:24)

(3.1)

(cid:5)γ =

β ∈ l2(cid:2)(cid:2)∗(cid:3)(cid:4) ∀ m ∈ (cid:2)∗(cid:4)

λ ≤ γ2
β2
m

(cid:29)

(cid:8)

λ>m

The following theorem gives a uniform risk bound for the penalized estimator
of Deﬁnition 3 over the set (cid:5)γ.

Theorem 2. Assume that one observes (cid:2)Yλ(cid:3)λ∈(cid:2)∗ given by the Gaussian seq-
uence model (2.3) and set β = (cid:2)βλ(cid:3)λ∈(cid:2)∗(cid:4) θ =
λ∈(cid:2)∗ βλελ.
Let K be some constant such that K > 1 and ˆθ be the corresponding penalized
estimator given by Deﬁnition 3. Let (cid:5)γ be deﬁned by (3.1). For any r such that
r < 2(cid:2)K − 1(cid:3), the following inequality holds:
(cid:7)

λ, and L(cid:2)β(cid:3) =

λ∈(cid:2)∗ β2

(cid:1)

(cid:1)

(cid:11)

(cid:7)(cid:17)
(cid:17)
(cid:17)
(cid:17)

Ɛβ

sup
β∈(cid:5)γ

ˆθ − θ −

(cid:17)
r(cid:9)
(cid:17)
(cid:17)
(cid:17)

2L(cid:2)β(cid:3)
√
n

≤ C(cid:2)r(cid:3) inf
m∈(cid:2)∗

γ2r
m +

m log(cid:2)m + 1(cid:3)
n2

(cid:13)r/2(cid:9)

(cid:4)

where C(cid:2)r(cid:3) is some constant depending only on r.

Comments.

(i) Although the above result is not asymptotic, we can use it

to derive asymptotic properties for our estimator: if the term

(cid:7)

(cid:11)

inf
m∈(cid:2)∗

γ2r
m +

m log(cid:2)m + 1(cid:3)
n2

(cid:13)r/2(cid:9)

is negligible as compared to n−r/2, then ˆθ is an efﬁcient estimator of θ. This
will depend on the structure of the sequence γ = (cid:2)γm(cid:3)m∈(cid:2)∗.

(ii) An ellipsoid :2(cid:4) c deﬁned by Deﬁnition 1 is included in the set (cid:5)γ if we
set γm = cm ∀ m ∈ (cid:2)∗. This is also the case for a hyperrectangle :∞(cid:4) c deﬁned
by Deﬁnition 1 if we set γ2
λ and for an lp-body :p(cid:4) c with p > 2
λ∈(cid:2)∗ c(cid:2)1/2−1/p(cid:3)−1
(cid:3)1/2−1/p. This means
and
that Theorem 2 can be used to analyze the behavior of our estimator on some
arbitrary lp-body with p ≥ 2.

< ∞ if we set γm = (cid:2)

λ>m c(cid:2)1/2−1/p(cid:3)−1

λ>m c2

m =

(cid:1)

(cid:1)

(cid:1)

λ

λ

It is interesting to look at the particular situation where γm = Rm−α. Let
us denote by (cid:5)α(cid:2)R(cid:3) the corresponding set (cid:5)γ. We derive from Comment (ii)
above that the following lp-bodies are all included in (cid:5)α(cid:2)R(cid:3):

(3.2)

(cid:14)p(cid:4) α(cid:23) (cid:2)R(cid:23)(cid:3) =

γ ∈ l2(cid:2)(cid:2)∗(cid:3)(cid:4)

(cid:23)

(cid:23)

(cid:8)

λ∈(cid:2)∗

λpα(cid:23) (cid:19)γλ(cid:19)p ≤ (cid:2)R(cid:23)(cid:3)p

(cid:24)

(cid:24)

if 2 ≤ p < ∞(cid:4)

(3.3)

(cid:14)∞(cid:4) α(cid:23) (cid:2)R(cid:23)(cid:3) =

γ ∈ l2(cid:2)(cid:2)∗(cid:3)(cid:4) ∀ λ ∈ (cid:2)∗(cid:4) (cid:19)γλ(cid:19) ≤ R(cid:23)λ−α(cid:23)

if p = ∞(cid:4)

where α(cid:23) = 1/2 + α − 1/p(cid:4) R(cid:23) = R if p = 2 and R(cid:23) = R(cid:2)α/(cid:2)1/2 − 1/p(cid:3)(cid:3)1/2−1/p
otherwise.



<!-- pdf-page: 16 -->
ESTIMATION OF A QUADRATIC FUNCTIONAL

1317

√

It should be noticed that (cid:5)α(cid:2)R(cid:3) is included in (cid:11)α(cid:4) 2(cid:4) ∞(cid:2)R(cid:3) which is easily
seen to be included in (cid:5)α(cid:2)R22α/
2α − 1(cid:3). This allows us to derive the fol-
lowing corollary of Theorem 2 which provides uniform risk bounds for the
penalized estimator given by Deﬁnition 3. Given α > 0(cid:4) R > 0, these risk
bounds are uniform over the Besov body (cid:11)α(cid:4) 2(cid:4) ∞(cid:2)R(cid:3), and therefore over the
lp-body (cid:14)p(cid:4)α(cid:23) (cid:2)R(cid:23)(cid:3) for p ≥ 2 and α(cid:23) = 1/2 + (cid:2)α − 1/p(cid:3), where R(cid:23) = R if p = 2,
and R(cid:23) = R(cid:2)α/(cid:2)1/2 − 1/p(cid:3)(cid:3)1/2−1/p otherwise.

Corollary 1. Assume that one observes (cid:2)Yλ(cid:3)λ∈(cid:2)∗ given by the Gaussian
sequence model (2.3). Let β = (cid:2)βλ(cid:3)λ∈(cid:2)∗ and θ =
λ. Let K be some
constant such that K > 1 and ˆθ be the corresponding penalized estimator given
by Deﬁnition 3. Assume that r is some positive real number which satisﬁes
r < 2(cid:2)K − 1(cid:3). For any R > 0 and α > 0(cid:4) let the Besov body (cid:11)α(cid:4) 2(cid:4) ∞(cid:2)R(cid:3) be
deﬁned by Deﬁnition 2.

λ∈(cid:2)∗ β2

(cid:1)

Assume that nR2 ≥ 1, then
r(cid:9)

(cid:7)(cid:17)
(cid:17)
(cid:17)
(cid:17)

ˆθ − θ −

(cid:17)
(cid:17)
(cid:17)
(cid:17)

2L(cid:2)s(cid:3)
√
n

sup
s∈(cid:11)α(cid:4) 2(cid:4) ∞(cid:2)R(cid:3)

Ɛs

(cid:7)

(cid:11)

≤ C(cid:2)r(cid:4) α(cid:3)

R2r/(cid:2)1+4α(cid:3)

log(cid:2)1 + nR2(cid:3)
n2

(cid:13)2rα/(cid:2)1+4α(cid:3)(cid:9)

(cid:4)

where C(cid:2)r(cid:4) α(cid:3) depends only on r and α. This leads to:

(i) If α ≤ 1/4,

(3.4)

sup
β∈(cid:11)α(cid:4) 2(cid:4) ∞(cid:2)R(cid:3)

Ɛβ

(ii) if α > 1/4,

(3.5)

(cid:3)

(cid:19) ˆθ − θ(cid:19)r

(cid:6)

≤ C(cid:23)(cid:2)r(cid:4) α(cid:3)

(cid:7)
R2r/(cid:2)1+4α(cid:3)

(cid:11)

log(cid:2)1 + nR2(cid:3)
n2

(cid:13)2rα/(cid:2)1+4α(cid:3)(cid:9)

(cid:31)

sup
β∈(cid:11)α(cid:4) 2(cid:4) ∞(cid:2)R(cid:3)

Ɛβ

(cid:3)

(cid:19) ˆθ − θ(cid:19)r

(cid:6)

≤ C(cid:23)(cid:2)r(cid:4) α(cid:3)

Rr
nr/2

(cid:4)

where C(cid:23)(cid:2)r(cid:4) α(cid:3) depends only on r and α.

If the sequence β = (cid:2)βλ(cid:3)λ∈(cid:2)∗ belongs to the Besov body (cid:11)α(cid:4) 2(cid:4) ∞(cid:2)R(cid:3) for some

α > 1/4, then

(3.6)

(3.7)

(cid:3)

nr/2Ɛβ

√

(cid:6)

n(cid:2) ˆθ − θ(cid:3) (cid:13)→ (cid:9) (cid:2)0(cid:4) 4θ(cid:3) as n → ∞(cid:4)

(cid:19) ˆθ − θ(cid:19)r

→ 2rθr/2Ɛ(cid:11)(cid:19)ξ(cid:19)r(cid:12) as n → ∞ if r ≥ 1(cid:4)

where ξ is a standard normal variable.

Comments.

(i) When R does not depend on n, the minimax rate of conver-
gence of ˆθ is (cid:2)log(cid:2)n(cid:3)/n2(cid:3)2α/(cid:2)1+4α(cid:3) if α ≤ 1/4 while if α > 1/4, (3.6) ensures that
ˆθ is an efﬁcient estimator of θ. Efro¨ımovich and Low (1996) have proved that
the logarithmic factor which appears in the rate of convergence for α < 1/4
cannot be avoided. Using Lepskii’s method for adaptation, Efro¨ımovich and
Low (1996) have also built an estimator which is adaptive on the class of
hyperrectangles (cid:14)∞(cid:4) α(cid:23) (cid:2)R(cid:3) with α(cid:23) = α + 1/2 in the sense that it achieves the
optimal rate (cid:2)log(cid:2)n(cid:3)/n2(cid:3)2α/(cid:2)1+4α(cid:3) for α < 1/4 and it is
n consistent whenever

√



<!-- pdf-page: 17 -->
1318

B. LAURENT AND P. MASSART

α ≥ 1/4. Our estimator presents the theoretical advantage that it is, moreover,
efﬁcient whenever α > 1/4 and that our risk bounds are valid for all lp-bodies
(cid:14)p(cid:4) α(cid:23) (cid:2)R(cid:3) simultaneously and not only for hyperrectangles. The estimator given
by Deﬁnition 3 is furthermore easily computable. Note also that results (3.4)
and (3.5) are non-asymptotic and allow R to depend on n.

(ii) If we modify the deﬁnition of the penalty function and take xn = 1
instead of xn = K log(cid:2)n + 1(cid:3) in Deﬁnition 3, it is easy to see that the resulting
penalized estimator ˆθ achieves the rate 1/
n when α =
1/4. Nevertheless, there is a price to pay for this: ˆθ is no longer efﬁcient for
α > 1/4 since the remainder term Rn = (cid:2)1/nr(cid:3)
m e−xm is then of
order n−r/2.

n instead of log(cid:2)n(cid:3)/

m∈(cid:7) Dr/2

(cid:1)

√

√

3.2. Arbitrary lp-bodies.

In this section, we shall propose an estimator of

θ with adaptivity properties over the set of lp-bodies,

(cid:23)

:p(cid:4) c =

γ ∈ lp(cid:2)(cid:2)∗(cid:3)(cid:4)

(cid:17)
p
(cid:17)
(cid:17)
(cid:17)

(cid:17)
(cid:17)
(cid:17)
(cid:17)

γλ
cλ

(cid:8)

λ∈(cid:2)∗

(cid:24)

≤ 1

(cid:4)

where (cid:2)cλ(cid:3)λ∈(cid:2)∗ is some positive and nonincreasing unknown sequence satisfy-
ing (2.18) if p > 2. If p ≤ 2(cid:4) :p(cid:4) c is included in :2(cid:4) c, which is itself included
in the set (cid:5)c deﬁned by (3.1). Hence, one could think of considering the esti-
mator deﬁned by Deﬁnition 3, which is furthermore known to be adaptive on
the lp-bodies for p ≥ 2, as shown in the previous section. So, let us consider,
for any m ∈ (cid:2)∗(cid:4) xm = 3 log(cid:2)m + 1(cid:3) and

(cid:12)

n pen(cid:2)m(cid:3) = m + 1 + 2

(cid:2)m + 1(cid:3)xm + 2xm(cid:29)

We deﬁne

(3.8)

ˆθ(cid:2)1(cid:3) = sup
m∈(cid:2)∗

(cid:7) m(cid:8)

λ=1

(cid:9)

Y2

λ − pen(cid:2)m(cid:3)

(cid:29)

It follows from Theorem 1 that for any p ≤ 2,
(cid:7)

(cid:7)(cid:17)
(cid:17)
(cid:17)
(cid:17)

ˆθ − θ −

r(cid:9)

(cid:17)
(cid:17)
(cid:17)
(cid:17)

2L(cid:2)β(cid:3)
√
n

sup
β∈:p(cid:4) c

Ɛβ

≤ C(cid:2)r(cid:3) inf
m∈(cid:2)∗

c2r
m +

(cid:11)

m log(cid:2)m + 1(cid:3)
n2

(cid:13)r/2(cid:9)

(cid:4)

where C(cid:2)r(cid:3) is some constant depending only on r. It turns out that this result
is too crude and that one can take advantage of the fact that, when p < 2,
nonlinear approximations perform better than linear approximations. This
invites us to consider collections of models where different models may have
the same dimension. A typical strategy of this kind can be described as follows.

We set, for any (cid:2)N(cid:4) D(cid:3) ∈ (cid:2)(cid:2)∗(cid:3)2,

(cid:11)

(3.9)

and deﬁne

xN(cid:4) D = 3D

1 + log

(cid:12)

(cid:11)

(cid:13)(cid:13)
(cid:4)

N
D

(3.10)

nw(cid:2)N(cid:4) D(cid:3) = D + 1 + 2

(cid:2)D + 1(cid:3)xN(cid:4) D + 2xN(cid:4) D(cid:29)



<!-- pdf-page: 18 -->
ESTIMATION OF A QUADRATIC FUNCTIONAL

1319

Let (cid:27)(cid:18)N(cid:4) D be a set of indices corresponding to the D largest elements of the
set (cid:13)(cid:19)Yλ(cid:19)(cid:4) λ = 1(cid:4) (cid:29) (cid:29) (cid:29) (cid:4) N(cid:14). We deﬁne

(3.11)

ˆθ(cid:2)2(cid:3) = sup
N∈(cid:2)∗

sup
1≤D≤N

(cid:9)

Y2

λ − w(cid:2)N(cid:4) D(cid:3)

(cid:29)

(cid:7)

(cid:8)

λ∈(cid:27)(cid:18)N(cid:4) D

Here ˆθ(cid:2)2(cid:3) can indeed be interpreted as a conveniently penalized estimator over
the collection of models deﬁned from the collection of all ﬁnite subsets of (cid:2)∗
(see the proof of Theorem 3). Since this collection involves an inﬁnite num-
ber of models with the same dimension, the penalty function must be taken
much larger than for the deﬁnition of ˆθ(cid:2)1(cid:3). This means that we have gained
something for the control of the bias term in the risk bound of Theorem 1 but
that simultaneously we have lost something in the variance term. The idea
is therefore to combine the two estimators and consider ˆθ = ˆθ(cid:2)1(cid:3) ∨ ˆθ(cid:2)2(cid:3) which
turns out to perform as well as ˆθ(cid:2)1(cid:3) and ˆθ(cid:2)2(cid:3).

Theorem 3. Assume that one observes (cid:2)Yλ(cid:3)λ∈(cid:2)∗ given by the Gaussian
λ∈(cid:2)∗ βλελ.

sequence model (2.3). We set β = (cid:2)βλ(cid:3)λ∈(cid:2)∗(cid:4) θ =
Let ˆθ(cid:2)1(cid:3) and ˆθ(cid:2)2(cid:3) be deﬁned by (3.8) and (3.11), respectively. We deﬁne ˆθ by

λ and L(cid:2)β(cid:3) =

λ∈(cid:2)∗ β2

(cid:1)

(cid:1)

ˆθ = ˆθ(cid:2)1(cid:3) ∨ ˆθ(cid:2)2(cid:3)(cid:29)

Let 0 < p ≤ ∞. We consider some nonincreasing and nonnegative sequence
c = (cid:2)cλ(cid:3)λ∈(cid:2)∗. There exists some absolute constant C such that the following
inequalities hold:

(i) If p < 2,

(cid:7)(cid:11)

sup
β∈:p(cid:4) c

Ɛβ

ˆθ − θ −

(cid:23)

(cid:7)

(cid:13)2(cid:9)

2L(cid:2)β(cid:3)
√
n

≤ C inf

inf
D∈(cid:2)∗

c4
D +

D log(cid:2)D + 1(cid:3)
n2

(cid:9)

(cid:4)

(cid:23)

(cid:7)(cid:28)

inf
N∈(cid:2)∗

inf
1≤D≤N

D1−2/pc2

D(cid:3)2 +

(cid:11)

D(cid:2)1 + log(cid:2)N/D(cid:3)(cid:3)
n

(cid:13)2(cid:9)

(cid:24)(cid:24)

+ c4
N

(cid:31)

(ii) if γ is a nonincreasing sequence, then

(3.12)

Ɛβ

sup
β∈(cid:5)γ

(cid:7)(cid:11)

ˆθ − θ −

2L(cid:2)β(cid:3)
√
n

(cid:13)2(cid:9)

(cid:7)

≤ C inf
D∈(cid:2)∗

γ4
D +

D log(cid:2)D + 1(cid:3)
n2

(cid:9)

(cid:29)



<!-- pdf-page: 19 -->
1320

B. LAURENT AND P. MASSART

Moreover, :2(cid:4) c ⊆ (cid:5)c and if p > 2, assuming that condition (2.18) holds, :p(cid:4) c ⊆
λ>D c(cid:2)1/2−1/p(cid:3)−1
(cid:5)γ where γ is given by γD =

(cid:5)1/2−1/p.

(cid:4)(cid:1)

λ

Comments.

Instead of ˆθ(cid:2)2(cid:3) we could as well consider the adaptive threshold
estimator ˜θ(cid:2)2(cid:3) deﬁned in the following way. For any (cid:2)N(cid:4) D(cid:3) ∈ (cid:2)(cid:2)∗(cid:3)2, we set
xN(cid:4) D = 3D(cid:2)1 + log(cid:2)N(cid:3)(cid:3), and we deﬁne

n (cid:29)w(cid:2)N(cid:4) D(cid:3) = 2D + 2

2DxN(cid:4) D + 2xN(cid:4) D(cid:29)

(cid:12)

Let

(cid:7)

˜θ(cid:2)2(cid:3) = sup
N∈(cid:2)∗

sup
A⊂(cid:13)1(cid:4)2(cid:4)(cid:29)(cid:29)(cid:29)(cid:4)N(cid:14)

λ∈A

(cid:8)

(cid:9)

Y2

λ − (cid:29)w(cid:2)N(cid:4) (cid:19)A(cid:19)(cid:3)

(cid:29)

Since (cid:29)w(cid:2)N(cid:4) (cid:19)A(cid:19)(cid:3) is proportional to the cardinality of A(cid:4) ˜θ(cid:2)2(cid:3) turns out to be
some adaptive threshold estimator. Namely,

˜θ(cid:2)2(cid:3) = sup
N∈(cid:2)∗

(cid:11) N(cid:8)

(cid:19)

λ=1

Y2

λ −

(cid:28)

2
n

(cid:12)

(cid:30)(cid:20)

1 +

6(cid:2)1 + log(cid:2)N(cid:3)(cid:3) + 3(cid:2)1 + log(cid:2)N(cid:3)(cid:3)

× (cid:1)

(cid:4)

Y2

λ>2/n

1+

√

6(cid:2)1+log(cid:2)N(cid:3)(cid:3)+3(cid:2)1+log(cid:2)N(cid:3)(cid:3)

(cid:13)

(cid:5)

(cid:29)

If we replace ˆθ(cid:2)2(cid:3) by ˜θ(cid:2)2(cid:3) in the deﬁnition of ˆθ given in Theorem 3, then the
properties of ˆθ are not as good as the properties of the estimator deﬁned in
Theorem 3; more precisely, the term log(cid:2)N/D(cid:3) appearing in the control of the
quadratic risk has to be replaced by log(cid:2)N(cid:3). However an advantage of the
adaptive threshold estimator as compared with ˆθ(cid:2)2(cid:3) could be its more explicit
expression.

We shall now give a corollary of Theorem 3 when cλ is a power of λ. Let us

therefore introduce, for any p > 0, α(cid:23) > 0 and R > 0, the lp-body

(3.13)

(cid:14)p(cid:4) α(cid:23) (cid:2)R(cid:3) =

β ∈ lp(cid:2)(cid:2)∗(cid:3)(cid:4)

(cid:23)

(cid:24)

λpα(cid:23) (cid:19)βλ(cid:19)p ≤ Rp

(cid:29)

(cid:8)

λ∈(cid:2)∗

The following corollary gives uniform risk bounds for the estimator ˆθ of
θ deﬁned in Theorem 3 over the sets (cid:14)p(cid:4) α(cid:23) (cid:2)R(cid:3) which are included in l2(cid:2)(cid:2)∗(cid:3);
namely, this is the case if α(cid:23) > 0 and α = α(cid:23) − 1/2 + 1/p > 0.

Corollary 2. One observes (cid:2)Yλ(cid:3)λ∈(cid:2)∗ given by the Gaussian sequence model
λ∈(cid:2)∗ βλελ. Let ˆθ(cid:2)1(cid:3) and

(2.3). We set β = (cid:2)βλ(cid:3)λ∈(cid:2)∗, θ =
λ, and L(cid:2)β(cid:3) =
ˆθ(cid:2)2(cid:3) be deﬁned by (3.8) and (3.11), respectively, and let

λ∈(cid:2)∗ β2

(cid:1)

(cid:1)

ˆθ = ˆθ(cid:2)1(cid:3) ∨ ˆθ(cid:2)2(cid:3)(cid:29)



<!-- pdf-page: 20 -->
ESTIMATION OF A QUADRATIC FUNCTIONAL

1321

Let p > 0, α(cid:23) > 0 and R > 0. We deﬁne α = α(cid:23) − 1/2 + 1/p and assume that
α > 0. If nR2 ≥ 1, one has:

(i) If p < 2,

(cid:10)(cid:11)

ˆθ − θ −

2L(cid:2)β(cid:3)
√
n

(cid:14)

(cid:13)2

sup
β∈(cid:14)p(cid:4) α(cid:23) (cid:2)R(cid:3)

Ɛβ

(3.14)

≤ C(cid:2)p(cid:4) α(cid:3) inf

R4/(cid:2)1+4α(cid:23)(cid:3)

(cid:23)

(cid:11)

R4/(cid:2)1+2α(cid:3)

log(cid:2)1 + nR2(cid:3)
n2

(cid:13)4α(cid:23)/(cid:2)1+4α(cid:23)(cid:3)

(cid:4)

(cid:11)

log(cid:2)1 + nR2(cid:3)
n

(cid:13)4α/(cid:2)1+2α(cid:3)(cid:24)

(cid:4)

where C(cid:2)p(cid:4) α(cid:3) is a constant depending only on p and α.

(ii) Moreover,

(3.15)

(cid:10)(cid:11)

ˆθ − θ −

2L(cid:2)β(cid:3)
√
n

(cid:14)

(cid:13)2

sup
β∈(cid:11)a(cid:4) 2(cid:4) ∞(cid:2)R(cid:3)

Ɛβ

≤ C(cid:2)α(cid:3)R4/(cid:2)1+4α(cid:3)

(cid:11)

log(cid:2)1 + nR2(cid:3)
n2

(cid:13)4α/(cid:2)1+4α(cid:3)(cid:13)

(cid:4)

where C(cid:2)α(cid:3) is a constant depending only α.

Comments.

(i) One can derive from (3.15) the same bounds as in Corol-

lary 1.

(ii) If 1 < p < 2, we obtain unusual rates of convergence, and we do not

know whether these rates are optimal or not.

(iii) Let us now discuss the efﬁciency of ˆθ. Comparing the right-hand side
of (3.14) with 1/n, one derives that if 4/3 ≤ p ≤ 2, ˆθ is an efﬁcient estimator
of θ as soon as α(cid:23) > 1/4, while if p ≤ 4/3, ˆθ is efﬁcient whenever α(cid:23) > 1 − 1/p.
In particular, for p ≤ 1, ˆθ is always efﬁcient.

(iv) One can also derive from (3.14) an upper bound for the uniform
quadratic risk of ˆθ. It sufﬁcies to notice that (cid:19)β(cid:19)2 ≤ R2 whenever β ∈ (cid:14)p(cid:4) α(cid:23) (cid:2)R(cid:3)
with p < 2. This leads via (3.14) to an upper bound for the quadratic risk
which, up to some constant depending on p and α, is equal to

(cid:31)

inf

R4/(cid:2)1+4α(cid:23)(cid:3)

(cid:11)

log(cid:2)1 + nR2(cid:3)
n2

(cid:13)4α(cid:23)/(cid:2)1+4α(cid:23)(cid:3)

(cid:4)

R4/(cid:2)1+2α(cid:3)

(cid:11)

log(cid:2)1 + nR2(cid:3)
n

(cid:13)4α/(cid:2)1+2α(cid:3)

+

R2
n

(cid:29)

It is interesting to consider some situations where Theorem 3 applies while
Corollary 2 does not. This will be the case for lp-bodies :p(cid:4) c for which p < 2
and (cid:2)cλ(cid:3)λ∈(cid:2)∗ converge very slowly towards 0; for example, if we look at the

 


<!-- pdf-page: 21 -->
1322

B. LAURENT AND P. MASSART

case where cλ = R(cid:2)log(cid:2)λ(cid:3)(cid:3)−η for some η > 0, we obtain

(cid:10)(cid:11)

(cid:14)

(cid:13)2

sup
β∈:p(cid:4) c

Ɛβ

ˆθ − θ − 2L(cid:2)β(cid:3)
n

√

(cid:25)

(3.16)

≤ C(cid:2)R(cid:4) p(cid:4) η(cid:3) inf

(cid:2)log(cid:2)1 + n(cid:3)(cid:3)−4(cid:4)

n(cid:2)2−p(cid:3)(cid:2)(cid:2)1/η(cid:3)(cid:2)1/p−1/2(cid:3)−1(cid:3) log2(cid:2)1 + n(cid:3)

(cid:26)

(cid:29)

This bound shows that the rate of convergence of the estimator ˆθ(cid:2)1(cid:3) is always
logarithmic; namely, it is equal to (cid:2)log(cid:2)1 + n(cid:3)(cid:3)−2η, while we obtain a rate
which is a negative power of n for the estimator ˆθ(cid:2)2(cid:3), and hence for ˆθ, as soon
as η > 1/p − 1/2.

(cid:1)

λ∈(cid:2)∗ β2

3.3. Special strategy for Besov bodies. We want to deal with the problem
of estimating
λ provided that the sequence (cid:2)βλ(cid:3)λ∈(cid:2)∗ belongs to some
(unknown) Besov body (cid:11)α(cid:4) p(cid:4) ∞. We begin with the simplest case where p = 2,
for which we have already proposed some adaptive estimators in Section 3.1
(see Corollary 1), our aim being here to show that the level thresholding esti-
mators considered in Johnstone (1999) can be interpreted as penalized esti-
mators.

3.3.1. Level thresholding estimators. For any j ∈ (cid:2)∗, let (cid:18)(cid:2)j(cid:3) = (cid:13)2j(cid:4) (cid:29) (cid:29) (cid:29) (cid:4)
2j+1 − 1(cid:14). Then (cid:2)∗ =
j≥0 (cid:18)(cid:2)j(cid:3). We wish to deﬁne (cid:7) as a collection of subsets
of (cid:2)∗. Let (cid:15) be the family of all subsets of (cid:13)0(cid:4) (cid:29) (cid:29) (cid:29) (cid:4) J(cid:14) where J = (cid:11)log2(cid:2)n2(cid:3)(cid:12).
We deﬁne for any (cid:15) ∈ (cid:15) ,

(cid:1)

(cid:8)

m(cid:15) =

(cid:18)(cid:2)j(cid:3)(cid:29)

Finally, let

j∈(cid:15)

!

(cid:7) =

m(cid:15) (cid:4) (cid:15) ∈ (cid:15)

"

(cid:29)

For any j ∈ (cid:2), let

(cid:12)

nw(cid:2)j(cid:3) = 2j + 1 + 2

(cid:2)2j + 1(cid:3)2C log(cid:2)2J(cid:3) + 4C log(cid:2)2J(cid:3)(cid:4)

C being some numerical constant larger than 1. Then, we deﬁne for any (cid:15) ∈ (cid:15) ,

(3.17)

pen(cid:2)m(cid:15) (cid:3) =

(cid:8)

j∈(cid:15)

w(cid:2)j(cid:3)(cid:29)

The resulting penalized estimator can be made explicit as a level thresholding
estimator which is an analogue (up to numerical constants) of the estimator
used in Donoho and Johnstone (1999). Indeed,





sup
(cid:15) ∈(cid:15)

(cid:8)



λ∈m(cid:15)

Y2

λ − pen(cid:2)m(cid:15) (cid:3)

 = sup

(cid:15) ⊂(cid:13)0(cid:4)(cid:29)(cid:29)(cid:29)(cid:4)J(cid:14)
(cid:10)

J(cid:8)

(cid:8)

=

(cid:21)

(cid:10)

(cid:8)

(cid:8)

(cid:22)(cid:14)

Y2

λ − w(cid:2)j(cid:3)

j∈(cid:15)

λ∈(cid:18)(cid:2)j(cid:3)

(cid:14)

Y2

λ − w(cid:2)j(cid:3)

(cid:1)(cid:1)

λ∈(cid:18)(cid:2)j(cid:3) Y2

λ≥w(cid:2)j(cid:3)(cid:29)

j=0

λ∈(cid:18)(cid:2)j(cid:3)



<!-- pdf-page: 22 -->
ESTIMATION OF A QUADRATIC FUNCTIONAL

1323

On the other hand, the penalty deﬁned by (3.17) satisﬁes condition (2.5) by
setting for every m ∈ (cid:7) , xm = 2C log(cid:2)2J(cid:3).

It is easy to check that the results of Corollary 1 still hold for this level
thresholding estimator. Note that a similar estimator has been introduced ﬁrst
by Gayraud and Tribouley (1999), the difference being that in their procedure
one considers

(3.18)

(cid:8)

λ∈ ˆm

Y2

λ −

D ˆm
n

(cid:4)

where ˆm = arg max

(cid:4) (cid:8)

m∈(cid:7)

λ∈m

Y2

λ − pen(cid:2)m(cid:3)

(cid:5)

, instead of

(cid:8)

λ∈ ˆm

Y2

λ − pen(cid:2) ˆm(cid:3)

as above or in Johnstone (1999). Gayraud and Tribouley’s proof relies on
asymptotic arguments and speciﬁcally deals with level thresholding estima-
tors. We do not know if in the generality of Theorem 1 the estimator (3.18)
would have the same properties as our estimator.

3.3.2. The Birg´e–Massart algorithm. Our purpose in this section is to
design a new strategy which takes advantage of the fact that β belongs to
some unknown Besov body. As compared to the strategy of the previous sec-
tion, this prior information allows using a penalized estimator involving a
smaller quantity of models. This leads to an improved risk bound. Our method
relies on the compression algorithm proposed by Birg´e and Massart (2000a).
This algorithm provides for any J ∈ (cid:2) a nonlinear approximation of β that
we denote by ˜β(cid:2)J(cid:3) such that

(3.19)

(cid:19)β − ˜β(cid:2)J(cid:3)(cid:19)2 ≤ C(cid:2)α(cid:4) p(cid:3)R2−Jα
provided that β ∈ (cid:11)α(cid:4) p(cid:4) ∞(cid:2)R(cid:3) with α > 1/p − 1/2. Setting (cid:18)(cid:2)j(cid:3) = (cid:13)2j(cid:4) (cid:29) (cid:29) (cid:29) (cid:4)
2j+1 − 1(cid:14), Birg´e and Massart’s procedure consists of retaining for each level
of resolution j a prescribed number KJ(cid:2)j(cid:3) of largest coefﬁcients (in absolute
value). For j ≤ J, one takes KJ(cid:2)j(cid:3) = 2j that is, one keeps all the coefﬁ-
cients while, for j > J, one deﬁnes KJ(cid:2)j(cid:3) = (cid:11)2J/(cid:2)j − J(cid:3)3(cid:12). Note that the
number of coefﬁcients which are kept is of order 2J. Let us now introduce the
corresponding estimation procedure for

(cid:1)

λ∈(cid:2)∗ β2
λ.

We set, for any J ∈ (cid:2),

(cid:12)

nw(cid:2)1(cid:3)(cid:2)J(cid:3) = 2J+1 + 1 + 2

2(cid:2)2J+1 + 1(cid:3) log(cid:2)2J+1(cid:3) + 4 log(cid:2)2J+1(cid:3)(cid:29)

We deﬁne

(3.20)

ˆθ(cid:2)1(cid:3) = sup
J∈(cid:2)

(cid:10)(cid:21)

J(cid:8)

(cid:8)

(cid:22)

(cid:14)

Y2
λ

− w(cid:2)1(cid:3)(cid:2)J(cid:3)

(cid:29)

j=0

λ∈(cid:18)(cid:2)j(cid:3)

We denote by (cid:27)(cid:18)J(cid:2)j(cid:3) a subset of (cid:18)(cid:2)j(cid:3) which contains the KJ(cid:2)j(cid:3) indices
corresponding to the largest values among the set (cid:13)(cid:19)Yλ(cid:19)(cid:4) λ ∈ (cid:18)(cid:2)j(cid:3)(cid:14). Let



<!-- pdf-page: 23 -->
1324

@J =

(cid:1)+∞

j=0 KJ(cid:2)j(cid:3). We set

B. LAURENT AND P. MASSART

nw(cid:2)2(cid:3)(cid:2)J(cid:3) = 10(cid:29)5(cid:2)@J + 1(cid:3)

and we deﬁne

(3.21)

ˆθ(cid:2)2(cid:3) = sup
J∈(cid:2)









+∞(cid:8)

(cid:8)

j=0

λ∈(cid:27)(cid:18)J(cid:2)j(cid:3)





Y2
λ

 − w(cid:2)2(cid:3)(cid:2)J(cid:3)

 (cid:29)

Theorem 4. Assume that one observes (cid:2)Yλ(cid:3)λ∈(cid:2)∗ given by the Gaussian
λ∈(cid:2)∗ βλAλ.

sequence model (2.3) and set β = (cid:2)βλ(cid:3)λ∈(cid:2)∗, θ =

λ, and L(cid:2)β(cid:3) =

Let ˆθ(cid:2)1(cid:3) and ˆθ(cid:2)2(cid:3) be deﬁned by (3.20) and (3.21), respectively. We deﬁne

λ∈(cid:2)∗ β2

(cid:1)

(cid:1)

ˆθ = ˆθ(cid:2)1(cid:3) ∨ ˆθ(cid:2)2(cid:3)(cid:29)

Let 0 < p ≤ +∞, α > 0, R > 0 and assume that α(cid:23) = 1/2 + α − 1/p > 0.
As soon as nR2 ≥ 1, the following inequalities hold:

(i) If p < 2,

sup
β∈(cid:11)α(cid:4) p(cid:4) ∞(cid:2)R(cid:3)

Ɛβ

(cid:10)(cid:11)

ˆθ − θ −

(cid:23)

2L(cid:2)β(cid:3)
√
n

(cid:11)

≤ C(cid:2)p(cid:4) α(cid:3) inf

R4/(cid:2)1+4α(cid:23)(cid:3)

(cid:14)

(cid:13)2

log(cid:2)1 + nR2(cid:3)
n2

(cid:13)4α(cid:23)/(cid:2)1+4α(cid:23)(cid:3)

(cid:24)

(cid:31) R4/(cid:2)1+2α(cid:3)n−4α/(cid:2)1+2α(cid:3)

(cid:4)

where C(cid:2)p(cid:4) α(cid:3) is a constant depending on p and α(cid:31)

(ii) if p ≥ 2, (cid:11)α(cid:4) p(cid:4) ∞(cid:2)R(cid:3) ⊆ (cid:11)α(cid:4) 2(cid:4) ∞(cid:2)R(cid:3) and

(cid:10)(cid:11)

ˆθ − θ −

2L(cid:2)β(cid:3)
√
n

(cid:14)

(cid:13)2

sup
β∈(cid:11)a(cid:4) 2(cid:4) ∞(cid:2)R(cid:3)

Ɛβ

≤ C(cid:2)α(cid:3)R4/(cid:2)1+4α(cid:3)

(cid:11)

log(cid:2)1 + nR2(cid:3)
n2

(cid:13)4α/(cid:2)1+4α(cid:3)

(cid:4)

where C(cid:2)α(cid:3) is a constant depending on α.

Comments.

(i) If p = q, the Besov body (cid:11)α(cid:4) p(cid:4) q(cid:2)R(cid:3) coincides with the lp-
body :p(cid:4) c if we set ∀ j ∈ (cid:2), ∀ λ ∈ (cid:18)(cid:2)j(cid:3), cλ = 2−jα(cid:23) . It is therefore interesting
to compare the results of Corollary 2 and Theorem 4 in this situation. Since
(cid:11)α(cid:4) p(cid:4) p(cid:2)R(cid:3) ⊂ (cid:11)α(cid:4) p(cid:4) ∞(cid:2)R(cid:3), Theorem 4 ensures that, for p < 2,

sup
β∈(cid:11)α(cid:4) p(cid:4) p(cid:2)R(cid:3)

Ɛβ

(cid:10)(cid:11)

ˆθ − θ −

2L(cid:2)β(cid:3)
√
n

(cid:14)

(cid:13)2

(cid:31)

≤ C(cid:2)p(cid:4) α(cid:3) inf

R4/(cid:2)1+4α(cid:23)(cid:3)

(cid:11)

log(cid:2)1 + nR2(cid:3)
n2

(cid:13)4α(cid:23)/(cid:2)1+4α(cid:23)(cid:3)

(cid:31) R4/(cid:2)1+2α(cid:3)n−4α/(cid:2)1+2α(cid:3)

(cid:4)

while in Corollary 2,
is replaced by (cid:2)n/ log(cid:2)1+
nR2(cid:3)(cid:3)−4α/(cid:2)1+2α(cid:3). Therefore, the rate obtained in Theorem 4 is a little bit better

the term n−4α/(cid:2)1+2α(cid:3)

 


<!-- pdf-page: 24 -->
ESTIMATION OF A QUADRATIC FUNCTIONAL

1325

than the rate obtained in Corollary 2 since we save a logarithmic factor. Never-
theless, Corollary 2 is in some sense more general; for example, it allows con-
sidering situations where the sequence (cid:2)cλ(cid:3)λ∈(cid:2)∗ converges very slowly towards
0 as shown by (3.16).

(ii) Since there is no major difference of behavior (in terms of risk bound)
between the estimator studied in Theorem 4 and the one studied in the pre-
vious section, the comments that we made about Corollary 2 are still valid
here.

4. Proof of the main theorem. The key tool for proving Theorem 1 is

an exponential inequality for chi-square distributions.

4.1. An exponential inequality for chi-square distributions. We indeed
prove a slightly more general inequality than what is really necessary for
the proof of Theorem 1. This generalization is painless and can prove to be
helpful for other purposes.

Lemma 1. Let (cid:2)Y1(cid:4) (cid:29) (cid:29) (cid:29) (cid:4) YD(cid:3) be i.i.d. Gaussian variables, with mean 0 and

variance 1. Let a1(cid:4) (cid:29) (cid:29) (cid:29) (cid:4) aD be nonnegative. We set

Let

(cid:19)a(cid:19)∞ = sup

i=1(cid:4)(cid:29)(cid:29)(cid:29)(cid:4)D

(cid:19)ai(cid:19)(cid:4)

(cid:19)a(cid:19)2

2 =

D(cid:8)

i=1

a2
i (cid:29)

Z =

D(cid:8)

i=1

ai(cid:2)Y2

i − 1(cid:3)(cid:29)

Then, the following inequalities hold for any positive x"

(4.1)

(4.2)

√

(cid:8)(cid:2)Z ≥ 2(cid:19)a(cid:19)2

x + 2(cid:19)a(cid:19)∞x(cid:3) ≤ exp(cid:2)−x(cid:3)(cid:4)
x(cid:3) ≤ exp(cid:2)−x(cid:3)(cid:29)

√

(cid:8)(cid:2)Z ≤ −2(cid:19)a(cid:19)2

Comments. As an immediate corollary of Lemma 1, one obtains an expo-
nential inequality for chi-square distributions. Let U be a χ2 statistic with D
degrees of freedom. For any positive x,

(4.3)

(4.4)

(cid:4)

(cid:8)

U − D ≥ 2
(cid:4)

Dx + 2x
√

(cid:8)

D − U ≥ 2

Dx

(cid:5)

≤ exp(cid:2)−x(cid:3)(cid:4)

(cid:5)

≤ exp(cid:2)−x(cid:3)(cid:29)

√

Proof of Lemma 1. Let Y a random variable with (cid:9) (cid:2)0(cid:4) 1(cid:3) distribution.

Let ψ denote the logarithm of the Laplace transform of Y2 − 1,

(cid:19)

(cid:19)

(cid:20)(cid:20)

exp(cid:2)u(cid:2)Y2 − 1(cid:3)(cid:3)

= −u − 1
2

log(cid:2)1 − 2u(cid:3)(cid:29)

ψ(cid:2)u(cid:3) = log

Ɛ

Then, for 0 < u < 1/2,

ψ(cid:2)u(cid:3) ≤

u2
(cid:2)1 − 2u(cid:3)

(cid:29)



<!-- pdf-page: 25 -->
1326

Indeed,

Therefore,

B. LAURENT AND P. MASSART

ψ(cid:2)u(cid:3) = 2u2

(cid:8)

k≥0

(cid:2)2u(cid:3)k
k + 2

and

u2
1 − 2u

(cid:8)

= u2

(cid:2)2u(cid:3)k(cid:29)

k≥0

log(cid:2)Ɛ(cid:11)euZ(cid:12)(cid:3) =

D(cid:8)

(cid:4)

(cid:3)

Ɛ

log

i=1

exp(cid:2)aiu(cid:2)Y2

i − 1(cid:3)(cid:3)

(cid:6)(cid:5)

≤

D(cid:8)

i=1

a2
i u2
1 − 2aiu

≤

(cid:19)a(cid:19)2
2u2
1 − 2(cid:19)a(cid:19)∞u

(cid:29)

We now refer to Birg´e and Massart (1998), where it is proved that if

then, for any positive x,

log(cid:2)Ɛ(cid:11)euZ(cid:12)(cid:3) ≤

vu2
2(cid:2)1 − cu(cid:3)

(cid:4)

(cid:28)

(cid:8)

Z ≥ cx +

(cid:30)

√

2vx

≤ e−x(cid:29)

Therefore (4.1) holds.

In order to prove (4.2), we just notice that for −1/2 < u < 0, ψ(cid:2)u(cid:3) ≤ u2.

This concludes the proof of Lemma 1. ✷

We are now in position to prove Theorem 1.

4.2. Proof of Theorem 1. The main issue is to prove inequality (2.8). Let

Vm = ˆθm − θ − 2L(cid:2)s(cid:3)/

Moreover, since

√

n. By deﬁnition of ˆθ,

ˆθ − θ −

2L(cid:2)s(cid:3)
√
n

= sup
m∈(cid:7)

Vm(cid:29)

(cid:17)
(cid:17)
(cid:17)
(cid:17) sup
m∈(cid:7)

(cid:7)

(cid:17)
(cid:17)
(cid:17)
(cid:17) ≤

Vm

(cid:9)

(cid:7)

(cid:9)

sup
m∈(cid:7)

(cid:2)Vm(cid:3)+

∨

inf
m∈(cid:7)

(cid:2)Vm(cid:3)−

(cid:4)

the following inequality holds:

(4.5)

(cid:7)(cid:17)
(cid:17)
(cid:17)
(cid:17) sup
m∈(cid:7)

Ɛs

(cid:17)
r(cid:9)
(cid:17)
(cid:17)
(cid:17)

≤

Vm

(cid:8)

(cid:3)

Ɛs

(cid:2)Vm(cid:3)r
+

(cid:6)

m∈(cid:7)

+ inf
m∈(cid:7)

Ɛs

(cid:3)

(cid:2)Vm(cid:3)r
−

(cid:6)

(cid:29)

We turn now to the control of Ɛs (cid:11)(cid:2)Vm(cid:3)r

+(cid:12) for all m ∈ (cid:7) ∗. Let us consider an
orthonormal basis of Sm denoted by (φλ(cid:4) λ ∈ (cid:18)m) where the cardinality of (cid:18)m
equals Dm. Let, for λ ∈ (cid:18)m, βλ = (cid:5)s(cid:4) φλ(cid:6). We recall that

(cid:8)

(cid:8)

sm =

βλφλ(cid:4)

ˆsm =

Y(cid:2)φλ(cid:3)φλ(cid:29)

λ∈(cid:18)m

λ∈(cid:18)m



<!-- pdf-page: 26 -->
ESTIMATION OF A QUADRATIC FUNCTIONAL

1327

By orthogonality, we obtain

Vm = (cid:1) ˆsm − sm(cid:1)2 − pen(cid:2)m(cid:3) + 2(cid:5)sm(cid:4) ˆsm − sm(cid:6) −

2
√
n

L(cid:2)s(cid:3) − (cid:1)s − sm(cid:1)2

=

1
n

(cid:8)

λ∈(cid:18)m

L2(cid:2)φλ(cid:3) − pen(cid:2)m(cid:3) +

2
√
n

L(cid:2)sm − s(cid:3) − (cid:1)s − sm(cid:1)2(cid:29)

Using the inequality 2ab ≤ a2 + b2 leads to

Vm ≤

1
n

(cid:8)

L2(cid:2)φλ(cid:3) − pen(cid:2)m(cid:3) +

L2(cid:2)s − sm(cid:3)
n(cid:1)s − sm(cid:1)2

(cid:29)

λ∈(cid:18)m
L2(cid:2)φλ(cid:3) is a χ2 statistic with Dm degrees of freedom.

(cid:1)

λ∈(cid:18)m

The variable Zm =
Let

Wm =

L(cid:2)s − sm(cid:3)
(cid:1)s − sm(cid:1)

(cid:29)

Wm has a (cid:9) (cid:2)0(cid:4) 1(cid:3) distribution and is independent of (L(cid:2)φλ(cid:3), λ ∈ (cid:18)m); hence, if
m, then Um is a χ2 statistic with Dm+1 degrees of freedom
we set Um = Zm+W2
and Vm ≤ Um/n − pen(cid:2)m(cid:3). Therefore, it remains to control the deviations of
Um. This can be performed via inequality (4.3) taking into account condition
(2.5) which in turn yields

where h(cid:2)ξ(cid:3) = 2

(cid:16)

(cid:8)(cid:2)nVm ≥ h(cid:2)ξ(cid:3)(cid:3) ≤ e−xme−ξ(cid:4)

(cid:2)Dm + 1(cid:3)ξ + 2ξ. Using the identity
r
nr

(cid:2)Vm(cid:3)r
+

(cid:15) ∞

Ɛs

=

(cid:3)

(cid:6)

tr−1(cid:8)(cid:2)nVm ≥ t(cid:3) dt(cid:4)

0

and the elementary inequality

h−1(cid:2)t(cid:3) ≥

t2
4(cid:2)(cid:2)Dm + 1(cid:3) + t(cid:3)

≥

t2
8(cid:2)Dm + 1(cid:3)

∧

t
8

(cid:4)

we obtain
(cid:15) +∞

0

tr−1(cid:8)(cid:2)nVm ≥ t(cid:3) dt ≤ exp(cid:2)−xm(cid:3)

(cid:7)

(cid:2)Dm + 1(cid:3)r/2

(cid:15) +∞

yr−1 exp(cid:2)−y2/8(cid:3) dy

0
(cid:15) +∞

0

(cid:9)
yr−1 exp(cid:2)−y/8(cid:3) dy

(cid:29)

+

Hence,

(cid:3)

Ɛs

(cid:2)Vm(cid:3)r
+

(cid:6)

≤

For m = 0, we similarly get Vm ≤ W2
variable. Therefore, if we deﬁne Dr by Dr = (cid:2)1/
D2r
nr

(cid:2)V0(cid:3)r
+

Ɛs

≤

(cid:3)

(cid:6)

(cid:4)

e−xmDr/2
m (cid:29)

C(cid:2)r(cid:3)
nr
0/n where W0 is a standard Gaussian
(cid:2) ∞
0 xr exp(cid:2)−x2/2(cid:3) dx, then

2π(cid:3)

√



<!-- pdf-page: 27 -->
1328

B. LAURENT AND P. MASSART

which, by (4.5), concludes the proof of (2.8). Let us now prove (2.9). We recall
that for all m ∈ (cid:7) ,

−Vm = −

Zm
n

+ pen(cid:2)m(cid:3) + (cid:1)s − sm(cid:1)2 +

2
√
n

(cid:2)L(cid:2)s − sm(cid:3)(cid:3)(cid:29)

Using the convexity, or the subadditivity of the function x → xr, whether r ≥ 1
or r < 1, we obtain

(cid:2)Vm(cid:3)r

− ≤ 4(cid:2)r−1(cid:3)+

(cid:7)

(cid:2)Dm − Zm(cid:3)r
+
nr

(cid:7)

(cid:11)

+

pen(cid:2)m(cid:3) −

(cid:13)r(cid:9)

Dm
n

+ 4(cid:2)r−1(cid:3)+

(cid:1)s − sm(cid:1)2r +

(cid:11)

(cid:13)r

(cid:3)

Ɛs

2
√
n

(cid:2)L(cid:2)s − sm(cid:3)(cid:3)r
+

(cid:9)

(cid:6)

(cid:29)

Using (4.4), we get

Moreover,

(cid:3)

Ɛs

(cid:2)Dm − Zm(cid:3)r
+

(cid:6)

≤

√

2π2r Dr/2

m rDr−1(cid:29)

(cid:3)

Ɛs

(cid:2)L(cid:2)s − sm(cid:3)(cid:3)r
+

(cid:6)

= (cid:1)s − sm(cid:1)rDr(cid:29)

Using again the inequality 2ab ≤ a2 + b2,

(cid:11)

(cid:13)r

(cid:3)

Ɛs

2
√
n

(cid:2)L(cid:2)s − sm(cid:3)(cid:3)r
+

(cid:6)

(cid:3)

≤ 2r−1Dr

n−r + (cid:1)s − sm(cid:1)2r

(cid:6)

and (2.9) follows. ✷

(cid:1)

In
5. Proofs of the results about the Gaussian sequence model.
order to prove Theorems 2, 3 and 4, we shall apply Theorem 1. We now intro-
duce some notations that will be used throughout these proofs. We consider
the Hilbert space (cid:1) = l2(cid:2)(cid:2)∗(cid:3) with its canonical basis (φλ(cid:4) λ ∈ (cid:2)∗) and recall
that when one observes (cid:2)Yλ(cid:3)λ∈(cid:2)∗, as deﬁned by (2.3), one can deﬁne a Gaussian
linear process Y(cid:2)·(cid:3) with mean s = β = (cid:2)βλ(cid:3)λ∈(cid:2)∗ and variance 1/n by setting
Y(cid:2)t(cid:3) =
λ∈(cid:2)∗ tλYλ. When applying Theorem 1, we shall consider collections of
models (cid:2)Sm(cid:3)m∈(cid:7) where Sm is deﬁned as the linear span of (φλ(cid:4) λ ∈ (cid:18)m) for
some subset (cid:18)m of (cid:2)∗ and therefore has dimension Dm = (cid:19)(cid:18)m(cid:19). The precise
description of the collection of sets (cid:2)(cid:18)m(cid:3)m∈(cid:7) will depend on the theorem to be
proved. It should be noticed that for every m ∈ (cid:7) , the orthogonal projection
of s over Sm and accordingly, the projection estimator of s over Sm, can be
described by their expansions on the basis (φλ(cid:4) λ ∈ (cid:2)∗) more preceisely,

(cid:8)

(cid:8)

sm =

βλφλ(cid:4)

ˆsm =

Yλφλ(cid:29)

λ∈λm

λ∈(cid:18)m

In the sequel, we shall denote by C some constants whose values may vary
from one line to another; we shall always mention the dependency of these
constants with respect to the parameters involved in the problem, that is, C(cid:2)α(cid:3)
stands for a constant depending only on α.



<!-- pdf-page: 28 -->
ESTIMATION OF A QUADRATIC FUNCTIONAL

1329

5.1. Proof of Theorem 2. We set here (cid:7) = (cid:2)∗ and for every m ∈ (cid:7) ,
(cid:18)m = (cid:13)1(cid:4) 2(cid:4) (cid:29) (cid:29) (cid:29) (cid:4) m(cid:14). We consider the penalties pen(cid:2)m(cid:3) and the weights xm of
Deﬁnition 3 and apply Theorem 1 to the corresponding penalized estimator.
We notice that

.r =

(cid:8)

m≥1

mr/2 exp(cid:2)−K log(cid:2)m + 1(cid:3)(cid:3) ≤

(cid:8)

m≥1

m−K+r/2 < ∞

since K > 1 + r/2, and so assumption (2.7) is fulﬁlled.

It follows from (2.8) and (2.9) that for any r > 0, and for any s ∈ (cid:5)γ,
(cid:17)
(cid:17)
(cid:17)
(cid:17)

ˆθ − θ −

≤ C(cid:2)r(cid:3)

(cid:10)(cid:17)
(cid:17)
(cid:17)
(cid:17)

Tn +

Ɛs

(cid:11)

(cid:13)

(cid:14)

(cid:4)

r

2L(cid:2)s(cid:3)
√
n

.r
nr

where

(cid:7)

(cid:11)

Tn = inf
m∈(cid:2)∗

(cid:1)s − sm(cid:1)2r +

m log(cid:2)m + 1(cid:3)
n2

(cid:13)r/2(cid:9)

(cid:29)

Assuming that the sequence s = (cid:2)βλ(cid:3)λ∈(cid:2)∗ belongs to the set (cid:5)γ implies that

(cid:1)s − sm(cid:1)2 =

(cid:8)

λ>m

λ ≤ γ2
β2
m(cid:29)

This concludes the proof of Theorem 2 by possibly enlarging C(cid:2)r(cid:3)(cid:29) ✷

5.2. Proof of Corollary 1.
body (cid:11)α(cid:4) 2(cid:4) ∞(cid:2)R(cid:3), then ∀ m ∈ (cid:2)∗,

If the sequence s = (cid:2)βλ(cid:3)λ∈(cid:2)∗ belongs to the Besov

(cid:8)

λ>m

βλ2 ≤ R2m−2α 24α
22α − 1

(cid:29)

Hence, by Theorem 2, ∀ r ≤ 2(cid:2)K − 1(cid:3),

sup
s∈(cid:11)α(cid:4) 2(cid:4) ∞(cid:2)R(cid:3)

Ɛs

(cid:7)(cid:17)
(cid:17)
(cid:17)
(cid:17)

ˆθ − θ −

r(cid:9)

(cid:17)
(cid:17)
(cid:17)
(cid:17)

2L(cid:2)s(cid:3)
√
n

≤ C(cid:2)r(cid:4) α(cid:3) inf
m∈(cid:2)∗

(cid:7)

(cid:11)

R2rm−2rα +

m log(cid:2)m + 1(cid:3)
n2

(cid:13)r/2(cid:9)

(cid:29)

We set

(cid:7)(cid:11)

mn =

n2R4
log(cid:2)1 + n2R4(cid:3)

(cid:13)1/1+4α(cid:9)

(cid:29)

Since for every positive x(cid:4) x ≥ log(cid:2)1 + x(cid:3), mn ≥ 1 ∨ (cid:2)1/2(cid:3)(cid:2)n2R4/ log(cid:2)1 + n2
R4(cid:3)(cid:3)1/1+4α. Moreover, since nR2 ≥ 1(cid:4) mn ≤ 2n2R4 and

log(cid:2)mn + 1(cid:3) ≤ log(cid:2)1 + 2n2R4(cid:3) ≤ 2 log(cid:2)1 + n2R4(cid:3)(cid:29)



<!-- pdf-page: 29 -->
1330

Therefore,

B. LAURENT AND P. MASSART

(cid:7)(cid:17)
(cid:17)
(cid:17)
(cid:17)

ˆθ−θ−

r(cid:9)

(cid:17)
(cid:17)
(cid:17)
(cid:17)

2L(cid:2)s(cid:3)
√
n

sup
s∈(cid:11)α(cid:4)2(cid:4)∞(cid:2)R(cid:3)

Ɛs

(cid:7)

≤ C(cid:2)r(cid:4)α(cid:3)

R2r/(cid:2)1+4α(cid:3)

(cid:7)

≤ C(cid:2)r(cid:4)α(cid:3)

R2r/(cid:2)1+4α(cid:3)

(cid:11)

(cid:11)

(cid:13)2rα/(cid:2)1+4α(cid:3)(cid:9)

log(cid:2)1+n2R4(cid:3)
n2

(cid:13)2rα/(cid:2)1+4α(cid:3)(cid:9)

log(cid:2)1+nR2(cid:3)
n2

hence, (3.4) is proved. This implies that

(cid:19)(cid:17)
(cid:17)
(cid:17) ˆθ−θ

(cid:17)
(cid:17)
(cid:17)

r(cid:20)

(cid:7)

(cid:11)

≤ C(cid:2)r(cid:4)α(cid:3)

R2r/(cid:2)1+4α(cid:3)

log(cid:2)1+nR2(cid:3)
n2

(cid:13)2rα/(cid:2)1+4α(cid:3)

+Rrn−r/2

sup
s∈(cid:11)α(cid:4)2(cid:4)∞(cid:2)R(cid:3)

Ɛs

since for any s ∈ (cid:11)α(cid:4) 2(cid:4) ∞(cid:2)R(cid:3)(cid:4) Ɛs(cid:2)(cid:19)L(cid:2)s(cid:3)/

√

n(cid:19)r(cid:3) ≤ C(cid:2)r(cid:4) α(cid:3)Rrn−r/2.

Conditions α ≤ 1/4 and nR2 ≥ 1 imply that

Rrn−r/2 ≤ C(cid:2)r(cid:4) α(cid:3)R2r/(cid:2)1+4α(cid:3)

(cid:11)

log(cid:2)1 + nR2(cid:3)
n2

(cid:13)2rα/(cid:2)1+4α(cid:3)

(cid:4)

(cid:4)

(cid:9)

hence, (3.4) holds.
If α > 1/4 then

R2r/(cid:2)1+4α(cid:3)

(cid:11)

log(cid:2)1 + nR2(cid:3)
n2

(cid:13)2rα/(cid:2)1+4α(cid:3)

≤ C(cid:2)r(cid:4) α(cid:3)Rrn−r/2(cid:4)

and therefore (3.5) holds.

If R and α are given with R > 0(cid:4) α > 1/4 and n goes to inﬁnity, then
n(cid:2) ˆθ − θ(cid:3) −
(cid:2)n2/ log(cid:2)n(cid:3)(cid:3)−2rα/(cid:2)1+4α(cid:3) = o(cid:2)n−r/2(cid:3); hence for any s ∈ (cid:11)α(cid:4) 2(cid:4) ∞(cid:2)R(cid:3), Ɛs(cid:11)(cid:19)
2L(cid:2)s(cid:3)(cid:19)r(cid:12) → 0 as n → ∞. Since L(cid:2)s(cid:3) has a (cid:9) (cid:2)0(cid:4) θ(cid:3) distribution, this implies that

√

√

n(cid:2) ˆθ − θ(cid:3)

(cid:13)
→(cid:9) (cid:2)0(cid:4) 4θ(cid:3) as n → ∞(cid:29)

If r ≥ 1, by the triangle inequality,
(cid:3)

(cid:6)

nr/2Ɛs

(cid:19) ˆθ − θ(cid:19)r

→ 2rƐs(cid:2)(cid:19)L(cid:2)s(cid:3)(cid:19)r(cid:3) = 2rθr/2Ɛ(cid:2)(cid:19)ξ(cid:19)r(cid:3) as n → ∞(cid:4)

where ξ is a standard normal variable. ✷

5.3. Proof of Theorem 3. We deﬁne

(cid:7) (cid:2)1(cid:3) = (cid:2)∗(cid:4)

(cid:7) (cid:2)2(cid:3) = (cid:13)m = (cid:2)N(cid:4) AN(cid:3)(cid:4) AN ∈ (cid:16) (cid:2)1(cid:4) 2(cid:4) (cid:29) (cid:29) (cid:29) (cid:4) N(cid:3)(cid:4) N ∈ (cid:2)∗(cid:14)(cid:4)

where (cid:16) (cid:2)1(cid:4) 2(cid:4) (cid:29) (cid:29) (cid:29) (cid:4) N(cid:3) denotes the set of all nonempty subsets of (cid:13)1(cid:4) 2(cid:4) (cid:29) (cid:29) (cid:29) (cid:4) N(cid:14).
Let (cid:7) = (cid:7) (cid:2)1(cid:3) × (cid:13)1(cid:14) ⊕ (cid:7) (cid:2)2(cid:3) × (cid:13)2(cid:14). Let m ∈ (cid:7) , if m = m1 × (cid:13)1(cid:14), we set
(cid:18)m = (cid:18)m1
= (cid:13)1(cid:4) 2(cid:4) (cid:29) (cid:29) (cid:29) (cid:4) m1(cid:14), and if m = m2 × (cid:13)2(cid:14), where m2 = (cid:2)N(cid:4) AN(cid:3), we
set (cid:18)m = (cid:18)m2
= AN. If m = m1 × (cid:13)1(cid:14), we consider the penalty pen(cid:2)m(cid:3) =
pen(cid:2)m1(cid:3) and the weight xm = xm1
of Deﬁnition 3 with K = 3. If m = m2 × (cid:13)2(cid:14),
with m2 = (cid:2)N(cid:4) AN(cid:3), we set xm = xN(cid:4) (cid:19)AN(cid:19) [where xN(cid:4) D is deﬁned by (3.9)] and



<!-- pdf-page: 30 -->
ESTIMATION OF A QUADRATIC FUNCTIONAL

1331

pen(cid:2)m(cid:3) = w(cid:2)N(cid:4) (cid:19)AN(cid:19)(cid:3) [where w(cid:2)N(cid:4) D(cid:3) is given by (3.10)]. It is clear that
(cid:7)

(cid:9)

ˆθ(cid:2)1(cid:3) = sup

Y2

λ − pen(cid:2)m1(cid:3)

(cid:8)

λ∈(cid:18)m1
and since when N is given, for m2 = (cid:2)N(cid:4) AN(cid:3) ∈ (cid:7) (cid:2)2(cid:3), the penalty of m2 depends
on AN only through its cardinality, one has

m1∈(cid:7) (cid:2)1(cid:3)

(cid:7)

(cid:8)

(cid:9)

ˆθ(cid:2)2(cid:3) = sup

Y2

λ − pen(cid:2)m2(cid:3)

m2∈(cid:7) (cid:2)2(cid:3)

λ∈(cid:18)m2

and therefore

ˆθ = ˆθ(cid:2)1(cid:3) ∨ ˆθ(cid:2)2(cid:3) = sup
m∈(cid:7)

(cid:9)

Y2

λ − pen(cid:2)m(cid:3)

(cid:29)

(cid:7)

(cid:8)

λ∈(cid:18)m

Hence we can apply Theorem 1 to ˆθ. To do so we have to check assumption (2.7)
with r = 2. We note that .2 = S(cid:2)1(cid:3) + S(cid:2)2(cid:3) with

(cid:8)

S(cid:2)i(cid:3) =

Dme−xm(cid:29)

We have to control the series S(cid:2)i(cid:3) for i = 1(cid:4) 2. We ﬁrst note that

m∈(cid:7) (cid:2)i(cid:3)

S(cid:2)1(cid:3) =

(cid:8)

m≥2

m−2 ≤ 1(cid:29)

Moreover,

Since

(cid:8)

(cid:8)

S(cid:2)2(cid:3) ≤

N∈(cid:2)∗

1≤D≤N

(cid:11)

(cid:13)

N
D

(cid:7)

(cid:11)

D exp

−3D

1 + log

(cid:13)(cid:13)(cid:9)

(cid:29)

(cid:11)

N
D

we derive that

(cid:11)

N
D

(cid:13)

(cid:11)

≤

(cid:13)D

(cid:4)

eN
D

(cid:8)

(cid:8)

S(cid:2)2(cid:3) ≤

N∈(cid:2)∗

1≤D≤N

De−2D

(cid:13)−2D

(cid:29)

(cid:11)

N
D

Using the fact that De−2D ≤ 1, for D ≤ N1/4 and (cid:2)N/D(cid:3)−D ≤ 1 for N1/4 < D ≤
N, one has

(cid:8)

De−2D

1≤D≤N

(cid:13)−2D

(cid:11)

N
D

(cid:8)

≤

1≤D≤N1/4

(cid:13)−2D

+

(cid:11)

N
D

(cid:8)

De−2D(cid:4)

N1/4<D≤N

which leads to

(cid:8)

De−2D

1≤D≤N

(cid:13)−2D

(cid:11)

N
D

≤

N−3/2
1 − N−3/2

+ N2e−N/2(cid:29)

Therefore the series S(cid:2)2(cid:3) is convergent.



<!-- pdf-page: 31 -->
1332

B. LAURENT AND P. MASSART

It follows from Theorem 1 that for any s ∈ :p(cid:4) c,

(cid:7)(cid:11)

Ɛs

ˆθ − θ −

(cid:13)2(cid:9)

(cid:11)

≤ C

2L(cid:2)s(cid:3)
√
n

(5.1)

and for i = 1(cid:4) 2,

T(cid:2)1(cid:3)

n ∧ T(cid:2)2(cid:3)

n +

(cid:13)

.2
n2

T(cid:2)i(cid:3)

n = inf

m∈(cid:7) (cid:2)i(cid:3)

(cid:23)(cid:11)

(cid:8)

λ /∈(cid:18)m

(cid:13)2

β2
λ

+

Dm
n2

(cid:11)

+

pen(cid:2)m(cid:3) −

(cid:13)2(cid:24)

(cid:4)

Dm
n

(5.1) ensures that ˆθ performs as well as ˆθ(cid:2)1(cid:3) and therefore (3.12) can be derived
from Theorem 2 and Comment (ii) following Theorem 2.

Let p < 2; in order to control T(cid:2)1(cid:3)

:p(cid:4) c, which means that
x (cid:30)→ xp/2 for p ≤ 2, one derives that
(cid:11)

(cid:1)

λ>D (cid:19)βλ(cid:19)p ≤ cp

n , we notice that s = β belongs to the lp-body
D. Using the subadditivity of the function

(cid:8)

β2

λ ≤

(cid:8)

(cid:13)2/p

(cid:19)βλ(cid:19)p

≤ c2
D(cid:29)

Hence,

λ>D

λ>D

(cid:7)

(cid:11)

T(cid:2)1(cid:3)

n ≤ inf
D∈(cid:2)∗

c4
D +

D log(cid:2)D(cid:3)
n2

(cid:13)(cid:9)

(cid:29)

n . For D ∈ (cid:2)∗ we deﬁne εD = D−1/pcD and GD = (cid:13)λ ∈

It remains to control T(cid:2)2(cid:3)
(cid:13)1(cid:4) 2(cid:4) (cid:29) (cid:29) (cid:29) (cid:4) N(cid:14)(cid:4) (cid:19)βλ(cid:19) ≥ εD(cid:14). Then, since
(cid:8)

(cid:8)

(cid:1)

β2

λ ≤

λ>D (cid:19)βλ(cid:19)p ≤ cp
D,
(cid:8)
β2

λ +

β2

λ +

(cid:8)

λ>N

β2
λ

λ /∈GD

λ /∈GD(cid:4) λ≤D

λ /∈GD(cid:4) D<λ≤N

≤ Dε2

D + ε2−p

D

(cid:8)

λ>D

(cid:19)βλ(cid:19)p + c2
N

≤ Dε2

D + ε2−p
p c2

D cp
D + c2
N

≤ 2D1− 2

D + c2

N

by deﬁnition of εD. To bound the cardinality of GD, we note that

(cid:8)

cp
D ≥

λ∈GD(cid:4) λ>D

(cid:19)βλ(cid:19)p ≥ εp

D(cid:19)(cid:13)GD ∩ (cid:13)λ(cid:4) λ > D(cid:14)(cid:14)(cid:19)(cid:4)

which implies that (cid:19)(cid:13)GD ∩ (cid:13)λ(cid:4) λ > D(cid:14)(cid:14)(cid:19) ≤ cp
of GD is bounded by 2D. This leads to

Dε−p

D = D. Therefore, the cardinality

T(cid:2)2(cid:3)

n ≤ C inf
N∈(cid:2)∗

inf
1≤D≤N

(cid:31)

(cid:28)

D1−2/pc2
D

(cid:11)

(cid:30)2

+

D(cid:2)1 + log(cid:2)N/D(cid:3)(cid:3)
n

(cid:13)2

+ c4
N

(cid:29)

This concludes the proof of Theorem 3. ✷

 


<!-- pdf-page: 32 -->
ESTIMATION OF A QUADRATIC FUNCTIONAL

1333

5.4. Proof of Corollary 2. We ﬁrst notice that (3.12) ensures that ˆθ behaves
as well as the estimator studied in Corollary 1; therefore (3.15) follows from (3.4).
We turn now to the proof of (3.14).

Let p ≤ 2; we derive from Theorem 3 that
(cid:13)2(cid:9)

(cid:7)(cid:11)

sup
s∈(cid:14)p(cid:4) α(cid:23) (cid:2)R(cid:3)

Ɛs

ˆθ − θ −

2L(cid:2)s(cid:3)
√
n

where

(cid:23)

(cid:7)(cid:28)

v1(cid:2)n(cid:3) = inf
N∈(cid:2)∗

inf
D∈(cid:2)∗

(cid:7)

v2(cid:2)n(cid:3) = inf
D∈(cid:2)∗

c4
D +

Here, cλ = Rλ−α(cid:23) . Let

D1−(cid:2)2/p(cid:3)c2
D

(cid:11)

(cid:30)2

+

D log(cid:2)D + 1(cid:3)
n2

(cid:9)

(cid:29)

≤ C inf (cid:13)v1(cid:2)n(cid:3)(cid:31) v2(cid:2)n(cid:3)(cid:14)(cid:4)

D(cid:2)1 + log(cid:2)N/D(cid:3)(cid:3)
n

(cid:13)2(cid:9)

(cid:24)

+ c4
N

(cid:4)

D1(cid:2)n(cid:3) =

(cid:7)(cid:11)

nR2
log(cid:2)1 + nR2(cid:3)

(cid:13)1/(cid:2)1+2α(cid:3)(cid:9)

and N(cid:2)n(cid:3) =

(cid:19)

(cid:2)nR2(cid:3)α/(cid:2)α(cid:23)(cid:2)1+2α(cid:3)(cid:3)

(cid:20)

(cid:29)

Note that D1(cid:2)n(cid:3) ≥ 1 and that N(cid:2)n(cid:3) ≥ 1. Since for p ≤ 2, α > α(cid:23),

(cid:11)

log

(cid:13)

N(cid:2)n(cid:3)
D1(cid:2)n(cid:3)

≤ C(cid:2)p(cid:4) α(cid:3) log

(cid:4)

1 + nR2

(cid:5)

which ensures that

v1(cid:2)n(cid:3) ≤ C(cid:2)p(cid:4) α(cid:3)R4/(cid:2)1+2α(cid:3)

(cid:11)

log(cid:2)1 + nR2(cid:3)
n

(cid:13)4α/(cid:2)1+2α(cid:3)

(cid:29)

Moreover, we set

D2(cid:2)n(cid:3) =

(cid:7)(cid:11)

n2R4
log(cid:2)1 + n2R4(cid:3)

(cid:13)1/1+4α(cid:23) (cid:9)

(cid:29)

Since D2(cid:2)n(cid:3) ≥ 1, we obtain by similar computations as in the proof of
Corollary 1 that

v2(cid:2)n(cid:3) ≤ C(cid:2)p(cid:4) α(cid:3)R4/(cid:2)1+4α(cid:23)(cid:3)

(cid:11)

log(cid:2)1 + nR2(cid:3)
n2

(cid:13)4α(cid:23)/(cid:2)1+4α(cid:23)(cid:3)

(cid:29)

This concludes the proof of Corollary 2. ✷

Proof of (3.16). When cλ = R(cid:2)log(cid:2)λ(cid:3)(cid:3)−α(cid:23) , let N ∈ (cid:2)∗ satisfy N nn(cid:2)1/α(cid:23) (cid:3)(cid:2)1/p−1/2(cid:3) ≤
N ≤ Cnn(cid:2)1/α(cid:23) (cid:3)(cid:2)1/p−1/2(cid:3) . Setting D1(cid:2)n(cid:3) = (cid:11)n(cid:2)p/2−p/2α(cid:23)(cid:3)(cid:2)1/p−1/2(cid:3)(cid:12) leads to v1(cid:2)n(cid:3) ≤
C(cid:2)R(cid:4) p(cid:4) α(cid:3)n(cid:2)2−p(cid:3)(cid:2)(cid:2)1/α(cid:23)(cid:3)(cid:2)1/p−1/2(cid:3)−1(cid:3) log2(cid:2)1 + n(cid:3). Moreover,
let D2(cid:2)n(cid:3) = (cid:11)n2/
(cid:2)log(cid:2)1 + n(cid:3)(cid:3)1+4α(cid:23) (cid:12); we get v2(cid:2)n(cid:3) ≤ C(cid:2)R(cid:4) α(cid:3)(cid:2)log(cid:2)1 + n(cid:3)(cid:3)−4α(cid:23) .



<!-- pdf-page: 33 -->
1334

B. LAURENT AND P. MASSART

5.5. Proof of Theorem 4. We set

(cid:7) (cid:2)1(cid:3) = (cid:2)

and for any J ∈ (cid:2),

!

(cid:7) (cid:2)2(cid:3)

J =

m ⊂ (cid:2)∗(cid:4) ∀ j ≥ 0(cid:4) (cid:19)m ∩ (cid:18)(cid:2)j(cid:3)(cid:19) = KJ(cid:2)j(cid:3)

"

which leads to the deﬁnition of (cid:7) (cid:2)2(cid:3) as

(cid:7) (cid:2)2(cid:3) =

+

J∈(cid:2)

(cid:7) (cid:2)2(cid:3)
J (cid:29)

Let (cid:7) = (cid:7) (cid:2)1(cid:3) × (cid:13)1(cid:14) ⊕ (cid:7) (cid:2)2(cid:3) × (cid:13)2(cid:14). Let m ∈ (cid:7) .

(i) If m = J × (cid:13)1(cid:14), with J ∈ (cid:2), we set (cid:18)m = (cid:18)J = ∪J

j=0(cid:18)(cid:2)j(cid:3)(cid:4) xm = xJ =

2 log(cid:2)Dm(cid:3) and pen(cid:2)m(cid:3) = pen(cid:2)J(cid:3) = w(cid:2)1(cid:3)(cid:2)J(cid:3).

(ii) If m = m2 ×(cid:13)2(cid:14) with m2 ∈ (cid:7) (cid:2)2(cid:3)

and pen(cid:2)m(cid:3) = pen(cid:2)m2(cid:3) = w(cid:2)2(cid:3)(cid:2)J(cid:3).

J , we set (cid:18)m = (cid:18)m2

= m2(cid:4) xm = xm2

= 3Dm

Note that with our deﬁnitions of the penalties and the weights, it is easy to

check that for any m ∈ (cid:7) ,

npen(cid:2)m(cid:3) ≥ Dm + 1 + 2

(cid:2)Dm + 1(cid:3)xm + 2xm(cid:4)

(cid:12)

which is the required assumption on the penalty function in Theorem 1. Moreover,
by deﬁnition,

(cid:11)

(cid:8)

ˆθ(cid:2)1(cid:3) = sup

m1∈(cid:7) (cid:2)1(cid:3)

λ∈m1

(cid:13)

Y2

λ − pen(cid:2)m1(cid:3)

and since, when J is given, for m2 ∈ (cid:7) (cid:2)2(cid:3)
for m2 =

(cid:27)(cid:18)J(cid:2)j(cid:3), one has

(cid:1)+∞
j=0

J the supremum of

(cid:1)

Y2

λ is achieved

λ∈m2

ˆθ(cid:2)2(cid:3) = sup
J≥0

= sup

sup
m2∈(cid:7) (cid:2)2(cid:3)
J
(cid:11)
(cid:8)

(cid:11)

(cid:13)

Y2

λ − w(cid:2)2(cid:3)(cid:2)J(cid:3)

(cid:8)

λ∈m2

(cid:13)

Y2

λ − pen(cid:2)m2(cid:3)

(cid:29)

m2∈(cid:7) (cid:2)2(cid:3)

λ∈m2

Hence,

ˆθ = sup
m∈(cid:7)

(cid:11)

(cid:8)

λ∈m

(cid:13)

Y2

λ − pen(cid:2)m(cid:3)



<!-- pdf-page: 34 -->
ESTIMATION OF A QUADRATIC FUNCTIONAL

1335

and therefore we can apply Theorem 1 to ˆθ provided that assumption (2.7) is
fulﬁlled with r = 2. In order to check (2.7), we notice that .2 = S(cid:2)1(cid:3) + S(cid:2)2(cid:3) with

(5.2)

S(cid:2)i(cid:3) =

S(cid:2)1(cid:3) =

S(cid:2)2(cid:3) =

(cid:8)

Dme−xm(cid:4)

m∈(cid:7) (cid:2)i(cid:3)
(cid:8)
(cid:4)

2J+1 − 1

(cid:5)−1 ≤ 2(cid:4)

J≥0
(cid:8)

J≥0

@J(cid:19)(cid:7) (cid:2)2(cid:3)

J (cid:19)e−3@J (cid:4)

where we recall that @J =

j=0 KJ(cid:2)j(cid:3). Now,

(cid:1)∞

where the product is indeed ﬁnite since

j>J
(cid:11)

the inequality

,

(cid:19)(cid:7) (cid:2)2(cid:3)

J (cid:19) =

(cid:11)

(cid:13)

2j
KJ(cid:2)j(cid:3)
(cid:13)

2j
KJ(cid:2)j(cid:3)

(cid:11)

log

k
(cid:11)kx(cid:12)

(cid:13)

(cid:11)

≤ kx

1 + log

(cid:11)

(cid:13)(cid:13)
(cid:4)

1
x

(cid:4)

= 1 for j large enough. Using

which holds for any x ∈(cid:12)0(cid:4) 1(cid:12) and k ∈ (cid:2)∗, we derive that

(cid:28)

log

(cid:19)(cid:7) (cid:2)2(cid:3)
J (cid:19)

(cid:30)

≤

(cid:8)

j>J
(cid:7)

≤ 2J

2J
(cid:2)j − J(cid:3)3

(cid:7)

(cid:11)

1 + log

(cid:13)(cid:9)

(cid:2)j − J(cid:3)3
2J−j

(cid:8)

1
l3

+ log(cid:2)2(cid:3)

(cid:8)

l≥1

1
l2

+ 3

(cid:8)

l≥1

log(cid:2)l(cid:3)
l3

(cid:9)

l≥1

≤ C32J(cid:4)

where

Hence,

C3 =

(cid:8)

l≥1

1
l3

+ log(cid:2)2(cid:3)

(cid:8)

l≥1

1
l2

+ 3

(cid:8)

l≥1

log(cid:2)l(cid:3)
l3

< 3(cid:29)

(5.3)

J (cid:19) ≤ exp(cid:2)C32J(cid:3)(cid:29)
Since @J ≥ 2J and x → xe−3x is decreasing on (cid:11)1(cid:4) ∞(cid:11), combining (5.2) and (5.3)
yields

(cid:19)(cid:7) (cid:2)2(cid:3)

S(cid:2)2(cid:3) ≤

2J exp(cid:2)C32J(cid:3) exp(cid:2)−32J(cid:3) < ∞(cid:29)

(cid:8)

J≥0

It follows that the series .2 is convergent. We get by Theorem 1 the following risk
bound:

(cid:7)(cid:11)

Ɛs

ˆθ − θ −

2L(cid:2)s(cid:3)
√
n

(cid:13)2(cid:9)

(cid:7)

≤ C

T(cid:2)1(cid:3)

n ∧ T(cid:2)2(cid:3)

n +

(cid:9)

(cid:4)

.2
n2



<!-- pdf-page: 35 -->
1336

where

B. LAURENT AND P. MASSART

(cid:7)(cid:11)

T(cid:2)1(cid:3)

n = inf
J≥0

(cid:8)

λ /∈(cid:18)J

β2
λ

(cid:13)2

(cid:11)

+

w(cid:2)1(cid:3)(cid:2)J(cid:3) −

(cid:13)2(cid:9)

(cid:4)

(cid:19)(cid:18)J(cid:19)
n

T(cid:2)2(cid:3)

n = inf
J≥0

inf
m∈(cid:7) (cid:2)2(cid:3)
J

(cid:7)(cid:11)

(cid:8)

λ /∈m

(cid:13)2

(cid:11)

β2
λ

+

w(cid:2)2(cid:3)(cid:2)J(cid:3) −

(cid:13)2(cid:9)

(cid:29)

@J
n

Let β ∈ (cid:11)α(cid:4) p(cid:4) ∞(cid:2)R(cid:3).

1. If p ≥ 2, then by convexity of the function x (cid:30)→ xp/2,
(cid:13)2/p
(cid:11)

(cid:8)

(cid:8)

β2

λ ≤

(cid:19)(cid:18)(cid:2)j(cid:3)(cid:19)p/2−1

(cid:19)βλ(cid:19)p

≤ R22−2jα

λ∈(cid:18)(cid:2)j(cid:3)

λ∈(cid:18)(cid:2)j(cid:3)

which ensures that (cid:11)α(cid:4) p(cid:4) ∞(cid:2)R(cid:3) ⊆ (cid:11)α(cid:4) 2(cid:4) ∞(cid:2)R(cid:3).
2. If p < 2, by subadditivity of the function x (cid:30)→ xp/2,

(cid:11)

(cid:8)

(cid:8)

β2

λ ≤

λ∈(cid:18)(cid:2)j(cid:3)

λ∈(cid:18)(cid:2)j(cid:3)

(cid:13)2/p

(cid:19)βλ(cid:19)p

≤ R22−2jα(cid:23) (cid:4)

where α(cid:23) = 1/2 + α − 1/p.

This implies that for every J ∈ (cid:7) (cid:2)1(cid:3) = (cid:2) and any p > 0,
(cid:8)

(cid:8)

(cid:8)

β2

λ =

λ ≤ C(cid:2)α(cid:23)(cid:3)R22−2Jα(cid:23)(cid:23) (cid:4)
β2

λ /∈(cid:18)J

j>J

λ∈(cid:18)(cid:2)j(cid:3)

where α(cid:23)(cid:23) = inf (cid:2)α(cid:4) α(cid:23)(cid:3) and since (cid:19)(cid:18)J(cid:19) ≤ 2J+1,
(cid:11)

(cid:13)2

w(cid:2)1(cid:3)(cid:2)J(cid:3) −

(cid:19)(cid:18)J(cid:19)
n

(cid:11)

2J(cid:2)J + 1(cid:3)
n2

(cid:13)

(cid:29)

≤ C

Hence

Let

This leads to

(cid:7)

T(cid:2)1(cid:3)

n ≤ C inf
J≥0

R42−4Jα(cid:23)(cid:23) +

2J(cid:2)J + 1(cid:3)
n2

(cid:9)

(cid:29)

(cid:7)

J(cid:2)1(cid:3)

n =

(cid:11)

1
1 + 4α(cid:23)(cid:23)

log2

n2R4
log(cid:2)1 + n2R4(cid:3)

(cid:13)(cid:9)

(cid:29)

T(cid:2)1(cid:3)

n ≤ C(cid:2)p(cid:4) α(cid:3)R4/(cid:2)1+4α(cid:23)(cid:23)(cid:3)

(cid:11)

log(cid:2)1 + nR2(cid:3)
n2

(cid:13)4α(cid:23)(cid:23)/(cid:2)1+4α(cid:23)(cid:23)(cid:3)

(cid:29)

We now turn to the control of T(cid:2)2(cid:3)

n for p < 2.



<!-- pdf-page: 36 -->
ESTIMATION OF A QUADRATIC FUNCTIONAL

1337

It follows from Birg´e and Massart (2000a) that for any J ∈ (cid:2) there exists
λ ≤ C(cid:2)p(cid:4) α(cid:3)R22−2Jα. Therefore, since @J ≤ κ2J

λ /∈m β2

(cid:1)

m ∈ (cid:7) (cid:2)2(cid:3)
where κ is an absolute constant,

J such that

(cid:11)

T(cid:2)2(cid:3)

n ≤ C(cid:2)p(cid:4) α(cid:3) inf
J≥0

R42−4Jα +

(cid:13)

(cid:29)

22J
n2

J(cid:2)2(cid:3)

n =

(cid:7)

1
1 + 2α

(cid:9)

log2(cid:2)nR2(cid:3)

(cid:29)

Let

This leads to

T(cid:2)2(cid:3)

n ≤ C(cid:2)p(cid:4) α(cid:3)R4/(cid:2)1+2α(cid:3)n−4α/(cid:2)1+2α(cid:3)(cid:29)

This concludes the proof of Theorem 4. ✷

REFERENCES

Baraud, Y. (2000). Model selection for regression on a ﬁxed design. Probab. Theory Related Fields

117 467–493.

Barron, A. R., Birg ´e, L. and Massart, P. (1999). Risk bound for model selection via penalization.

Probab. Theory Related Fields 113 301–415.

Bickel, P. and Ritov, Y. (1988). Estimating integrated squared density derivatives: sharp best

Birg ´e, L.

order of convergence estimates. Sankhy ¯a Ser. A 50 381–393.
(1983). Approximation dans les espaces m´etriques et

th´eorie de l’estimation.

Z. Wahrsch. Verw. Gebiete 65 181–237.

Birg ´e, L. and Massart, P. (1995). Estimation of integral functionals of a density. Ann. Statist.

23 11–29.

Birg ´e, L. and Massart, P. (1997). From model selection to adaptive estimation. In Festschrift for
Lucien Le Cam: Research Papers in Probability and Statistics (D. Pollard, E. Torgersen
and G. Yang, eds.) 55–87. Springer, New York.

Birg ´e, L. and Massart, P. (1998). Minimum contrast estimators on sieves: exponential bounds

and rates of convergence. Bernoulli 4 329–375.

Birg ´e, L. and Massart, P. (2000a). An adaptive compression algorithm in Besov spaces. Constr.

Approx. 16 1–36.

Birg ´e, L. and Massart, P. (2000b). Gaussian model selection. Technical Report 2000.05, Univ.

Paris Sud.

DeVore, R. A., Jawerth, B. and Popov, V. (1992). Compression of wavelet decompositions. Amer.

J. Math. 114 737–785.

DeVore, R. A. and Lorentz, G. G. (1993). Constructive Approximation. Springer, New York.
DeVore, R. A., Kyriazis, G. Leviatan, D. and Tikhomirov, V. M. (1993). Wavelet compression

and nonlinear n-widths. Adv. Comput. Math. 1 197–214.

Johnstone, I. (1999). Chi-square oracle inequalities. Preprint.
Donoho, D. and Johnstone, I. (1998). Minimax estimation via wavelet shrinkage. Ann. Statist.

26 879–921.

Donoho, D. and Liu, R. (1991). Geometrizing rates of convergence II. Ann. Statist. 19 633–668.
Donoho, D. and Nussbaum, M. (1990). Minimax quadratic estimation of a quadratic functional.

J. Complexity 6 290–323.

Dudley, R. M. (1973). Sample functions of the Gaussian process. Ann. Probab. 1 66–103.
Efro¨imovich, S. and Low, M. (1996). On optimal adaptive estimation of a quadratic functional.

Ann. Statist. 24 1106–1125.

Gayraud, G. and Tribouley, K. (1999). Wavelet methods to estimate an integrated quadratic
functional: adaptivity and asymptotic law. Statist. Probab. Lett. 44 109–122.



<!-- pdf-page: 37 -->
1338

B. LAURENT AND P. MASSART

Laurent, B. (1996). Efﬁcient estimation of integral functionals of a density. Ann. Statist. 24

659–681.

Lepskii, O. V. (1990). On a problem of adaptive estimation in Gaussian white noise. Theory

Probab. Appl. 35 454–466.

Lepskii, O. V. (1992). On problems of adaptive estimation in Gaussian white noise. Adv. Soviet

Math. 12 87–106.

Laboratoire de math ´ematiques
Bat. 425
Universit ´e Paris Sud
F-91405 Orsay C ´edex
France
E-mail: Beatrice.Laurent@math.u-psud.fr

Pascal.Massart@math.u-psud.fr


