<!-- generated-by: proofmatch local extraction -->
<!-- source-pdf-sha256: 988dc9f0ae91c3a654cefe58b04f061cb2562d93b3d95f61835c530796c7992e -->
<!-- extractor: pdfminer.six v20260107 -->

<!-- pdf-page: 1 -->
On teaching the approximation method for circuit lower bounds*

Oded Goldreich
Department of Computer Science
Weizmann Institute of Science, Rehovot, Israel.

March 15, 2023

Abstract

This text provides a basic presentation of the the approximation method of Razborov
(Matematicheskie Zametki, 1987) and its application by Smolensky (19th STOC, 1987) for prov-
ing lower bounds on the size of AC0[p]-circuits that compute sums mod q (for primes q ̸= p).
The textbook presentations of the latter result concentrate on proving the special case of q = 2,
and do not provide details on the proof of the general case. Furthermore, the presentations I
have read tend to be too terse to my taste. The current text provides a detailed exposition of
both the special case and the general case. Nevertheless, I agree with the common practice of
covering only the case of q = 2 in class, and suggest leaving the general case (i.e, q > 2) for
advanced reading.

Contents

1 Introduction (mainly for the teacher)

2 The basic material

2.1 Overview . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . .
2.2 The actual theorem and its proof . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . .

3 Advanced reading

3.1 The case of q < p . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . .
3.2 The case of q > p . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . .

4 Beyond the recommended reading

4.1 The case of q < p . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . .
4.2 The case of q > p . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . .

Appendix: Low degree polynomials and approximating Majority

Acknowledgements

Bibliography

1

1
2
3

9
10
13

14
14
17

18

20

20

*Partially supported by the Israel Science Foundation (grant No. 1041/18) and by the European Research Council
(ERC) under the European Union’s Horizon 2020 research and innovation programme (grant agreement No. 819702).

1



<!-- pdf-page: 2 -->
1

Introduction (mainly for the teacher)

The approximation method of Razborov [5] and its application by Smolensky [4] for proving lower
bounds on the size of AC0[p]-circuits that compute sums mod q (for primes q ̸= p) are among the
most celebrated results of circuit complexity. The textbook presentations of the latter result (see,
e.g., [1, 3]) concentrate on proving the special case of q = 2, and do not provide details on the
proof of the general case. Furthermore, the presentations I have read tend to be too terse to my
taste. Aiming at making the proof of the result more accessible, I worked out a more detailed and
friendly presentation of both the special case (i.e., q = 2) and the general case.

My presentation is aimed at graduate students interested in the theory of computation at large,
and not necessarily at those focused on complexity theory, let alone circuit complexity. I assume
that these students are familiar with the notion of Boolean circuits (including the notions of depth
and fan-in). Such a familiarity is essential for the technical description. In addition, for the sake of
perspective, I assume that the students are familiar with the P-vs-NP problem and the fact that
our current state of knowledge regarding it is in its infancy. In particular, I assume that they know
that even extremely modest (in comparison) separations (e.g., AC0 cannot compute Parity) are
quite challenging to prove. Needless to say, if any of these assumptions does not hold, then one
should start by correcting this state of affairs.

Turning to the actual contents, recall that proving lower bounds on the size of AC0[p]-circuits
that compute sums mod q (for primes q ̸= p) consists of two steps: (1) Showing that the compu-
tation of AC0[p]-circuits can be (well) approximated by low degree polynomials over GF(p); and
(2) Showing that summation mod q cannot be approximated (well) by low degree polynomials over
GF(p).

Step (1) is very intuitive and its presentation in standard texts is quite adequate; still, I will
provide my own presentation of it (see Section 2.1 and Lemma 2 (in Section 2.2)). The problem
is with the presentation of Step (2) and specifically with the case of q > 2. The special case of
q = 2 is captured by Lemma 3, which is also presented in Section 2.2, whereas the general case is
treated in Section 3. (Section 2.2 also presents a derivation of the lower bound for Majority, via a
reduction of modular sums to it.)

I agree with the common practice of covering only Step (1) and the special case (i.e., q = 2)
of Step (2) in class. I suggest using Section 2 as a basis for teaching this material, while leaving
Section 3 (which covers the general case (i.e., q ≥ 2)) for advanced reading. In contrast to these
sections, Section 4 is not intended for the students: It presents a more complicated (alternative)
proof of the general case, which may be of independent interest.

2 The basic material

The approximation method is pivoted at the discrepancy between the ability of low degree polyno-
mials (over a small prime field) to approximate functions computed by certain classes of Boolean
circuits and their inability to approximate modular sums modulo a different prime (i.e., different
from the field size). In particular, we shall prove that, on the one hand, low degree polynomials
over GF(p) can (well) approximate constant-depth (unbounded fan-in) circuits, but, on the other
hand, they cannot (well) approximate the sum modulo q, for any prime q ̸= p. The conclusion is
that constant-depth (unbounded fan-in) circuits cannot compute such modular sums. (We mention
that the foregoing holds also when the circuits are equipped with (unbounded fan-in) MOD p gates.)

1



<!-- pdf-page: 3 -->
The foregoing emphasis on low degree is crucial: Polynomials of degree n over GF(2) can
compute any n-variate Boolean function.1 On the other hand, the number of low degree n-variate
polynomials is much small than the number of n-variate Boolean function.2

The concept of approximation is also crucial here, because no low degree polynomial can per-
fectly agree (even) with extremely simple functions such as the n-wide AND (or OR).3 Hence, we
consider the class of functions that can be well approximated by low degree polynomials, showing
that this class contains all functions computed by constant-depth (unbounded fan-in) circuits, but
not some other simple functions (e.g., Majority and MOD q for q different from the field size). We
start with an overview, which is focused on the first aspect.

2.1 Overview

The key observation that underlies the approximation method is that an unbounded fan-in OR-
gate can be well approximated by a low degree polynomial (say, over GF(2)); that is, for every
distribution D over {0, 1}w, there exists a degree ℓ polynomial P : GF(2)w → GF(2) such that

Pr(y1,...,yw)∼D

(cid:104)

(cid:105)
P (y1, ..., yw) = OR(y1, ..., yw)

≥ 1 − 2−ℓ.

(1)

We stress that the degree of the polynomial is logarithmic in the (reciprocal of the) desired error
bound, and does not depend on the number of variables. Furthermore, the claim holds for any
distribution D (rather than only for the uniform distribution over {0, 1}w).4 The latter fact becomes
crucial when we wish to replace an intermediate gate in a circuit (i.e., a gate that is fed by the
outputs of other gates).

The foregoing claim is proved by observing that, for every (y1, ..., yw) ∈ {0, 1}w \{0w}, a random
linear function L : GF(2)ℓ → GF(2) satisfies PrL[L(y1, ..., yw) = 1] = 1/2, whereas L(0, ..., 0) = 0
for every linear function L. Hence, for every (y1, ..., yw) ∈ {0, 1}w, it holds that

PrL1,....,Lℓ

(cid:104)
OR(L1(y1, ..., yw), ..., Lℓ(y1, ..., yw)) = OR(y1, ..., yw)

(cid:105)

≥ 1 − 2−ℓ,

where L1, ..., Lℓ are random linear functions. It follows that there exists linear functions L1, ..., Lℓ
such that

Pr(y1,...,yw)∼D

(cid:104)

(cid:105)
OR(L1(y1, ..., yw), ..., Lℓ(y1, ..., yw)) = OR(y1, ..., yw)

≥ 1 − 2−ℓ.

Hence, replacing OR(z1, ..., zℓ) by the polynomial 1 − (cid:81)
j∈[ℓ](1 − zj), we derive Eq. (1); specifically,
we define P (y1, ..., yw) def= 1 − (cid:81)
j∈[ℓ](1 − Lj(y1, ..., yw)), where the Lj’s are the foregoing linear
functions. A similar idea can be applied in GF(p), for any prime p, but in that case we raise the

1Hint: Write the function in DNF using terms of size n, and note that the conjunction of n literals can be computed

by multiplying the corresponding linear function (e.g., x1 ∧ (¬x2) ∧ x3 can be computed by x1 · (1 − x2) · x3).

2Hint: The unber of degree d mononimals over n varaiables is (cid:0)n
3Hint: Use the fact that a non-zero degree d polynomial over GF(2) evaluates to 1 with probability at least 2−d.
4Note that when seeking to approximate an OR-gate under the uniform distribution, we can use

(cid:1).

d

Pr(y1,...,yw )∈{0,1}n

OR(y1, ..., yℓ) = OR(y1, ..., yw)

(cid:20)

(cid:21)

≥ 1 − 2−ℓ,

and then replace OR(y1, ..., yℓ) by the polynomial 1 − (cid:81)

j∈[ℓ](1 − yj).

2



<!-- pdf-page: 4 -->
linear functions to power p − 1 in order to guarantee an answer in {0, 1}. Consequently, the degree
of the polynomial is (p − 1) · ℓ.

Applying the analogous replacement to all (OR and AND) gates of a depth d circuit of size s,
we obtain a degree d · (p − 1) · ℓ polynomial over GF(p) that approximates the circuit up to error
of s · 2−ℓ, even if the circuit has unbounded fan-in MOD p gates. The replacement process will be
described and analyzed in detail in the proof of Lemma 2. In contrast, it can be shown that low
degree polynomials cannot approximate the MOD q function with such a small error rate, where q
is an arbitrary fixed prime different from p. Indeed, we said nothing about how the latter claim
is proved: The special case of q = 2 is stated in Lemma 3, whereas the general case is treated in
Section 3.

2.2 The actual theorem and its proof

We start by recalling the general background and the relevant preliminaries.

General background. When discussing circuit (size and/or depth) lower bounds, the point is
obtaining them for explicit functions; in contrast, it is trivial to get such lower bounds for non-
explicit functions or even for functions of high (uniform) time complexity (i.e., just let the algorithm
try all functions and all circuits). The question is what is “explicit” and the answer is undetermined;
actually, one often wants things to be as explicit as possible. Still, the first choice would be that
explicit means computable in polynomial-time. Often (see, e.g., [1, Sec. 6.1] and [2, Sec. 5.2.3]), one
may require even more; e.g., computability in log-space. Here, we shall discuss size lower bounds
for very explicit functions (e.g., Majority, Parity, etc).

Preliminaries. The class AC0[m] consists of Boolean functions computable by families of cir-
cuits of polynomial size and constant depth having unbounded fan-in AND, OR, NOT, and MOD m
gates, where m > 1 is an arbitrary constant. The MOD m gates, denoted MODm, are defined such
that MODm(x1, ..., xw) = 0 if (cid:80)
i∈[w] xi mod m ∈
{1, ..., m − 1}). Indeed, MOD2 coincides with XOR (equiv, the Parity function). We shall focus on the
case that m is a prime number, while warning that the case of composite m’s (even m = 6) is wide
open (with the exception of prime powers).5

(mod m) and 1 otherwise (i.e., if (cid:80)

i∈[w] xi ≡ 0

The following result implies that, for any prime p, the class AC0[p] cannot compute simple
functions such as Majority or MODq, where q ̸= p. Indeed, this result does fit the intuition that
functions of a “counting” falvor (other than MODp itself) cannot be computed by AC0[p], but the

5Essentially, for every prime power pe, it holds that AC0[pe] = AC0[p], because MODpe can be implemented in
AC0[p] (and MODp can be implemented in AC0[pe] (e.g., by duplicating each input pe−1 times)). Specifically, we can
compute MODpe (x) using MODpe−1 and MODp gates as follows.

(cid:136) For every i ∈ [n], we compute yi = MODpe−1 (x1, ..., xi).
Note that (yi−1, yi) = (1, 0) holds if any only if (cid:80)

j∈[i−1] xi ≡ −1

(mod pe−1) and xi = 1.

This implies that |{i ∈ {2, ..., n} : (yi−1, yi) = (1, 0)}| equals

(cid:106) (cid:80)

i∈[n] xi/pe−1(cid:107)
.

(cid:136) For every i ∈ {2, ..., n}, we compute zi = AND(yi−1, ¬yi).

Note that (cid:80)

i∈[n] xi = pe−1 ·

(cid:16)(cid:80)

i∈{2,...,n} zi

+

i∈[n] xi mod p

(cid:17)

(cid:16)(cid:80)

(cid:17)
.

Hence, MODpe (x) = 0 if and only if both MODp(z) = 0 and MODp(x) = 0.

3



<!-- pdf-page: 5 -->
point is that we can actually prove this statement. In contrast, we do not know a proof of the
equally intuitive conjecture that AC0[6] cannot compute Majority.

Theorem 1 (size lower bounds for constant-depth Boolean circuits with AND, OR, NOT, and MODp
gates, when p is a prime): For any prime p ≥ 2, the following holds.

1. Computing the majority of n bits by a depth d circuit with unbounded fan-in AND, OR, NOT,

and MODp gates requires size exp(Ω(n1/2d)).

2. For any prime q different from p, computing the MODq of n bits by a depth d circuit with

unbounded fan-in AND, OR, NOT, and MODp gates requires size exp(Ω(n1/2d)).

In particular, Part 1 (with p = 2) implies that AC0[2] cannot compute Majority, whereas Part 2
(with p = 3 and q = 2) implies that AC0[3] (let alone AC0 itself) cannot compute Parity. In general,
Part 2 implies that AC0[p] cannot compute MODq, for q ̸= p.

We shall focus on proving Part 2, while noting that it implies a (weaker but sufficiently inter-

esting) version of Part 1. In general, the proof of Theorem 1 combines two steps:

Step 1: Proving that the computation of AC0[p] circuits can be well approximated by polynomials

of low degree over the finite field of p elements, denoted GF(p).

This will be proved in Lemma 2 using the ideas presented in the overview (for the case of
p = 2).

Step 2: Proving that the target functions (i.e., n-wise Majority and n-wise MODq, for q ̸= p) cannot

be well approximated by low degree polynomials over GF(p).

This will be proved in Lemma 3 for MOD2 and any fixed prime p ̸= 2, which is sufficiently
interesting. The general case of MODq for any fixed primes q ̸= p is treated in Section 3.

We shall also show that the lower bound for computing MODq, for any q (e.g., q = 2), yields a lower
bound for Majority. Starting with Step 1, we prove the following.

Lemma 2 (approximating AC0[p] by low degree polynomials over GF(p)): For any prime p ≥ 2,
let C : {0, 1}n → {0, 1} be a depth d circuit of size s with unbounded fan-in AND, OR, NOT, and MODp
gates. Then, there exists a degree D polynomial A over GF(p) such that

Prx∈{0,1}n [A(x) = C(x)] > 1 −

s
exp(Ω(D1/d))

where the Omega-notation hides a log p

p−1 factor.

√

Setting D =
of o(1). (In contrast, we shall later show that degree
Ω(1) with respect to MODq : {0, 1}n → {0, 1}, for any fixed prime q ̸= p.)

n and using a sufficiently small s = exp(Ω(n1/2d)), we get an approximation error
n polynomials over GF(p) have error rate

√

Proof: The proof is by induction on the structure of C, and all arithmetic expressions are in GF(p).
Denoting the function computed by the top (output) gate by g, we consider the four possible cases.

4



<!-- pdf-page: 6 -->
1. The top gate is a NOT gate: If g = ¬f , then we approximate g by (cid:101)g def= 1 − (cid:101)f , where (cid:101)f is the

polynomial that approximates f .
Note that (cid:101)g has the same degree as (cid:101)f , and that (cid:101)g(x) ∈ {0, 1} whenever (cid:101)f (x) ∈ {0, 1}.
Furthermore, if (cid:101)f (x) = f (x), then (cid:101)g(x) = g(x). Hence, the current replacement adds no
approximation error.

2. The top gate is a MODp gate: If g = MODp(f1, ..., fw), then we approximate g by the polynomial

(cid:16)(cid:80)

(cid:17)p−1

i∈[w] (cid:101)fi

, where (cid:101)fi is the polynomial that approximates fi.

(cid:101)g def=
Note that (cid:101)g has degree (p−1)·maxi∈[w]{deg( (cid:101)fi)}, and that (cid:101)g(x) ∈ {0, 1} for every x ∈ {0, 1}n.
Furthermore, for every x, if (cid:101)fi(x) = fi(x) for every i ∈ [w], then (cid:101)g(x) = g(x), because in that
case





p−1

(cid:101)g(x) =



(cid:88)

fi(x)



i∈[w]

= MODp(f1(x), ..., fw(x)),

where the last equality uses the fact that vp−1 = 1 for every v ∈ GF(p) \ {0} (and 0p−1 = 0).
Again, the current replacement adds no approximation error.

3. The top gate is an OR gate: If g = OR(f1, ..., fw), then, using suitable (see next) linear functions
Lj : GF(p)w → GF(p), for j = 1, ..., ℓ, where ℓ is currently a free parameter, we approximate
g by the polynomial

(cid:101)g def= 1 −

(cid:89)

(cid:16)

1 − Lj( (cid:101)f1, ..., (cid:101)fw)p−1(cid:17)

j∈[ℓ]

where (cid:101)fi is the polynomial that approximates fi.
(cid:0)1 − Lj(v1, ..., vw)p−1(cid:1) ∈
Note that (cid:101)g has degree ℓ·(p−1)·maxi∈[w]{deg( (cid:101)fi)}, and that 1−(cid:81)
{0, 1} for every v1, ..., vw ∈ GF(p). Hence, (cid:101)g(x) ∈ {0, 1} for every x ∈ {0, 1}n. The key issue
is the selection of the Lj’s, and the clue for it is provided by the following claim.

j∈[ℓ]

Claim 2.1 (on a random linear combination of elements of a non-zero sequence): Suppose
that v1, ..., vw ∈ {0, 1} such that OR(v1, ..., vw) = 1. Then, for a random linear function
L : GF(p)w → GF(p), it holds that PrL[L(v1, ..., vw) = 0] = 1/p.

Proof: The value of a random linear function L : GF(p)w → GF(p) at a non-zero point
(v1, ..., vw) ∈ GF(p)w is uniformly distributed in GF(p), because L(z1, ..., zw) = (cid:80)
i∈[w] rizi,
where the ri’s are uniformly and independently distributed.

Selecting linear function L1, ..., Lℓ : GF(p)w → GF(p) uniformly at random, the following
holds for every x ∈ {0, 1}n such that (cid:101)fi(x) ∈ {0, 1} for every i ∈ [w]:

(cid:136) If (cid:101)f1(x) = · · · = (cid:101)fw(x) = 0, then all Lj’s evaluate to 0, which implies that (cid:81)

is identically 1.

j∈[ℓ](1−Lp−1

j

)

(cid:136) If (cid:101)fi(x) = 1 for some i ∈ [w], then each Lj evaluates to 0 with probability 1/p (equiv.,
evaluates to 1 with probability 1/p), which implies that the product
) is 1 with probability p−ℓ.

each 1 − Lp−1
(cid:81)
j∈[ℓ](1 − Lp−1

j

j

5



<!-- pdf-page: 7 -->
Recalling that 1 − (cid:81)

j∈[ℓ](1 − Lp−1

j

) ∈ {0, 1} always holds, we get



PrL1,...,Lw

OR( (cid:101)f1(x), ..., (cid:101)fw(x)) ̸= 1 −

(cid:89)

(cid:16)

1 − Lj( (cid:101)f1(x), ..., (cid:101)fw(x))p−1(cid:17)


 ≤ p−ℓ

(2)

j∈[ℓ]

Using an averaging argument, it follows that there exists a choice of linear function L1, ..., Lℓ :
GF(p)w → GF(p) such that, for a uniformly distributed x, it holds that



Prx∈{0,1}n

OR( (cid:101)f1(x), ..., (cid:101)fw(x)) ̸= 1 −

(cid:89)

(cid:16)

1 − Lj( (cid:101)f1(x), ..., (cid:101)fw(x))p−1(cid:17)


 ≤ p−ℓ.

(3)

j∈[ℓ]

It follows that replacing OR( (cid:101)f1(x), ..., (cid:101)fw(x)) by (cid:101)g adds an approximation error of at most p−ℓ.
4. The top gate is an AND gate: Analogously, if g = AND(f1, ..., fw), then we approximate g by (cid:101)g def=
), where (cid:101)fi is the polynomial that approximates fi and
the Lj’s are suitable linear functions.6 Again, the current replacement adds an approximation
error of p−ℓ.

1 − Lj(1 − (cid:101)f1, ..., 1 − (cid:101)fw

(cid:17)p−1

j∈[ℓ]

(cid:81)

(cid:16)

Hence, replacing each of the gates by the corresponding polynomial adds an approximation error of
at most p−ℓ, and so replacing all s gates yields an approximation error of at most s·p−ℓ. The degree
of the resulting polynomial, which approximates the circuit C, is at most ((p − 1) · ℓ)d. Aiming at
((p − 1) · ℓ)d ≤ D, we use ℓ = 1

p−1 · D1/d, and obtain an approximation error of s · p−D1/d/(p−1).

Digest. The key fact, captured by Claim 2.1, is that a random choice of a linear function is
positively correlated with an OR-gate. (We note that a somewhat weaker result can be achieved by
using a random 0-1 linear function (i.e., 0-1 coefficients only)).) In any case, Eq. (3) upper-bounds
the approximation error of replacing a single OR-gate (by a suitable degree (p − 1) · ℓ polynomial),
and the error bound of Lemma 2 follows by applying a union bound over all gates (while using an
adequate setting of ℓ). Note that raising various GF(p)-expressions to the power of p − 1 guarantees
that the resulting polynomial always yields a value in {0, 1}.

Proving Part 1 of Theorem 1. As stated above, Part 2 of the theorem (i.e., a lower bound for
MODq) is established by combining Lemma 2 with a proof that a degree
n polynomial over GF(p)
cannot approximate the n-bit MODq function. While Part 1 (i.e., a lower bound for Majority) can
be proven analogously (see Appendix), we establish a weaker version of Part 1 by observing that
any symmetric function (e.g., Parity (i.e., MOD2)) can be AC0-reduced to computing Majority. This
observation is proved next.

√

Let THn

k : {0, 1}n → {0, 1} denote the function that return 1 if and only if its input contains at
n+1 (x1n+1−k0k), where TH2n+1
least k ones, and note that THn
n+1 is the (2n + 1)-bit Majority
function. Now, letting wt(x1, ..., xn) def= |{i ∈ [n] : xi = 1}|, suppose that for some S ⊆ [n] the function

k (x) = TH2n+1

6Indeed, the expression for (cid:101)g can be obtained by observing that g = ¬OR(¬f1, ..., ¬fw).

6



<!-- pdf-page: 8 -->
f : {0, 1}n → {0, 1} satisfies f (x) = 1 if and only if wt(x) ∈ S. Then, for S = {s1, ..., sm}, it holds
that

f (x) =

(cid:95)

AND(THn

si(x), ¬THn

si+1(x)),

i∈[m]

s (x), ¬THn

because AND(THn
s+1(x)) = 1 if and only if wt(x) = s. Hence, a lower bound on the size of
AC0[p]-circuits of depth d + 3 that compute f (e.g., f = MOD2) yields a lower bound on the size of
AC0[p]-circuits of depth d that compute Majority. Actually, using specific features of the foregoing
reduction, a lower bound on the size of AC0[p]-circuits of depth d that compute f yields a lower
bound on the size of AC0[p]-circuits of depth d that compute Majority.7

Proving a special case of Part 2 of Theorem 1. We now turn to Part 2 of Theorem 1 (i.e.,
a lower bound for MODq). Specifically, we prove a special case of Part 2 (i.e., the case of q = 2), by
combining Lemma 2 with the following result –

Lemma 3 (on the error rate of low degree polynomials over GF(p) that approximate MOD2): There
exists a constant ϵ > 0 such that, for any prime p ≥ 3, any n-variate polynomial Q : GF(p)n →
n fails to compute the n-ary parity on at least ϵ · 2n of the n-bit inputs;
GF(p) of degree at most
that is,

√

Prx∈{0,1}n[Q(x) ̸= MOD2(x)] ≥ ϵ.

√

For any constant δ > 0, the claim holds (with a different ϵ > 0) also for polynomials of degree δ ·
n:
In particular, for δ < 1 we get ϵ = 0.5 − O(δ) whereas for δ > 1 we get ϵ = exp(−O(δ2)); actually,
the result holds also for non-constant δ (see Footnote 8 for details). The special case of Part 2
of Theorem 1 (i.e., the case of q = 2) follows by a suitable setting of parameters in Lemma 2.
Specifically, in contrast to Lemma 3, this setting implies that for a sufficiently small c > 0, it holds
that AC0[p]-circuits of depth d and size exp(c · n1/2d) can be approximated by degree
n polynomials
with an approximation error o(1).
Proof: Let G def= {x ∈ {0, 1}n : Q(x) = MOD2(x)} denote the set of inputs on which Q equals
MOD2. We shall prove that G misses a constant fraction of {0, 1}n by using Q to present a class
of p(1−Ω(1))·2n polynomials that can compute p|G| different functions. Specifically, the low degree
of Q will be used to upper-bound the degree of the polynomials in the foregoing class (which will
contain only multi-linear polynomials).

√

The crucial step is a variable substitution that maps xi ∈ {0, 1} to (−1)xi ∈ {±1} ≡ {1, q − 1},
where, for xi ∈ {0, 1}, it holds that (−1)xi = (1 − xi) · (−1)0 + xi · (−1)1 = 1 − 2xi. The bene-
fit of this technical step is that it related MOD2(x1, ..., xn) to (cid:81)
i∈[n](−1)xi; that is, (−1)MOD2(x1,...,xn) =
(cid:81)

i∈[n](−1)xi. Accordingly, we consider the polynomial R : GF(p)n → GF(p) defined as R(y1, ..., yn) def=

1 − 2 · Q(x1, ..., xn), where xi = (1 − yi)/2 (equiv., yi = 1 − 2xi), noting that R has the same degree
as Q. The salient feature of the polynomial R is that R(y1, ..., yn) = (cid:81)
i∈[n] yi holds whenever the
corresponding (x1, ..., xn) is in G. This is the case because for every (x1, ..., xn) ∈ {0, 1}n it holds

7Specifically, we use the fact that f (x) equals (cid:80)

si+1(x))), when the sum and the 2-argument
multiplication are in GF(p), and the fact that a (depth d+3) circuit that has a corresponding form can be approximated
by a polynomial that has degree twice the degree of the depth d circuit that computes THn
s .

si (x) · (1 − THn

i∈[m](THn

7



<!-- pdf-page: 9 -->
that

(1 − 2xi) =

(cid:89)

i∈[n]

(cid:89)

(−1)xi

i∈[n]

= (−1)MOD2(x1,....,xn)
= 1 − 2 · MOD2(x1, ...., xn)

whereas (x1, ..., xn) ∈ G implies that MOD2(x1, ...., xn) = Q(x1, ..., xn). Hence, (cid:81)
1 − 2 · Q(x1, ...., xn) for every (x1, ..., xn) ∈ G, which means that (cid:81)
((1 − y1)/2, ...., (1 − yn)/2) ∈ G.
Consequently, letting H def=

(cid:110)
y ∈ {±1}n : R(y) = (cid:81)

, and observing that |H| = |G|, we
seek to upper-bound |H|. The key fact that we shall use is that R has a magical feature: It
is a degree
n polynomial that, when restricted to H, equals a degree n polynomial (specifically,
(cid:81)
i∈[n] yi). (Indeed, the letter ‘R’ was chosen for evoking the degree-reduction feature of R (when

i∈[n](1 − 2xi) =
i∈[n] yi = R(y1, ...., yn) for every

i∈[n] yi

√

(cid:111)

restricted to H).)

Towards upper-bounding |H|, we consider the class F of all function f : H → GF(p), and
note that |F| = p|H|. We first observe that each f ∈ F can be written as a linear combination of
multi-linear monomials, because σ2 = 1 for every σ ∈ {±1}. Hence, for every y ∈ H,

f (y) =

(cid:88)

fI ·

I⊆[n]

yi,

(cid:89)

i∈I

where the fI ’s are in GF(p). Furthermore, for every y ∈ H, using R(y) = (cid:81)
the degree of any monomial to at most (n +
R(y)·(cid:81)
i∈[n]\I yi, which has degree
√
n)/2. (We stress that R(y) · (cid:81)
(n +
√
n)/2, where here, and in the line above, we used y2
(n +
t def= (n +

i∈[n] yi we decrease
n)/2, because (cid:81)
· (cid:81)
i∈I yi =
i∈[n]\I yi =
√
n+(n−|I|), whereas either |I| ≤ (n+
n+(n−|I|) <
i∈[n]\I yi is a sum of multi-linear monomials of degree at most
i = 1 for yi ∈ {±1}.) Hence, letting

i∈[n] yi
n)/2 or

n)/2, we get

(cid:16)(cid:81)
√

√

√

√

(cid:17)

f (y) =

(cid:88)

=

I⊆[n]:|I|≤t
(cid:88)

I⊆[n]:|I|≤t

fI ·

fI ·

(cid:89)

i∈I
(cid:89)

i∈I

yi +

yi +

(cid:88)

I⊆[n]:|I|>t
(cid:88)

I⊆[n]:|I|>t

fI ·

yi

(cid:89)

i∈I

fI · R(y) ·

(cid:89)

yi

i∈[n]\I

which means that each f ∈ F can be represented as a linear combination of multi-linear monomials
(cid:1), we
of degree at most t = (n +
(cid:1), and the claim follows (because

n)/2. Noting that the number of such monomials is (cid:80)t
i), which implies |H| ≤ (cid:80)t

(cid:0)n
i

i=0

√

(cid:80)t

(cid:0)n
i

i=0

conclude that |F| ≤ p
(cid:80)
√

i=0 (n
(cid:1) = (1 − Ω(1)) · 2n).8

i≤0.5n+O(

n)

(cid:0)n
i

8More generally, denoting the degree of Q by D and letting t = (n + D)/2, we need to upper-bound (cid:80)

(cid:0)n
i

(cid:1).

i≤t

√

For D ≤

n, we use

(cid:88)

i≤t

(cid:32)

(cid:33)

n
i

(cid:88)

≤

i≤(n−1)/2

(cid:32)

(cid:33)

n
i

+ (1 + (D/2)) · O(2n/

√

n) ≤ (0.5 + O(D/

√

n)) · 2n

whereas for D >

√

n we have 2−n · (cid:80)

i≤t

(cid:0)n
i

(cid:1) = 1 − exp(−O(D2/n)).

8



<!-- pdf-page: 10 -->
√

Digest. Lemma 3 starts with an algebraic manipulation that translates the existence of a low
degree polynomial that approximates MOD2 (over {0, 1}n) to the existence of a low degree polynomial
that allows to effectively (i.e., w.r.t {±1}n) decrease the degree of any monomial to t def= 0.5n +
O(
n), which in turn upper-bounds the quality of the initial approximation. Specifically, if the
initial approximation is correct on N of the inputs (in {0, 1}n), then the degree reduction holds
for N other inputs (in {±1}n ⊆ GF(p)n), which span a vector space of dimension N , whereas
the space of functions (defined over these N inputs) that can be express as a linear combination
(cid:1) = (1 − Ω(1)) · 2n.
of multi-linear monomials of degree at most t has dimension at most (cid:80)
(Hence, N ≤ (1 − Ω(1)) · 2n.)

The observation that enables this miraculous degree reduction is that (−1)MOD2(x) = (cid:81)

i∈[n](−1)xi.
This observation is put into work by the mapping xi (cid:55)→ (−1)xi, which coincides (over {0, 1}) with
the linear function L(ζ) = 1 − 2ζ = (1 − ζ) · (−1)0 + ζ · (−1).

(cid:0)n
i

i≤t

Extension to arbitrary q ̸= p.
It is tempting to try to extend the foregoing argument to MODq,
when using a qth root of unity (over the complex numbers) and the corresponding extension field
of GF(p). Although this idea may not be work as stated, something along these lines does work
(i.e., we consider a (q − 1)-dimensional extension field and an element of multiplicative order q in
it).9 But the real difficulty is that, in general, unlike in the case of q = 2, it does not hold that
MODq(x1, ..., xn) equals to modq(x1, ..., xn) def= (cid:80)
i∈[n] xi mod q, even when the xi’s are restricted to
{0, 1}. Loosely speaking, this difficulty is resolved by working with modq (rather than with MODq).
Another difficulty is that the product of multi-linear monomials is not necessarily a multi-linear
monomial, even when the variables are restricted to {1, ω}, where ω denotes an element of order q in
the extension field. (This is because, unlike in the case of q = 2, it does not holds that ωe ∈ {1, ω}
for every e ∈ Zq = {0, 1, ..., q − 1}.) This difficulty is resolved by observing that we can reduce the
individual degrees of variables over {1, ω} by using adequate linear transformations; that is, for a
variable ζ ∈ {1, ω}, for any e ∈ Zq, we can replace ζ e with the linear (in ζ) function ζ−1
ω−1 · ωe + ζ−ω
1−ω .
The bottom-line is that, using the foregoing modifications, it is possible to prove an extension
of Lemma 3 to arbitrary q ̸= p, where this extension refers to approximating modq rather than to
approximating MODq. Although this extension does not fit Lemma 2, which refers to approximating
MODq, we shall also show how to bridge this gap. For details see Section 3.

3 Advanced reading

Recall that Lemma 3 relies on translating a low degree polynomial (over GF(p)) that approximates
MOD2 ≡ mod2 over {0, 1}n to a low degree polynomial (also over GF(p)) that approximates the
product of n variables that assume values in {±1} = {1, p − 1}. As stated in the foregoing digest,
it is tempting to try to extend this strategy to modq by using a qth root of unity (over the complex
numbers) and the corresponding extension field of GF(p).

One reason to be alarmed about this proposal is that it is unclear where we use the condition
p ̸= q. In fact, in case p = q, for every e ∈ Z, it holds that pe − 1 is not divisible by q, which means
that the corresponding extension field has no element of multiplicative order q. In contrast, when
p ̸= q, it holds that pq−1 ≡ 1 (mod q), which means that q divides pq−1 − 1, which implies the
(q − 1)-dimensional extension field of GF(p) has elements of multiplicative order q.

9See discussion at the beginning of Section 3.

9



<!-- pdf-page: 11 -->
A parenthetical question is whether the foregoing ((q−1)-dimensional) extension field (of GF(p))
is spanned by the powers of the qth root of unity (over the complex numbers). This is the case if
and only if (xq − 1)/(x − 1) = (cid:80)q−1
i=0 xi is an irreducible polynomial over GF(p). Note that for some
p ̸= q the answer is positive, whereas for others it is negative.

Notation:
In light of the foregoing, fixing an arbitrary pair of primes, denoted p ̸= q, we denote
by K the (q − 1)-dimensional extension field of GF(p), and denote by ω ∈ K an arbitrary element
of multiplicative order q. We shall also use the notation Zq

def= {0, 1, ..., q − 1}.

Recalling that modq : {0, 1}n → Zq is defined such that modq(x1, ..., xn) def= (cid:80)

i∈[n] xi mod q, we
face the fact that functions with range in GF(p) cannot possibly approximate modq well if q > p.
This problem does not arise when q < p, because then we can embed Zq in GF(p), let alone do so
in a straightforward and transparent manner. Hence, we start with the case of q < p, and postpone
the case of q > p to later.

3.1 The case of q < p

With the foregoing preliminaries in place, we start by stating and proving the natural extension of
Lemma 3. Note that this extension refers to modq rather than to MODq, but mod2 ≡ MOD2 and indeed
the extension coincides with Lemma 3 when q = 2.

Lemma 4 (on the error rate of low degree polynomials over GF(p) that approximate modq): There
exists a constant ϵ > 0 such that, for any prime p > q, any n-variate polynomial Q : GF(p)n →
GF(p) of degree at most

n fails to compute modq on at least ϵ · 2n of the n-long inputs; that is,

√

Prx∈{0,1}n[Q(x) ̸= modq(x)] ≥ ϵ.

q + q

As stated above, there is no point in considering the case of p < q, because in that case no
polynomial over GF(p) can approximate modq with error rate smaller than (q − p − o(1))/q, since
Prx∈{0,1}n[modq(x) ∈ {0, 1..., p − 1}] ≤ p
2n . Note that, while Lemma 4 asserts that low de-
gree polynomials over GF(p) cannot approximate modq well, the contrast with Lemma 2 requires
obtaining such a result for MODq. We shall address this gap later.
Proof: Following the proof strategy of Lemma 3, letting G def= {x ∈ {0, 1}n : Q(x) = modq(x)}, we
shall prove that G misses a constant fraction of {0, 1}n by using Q to present a class of |K|(1−Ω(1))·2n
polynomials that can compute |K||G| different functions. We prove this assertion by extending the
proof of Lemma 3. The extension is conceptually straightforward, but involves more technicalities
than the special case of q = 2. Details follow.

Again, the crucial step is a variable substitution. Here, we map xi ∈ {0, 1} to ωxi ∈ {1, ω} ⊂ K,
where ω is an arbitrary fixed element of order q in the multiplicative group of the extension field
K. (Indeed, for q = 2, it holds that ω = −1 and K = GF(p).) The benefit of this substitution
is that it allows to relate modq(x1, ..., xn) to (cid:81)
i∈[n] ωxi. Noting
that modq(x) is in Zq, it is useful to consider the mapping ζ (cid:55)→ ωζ as defined over Zq, and actually
to extend it to K. We note that this mapping as well as its inverse can be computed by degree q − 1
polynomials over K, denoted M and M ′; that is, there exists degree q − 1 polynomials M, M ′ :
K → K such that M (ζ) = ωζ and M ′(M (ζ)) = ζ for every ζ ∈ Zq.

i∈[n] ωxi; that is, ωmodq(x1,...,xn) = (cid:81)

10



<!-- pdf-page: 12 -->
Accordingly, we consider the polynomial R : Kn → K defined as R(y1, ..., yn) def= M (Q(x1, ..., xn)),
where xi = M ′(yi) (equiv. (for xi ∈ {0, 1}), yi = M (xi)), while noting that R has degree (q−1)2·
n.
Actually, defining R (over K) requires viewing Q as a polynomial over K, which means replacing
the field operations of GF(p) by field operations of K. The salient feature of the polynomial R is
that R(y1, ..., yn) = (cid:81)
i∈[n] yi holds whenever the corresponding (x1, ..., xn) = (M ′(y1), ...., M ′(yn))
is in G. This is the case because for every (x1, ..., xn) ∈ {0, 1}n it holds that

√

(cid:89)

i∈[n]

M (xi) =

(cid:89)

ωxi

i∈[n]

= ωmodq(x1,....,xn)
= M (modq(x1, ...., xn))

whereas (x1, ..., xn) ∈ G implies that modq(x1, ...., xn) = Q(x1, ..., xn). Hence, (cid:81)
M (Q(x1, ...., xn)) for every (x1, ..., xn) ∈ G, which means that (cid:81)
(y1, ..., yn) ∈ {1, ω}n such that (M ′(y1), ...., M ′(yn)) ∈ G.

i∈[n] M (xi) =
i∈[n] yi = R(y1, ...., yn) for every

(cid:110)
y ∈ {1, ω}n : R(y) = (cid:81)

Consequently, letting H def=

i∈[n] yi

, and observing that |H| ≥ |G|, we
seek to upper-bound |H|. The key fact that we shall use is that R has a magical feature: It is a
degree (q −1)2 ·
n polynomial that, when restricted to H, equals a degree n polynomial (specifically,
(cid:81)
i∈[n] yi).
Towards upper-bounding |H|, we consider the class F of all function f : H → K, and note that
|F| = |K||H|. We first show that each f ∈ F can be written as a linear combination of multi-linear
monomials. This is the case because, for any distinct α, β ∈ K, any function g : {α, β} → K can be
written as a linear function; that is,

√

(cid:111)

Lα,β,g(ζ) def=

ζ − β
α − β

· g(α) +

ζ − α
β − α

· g(β)

(4)

satisfies Lα,β,g(α) = g(α) and Lα,β,g(β) = g(β). In particular, for any e1, ..., en ∈ Zq, we can replace
(cid:81)
(yi), where ge(ζ) = ζ e, because we wish to preserve the value only over
(y1, ..., yn) ∈ {1, ω}n. Hence, for every y ∈ H, it holds that

i with (cid:81)

i∈[e] L1,ω,gei

i∈[e] yei

f (y) =

(cid:88)

fI ·

I⊆[n]

yi,

(cid:89)

i∈I

where the fI ’s are in K. Furthermore, for every y ∈ H, using R(y) = (cid:81)
i∈[n] yi we decrease the
√
number of variables that appear in any monomial to at most (n + (q − 1)2 ·
n)/2. This is the case
because





(cid:89)

i∈I

yi =



(cid:89)

yi

 ·

(cid:89)

yq−1
i = R(y) ·

(cid:89)

yq−1
i

,

i∈[n]

i∈[n]\I

i∈[n]\I

i = 1 for each i ∈ I (while relying on yi ∈ {1, ω}), whereas R(y) · (cid:81)

where we use yq
a linear combination of monomials such that each contain at most
so, either |I| ≤ (n + (q − 1)2 ·
t def= (n + (q − 1)2 ·

n)/2, we get

n + (n − |I|) < (n + (q − 1)2 ·

is
n + (n − |I|) variables (and
n)/2). Thus, letting

i∈[n]\I yq−1

n)/2 or

√

√

√

√

√

i

f (y) =

(cid:88)

I⊆[n]:|I|≤t

fI ·

(cid:89)

i∈I

yi +

(cid:88)

I⊆[n]:|I|>t

fI ·

yi

(cid:89)

i∈I

11



<!-- pdf-page: 13 -->
(cid:88)

=

I⊆[n]:|I|≤t

fI ·

(cid:89)

i∈I

yi +

(cid:88)

fI · R(y) ·

(cid:89)

yq−1
i

I⊆[n]:|I|>t

i∈[n]\I

which means that each f ∈ F can be represented as a linear combination of monomials such that
each monomial contains at most t = (n + (q − 1)2 ·
n)/2 variables. Replacing powers of the various
i is replaced by L1,ω,ge, where ge(ζ) = ζ e), it
variables by the corresponding linear function (i.e., ye
follows that each f ∈ F can be represented as a linear combination of multi-linear monomials of
(cid:1), we conclude that
degree at most t. Noting that the number of such monomials is N def= (cid:80)t
|F| ≤ |K|N , and the claim follows (because N = (1 − exp(−Ω(q4))) · 2n = (1 − Ω(1)) · 2n).

(cid:0)n
i

i=0

√

Digest. The proof of Lemma 4 mimics the proof of Lemma 3, while replacing the field GF(p) by
its q − 1 dimensional extension K and replacing −1 ∈ GF(p) by ω ∈ K (of multiplicative order q).
We highlight two additional modifications:

1. Although the inputs to modq are bits, the mapping ζ (cid:55)→ ωζ is defined over Zq (in order to
accommodate also the output value). This mapping and its inverse are performed by degree
(q − 1) polynomials over K, and consequently the degree of R is larger by a factor of (q − 1)2
than the degree of Q.

2. In two places, arbitrary powers of yi ∈ {1, ω} are replaced by linear functions of yi (presented
in Eq. (4)). This replacement allows the continued pivoting of the argument on multi-linear
(low degree) polynomials that compute functions in F.

We stress that Lemma 4 refers to approximating modq : {0, 1}n → Zn, whereas the contrast with
Lemma 2 (which allows establishing Part 2 of Theorem 1) refers to approximating MODq : {0, 1}n →
{0, 1}. This gap is addressed next.

Bridging the gap (between approximating MODq : {0, 1}n → {0, 1} and approximating
modq : {0, 1}n → Zq). Recall that Lemma 4 asserts that low degree polynomials over GF(p) cannot
approximate modq well; specifically, every degree
n polynomial over GF(p) approximates modq
with error rate Ω(1). However, the contrast with Lemma 2 requires obtaining such a result for
MODq (i.e., showing that low degree polynomials over GF(p) have error rate Ω(1) with respect to
MODq). We prove the contrapositive: Starting with a polynomial (over GF(p)) that approximates
MODq with error rate o(1), we present a polynomial of the same degree (over the same field) that
approximates modq with error rate o(1).

√

We first observe that computing modq : {0, 1}n → Zq can be reduced to computing MODq :

{0, 1}n+q → {0, 1}. This is done by observing that

modq(x) =

(cid:88)

i∈[q−1]

(1 − MODq(x1q−i0i)) · i,

which holds because MODq(x1q−i0i)) = 0 if and only if modq(x1q−i0i) = 0 (which holds if and only
if modq(x) = i). Analogously, an approximating polynomial Q for MODq can be converted to an
approximating polynomial Q′ for modq; that is, Q′(x) = (cid:80)
i∈[q−1](1 − Q(x1q−i0i)) · i. Note that
although the resulting polynomial Q′ preserves the degree of Q, it does does not preserve the error

12



<!-- pdf-page: 14 -->
rate of Q; yet, the error rate of Q′ is at most a (q − 1) · 2q factor larger than the error rate of Q;
that is,

Prx∈{0,1}n[Q′(x) ̸= modq(x)] ≤

(cid:88)

i∈[q−1]

Prx∈{0,1}n[Q(x1q−i0i) ̸= MODq(x1q−i0i)]

≤ (q − 1) ·

Prz∈{0,1}n+q [Q(z) ̸= MODq(z)]
2−q

which we can tolerate (because q is a constant whereas the error rate of Q is o(1)).

3.2 The case of q > p

The hypothesis q < p was (only) used in Section 3.1 in order to allow for an embedding of Zq in
GF(p). In addition, the association of Zq with {0, 1, ..., q − 1} and of GF(p) with {0, 1, ..., p − 1}
allowed for a straightforward embedding that was not even stated explicitly. Essentially, all that
is needed when turning to the case of q > p is to pick an integer e > 1 such that q < pe (e.g.,
e = ⌈logp q⌉), and consider an embedding of Zq in GF(p)e. Denoting the embedding by ψ : Zq →
GF(p)e, specific modifications to Section 3.1 include:

(cid:136) In Lemma 4, we consider Q : GF(p)n → GF(p)e, and state the hypothesis as

Prx∈{0,1}n[Q(x) ̸= ψ(modq(x))] ≥ ϵ.

Note that there is no need to apply ψ to the (binary) input; we only apply it to the desired
output (which is in Zq).
Similarly, we start the proof by defining G def= {x ∈ {0, 1}n : Q(x) = ψ(modq(x))}.

(cid:136) In the proof of Lemma 4, we replace the mapping M : K → K and M ′ : K → K with
the mappings M : Ke → K and M ′ : K → K such that M (ψ(ζ)) = ωζ for every ζ ∈ Zq
and M ′(ωζ) = ζ for every ζ ∈ {0, 1}. We stress that now M is computed by an e-variate
polynomial of individual degree p − 1 and M ′ is computed by a linear function.10 We then
define R : Kn → K such that R(y1, ..., yn) def= M (Q(M ′(y1), ..., M ′(yn))), while noting that R
has degree e · (p − 1) ·

n, and observe that for (x1, ..., xn) ∈ G it holds that

√

R(ωx1, ..., ωxn) = M (Q(M ′(ωx1), ..., M ′(ωxn)))

= M (Q(x1, ..., xn))
= M (ψ(modq(x1, ..., xn)))
= ωmodq(x1,....,xn)
=

ωxi.

(cid:89)

i∈[n]

10Indeed, the definition of M ′ differs from the one used in the proof of Lemma 4, but we could have used the
current definition also there (because we only refer to the value of M ′ on {1, ω}).
In contrast, an extension of
the definition of M ′ that was used in the proof of Lemma 4 would let M ′ : K → Ke be computed by an e-long
sequence of univariate polynomials of degree q − 1 such that M ′(ωζ) = ψ(ζ) for every ζ ∈ Zq.
(In that case,
R(y1, ..., yn) def= M (Q(M ′(y1), ..., M ′(yn))), where Q operates on embeddings of elements of Zq in Ke, would have had
degree e · (p − 1) · (q − 1) ·

n.

√

13



<!-- pdf-page: 15 -->
(cid:110)
y ∈ {1, ω}n : R(y) = (cid:81)

Letting H def=
, and observing that |H| ≥ |G| (as before), we
proceed exactly as in the second part of the proof (i.e., the part in which |H| is upper-
bounded).

i∈[n] yi

(cid:111)

(cid:136) When bridging the gap between MODq : {0, 1}n → {0, 1} and modq : {0, 1}n → Zq, we define

Q′(x) = (cid:80)

i∈[q−1](1 − Q(x1q−i0i)) · ψ(i) ∈ GF(p)e.

We stress that the foregoing refers to a restating of Lemma 4 in which the approximation of modq
is provided by an e-long sequence of (n-variant) polynomials over GF(p), where e = ⌈logp q⌉. An
alternative presentation, which avoids the distinction between the case of q < p and the case of
q > p, can be obtained by considering ωmodq(x) as a representation of modq(x); this means starting
with a (low degree) polynomial Q : Kn → K and lower-bounding Prx∈{0,1}n[Q(x) ̸= ωmodq(x)].

4 Beyond the recommended reading

Recall that modq was defined over {0, 1}n and Lemma 4 refers to the error rate (w.r.t modq) of any
low-degree polynomial Q : GF(p)n → GF(p); that is, the error rate is Prx∈{0,1}n[Q(x) ̸= modq(x)]. It
is natural to extend modq over Zn
q : Zn
i∈[n] xi mod q)
q) of any low-degree polynomial Q : GF(p)n → GF(p); that
and consider the error rate (w.r.t mod′
q [Q(x) ̸= mod′
q(x)].
is, the error rate is Prx∈Zn

q → Zq be defined as mod′

q (i.e., let mod′

q(x) = (cid:80)

As shown at the end of Section 4.1, approximating modq (by low degree polynomials over GF(p))
is reducible to approximating mod′
q (by such polynomials). The converse holds too, and combining
the converse reduction with a lower bound on the error rate of low degree polynomials wrt mod′
q
yields an alternative proof of Lemma 4. The resulting proof is more complicated than the one
Indeed, in this section, we shall prove that
presented in Section 3, but it has its own merits.
the error rate of any degree
q is lower-bounded by a positive
constant. The proof will extend and modify the proof that was presented in Section 3.

n polynomial over GF(p) wrt mod′

√

When trying to extend Lemma 4 to mod′

q, we face (again) the fact the product of multi-linear
monomials is not necessarily a multi-linear monomial. This difficulty was resolved in the proof of
Lemma 4 by reducing all individual degrees to 1, while capitalizing on the fact that we only cared
about the value of the corresponding univariate functions at two points (i.e., 1 and ω). This is
no longer the case in the current context, because we care about the values of these univariate
functions at all powers of ω. However, this is not a problem because we can consider all monomials
of total degree at most t and individual degree at most q − 1. Their number will be contrasted with
the number of functions over the subset of Zn

q on which Q agrees with mod′
q.

Notation and organization: As in Section 3, fixing an arbitrary pair of primes, denoted p ̸= q,
we denote by K the q − 1 dimensional extension field of GF(p), and denote by ω ∈ K an arbitrary
element of multiplicative order q. We distinguish again between the case of q < p, where we can
embed Zq in GF(p), and the case of q > p, where we embed Zq in GF(p)e for e = ⌈logp q⌉.

4.1 The case of q < p

Recall that mod′

q : Zn

q → Zq is defined by mod′

q(x1, ..., xn) def= (cid:80)

i∈[n] xi mod q.

14



<!-- pdf-page: 16 -->
Lemma 5 (on the error rate of low degree polynomials over GF(p) that approximate mod′
q): There
exists a constant ϵ > 0 such that, for any prime p > q, any n-variate polynomial Q : GF(p)n →
GF(p) of degree at most

q on at least ϵ · qn of the n-long inputs; that is,

n fails to compute mod′

√

Prx∈{0,1,...,q−1}n[Q(x) ̸= mod′

q(x)] ≥ ϵ.

q : Q(x) = mod′

Proof: Let G def= {x ∈ Zn
q. We
q by using Q to present a class of |K|(1−Ω(1))·qn
shall prove that G misses a constant fraction of Zn
polynomials that can compute |K||G| different functions. We prove this assertion by extending the
proof of Lemma 4. The extension is conceptually straightforward, although it differs in its technical
details.

q(x)} denote the set of inputs on which Q equals mod′

Again, the crucial step is a variable substitution. Here, we map xi ∈ Zq to ωxi, noting that
q(x1,...,xn) = (cid:81)
ωmod′
i∈[n] ωxi. Note that the mapping ζ (cid:55)→ ωζ as well as its inverse can be computed by
degree q − 1 polynomials over K, denoted M and M ′; that is, there exists degree q − 1 polynomials
M, M ′ : K → K such that M (ζ) = ωζ and M ′(M (ζ)) = ζ for every ζ ∈ Zq. Accordingly, we consider
the polynomial R : Kn → K defined as R(y1, ..., yn) def= M (Q(x1, ..., xn)), where xi = M ′(yi) (resp.,
yi = M (xi) when xi ∈ Zq ⊂ GF(p)). (Again, defining R (over K) requires viewing Q as a polynomial
over K, which means replacing the field operations of GF(p) by field operations of K.) Note that
although G is defined differently than in the proof of Lemma 4, the definitions of M, M ′ and R
(and the following feature of R) remain intact.
The salient feature of the degree (q − 1)2 ·

i∈[n] M (xi) equals M (Q(x1, ...., xn)) for every (x1, ..., xn) ∈ G, which means that (cid:81)

i∈[n] yi
holds whenever the corresponding (x1, ..., xn) is in G (i.e., (M ′(y1), ...., M ′(yn)) ∈ G).11 Hence,
(cid:81)
i∈[n] yi =
R(y1, ...., yn) for every (y1, ...., yn) ∈ {ωe : e ∈ Zq}n such that (M ′(y1), ...., M ′(yn)) ∈ G. Thus,
(cid:111)
letting H def=
, and observing that |H| ≥ |G|, we seek to upper-
bound |H|. The key fact that we shall use is that R has a magical feature: It is a polynomial of
degree at most (q − 1)2 ·
n that, when restricted to H, equals a degree n polynomial (specifically,
(cid:81)
i∈[n] yi). Indeed, the foregoing mimics the proof of Lemma 4, and the deviation comes in the next

n polynomial R is that R(y1, ..., yn) = (cid:81)

(cid:110)
y ∈ {ωe : e ∈ Zq}n : R(y) = (cid:81)

i∈[n] yi

√

√

paragraph.

Towards upper-bounding |H|, we consider the class F of all function f : H → K, and note that
|F| = |K||H|. We first observe that each f ∈ F can be written as a linear combination of monomials
of individual degree at most q − 1, because σq = 1 for every σ ∈ {ωe : e ∈ Zq}. Furthermore, for
every y ∈ H, using R(y) = (cid:81)
i∈[n] yi we shall decrease the total degree of any monomial to at
√
most t def= ((q − 1) · n + 2(q − 1)3 ·
n)/2, by multiplication with a small power of R. Specifically,
consider an arbitrary monomial (cid:81)
i∈[n] yei
i , where all ei’s are in Zq. Then, there exists j ∈ Zq
such that (cid:80)
i∈[n](ei + j mod q) ≤ (q − 1) · n/2, where the latter sum is over the integers, because

11As in the proof of Lemma 4, this is the case because for every (x1, ..., xn) ∈ Zn

q it holds that

(cid:89)

i∈[n]

M (xi) =

(cid:89)

ωxi

i∈[n]

q (x1,....,xn)

= ωmod′
= M (mod′

q(x1, ...., xn))

whereas (x1, ..., xn) ∈ G implies mod′

q(x1, ...., xn) = Q(x1, ..., xn).

15



<!-- pdf-page: 17 -->
Ej∈Zq [ei + j mod q] = Ej∈Zq [j] = (q − 1)/2. Using this j ∈ Zp and writing






j





(cid:89)

yi



·



(cid:89)

yei
i

 =

i∈[n]

i∈[n]

yei+j mod q
i

(cid:89)

i∈[n]

(5)

it follows that the r.h.s of Eq. (5) has total degree at most (q − 1) · n/2. Hence, using suitable je’s
in Zq (i.e., for every e = (e1, ..., en), we use je ∈ Zq such that (cid:80)
i∈[n](ei + je mod q) ≤ (q − 1) · n/2,
where the latter sum is over the integers), we can write any f ∈ F as

f (y) =

(cid:88)

fe ·

(cid:89)

yei
i

e=(e1,...,en)∈Zn
q

i∈[n]




q−je mod q

=

=

(cid:88)

e=(e1,...,en)∈Zn
q
(cid:88)

e=(e1,...,en)∈Zn
q

fe ·



(cid:89)

i∈[n]

yi



fe · R(y)q−je mod q ·

(cid:89)

·

yei+je mod q
i

i∈[n]
yei+je mod q
i

(cid:89)

i∈[n]

where the fe’s are in K. We note that R(y)q−je mod q · (cid:81)
is a linear combination of
monomials of total degree at most (q − 1) · deg(R) + ((q − 1) · n/2) ≤ t and individual degree at most
q − 1, where the later fact uses yq
i = 1 for yi ∈ {ωe : e ∈ Zq}. This means that each f ∈ F can be
represented as a linear combination of monomials of total degree at most t and individual degree at
most q − 1. The number of such monomials is (1 − exp(−O(q4))) · qn, because the probability that
the sum of n independent random variables that are uniformly and independently distributed in
Zq exceeds t = 0.5(q − 1)n + (q − 1)3√

n is exp(−O(q4)). It follows that |F| ≤ |K|(1−Ω(1))·qn.

i∈[n] yei+je mod q

i

q : Zn

q → Zq to approximating modq : {0, 1}n → Zq.
Reducing the approximation of mod′
The reduction is quite straightforward: Essentially, we may Zq to (q − 1)-bit long strings such
that w ∈ Zq is mapped to a string of Hamming weight w. That is, we use the unary encoding
U : Zq → {0, 1}q−1 such that U (σ) = 1σ0q−1−σ, while noting that this encoding can be computed
by an (q − 1)-long sequence of degree q − 1 univariate polynomials over GF(p), where Zq ⊆ GF(p)
q → Zq to computing
relies on q < p. Using this encoding, we can reduce computing mod′
modq : {0, 1}(q−1)·n → Zq by observing that

q : Zn

mod′

q(x1, ..., xn) = modq(U (x1), ..., U (xn)).

Analogously, an approximating polynomial Q for modq can be converted to an approximating poly-
nomial Q′ for mod′
q; that is, Q′(x) = Q(U (x1), ..., U (xn)). Indeed, the degree of Q′ is q − 1 times
larger than the degree of Q, but the real problem is that the error rate is not preserved; in fact,
the error rate may increase by a factor of (2q−1/q)n, which we cannot afford.

Thus, an additional idea is needed. Specifically, letting n′ = (q − 1) · n, we use a random
bijection Π : {0, 1}n′ → {0, 1}n′ that preserves the Hamming weight of the n′-bit long string;
that is Π(z1, ...., zn′) = (zπ(1), ...., zπ(n′)), where π is a random permutation of [n′]. Note that
if X = (X1, ..., Xn) is uniformly distributed in Zn
q , then Π(U (X1), ..., U (Xn)) is o(1)-close to be
uniformly distributed in {0, 1}n′, because the total variation distance between the number of 1’s

16



<!-- pdf-page: 18 -->
in (U (X1), ..., U (Xn)) (which equals (cid:80)
n′-bit long string vanishes with n. Hence,

i∈[n] Xi) and the number of 1’s in a uniformly distributed

Pr(x1,...,xn)∈Zn

q ,π∈Symn′ [Q(Π(U (x1), ..., U (xn))) ̸= mod′

q(x1, ...., xn)]

= Pr(x1,...,xn)∈Zn
≤ Pr(z1,...,zn′ )∈{0,1}n′ [Q(z1, ..., zn′) ̸= modq(z1, ...., zn′)] + o(1)

q ,π∈Symn′ [Q(Π(U (x1), ..., U (xn))) ̸= modq(U (x1), ...., U (xn))]

and it follows that there exists a permutation π such that the corresponding (routing permutation)
Ππ (i.e., Ππ(z1, ...., zn′) = (zπ(1), ...., zπ(n′))) satisfies

Pr(x1,...,xn)∈Zn

q

[Q(Ππ(U (x1), ..., U (xn))) ̸= mod′

q(x1, ...., xn)]

≤ Pr(z1,...,zn′ )∈{0,1}n′ [Q(z1, ..., zn′) ̸= modq(z1, ...., zn′)] + o(1).

Using this π, we redefine Q′(x) def= Q(Ππ(U (x1), ..., U (xn))), and obtain the desired approximating
polynomial (while observing that Ππ only permutes variables).

q : Zn
q → Zq.
Reducing the approximation of modq : {0, 1}n → Zq to the approximating mod′
We first present a randomized reduction of computing modq to approximating mod′
q. Essentially, on
input x = (x1, ..., xn) ∈ {0, 1}n, the reduction selects a random r = (r1, ..., rn) ∈ Zn
q , and outputs
the sum (mod q) of q − mod′
q(r + x mod q), where (r + x mod q) = ((r1 + x1 mod
q), ..., (rn + xn mod q)). Analogously, an approximating polynomial Q for mod′
q can be converted to
a “randomized polynomial” Qr that computes modq correctly (w.h.p.) on each input. Specifically,
observing that the (2-argument) addition (modulo q) can be computed by a bivariate polynomial of
individual degree q − 1, denoted A, and letting Qr(x) def= A(q − mod′
q(r), Q(A(r1, x1), ..., A(rn, xn))),
for every x ∈ {0, 1}n, we have

q(r) and mod′

Prr∈Zn

q [Qr(x) = modq(x)] = Prr∈Zn
= Prr∈Zn

q [Q(r + x mod q) = modq(r + x mod q)]
(cid:2)Q(r) = mod′

q(r)](cid:3) ,

q

which means that (for every x) the randomized polynomial Qr (in which q − mod′
computes modq(x) with error probability that equals the error rate of Q w.r.t mod′
Hence,

q(r) is a constant)
q → Zq.

q : Zn

Er∈Zn

q

(cid:2)Prx∈{0,1}n[Qr(x) = modq(x)](cid:3) = Ex∈{0,1}n

(cid:105)
q [Qr(x) = modq(x)]

(cid:104)

Prr∈Zn
(cid:2)Q(r) = mod′

q(r)](cid:3) .

= Prr∈Zn

q

It follows that there exists r ∈ Zn
(i.e., Prx∈{0,1}n[Qr(x) ̸= modq(x)]) is upper-bounded by the error rate of Q w.r.t mod′
Observing that the degree of Qr is (q − 1)2 times the degree of Q, the claim follows.

q such that the error rate of Qr w.r.t modq : {0, 1}n → Zq
q → Zq.

q : Zn

4.2 The case of q > p

As in Section 3, the hypothesis q < p was (only) used in Section 4.1 in order to allow for an
embedding of Zq in GF(p). In addition, the association of Zq with {0, 1, ..., q − 1} and of GF(p)
with {0, 1, ..., p − 1} allowed for a straightforward embedding that was not even stated explicitly.

17



<!-- pdf-page: 19 -->
Essentially, all that is needed when turning to the case of q > p is to pick an integer e > 1 such that
q < pe, and consider an embedding of Zq in GF(p)e. As in Section 3.2, denoting the embedding by
ψ : Zq → GF(p)e, specific modifications to Section 4.1 include:

(cid:136) In Lemma 5, we consider Q : GF(p)en → GF(p)e, and state the hypothesis as

Prx∈Zn

q [Q(ψ(x)) ̸= ψ(modq(x))] ≥ ϵ

where ψ(x1, ...., xn) = (ψ(x1), ..., ψ(xn)) and modq : Zn
Similarly, we start the proof by defining G def= {x ∈ Zn

q → Zq remains intact.

q : Q(ψ(x)) = ψ(modq(x))}

(cid:136) In the proof of Lemma 5, we use the mappings M : Ke → K and M ′ : K → Ke such that
M (ψ(ζ)) = ωζ and M ′(ωζ) = ψ(ζ) for every ζ ∈ Zq, while noting that now M is computed
by an e-variate polynomial of individual degree p − 1 and M ′ is computed by an e-long
sequence of univariate polynomials of degree q − 1. We then define R : Kn → K such that
R(y1, ..., yn) def= M (Q(M ′(y1), ..., M ′(yn))), while noting that R has degree e·(p−1)·(q−1)·
n,
and observe that for (x1, ..., xn) ∈ G it holds that

√

R(ωx1, ..., ωxn) = M (Q(M ′(ωx1), ..., M ′(ωxn)))

= M (Q(ψ(x1), ..., ψ(xn)))
= M (ψ(mod′
q(x1, ..., xn)))
= ωmod′
(cid:89)
=

q(x1,....,xn)

ωxi.

i∈[n]

Letting H def=
we proceed exactly as in the second part of the proof.

(cid:110)
y ∈ {ωe : e ∈ Zq}n : R(y) = (cid:81)

i∈[n] yi

(cid:111)

, and observing that |H| ≥ |G| (as before),

(cid:136) When reducing mod′

q to modq we use the same unary encoding U : Zq → {0, 1}q−1, but
compute it as a function over GF(p)e; that is, when defining Q′, we use U ′(ψ(ζ)) = U (ζ),
for ζ ∈ Zq. Specifically, we compute the individual bits of U (ζ) by using e-variate poly-
nomials that act on ψ(ζ) ∈ GF(p)e, where ζ ∈ Zq. In other words, for x ∈ Zn
q , we define
the polynomial Q′(ψ(x)) def= Q(Ππ(U ′(ψ(x1)), ..., U ′(ψ(xn)))), and note that its value equals
Q(Ππ(U (x1), ..., U (xn))).

q : Zn

(cid:136) When reducing modq to mod′

q, we are given Q : GF(p)en → GF(p)e that approximates the value
q → Zq (embedded in GF(p)e using ψ), and derive Qr : GF(p)n → GF(p)e that
of mod′
q , we define Qr(x) def= A(ψ(q −
approximates the value of modq : {0, 1}n → Zq. Here, for r ∈ Zn
mod′
q(r)), Q(A(ψ(r1), ψ(x1)), ..., A(ψ(rn), ψ(xn)))), where A : GF(p)e×GF(p)e → GF(p)e is an
e-long sequence of e-variate polynomials that compute (a representation of) addition mod q.

18



<!-- pdf-page: 20 -->
Appendix: Low degree polynomials and approximating Majority

k : {0, 1}n → {0, 1} denotes the function that return 1 if and only if its input
n+1 (x1n+1−k0k),
is the (2n + 1)-bit Majority function. Hence, for any t ∈ [n], a lower bound for

Recall that THn
contains at least k ones (i.e., THn
where TH2n+1
n+1
(2n + 1)-bit Majority follows from a lower bound for THn
that low degree polynomials over GF(2) cannot approximate THn

k (x) = 1 iff wt(x) ≥ k), and that THn

t . Letting t(n) def= ⌈(n +
t(n) well.

k (x) = TH2n+1

n)/2⌉, we prove

√

Lemma 6 (on the error rate of low degree polynomials over GF(2) that approximate THn
n-variate polynomial Q : GF(2)n → GF(2) of degree smaller than
Ω(2n/

n) of the n-bit inputs; that is,

n fails to compute THn

t(n)): Any
t(n) on

√

√

Prx∈{0,1}n[Q(x) ̸= THn

t (x)] = Ω(1/

√

n).

Combining (or rather contrasting) Lemma 6 with Lemma 2 establishes Part 1 of Theorem 1 for the
special case of p = 2.

Proof: Writing x ≤ s if for every i ∈ [n] it holds that xi ≤ si, we first observe that for every
s ∈ {0, 1}n such that wt(s) ≥
(mod 2). The claim holds
by considering each monomial of Q, and observing that for I ⊆ [n] of size smaller than
n it holds
that

x∈{0,1}n:x≤s Q(x) ≡ 0

n it holds that (cid:80)

√

√

(cid:88)

(cid:89)

x∈{0,1}n:x≤s

i∈I

xi = |{x ∈ {0, 1}n : (x ≤ s) ∧ (∀i ∈ I) xi = 1}|

=

(cid:26) 2wt(s)−|I||

0

if I ⊆ {i ∈ [n] : si = 1}
otherwise (i.e., I ∩ {i ∈ [n] : si = 0} ̸= ∅)

√

√

n).

Letting Wt

whereas wt(s) − |I| ≥ 1 (because wt(s) ≥

n and |I| <
def= {x ∈ {0, 1}n : wt(x) = t(n)} and D def= {x ∈ {0, 1}n : Q(x) ̸= THn
t(n)}, we consider
a Boolean matrix with rows corresponding to Wt and columns corresponding to D such that the
(r, c)th entry equals χ(r ≥ c), where χ is a 0-1 indicator that equals 1 if and only if the condition
holds. We consider the rank of this matrix over GF(2). Specifically, for every r ∈ Wt, we shall
show that there exists a linear combination of the columns that yields a unit vector with 1 in row
r. In particular, consider Dr

def= {c ∈ D : c ≤ r}. Then, for every r′ ∈ Wt, it holds that
(cid:88)

(cid:88)

χ(r′ ≥ c) =

χ((c ≤ r) ∧ (c ≤ r′))

c∈Dr

=

c∈D

(cid:88)

x≤r∧r′

χ(x ∈ D)

where (r1, ..., rn) ∧ (r′
holds if and only if Q(x) + THn

1, ..., r′

n) = (r1 ∧ r′
t(n)(x) ≡ 1

(mod 2), we have

1, ..., rn ∧ r′

n). Observing that x ∈ D (i.e., Q(x) ̸= THn

t(n)(x))

(cid:88)

x≤r∧r′

χ(x ∈ D) ≡

≡

(cid:88)

x≤r∧r′
(cid:88)

x≤r∧r′

(Q(x) + THn

t(n)(x))

(mod 2)

Q(x) +

(cid:88)

x≤r∧r′

THn

t(n)(x)

(mod 2).

19



<!-- pdf-page: 21 -->
Noting that wt(r ∧ r′) ≥ wt(r) + wt(r′) − n = 2 · t(n) − n ≥
n and using the initial claim (with
s = r ∧ r′), it follows that (mod 2) the first sum equals 0. On the other hand, the second sum
equals 0 if r′ ̸= r (because then wt(r ∧ r′) < t(n)) and equals 1 otherwise (due to the contribution
of the term associated with x = r).

√

Hence, we showed that, for every r ∈ Wt, there exists a linear combination of the columns that
yields a unit vector with 1 in row r. It follows that the matrix has rank at least |Wt|, which in turn
implies that |D| ≥ |Wt| = (cid:0) n

n). The lemma follows.

(cid:1) = Θ(2n/

√

t(n)

Acknowledgements

I am grateful to Avishay Tal for extremely helpful comments.

References

[1] S. Arora and B. Barak. Computational Complexity: A Modern Approach. Cambridge University

Press, 2009.

[2] O. Goldreich. Computational Complexity: A Conceptual Perspective. Cambridge University

Press, 2008.

[3] S. Jukna. Boolean Function Complexity: Advances and Frontiers. Algorithms and Combina-

torics, Vol. 27, Springer, 2012.

[4] R. Smolensky. Algebraic Methods in the Theory of Lower Bounds for Boolean Circuit Com-

plexity. In 19th ACM Symposium on the Theory of Computing, pages 77–82, 1987.

[5] A. Razborov. Lower bounds on the size of bounded-depth networks over a complete basis with
logical addition. In Matematicheskie Zametki, Vol. 41, No. 4, pages 598–607, 1987 (in Russian).
English translation in Mathematical Notes of the Academy of Sci. of the USSR, Vol. 41 (4),
pages 333–338, 1987.

20


