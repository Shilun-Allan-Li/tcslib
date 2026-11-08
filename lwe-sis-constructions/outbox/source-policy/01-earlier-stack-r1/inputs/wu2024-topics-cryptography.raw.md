<!-- generated-by: proofmatch local extraction -->
<!-- source-pdf-sha256: c0f87bf2e871180d62b2b27d38b916bce1a7b2228dbb68de72341597341d6d87 -->
<!-- extractor: pdftotext version 26.10.0; -layout -->

<!-- pdf-page: 1 -->
                            CS 395T: Topics in Cryptography
                                        Topic: Pairings and Lattices

                                           Instructor: David Wu
                               Compilation of scribe notes from Spring 2024

Warning: These notes are a direct compilation of scribe notes from the Spring 2024 offering of the course. They are
only lightly edited for correctness and completeness. There may be typos and errors.
Last updated: April 30, 2024


<!-- pdf-page: 2 -->
Contents

Lecture 1: Elliptic Curves                                 1

Lecture 2: Pairing Groups                                  5

Lecture 3: Short Signatures                                9

Lecture 4: Aggregate and Threshold Signatures             13

Lecture 5: Threshold Signatures                           16

Lecture 6: Identity-Based Encryption                      20

Lecture 7: Broadcast Encryption                           24

Lecture 8: Distributed Broadcast Encryption               28

Lecture 9: Attribute-Based Encryption                     34

Lecture 10: Attribute-Based Encryption                    40

Lecture 11: Somewhat Homomorphic Encryption               44

Lecture 12: Non-Interactive Zero Knowledge                48

Lecture 13: Batch Arguments                               53

Lecture 14: RAM Delegation                                57

Lecture 15: Polynomial Commitments                        60

Lecture 16: Succinct Non-Interactive Arguments (SNARGs)   64

Lecture 17: Introduction to Lattices                      68

Lecture 18: Short Integer Solutions                       72

Lecture 19: Lattice Trapdoors                             76


<!-- pdf-page: 3 -->
Lecture 20: Lattice-based Signatures and Learning with Errors (LWE)   79

Lecture 21: Regev Encryption and Fully Homomorphic Encryption         82

Lecture 22: FHE Bootstrapping and Key Agreement from LWE              86

Lecture 23: Homomorphic Signatures                                    88

Lecture 24: Homomorphic Commitments                                   91

Lecture 25: Functional Commitments                                    95

Lecture 26: Attribute Based Encryption                                99


<!-- pdf-page: 4 -->
  CS 395T: Topics in Cryptography                                                               January 16, 2024

                                        Lecture 1: Elliptic Curves
  Lecturer: David Wu                                                                           Scribe: David Wu

Let G be a group of prime order p with generator g. Recall that the discrete log problem over G says that given
                             r
(g, h) where h = g x and x ←   Zp , it is computationally hard to compute x. Recall from the first course in
cryptography that the hardness of the discrete logarithm problem (and its variants such as the computational
Diffie-Hellman and decisional Diffie-Hellman problems) are very useful for building many public-key
cryptographic primitives (such as public-key encryption, digital signatures, and more). The question then
is to identify groups where the discrete log problem is believed to be hard. The primary instantiations
considered today are (1) the integers modulo a prime p; and (2) the group of points on an elliptic curve.

Integers modulo a prime p. The first example of a group G where the discrete log problem is believed
to be hard is the group G = Z∗p where p is a (large) prime. Note that the group Z∗p has order p − 1, which
is not prime. It is often convenient to work over a group of prime order, so we typically take G to be a
subgroup of Z∗p . For instance, suppose p = kq + 1 for some positive integer k ∈ N and q is prime (this
setting is often called a “Schnorr group.”) Then, we can take G ⊂ Z∗p to be the subgroup of Z∗p of order q
(i.e., if g is a generator of Z∗p , then g k is a generator of G).
      When setting parameters for a Schnorr group, the prime p is typically around 2048 bits (when targeting
128 bits of security). This is necessary to resist attacks    √
                                                                  based on index calculus and the general number
                                                              3
field sieve (GNFS) whose running time is roughly 2        Õ(   log p) , where the Õ(·) term suppresses constants and

poly(log log p) terms. The smaller prime q is set to be 256 bits to resist generic discrete log algorithms (e.g.,
Pollard rho). The need for such a large prime p is to resist GNFS, and this is a major source of inefficiency
when it comes to deploying cryptographic systems that rely on hardness of discrete log over Z∗p .

Elliptic curves. An alternative family of groups where the discrete log problem is believed to be hard is
to consider the set of points on an elliptic curve. Remarkable, such objects have been studied since antiquity.
One of the earliest known examples is from the work of the Greek mathematician Diophantus from the 3rd
century AD. Diophantus was specifically interested in the rational roots of various bivariate polynomials
f (x, y) = 0. The particular setting we will be interested in corresponds to the case where f (x, y) is a cubic
polynomial in the following form:
                                        f (x, y) = y 2 − (x3 + Ax + B),
where A, B ∈ Q are constants. Here, we view f : R2 → R as a polynomial over the real numbers with
rational coefficients. A “rational” solution to f (x, y) is a pair (x, y) ∈ Q2 where f (x, y) = 0, or equivalently,
a pair (x, y) ∈ Q2 along the curve E : y 2 = x3 + Ax + B. As a concrete example, we plot the curve
y 2 = x3 − x + 1 and provide some examples of rational points on the curve in Fig. 1.1a.

The chord method for constructing rational points. Suppose we have two rational points P1 =
(x1 , y1 ) and P2 = (x2 , y2 ) on the curve E. Consider the line y = αx + β, where α, β ∈ Q that interpolates
these two points. It is easy to see that this line will intersect the curve at a third point. Namely, the
x-coordinates of the points of intersection are the solutions to the cubic equation
                                     f (x) := (αx + β)2 − (x3 + Ax + B).

                                                          1


<!-- pdf-page: 5 -->
                        y                                          y                                             y
                    2                                          2                                           2
                        (0, 1)                                         P1                             P
                                                      P2
                                         x                                          x                                       x
        −2                          2              −2                  P1 ⊞ P2 2              −2                       2
                                                                                                                     P ⊞P
     (−1, −1)
                  −2                                         −2                                           −2


(a) Examples of rational points on E.                   (b) The chord method.                    (c) The tangent method.

                                    Figure 1.1: The elliptic curve E : y 2 = x3 − x + 1.


This is a cubic equation and two of its roots are x1 , x2 ∈ Q. Thus, we can write f (x) = (x−x1 )(x−x2 )g(x),
where g(x) is a linear polynomial. Since f (x) has rational coefficients and x1 , x2 ∈ Q, the polynomial g
also has rational coefficients. Finally, since g is a linear polynomial, it has exactly one root x3 ∈ Q. Setting
y3 = αx3 + β, we conclude that (x3 , y3 ) ∈ Q2 is also a rational point on the curve E. This approach
provides a general procedure for constructing rational points on an elliptic curve E:

       1. Start with two rational points P1 = (x1 , y1 ) and P2 = (x2 , y2 ) where (x1 , y1 ) ̸= (x2 , −y2 ).

       2. Construct the line L that interpolates P1 and P2 .

       3. Compute the intersection of L and E. The intersection is a rational point P3 = (x3 , y3 ). Note that it
          could be the case that P3 ∈ {P1 , P2 } (i.e., this method is not guaranteed to yield a new rational point).

This approach for constructing rational points on an elliptic curve is called the chord method.

The tangent method for constructing rational points. A second method for constructing rational
points on the curve E is to take a rational point P = (x, y) with y ̸= 0 and consider the line that is tangent
to the curve at P . To ensure that the tangent line is well-defined1 at every point P on the curve, we require
that 4A3 + 27B 2 ̸= 0. The quantity 4A3 + 27B 2 is referred to as the discriminant of the elliptic curve.
    From calculus we see that the slope of the tangent line at P is (3x2 + A)/(2y), so if x, y ∈ Q, then
the tangent line also has rational coefficients. Let the line y = αx + β be the line that is tangent to E at
a point P = (x1 , y1 ). We argue that the tangent line will intersect the curve at exactly one other (rational)
point. By definition, the x-coordinates of the points of intersection are the roots of the polynomial

                                             f (x) := (αx + β)2 − (x3 + Ax + B).

Since αx + β is the tangent line at P = (x1 , y1 ), this means f (x1 ) = 0 and f ′ (x1 ) = 0. Since f (x1 ) = 0,
we can write
                                        f (x) = (x − x1 ) · g(x)
1
    Note that we do allow the slope of the tangent line to be ∞, which corresponds to a vertical tangent line.




                                                                   2


<!-- pdf-page: 6 -->
for some quadratic polynomial g(x). Next, from calculus, we know that
                                                f ′ (x) = g(x) + (x − x1 )g ′ (x).
This means 0 = f ′ (x1 ) = g(x1 ), which means x1 is also a root of g. We conclude that
                                          f (x) = (x − x1 )g(x) = (x − x1 )2 h(x),
where h(x) is a linear polynomial. Since f has rational coefficients and x1 ∈ Q, it follows that the coef-
ficients of h are also rational. Taking x2 ∈ Q to be the root of h and setting y2 = αx2 + β, we obtain a
new rational point (x2 , y2 ) on the curve E. This approach for constructing rational points on an elliptic
curve is called the tangent method.

The group law. The chord and tangent methods provides a procedure that takes one or two rational
points on an elliptic curve E and outputs another rational point on the curve E. Remarkably, it can be
shown that this procedure can be used as the basis of a group law on the set of rational points on the elliptic
curve. Namely, for an elliptic curve E : y 2 = x3 + Ax + B with non-zero discriminant, we define E(Q)
to be the set of rational points on E together with a special point at infinity O:
                           E(Q) := (x, y) ∈ Q2 : y 2 = x3 + Ax + B ∪ {O} .
                                     

We now proceed to define the group structure over E(Q):
        • Negation: If P = (x, y) ∈ E(Q), then we define −P := (x, −y) ∈ E(Q).
        • Identity element: For all P ∈ E(Q), we define P + (−P ) = O and P + O = P = O + P .
        • Group operation: Given P1 = (x1 , y1 ) ∈ E(Q) and P2 = (x2 , y2 ) ∈ E(Q), we define the group
          operation P1 ⊞ P2 as follows:
              – If x1 ̸= x2 , the “sum” of P1 and P2 is obtained by applying the chord method to P1 and P2 . Let
                P̃3 be the rational point output by the chord method. Then, the group operation is defined as
                P1 ⊞ P2 := −P̃3 . Visually, this corresponds to drawing the line between P1 and P2 , finding the
                third point of intersection P̃3 with the curve E, and then reflecting P̃3 about the x-axis. This
                process is illustrated in Fig. 1.1b. We can also express this algebraically as follows:
                                           x3 := s2 − x1 − x2         and y3 := s(x1 − x3 ) − y1              (1.1)
                where s = (y2 − y1 )/(x2 − x1 ) is the slope of the chord.
              – If x1 = x2 and y1 = y2 ̸= 0 (i.e., P1 = P2 ), then the “sum” of P1 and P2 is obtained by applying
                the tangent method to P1 . Let P̃3 be the rational point output by the tangent method. The group
                operation is defined as P1 ⊞ P1 := −P̃3 . Visually, this corresponds to drawing the tangent line
                to the curve E at point P1 , finding the point P̃3 where the tangent line intersects E and then
                reflecting P̃3 about the x-axis. This process is illustrated in Fig. 1.1c. We can also express this
                algebraically as follows:
                                             x3 := s2 − 2x1        and y3 := s(x1 − x3 ) − y1 ,               (1.2)
                where s = (3x21 + A)/(2y1 ) is the slope of the tangent line.
              – When x1 = x2 and y1 = −y2 (i.e., if P1 = −P2 ), the output is the identity element O. In this
                case, the line that passes through P1 and P2 is a vertical line; we say that this line intersects
                the curve “at infinity.”2
2
    The geometric intuition can be formalized by working in the projective plane.


                                                                  3


<!-- pdf-page: 7 -->
Elliptic curves over finite fields. Thus far, we have described elliptic curves over the rationals. In
cryptography, we will work over a finite domain, and instead, consider elliptic curves over a finite field
F. First, we introduce the notion of a field:
        • A field consists of a set of elements F equipped with two binary operations: addition (denoted +)
          and multiplication (denoted ×).
        • The set F together with the addition operation + is a commutative group. We typically write 0 to
          denote the additive identity in F.
        • The set F× := F \ {0} together with the multiplication operation × is also a commutative group. We
          typically write 1 to denote the multiplicative identity in F.
        • Finally, multiplication distributes over addition: namely, for all α, x, y ∈ F, it holds that α(x + y) =
          αx + αy.
Notably, every element in a field has an additive inverse, and every non-zero element in a field has a
multiplicative inverse. Examples of fields include the real numbers, the rationals, and the integers modulo
p where p is a prime. In this course, we consider finite fields. In this case, for a prime p, we will write Fp
to denote the integers modulo p (in this course, we may abuse notation and interchange Zp and Fp ). We
now define the notion of an elliptic curve over Fp . For simplicity, we assume p > 3 throughout this course.
Let E : y 2 = x3 + Ax + B 3 where A, B ∈ Fp and 4A3 + 27B 2 ̸= 0. We write E(Fp ) to denote the group
of points on the elliptic curve together with the point at infinity:
                            E(Fp ) := (x, y) ∈ Fp : y 2 = x3 + Ax + B ∪ {O} .
                                     

The group law is defined using the same algebraic relations (specifically, by Eqs. (1.1) and (1.2)) as for
the case over the rationals. When working over finite fields, the group law no longer has a clean visual
interpretation; nonetheless, the same algebraic expressions are equally well-defined (since Fp is a field).

Elliptic curves in practice. For many elliptic curves E over a finite field Fp , the best-known algorithm
for the discrete logarithm problem is the “generic” one (i.e., a discrete log algorithm that is agnostic to
the particular implementation details of the group). In particular, for many curves E, if |E(Fp )| = q for
                                                                            √
some prime q, then the best algorithm for discrete log runs in time O( q). Thus, to achieve 128-bits of
security, it suffices to consider an elliptic curve group with ≈ 2256 points (it suffices to work over a finite
field of order p ≈ 2256 to realize this). Importantly, the order of E(Fp ) should not be p; such curves have
embedding degree 1 and are referred to as “anomalous” curves. As we will see later, for anomalous curves
the discrete log problem over E(Fp ) can be reduced to the discrete problem over Fp . In this case, there
is no advantage to using elliptic curves as opposed to the integers modulo p.
     Today, there are several widely-used elliptic curves that have been standardized. Two prominent exam-
ples are secp256r1 (P-256) and Curve25519. Both of these are 256-bit elliptic curves (i.e., the group order
is roughly 2256 ) and are believed to be secure at the 128-bit security level. P-256 was standardized by the
National Institute of Standards (NIST) in 1999 while Curve25519 was designed by Dan Bernstein [Ber06].
Both families of curves are widely used in Diffie-Hellman key agreement. More generally, due to their
efficiency, elliptic-curve groups are the most common instantiations for public-key cryptographic systems
that rely on the hardness of discrete log.
3
    This is often referred to as the Weierstrass representation of an elliptic curve. For some elliptic curves, there are alternative (and
    equivalent) ways to describe the curve equation and the group law that can be more amenable for computation. These include the
    Montgomery representation and the Edwards representation. We will not cover these alternative representations in this course.


                                                                     4


<!-- pdf-page: 8 -->
  CS 395T: Topics in Cryptography                                                              January 18, 2024

                                       Lecture 2: Pairing Groups
  Lecturer: David Wu                                                                          Scribe: David Wu

Beyond their direct application as a group where the discrete log problem is difficult, the structure of certain
elliptic curves enables new capabilities that have far-reaching implications in cryptography. Specifically,
we focus on elliptic curves that support a “pairing.” As we will see, the pairing enables a broad range of
new cryptographic capabilities beyond basic public-key cryptography. We begin with the basic definition:

Definition 2.1 (Symmetric Pairing Group). A symmetric pairing group (G, GT , e) consists of two groups G
(with generator g) and GT , each of prime order p, and an efficiently-computable mapping e : G × G → GT
(called the “pairing”) that satisfies the following properties:

    • Non-triviality: It holds that e(g, g) ̸= 1. In other words, e(g, g) is a generator of GT .

    • Bilinearity: For all x, y ∈ Zp , it holds that e(g x , g y ) = e(g, g)xy .

We typically refer to G as the “base group” and GT as the “target group.”

     Intuitively, the pairing provides an efficient way to “multiply in the exponent.” Namely, if we think
of g x as an encoding of x ∈ Zp and g y as an encoding of y ∈ Zp , then e(g x , g y ) is an encoding of xy ∈ Zp
in GT (with respect to the generator e(g, g)). An immediate consequence is that the DDH assumption does
not hold in the base group G. Specifically, we can construct the following distinguisher:

    • On input a DDH challenge (g, u, v, w), output 1 if e(u, v) = e(g, w) and 0 otherwise.

We claim that this breaks DDH with advantage close to 1:

    • If u = g x , v = g y , and w = g xy , then

                               e(u, v) = e(g x , g y ) = e(g, g)xy = e(g, g xy ) = e(g, w).

      In this case, the algorithm always outputs 1.
                                                       r
    • If u = g x , v = g y , and w = g r where r ←       Zp , then with probability 1 − 1/p, it holds that r ̸= xy.
      In this case,
                                 e(u, v) = e(g x , g y ) = e(g, g)xy ̸= e(g, g r ) = e(g, w).
      In this case, the algorithm outputs 0 with probability 1 − 1/p.

Thus, the pairing yields a DDH distinguisher that succeeds with probability 1 − 1/p. While the DDH
assumption does not hold in the group G, other problems such as the discrete log problem or the CDH
problem can still plausibly hold in G. Observe that if a particular assumption holds in G, then it must also
hold in GT (since we can always lift an element in the base group to one in the target group). We will also
introduce new computational assumptions that are conjectured to hold in pairing groups.




                                                          5


<!-- pdf-page: 9 -->
An application: tripartite Diffie-Hellman. We will begin with a simple application of pairings to
three-party key-agreement introduced by Joux [Jou00]. Recall that the classic Diffie-Hellman key-agreement
protocol allows two parties (e.g., Alice and Bob) to securely agree on a shared key (by broadcasting just
a single message). Suppose instead we had three parties: Alice, Bob, and Carol. Can we construct a non-
interactive key-agreement protocol? With pairing-free groups, it is not clear how to do this, but with pairings,
this is straightforward. We will work in a (symmetric) pairing group (G, GT , e) of order p and generator g.

        • We will label the three parties with an index i ∈ {1, 2, 3}.
                                                        r
        • Each party starts by sampling an exponent xi ←  Zp and publishes g xi ∈ G. This is the exact same
          setup as standard Diffie-Hellman key exchange.

        • The shared key is e(g, g)x1 x2 x3 .

First, we observe that each party is able to compute the shared key (with the help of the pairing). Consider
the view of Party 1:
                                          r
        • Party 1 chooses the exponent x1 ← Zp and receives g x2 and g x3 from the other two parties.

        • Party 1 can compute the shared key using the pairing: K = e(g x2 , g x3 )x1 = e(g, g)x1 x2 x3 . Formally,
          the actual key would be obtained by applying a randomness extractor (i.e., a hash function) to K.

Parties 2 and 3 can perform an analogous calculation to obtain the shared key K: namely they pair the
public keys from the other two parties, and then exponentiates the result to their own secret key. The
security of the protocol relies on the assumption that it should be difficult to compute (or distinguish)
K = e(g, g)x1 x2 x3 given only (g, g x1 , g x2 , g x3 ). These assumptions can be viewed as the analog of the
CDH and DDH assumptions in the pairing-based world. Both assumptions are defined with respect to a
pairing group (G, GT , e) of order p and generator g:
                                                                                           r
        • Bilinear Diffie-Hellman (BDH) problem: Given (g, g x , g y , g z ) where x, y, z ← Zp , compute
          e(g, g)xyz ∈ GT .

        • Decisional bilinear Diffie-Hellman (DBDH) problem: Distinguish (g, g x , g y , g z , e(g, g)xyz ) from
                                                            r
          (g, g x , g y , g z , e(g, g)r ) where x, y, z, r ← Zp .

We say the BDH (resp., DBDH) assumption holds with respect to a pairing group (G, GT , e) if the advan-
tage of every efficient adversary in solving the BDH problem (resp., DBDH) problem is negligible (resp.,
negligibly close to 1/2).1
    In traditional groups, it is easy to compute ‘linear” functions in the exponent (using the group operation),
while computing quadratic functions is believed to be difficult (i.e., this is the CDH problem). In a pairing
group, it is easy to compute quadratic functions in the exponent (via the pairing), while computing cubic
functions is believed to be difficult (i.e., this is the BDH problem). It turns out that the difference between
being able to compute linear functions vs. being able to compute quadratic functions is very significant.
1
    Formally, the group description (G, GT , e) is sampled from a distribution that is parameterized by the security parameter. The
    adversary’s running time and advantage are correspondingly parameterized by the security parameter.




                                                                  6


<!-- pdf-page: 10 -->
Beyond three parties. As illustrated above, pairings immediately give a solution to the problem of
three-party non-interactive key-agreement. A natural question is whether we can go beyond three parties.
In general, can we come up with an n-party non-interactive key-agreement protocol? One possibility is to
use an (n − 1)-way multilinear map (i.e., an n-way multilinear map e : Gn → GT is an efficient mapping
where e(g x1 , . . . , g xn ) = e(g, . . . , g)x1 ···xn ). However, we do not have algebraic constructions of groups
with n-linear maps (for n > 2) where the multilinear map is efficiently computable and the discrete log
assumption still plausibly holds over the group. The only approach we have for constructing multilinear
maps (and more generally, n-party key-agreement) is through the use of indistinguishability obfuscation.
This is a powerful cryptographic primitive that can be built from standard assumptions, but requires very
heavy machinery to realize. It remains an open question to come up with a simple (and concretely-efficient)
n-party key-agreement protocol (or more generally, construct an efficient n-way multilinear map over a
group where the discrete log problem plausibly holds).

Where do pairings come from? As noted earlier, pairing groups are built from elliptic curve groups.
There are two main types of pairing groups: (1) a symmetric pairing group (Definition 2.1) where there
is a single base group G and the pairing map is a mapping e : G × G → GT ; and (2) an asymmetric pairing
group where there are two base groups G1 , G2 and the pairing is an efficient mapping e : G1 × G2 → GT .
In the asymmetric setting, the groups (G1 , G2 , GT ) are all cyclic groups of the same order. Bilinearity in
the asymmetric setting says the following:

                                          ∀x, y ∈ Z : e(g1x , g2y ) = e(g1 , g2 )xy ,

where g1 ∈ G1 and g2 ∈ G2 are generators of their respective groups. As in the symmetric case, we require
that e(g1 , g2 ) be a generator of the target group GT . Most pairing-based constructions can be adapted
to work with both symmetric pairing groups or asymmetric pairing groups. In this course, we will see
examples in both settings, depending on which instantiation is simpler to describe.
    The pairing groups we use in cryptography are based on elliptic curve groups. Specifically, let E(Fp )
be the group of points on an elliptic curve E with coefficients in Fp . In the case of an asymmetric pairing
group of prime order q, the groups (G1 , G2 , GT ) are typically instantiated as follows:2

    • The base group G1 ⊆ E(Fp ) is an order-q subgroup of E(Fp ).

    • The base group G2 ⊆ E(Fpd ) is an order-q subgroup of the elliptic curve group defined over the
      extension field Fpd where d > 1.3 Moreover, G2 ∩ G1 = {O}.

    • The target group GT ⊆ F×
                             pd
                                is a multiplicative subgroup of the extension field Fpd of order q.

In other words, the pairing takes an element over the elliptic curve over Fp , an element on the elliptic curve
defined over the extension Fpd , and outputs an element in the extension field itself. The constant d is a
property of the elliptic curve and is called the embedding degree of the elliptic curve E (the embedding
degree d is the smallest value where Fpd contains a multiplicative subgroup of order q, or equivalently, the
smallest d such that q | pd − 1). Since the base group G2 and GT are defined over the extension field Fpd ,
2
  Symmetric pairings groups can be constructed in a similar manner, albeit over “supersingular” elliptic curves. For simplicity,
  we will just describe the instantiation for asymmetric pairing groups here.
3
  We will not formally define extension fields in this class, but concretely, the elements of Fpd can be viewed as polynomials of
  degree d − 1 with coefficients in Fp . The elliptic curve group E(Fpd ) is the set of points (x, y) ∈ Fpd × Fpd that satisfy the
  curve equation E. Note that Fpd contains Fp as a sub-field, we always have that E(Fp ) ⊆ E(Fpd ).


                                                                7


<!-- pdf-page: 11 -->
the embedding degree has to be small for the pairing to be efficiently-computable. Thus, elliptic curves
with a small embedding degree (e.g., d ≤ 16) are said to be “pairing-friendly.” Standard elliptic curves like
P-256 or Curve25519 are not pairing-friendly. For instance, the embedding degree of P-256 is d > 2253 and
that of Curve25519 is d > 2249 . As we discuss more below, having a high embedding degree is desirable
for security when considering pairing-free elliptic-curve groups.

Pairings in practice. A common pairing-friendly elliptic curve group is bls381, which is a Barreto-Lynn-
Scott (BLS) curve [BLS02] and conjectured to provide roughly 128-bits of security. The bls381 curve has
embedding degree d = 12 and is of prime order q where q is a 256-bit prime. As the name suggests, the elliptic
curve itself is defined over Fp where p is a 381-bit prime. We now discuss some practical considerations:
    • Elements of G1 can be described by a pair of points (x, y) ∈ Fp . Note that given the value of x ∈ Fp
      and the curve equation E, the value of y is fully determined, up to its sign. Thus, we can define the
      compressed representation of an elliptic curve point (x, y) to be x along with a sign bit; this trick
      is often referred to as “point compression.” The size of an element in G1 is thus 381/8 ≈ 48 bytes.

    • Naı̈vely, an element of G2 would be a pair of points (x, y) ∈ Fpd . Since d = 12, this would normally
      require storing at least 12 elements of Fp , which will be expensive for computation and for com-
      munication or storage. However, there is a clever way to reduce these costs. The trick is to rely on
      the fact that there is an efficiently-computable injective group homomorphism ψ from E ′ (Fp2 ) to
      E(Fp12 ), where E ′ is an elliptic curve related to E (specifically, E ′ is the “twist” of E). Thus, instead
      of working over E(Fp12 ), we instead treat G2 = E ′ (Fp2 ). When we need to apply the pairing, then
      we first apply ψ to the element in G2 to obtain an element over E(Fp12 ), which we then use in the
      pairing. Observe now that elements of G2 can be represented by a pair of elements in Fp (as opposed
      to d = 12 elements). Correspondingly, group operations in G2 are roughly 2× slower than those
      in G1 . The size of an element in G2 is twice that of an element in G1 , or 96 bytes.

    • The target group is the finite field Fp12 , so each element is 576 bytes.
In terms of computational costs, the pairing is roughly 10× slower than exponentiation in the base group G1 .

Using pairings to solve discrete log. Recall from above that the pairing is a mapping e : E(Fp ) ×
E(Fpd ) → Fpd . Notably, the output of the pairing is not a point on an elliptic curve. Instead, it is an element
of the finite field Fpd . As mentioned before, there are sub-exponential time algorithms for solving discrete
log over finite fields (based on index calculus). One of the first application of pairings to cryptography was
proposed by Menezes, Okamoto, and Vanstone as an algorithm for solving the discrete log problem over
an elliptic curve group [MVO91].
    Specifically, if E is an elliptic curve with low embedding degree d ∈ N over Fp , then the discrete log
problem over E(Fp ) is no harder than the discrete log problem over Fpd . This follows by the following
observation: given h = g1x where g ∈ E(Fp ), the algorithm uses the pairing to project h = g x onto
e(h, g2 ) = e(g1 , g2 )x ∈ Fpd . Recovering x ∈ Zq is now the problem of computing the discrete log of
e(h, g2 ) base e(g1 , g2 ) in Fpd . This is a discrete log problem over Fpd , which can be tackled using index
calculus algorithm in sub-exponential time (i.e., sub-exponential in the order pd ). The MOV attack is the
reason we prefer elliptic curves with high embedding degree. Of course, if we want to also use the pairing
constructively, then we need pairing-friendly curves with an embedding degree d that is small enough to
be efficient, but large enough such that the discrete log problem in Fpd is still sufficiently hard (e.g., for
128-bits of security, we minimally require that pd ≥ 2048).

                                                       8


<!-- pdf-page: 12 -->
     CS 395T: Topics in Cryptography                                                                          January 23, 2024

                                              Lecture 3: Short Signatures
     Lecturer: David Wu                                                                                    Scribe: Alex Burton

In the previous lecture, we saw how pairings can be used to break problems such as DDH. In this lecture, we
will see how to build new cryptography from pairings. The key intuition behind our first construction is that a
pairing allows us to easily solve DDH (since we can check for equality in GT ), but is not directly useful in solv-
ing CDH (since we cannot go from GT back into G). This idea is the basis for the BLS digital signature scheme.

Digital signature schemes. First, we recall several signature schemes and compare their signature
lengths relative to concrete and asymptotic security parameters (where the bounds are based on the
best-known attack on the associated assumptions).

                                  Scheme              128 bits of security           λ bits of security
                                    RSA                3072 bit signatures         Õ(λ3 ) bit signatures
                                  ECDSA                512 bit signatures            4λ bit signatures
                                  Schnorr              384 bit signatures            3λ bit signatures
                                    BLS                256 bit signatures            2λ bit signatures
                           Obfuscation-Based            128 bit signatures            λ bit signatures

    The table contains the Boneh-Lynn-Shacham (BLS) signature scheme [BLS01],1 which we are about
to introduce. Certainly, to achieve λ-bit of security, the signature must be at least λ-bits long. Thus,
the obfuscation-based construction [SW14] is essentially optimal in terms of signature size. However,
this scheme is currently only of theoretical interest. The concrete costs of signature verification for the
obfuscation-based scheme is too large to be practically viable (or even implementable). Thus, BLS signatures
give the shortest signatures that can be used in practical applications.

PRFs from DDH. The starting point for the BLS signature scheme is the following DDH-based PRF (in
the random oracle model). This construction uses a random oracle, which we will define precisely later.
Informally, one can think of a random oracle as a random function that everyone has access to.
Construction 3.1 (PRF from DDH in the Random Oracle Model). Let G be a DDH-hard group of order
p. Let H : {0, 1}n → G be a random oracle. Define a PRF as follows:
                                          r
        • Setup(1λ ): Sample and output k ← Zp .
        • Eval(k, x): Output H(x)k .
     To argue security informally: consider an adversary that evaluates the PRF on inputs x1 , . . . , xq . Then,
it learns the pairs (y1 , y1k ), . . . , (yq , yqk ) where yi = H(xi ). Since H is a random oracle, the distribution of
each yi is independent and uniform over G. A hybrid argument using DDH allows us to replace each yik
          r
with zi ←   G one by one.2 Thus, every output of the PRF appears random.
1
    The “BLS signature scheme” [BLS01] is a different BLS than that of “BLS curves.” [BLS02]
2                                                                                                                                   r
    For this hybrid, it is convenient to use the following assumption equivalent to DDH: the distribution {(g, g s , h, hs ) : g, h ←
          r                                                                           r      r
    G, s ←  Zp } is computationally indistinguishable from {(g, g s , h, z) : g, h, z ← G, s ← Zp }. Note that we can also get a tight
    reduction (without a hybrid argument) by relying on random self-reducibility of DDH.


                                                                   9


<!-- pdf-page: 13 -->
Oblivious PRFs and oblivious transfer. The PRF above can be extended into a primitive known as
an oblivious PRF (OPRF). In this scenario, the server holds a PRF secret key k, and a client wants to learn
Eval(k, x) without revealing x to the server. To build this protocol from the previous PRF construction, the
                           r
client samples r ←           Zp and sends y = H(x)r to the server. The server replies with z = y k = H(x)rk , from
                                         −1
which the client computes z r mod p = H(x)k . Observe that the client’s message y completely hides x
unless H(x) = 1, which for any choice of x, happens with 1/p probability over the oracle’s randomness.
     Note that there is a subtlety if we want to establish the following security property of the above OPRF: the
client ought to only learn m many PRF evaluations from m executions of the OPRF evaluation. It turns out
                                                                                                           d
that this requires a stronger assumption than DDH: observe that a client can learn yd := g k by first setting
                                                                                                                     i
y0 := g. Then, for each i ∈ [d], the client passes yi−1 to the server, who replies with yi := yi−1           k  = g k . This
                                            2        d
allows the client to learn g, g k , g k , . . . , g k . It turns out that computing the discrete log k given the sequence
             2             d
(g, g k , g k , . . . , g k ) is easier than computing the discrete      log√over G. Specifically, if d | p − 1, then there
is a discrete log algorithm that recovers k in time Õ( p/d + d). A generic discrete log algorithm over G
                                                                  p
                               √
would run in time Õ( p). We leave it as a homework exercise to develop this better discrete log algorithm.
     OPRFs are useful since they immediately imply oblivious transfer (OT). In an OT protocol, a sender
has two messages m0 , m1 , and a receiver wants to learn the message mb where b ∈ {0, 1}. The privacy
requirement is that the sender does not learn the selection bit b, and the receiver does not learn the unqueried
message m1−b . It turns out that oblivious transfer is both necessary and sufficient for general multiparty
computation (i.e., a protocol that allows a group of mutually distrusting parties to compute an arbitrary
function over their joint private inputs).
     To obtain an OT protocol from an OPRF scheme, we proceed as follows. The sender starts by sending the
blinded messages c0 = m0 ⊕Eval(k, 0) and c1 = m1 ⊕Eval(k, 1).3 The receiver then executes an OPRF evalu-
ation to learn Eval(k, b), from which they can recover mb = cb ⊕Eval(k, b). This is an example of a 1-out-of-2
OT protocol (i.e., the sender has two messages and the receiver is obliviously selecting one of them). We can
also consider a 1-out-of-N protocol where the sender has N messages m1 , . . . , mN and the receiver’s goal is
to learn mi without revealing its index i ∈ [N ]. The basic OPRF protocol directly generalizes to this setting.

BLS signatures. We now introduce BLS digital signatures [BLS01]. One way to view this construction
is to apply the standard “MAC from PRF” construction to Construction 3.1, and replace the secret key
verification procedure with a public key verification procedure via the pairing.

Construction 3.2 (Boneh-Lynn-Shacham Digital Signatures [BLS01]). Let (G, GT , e) be a CDH-hard
symmetric pairing group with generator g and prime order p. Let H : {0, 1}n → G be a hash function
(modeled as a random oracle). Define a digital signature scheme as follows:
                               r
       • KeyGen(1λ ): Sample k ← Zp . Output the signing key sk = k and the verification key vk = g k .

       • Sign(sk, m): Output the signature σ = H(m)sk .

       • Verify(vk, m, σ): Check if e(vk, H(m)) = e(g, σ).

Correctness is immediate from properties of e:

                                      e(g k , H(m)) = e(g, H(m))k = e(g, H(m)k ).
3
    Here, assume that the output space of the PRF is a bit-string. This can be assumed without loss of generality by composing
    the PRF with a randomness extractor.




                                                               10


<!-- pdf-page: 14 -->
Random oracles. Before we give the security proof for BLS, we recall the precise notion of a random
oracle and the random oracle model. A random oracle (RO) H is simply an oracle to a random function.
One can view queries to a random oracle like a “remote procedural call;” notably, such a query is distinct
from a circuit or piece of code that can be evaluated. The random oracle model (ROM) is a model in which
everyone has public access to a random oracle. Importantly, the random oracle model is not an assumption.
In practice, SHA-256 is commonly used to heuristically instantiate the random oracle.
    The power of the ROM is that a reduction algorithm gets to respond to an adversary’s queries to the
random oracle, provided that the responses have the same distribution as a random function. This technique
is called “programming the random oracle.”

The paradox of secure signatures. There is an apparent paradox in proving the security of a digital
signature scheme from a concrete assumption. Consider an adversary A and a reduction algorithm B. On
the one hand, B must be able to respond to signing queries made by A. However, B cannot know how to
sign the message for which A produces a forgery—otherwise, B could replace A’s forgery with a signature
computed by itself, but then B breaks the assumption unconditionally!
    Programming the random oracle allows us to sidestep this paradox. Let m∗ be the message on which
A forges. In essence, we will program H(m) := g αm for m ̸= m∗ where the reduction algorithm chooses
     r
αm ←    Zp itself. The reduction algorithm then defines H(m∗ ) to be an embedding of the CDH challenge.
In particular, the reduction algorithm will be able sign any message except for m∗ , and A’s forgery on m∗
will allow us to solve CDH. Of course, we don’t know m∗ ahead of time; we resolve this by guessing.
Theorem 3.3 (Security of BLS signatures). If CDH holds in G, then the BLS scheme is secure (i.e., existentially
unforgeable under a chosen-message attack) in the random oracle model.
Proof. Suppose A is an adversary for the signature security game. Assume without loss of generality that
A has the following properties:4
      (a) A makes at most Q queries to the random oracle for some polynomial Q = poly(λ).

     (b) A always queries the random oracle for m before querying for a signature on m.

      (c) A always queries the random oracle for m∗ , where (m∗ , σ ∗ ) is the forgery attempt.

     (d) For a given message m, A make at most one random oracle query for m.
Define the adversary B for CDH as follows.
        • Let (g, u = g x , v = g y ) be the CDH challenge. Run A, and give vk = u to A.
                            r
        • Guess an index i∗ ← [Q].

        • Given the ith random oracle query from A, for the message m:

              – If i = i∗ , reply with H(m) := v.
                                     r
              – Otherwise, sample αm ← Zp and reply with H(m) := g αm .

        • Given a signing query from A for the message m:
4
    We can justify these as follows. (a) is immediate, since A is efficient. For (b) resp. (c): given any A, we can easily construct
    A′ (with identical advantage to A) that satisfies (b) resp. (c) by adding random oracle queries and discarding the result. For
    (d): we can construct A′ that maintains a table of previous random oracle queries, and uses that table for any repeated query.


                                                                  11


<!-- pdf-page: 15 -->
              – If m was the (i∗ )th query to the random oracle, abort with output ⊥.
              – Otherwise, reply with σm := uαm .

        • Let (m∗ , σ ∗ ) be the output from A. Output σ ∗ .

We now claim that
                                                                      1
                                                  CDHAdv[B] ≥           SigAdv[A].
                                                                      Q
Consider the event E that i∗ is the correct guess (i.e., the forged message m∗ was the (i∗ )th query to the
random oracle. Event E occurs with probability 1/Q and independently of A’s execution.5
    Now conditioning on E, A’s view of the random oracle is correct (uniformly random), since in
                                                r
either case the output is g r for a random r ←      Zp . A’s view of the signing queries is also correct:
the first case cannot occur, since A does not makes a signing query on m∗ , and in the second case,
uαm = g αm x = H(m)x = Sign(x, m). Finally, if σ ∗ is a valid forgery, then

                          e(u, H(m∗ )) = e(g, σ ∗ ) =⇒ e(g, g)xy = e(g, σ ∗ ) =⇒ σ ∗ = g xy .

So σ ∗ is indeed the CDH solution.

Tight reductions for BLS signatures. The factor 1/Q in the advantage analysis is called the security
loss. This factor is impactful in practice: for example, if we want to support Q ∼ 220 queries for a 128-bit
secure signature, we would need a 148-bit hard pairing group.
     It turns out that there is a straightforward adaptation to BLS that allows for a tight reduction (i.e., a
constant security loss of 1/2 instead of 1/Q). This is left as an exercise for the reader. As a hint, the modified
construction will have two valid signatures for each message, and the signatures will be one bit longer.




5
    There is a subtlety here that we are glossing over: it is not immediately clear that A’s view is actually independent of i∗ . One
    way to fix this is to first consider an intermediate (hybrid) experiment that is identical to the normal game except the challenger
                              r
    randomly chooses i∗ ←        [Q] at the beginning; in addition to the normal win condition, the adversary’s forgery message m∗
                    ∗ th
    must be the (i ) random oracle query. Clearly, going from the normal game to this intermediate experiment reduces the
    win probability of any adversary by exactly a factor of 1/Q, since i∗ is actually independent of A’s view. Once we are in the
    intermediate experiment, our reduction algorithm B gets to set i∗ itself.


                                                                   12


<!-- pdf-page: 16 -->
  CS 395T: Topics in Cryptography                                                                            January 25, 2024

                        Lecture 4: Aggregate and Threshold Signatures
  Lecturer: David Wu                                                                                    Scribe: Alex Burton

BLS signatures, introduced in the previous lecture, have many useful properties. We start by showing
how to construct aggregate signatures—a scheme in which signatures can be combined into a single short
signature—essentially for free [BGLS03].
Definition 4.1 (Aggregate Signature Scheme). An aggregate signature scheme is a digital signature scheme
augmented with a pair of efficient algorithms (Aggregate, VerifyAggregate):
    • Aggregate((vk1 , m1 , σ1 ), . . . , (vkn , mn , σn )) → σagg : Given a set of verification keys vk1 , . . . , vkn ,
      messages m1 , . . . , mn , and associated signatures σ1 , . . . , σn , the aggregate algorithm outputs a single
      aggregated signature σagg .

    • VerifyAggregate((vk1 , . . . , vkn ), (m1 , . . . , mn ), σagg ) → {0, 1}: Check if σagg is a valid signature
      for the messages (m1 , . . . , mn ) with respect to verification keys (vk1 , . . . , vkn ).

Correctness. The correctness requirement is the following: if Verify(vki , mi , σi ) = 1 for all i ∈ [n] and
σagg ← Aggregate((vk1 , m1 , σ1 ), . . . , (vkn , mn , σn )). Then

                     Pr[VerifyAggregate((vk1 , . . . , vkn ), (m1 , . . . , mn ), σagg ) = 1] = 1.

Succinctness. A trivial aggregate signature scheme is to take σagg = (σ1 , . . . , σn ). Since the whole point
of aggregation is to reduce communication, we generally only consider aggregate signatures where |σagg | =
poly(λ, log n). Technically, an aggregate signature with size sublinear in n (e.g., |σagg | = o(n) · poly(λ))
is also interesting.

Applications and multi-signatures. Aggregate signatures reduce the communication cost of having
to send multiple signatures at once. A simple application is aggregating the certificate chain in TLS ses-
sion setup; another is aggregating signatures in blockchain (e.g., aggregating the signatures on different
transactions within a block). Another example is a setting where many authorities need to sign off on a
certain message, (e.g., issuing a nuclear launch command). In this setting, the aggregation is performed
over signatures on the same message. This is often referred to as a multi-signature.

Security. Defining security for signature aggregation is more subtle. We first describe an attack on a
“natural” aggregate version of BLS, which is to simply multiple the input signatures together:
    • Aggregate((vk1 , m1 , σ1 ), . . . , (vkn , mn , σn )) → σagg : Output σagg ← i∈[n] σi .
                                                                                  Q

                                                                                               ?
    • VerifyAggregate((vk1 , . . . , vkn ), (m1 , . . . , mn ), σagg ): Check that e(g, σagg ) =
                                                                                                         Q
                                                                                                             i∈[n] e(vki , H(mi )).

Correctness is satisfied, since
                                                    
                                            Y                Y                      Y
                      e(g, σagg ) = e g,           σi  =           e (g, σi ) =           e(vk, H(mi )).
                                            i∈[n]            i∈[n]                  i∈[n]


                                                             13


<!-- pdf-page: 17 -->
Remark 4.2 (Fast Verification for Multi-Signatures). As described above, signature verification requires
computing n pairings. For the particular case of a multi-signature (i.e., where mi = m for all i ∈ [n]), we
can first “aggregate” the verification keys and implement the verification algorithm with a single pairing.
This follows by the following calculation:
                                                             
                       Y                         Y
                           e(vki , H(m)) = e       vki , H(m) = e(vkagg , H(m)),
                         i∈[n]                         i∈[n]

where vkagg =    i∈[n] vki is the “aggregated” verification key. Namely, the aggregate verification algorithm
                 Q
                        ?
now checks e(g, σagg ) =  e(vkagg , H(m)), which requires a single pairing operation. For settings where one
frequently verifies signatures from the same quorum of users (i.e., the same set of vki ), one can precompute
and cache the aggregated verification key vkagg . In this case, verifying a multi-signature has the same cost
as verifying a single signature.

Rogue key attacks. However, the basic scheme described above is trivially broken in the following
sense. Suppose Alice’s verification key is vkA = g kA . An attacker can come up with a “bad” verifica-
tion key vk′ such that it is easy to forge an aggregate signature with respect to (vkA , vk′ ). In particular,
                               r
the attacker can choose x ←       Zp and set vk′ = g x · vk−1
                                                           A = g
                                                                   x−kA . Then σ ∗
                                                                                 agg = H(m ) satisfies
                                                                                                 ∗ x
                           ′     ∗    ∗   ∗
VerifyAggregate((vkA , vk ), (m , m ), σagg ) = 1:
                             ∗
                       e(g, σagg ) = e(g, H(m∗ ))x = e(g, H(m∗ ))kA · e(g, H(m∗ ))x−kA
                                    = e(vkA , H(m∗ )) · e(vk′ , H(m∗ )).

We refer this as a “rogue key attack” since the adversary can register a new public key (correlated with
an honest user’s public key) and in turn, forge an aggregate signature on behalf of the honest user. Thus,
for an aggregate signature scheme to be secure, the adversary should not be able to claim an honest user
signed a message they did not explicitly sign. We capture this in the following definition:

Definition 4.3 (Secure Aggregation). Consider the following security game between an adversary and
a challenger:

    • The challenger samples (vk, sk) ← KeyGen(1λ ). The challenger sends vk to the adversary.

    • The challenger allows the adversary to make arbitrarily many signing queries Sign(sk, ·).

    • The adversary outputs a forgery ((vk∗1 , . . . , vk∗n ), (m∗1 , . . . , m∗n ), σagg
                                                                                      ∗ ).


The adversary wins if the following conditions hold:

    • VerifyAggregate((vk∗1 , . . . , vk∗n ), (m∗1 , . . . , m∗n ), σagg
                                                                     ∗ ) = 1,


    • For some i ∈ [n], vk∗i = vk and the adversary did not query for a signature on mi .

An aggregate signature scheme is secure if no efficient adversary A in the above game can win with
non-negligible probability.




                                                               14


<!-- pdf-page: 18 -->
Securely aggregating BLS signatures. We describe two approaches to modify BLS signatures to support
secure aggregation:
   1. Sign the verification key in addition to the message: Instead of signing m, the user now signs
      the pair (vk, m). In other words, the signature is now H(vk∥m)k . Correspondingly, the aggregate
      verification relation is now
                                                 ?
                                                   Y
                                     e(g, σagg ) =      e(vki , H(vki , mi )).
                                                       i∈[n]

   2. Add a proof of possession for the verification key: In the case of BLS, the proof can be imple-
      mented by a signature on the verification key. In particular, the verification key is now vk = (u, π)
      where u = g k and π = H′ (u)k . The verification relation will check the validity of the verification
      key: namely, that e(g, π) = e(u, H′ (u)). Note that we need to use a different (and independent)
      random oracle H′ or the scheme is insecure.

Threshold signatures. In threshold cryptography, the goal is to protect a cryptographic key by splitting it
into many different pieces (i.e., “shares”). A compromise of a small number of shares should not compromise
the overall scheme. For example, a certificate authority may distribute their signing key across many
different machines such that even if a few machines get compromised, its root signing key remains secure.
In this setting, the holder of the signing key sk can split it into n individual keys sk1 , . . . , skn and give each
key-share to a different party. The ith party can use ski to independently produce a partial signature σi
on a message m. In a t-out-of-n scheme, a user should be able to take any subset of t partial signatures
and combine them into a signature σ on m (with respect to the verification key vk associated with sk). The
security requirement is that an adversary cannot forge a signature on any message m given t − 1 partial
signatures (or even t − 1 shares of sk).

n-out-of-n threshold signatures for BLS. We start with an n-ouf-of-n threshold             signature scheme.
                                                             r
Given a BLS signing key k ∈ Zp , we sample k1 , . . . , kn−1 ← Zp and set kn ← k − i∈[n−1] ki . Equivalently,
                                                                                   P
                                 r
we are sampling k1 , . . . , kn ←  Zp conditioned on i∈[n] ki = k. A partial signature σi on message m with
                                                      P

respect to the ith key-share ki is a standard BLS signature on m under ki : σi = H(m)ki . Given n signature
shares σ1 , . . . , σn on the same message m, we can recover a signature on m by computing
                                         Y                P
                                    σ=        σi = H(m) i∈[n] ki = H(m)k .
                                         i∈[n]

Intuitively, security holds because if a single share is unknown, then k is uniformly distributed in Zp .

Additive secret sharing. This construction implicitly uses a n-out-of-n threshold secret sharing scheme.
In this setting, a secret s ∈ Zp is split into many shares s1 , . . . , sn such that any set of n − 1 shares
perfectly hide
           P the secret s. In the scheme above, we secret share the key k into random shares k1 , . . . , kn
subject to i∈[n] ki = k. We often refer to this as an additive secret sharing of the secret key k. Since the
reconstruction algorithm (i.e., the algorithm to recover k from the shares k1 , . . . , kn is linear—in fact, just
taking the sum), we can implement it “in the exponent.” This yields the n-out-of-n threshold version of
BLS signatures described above.
    In the following lecture, we will develop a more powerful approach for t-ouf-of-n secret sharing for
arbitrary thresholds t. This construction (called Shamir secret sharing) also has a linear reconstruction
algorithm and will allow us to construct a t-out-of-n threshold signature scheme.

                                                         15


<!-- pdf-page: 19 -->
  CS 395T: Topics in Cryptography                                                                January 30, 2024

                                    Lecture 5: Threshold Signatures
  Lecturer: David Wu                                                                    Scribe: Jonathan Browne

In the last lecture, we constructed n-out-of-n threshold signatures from BLS. Let vk = g k be a BLS ver-
ification key and k be the associated signing key. We previously showed how to split the signing key k
into n different shares k1 , . . . , kn that can be distributed to n different parties. Each party can use their
individual key share ki to sign a message m; this yields a “signature share” σi on m (in fact, σi = H(m)ki
is simply a BLS signature on m under the ith user’s signing key). Given n signature shares σ1 , . . . , σn on
a message m, a user can reconstruct a signature on the message m that verifies under the verification key
vk. In this lecture, we will expand this notion to threshold BLS signatures where instead of requiring a
signature share from all n parties, it suffices to obtain shares from any subset of t parties for some threshold
t where 1 ≤ t ≤ n. To do so, we will rely on properties of polynomials.

The polynomial interpolation problem. Let F be a field. Pick d distinct points x1 , . . . , xd ∈ F. We
will show that for every y1 , . . . , yd ∈ F, there exists a unique polynomial f : F → F of degree at most
d − 1 such that for all i ∈ [d], f (xi ) = yi . Given (x1 , y1 ), . . . , (xd , yd ), the problem of finding such an f
is known as the polynomial interpolation problem.

The Vandermonde matrix. Let f (x) = i∈[d] fi−1 xi−1 . Observe that we can express the evaluation
                                                   P
of f at a point x ∈ F as an inner product between the coefficient vector f = [f0 | f1 | · · · | fd−1 ]T and the
vector x = [1 | x | x2 | · · · | xd−1 ]T . In particular, we can write
                                                                               
                                                                            f0
                                                                           f1 
                               f (x) = xT f = [x0 | x1 | · · · | xd−1 ] ·  .  ∈ F.
                                                                               
                                                                             .
                                                                           . 
                                                                           fd−1
This naturally extends to evaluating the polynomial f at d points x1 , . . . , xd as follows:

                              1 x1 x21 · · · xd−1
                                                                           
                                                 1         f0          f (x1 )
                             1 x2 x2 · · · xd−1   f1  f (x2 )
                                         2       2  
                              .. ..   ..         ..  ·  ..  =  ..                                          (5.1)
                                                                             
                             . .       .          .      .             .   
                                   1 xd x2d · · ·     xd−1
                                                       d
                                                                  fd−1       f (xd )
                               |           {z                 }
                                             V

We refer to the matrix V ∈ Fd×d as the Vandermonde matrix associated with the points (x1 , . . . , xd ). We
now show that if x1 , . . . , xd are distinct, then the Vandermonde matrix is invertible. Our analysis will rely
on the fact that a univariate polynomial of degree d over a field F has at most d roots. This basic fact about
polynomials has a remarkable number of applications (not only to cryptography but also to theoretical
computer science).
Fact 5.1 (Roots of Polynomials). Let F be a field
                                               P and f : F → i−1F be a non-zero (univariate) polynomial of de-
gree at most d. Namely, we can write f (x) = i∈[d+1] fi−1 x         for some set of coefficients f0 , . . . , fd ∈ F.
Then, the polynomial f has at most d roots (i.e., there are at most d points x1 , . . . , xd ∈ F where f (xi ) = 0).

                                                         16


<!-- pdf-page: 20 -->
Lemma 5.2 (Invertibility of the Vandermonde Matrix). Let x1 , . . . , xd ∈ F be distinct points over a field
F, and let V ∈ Fd×d be the Vandermonde matrix associated with (x1 , . . . , xd ). Then, V is invertible.

Proof. Take any set of distinct values x1 , . . . , xd ∈ F and let V ∈ Fd×d be the Vandermonde matrix
associated with (x1 , . . . , xd ). We argue
                                         P that the kernel of V is trivial. Suppose Vf = 0 for some
f T = [f0 | · · · | fd−1 ] ∈ Fd . Let f = i∈[d] fi−1 xi−1 be the polynomial whose coefficients are given by
f . By Eq. (5.1), we have that                                  
                                                         f (x1 )
                                                       f (x2 )
                                                Vf =  .  .
                                                                
                                                        .. 
                                                            f (xd )
By definition, the polynomial f has degree at most d − 1, but f (xi ) = 0 for all i ∈ [d]. Since the xi ’s are
distinct, this means the polynomial f has at least d roots. By Fact 5.1, a non-zero polynomial of degree
d − 1 can have at most d − 1 roots, so this means that the polynomial f is the identically-zero polynomial.
In this case, f = 0, and the claim holds (i.e., Vf = 0 if and only if f = 0). Since the kernel of V is empty,
it follows that V is full rank, and thus, invertible.

Lagrange interpolation. We now return to the problem of polynomial interpolation. Consider again a
sequence of points (x1 , y1 ), . . . , (xd , yd ) where all the xi ’s are distinct. Let V ∈ Fd×d be the Vandermonde
matrix associated with x1 , . . . , xd and let y = [y1 | · · · | yd ]T be the vector of targets. Then, the problem
of polynomial interpolation equates to finding a solution to the linear system Vf = y. By Lemma 5.2,
V is invertible,  so we can write f = V−1 y. If we parse f = [f0 | · · · | fd−1 ]T , then the polynomial
f (x) := i∈[d] fi−1 xi−1 satisfies f (xi ) = yi for all i ∈ [d]. The columns of V−1 are often referred to as
         P
the coefficients of the Lagrange interpolation polynomials. Namely, suppose we write
                                                                              
                                                 ℓ1,0   ℓ2,0 · · ·       ℓd,0
                                              ℓ1,1     ℓ2,1 · · ·       ℓd,1 
                                V−1 =  .                 .                ..  ∈ F .
                                                                                      d×d
                                                                              
                                              .   .      .
                                                          .                 . 
                                          ℓ1,d−1 ℓ2,d−1 · · ·         ℓd,d−1

For i ∈ [d], let Li (x) :=                    j−1 . From Eq. (5.1), we can write
                             P
                             j∈[d] ℓi,j−1 x
                                                                                     
                               L1 (x1 ) L2 (x1 ) · · ·            Ld (x1 )    1
                             L1 (x2 ) L2 (x2 ) · · ·             Ld (x2 )  1
                                                                                       
                      VV−1 =  .            ..                        ..  =    ..     .
                                                                                       
                              ..            .                         .          . 
                              L1 (xd ) L2 (xd ) · · ·             Ld (xd )            1

In particular, this means that Li (xj ) = 1 if i = j and Li (xj ) = 0 if i ̸= j. Then, another way we can
express the polynomial f : F → F that interpolates the points (x1 , y1 ), . . . , (xd , yd ) is
                                                    X
                                           f (x) :=     yi Li (x).
                                                          i∈[d]

To summarize, we obtain the following corollary to Lemma 5.2:



                                                           17


<!-- pdf-page: 21 -->
Corollary 5.3 (Polynomial Interpolation). Take any collection of points (x1 , y1 ), . . . , (xd , yd ) ∈ F2 where
all the xi ’s are distinct. Then, there exists a unique polynomial f : F → F of degree at most d − 1 such that
f (xi ) = yi for all i ∈ [d].
Proof. Let f be a polynomial of degree at most d − 1 whose coefficients are given by a vector f ∈ Fd .
Let V ∈ Fd×d be the Vandermonde matrix associated with (x1 , . . . , xd ) and y = [y1 | · · · | yd ]T ∈ Fd . If
f (xi ) = yi for all i ∈ [d], then Vf = y. By Lemma 5.2, V is invertible, so this linear system has a unique
solution: f = V−1 y.

Shamir secret sharing. Before showing how to construct a t-out-of-n threshold signature scheme, we
start with a more basic problem: how to share a secret s with n users such that any t-subset of the parties
are able to reconstruct the secret. Moreover, we say the secret sharing scheme satisfies perfect secrecy if
every set with fewer than t shares perfectly hide the secret s. We typically refer to the user that generates
the shares as the “dealer.”
Construction 5.4 (Shamir Secret Sharing). Let F be a field and take any n < |F|. Let 1 ≤ t ≤ n be a
threshold. The t-out-of-n Shamir secret sharing scheme over F is then defined as follows:
    • Share generation: To construct a t-out-of-n secret-sharing of a secret s ∈ F, the dealer samples
                         r
      α1 , . . . , αt−1 ←   F and defines the polynomial f (x) = s + α1 x + α2 x2 + ... + αt−1 xt−1 . Let
      x1 , . . . , xn ∈ F be a collection of distinct non-zero points in F. For each i ∈ [n], the dealer defines
      the ith share of the secret to be si = (xi , f (xi )).

    • Reconstruction: To reconstruct s using a collection of shares {(xi , yi )}i∈T where |T | ≥ t, the users
      interpolate the polynomial f : F → F where f (xi ) = yi for all i ∈ T . They then recover the secret
      s by computing s = f (0).

Correctness of Shamir secret sharing. Consider a set of {(xi , yi )}i∈T shares where |T | ≥ t. Since
each share (xi , yi ) is a point on some polynomial f (chosen by the dealer) and f has degree at most t − 1,
it is uniquely determined by any collection of t points (Corollary 5.3). Thus, any set of t shares uniquely
determine the dealer’s polynomial f ; in this case, s = f (0) by construction.

Perfect security of Shamir secret sharing. For security, suppose we have fewer than t shares. Without
loss of generality, we will assume that we have exactly t − 1 shares (if the secret cannot be reconstructed
with a set of t − 1 shares, then it also cannot be constructed by any smaller set). Let {(xi , yi )}i∈T be a
collection of shares where |T | < t. We will show that the following two distributions are identical:
                                                  r
    • Real distribution: Sample α1 , . . . , αt−1 ← F, let f (x) = s + α1 x + α2 x2 + · · · + αt−1 xt−1 , and
      output the shares {(xi , f (xi ))}i∈T .
                                    r
    • Ideal distribution: Sample yi ← F for all i ∈ T and output {(xi , yi )}i∈T .
Perfect secrecy follows immediately since the shares output by the ideal distribution are independent of the
secret s. It suffices to argue that these two distributions are identical. To argue this, consider the mapping

                      Shares : (α1 , . . . , αt−1 ) ∈ Ft−1 7→ [g(xi1 ), . . . , g(xit−1 )] ∈ Ft−1            (5.2)

where g(x) := s + α1 x + α2 x2 + · · · + αt−1 xt−1 and T = {i1 , . . . , it−1 } ⊂ [n]. Here, the input is a vector
of polynomial coefficients, which correspond to the dealer’s randomness in the real distribution, and the

                                                          18


<!-- pdf-page: 22 -->
output is a set of t − 1 shares. We claim that for all s ∈ F, Shares function is injective. Suppose Shares (α) =
             where α, α′ ∈ Ft−1 . We write
Shares (α′ ) P                                P α = [α      1 | · · · | αt−1 ] and α = [α1 | · · · | αt−1 ] Let
                                                                              T      ′       ′         ′    T

g(x) = s + i∈[t−1] αi x and g (x) = s + i∈[t−1] αi x . Let h ≡ g − g . Since g(0) = g (0), it follows that
                            i     ′                       ′  i                  ′              ′

h(0) = 0. Moreover, since Shares (α) = Shares (α′ ), we have that g(xij ) = g ′ (xij ) for all j ∈ [t − 1]. Thus,

                                      h(0) = h(xi1 ) = · · · = h(xit−1 ) = 0.

This means the polynomial h has at least t roots. Since g, g ′ are polynomials with degree at most t − 1, the
degree of h is also at most t−1. By Fact 5.1, this means that h must be the identically-zero polynomial, and so
g = g ′ . Since α and α′ are the coefficients of g, g ′ , respectively, this means that α = α′ . We conclude that the
Shares mapping in Eq. (5.2) is injective, and thus bijective. But if Shares is a bijection, then the distribution of
                    r
Shares (α) for α ←     Ft−1 is also uniform over Ft−1 . This matches the ideal distribution, and the claim holds.

A threshold BLS signature scheme. Suppose we have t Shamir secret sharing shares (x1 , y1 ) . . . (xt , yt ).
The reconstruction algorithm computes the Vandermonde matrix V, interpolates the polynomial f , and
output f (0). Here, f (0) is simply the constant coefficient in f (i.e., its first coordinate). Thus, we can
combine the second and third steps into a single equation:

                                               s = eT1 f = eT1 V−1 y,

where e1 denote the first canonical basis vector e1 = [1 | 0 | · · · | 0]T , and y denotes the vector of shares.
    Observe that this equation is linear in terms of the shares y. This means we can convert the equation
to a dot product s = λT y, where the reconstruction coefficients λ is λ := eT1 V−1 . Applying this to the
BLS signature scheme, we get the following equation:
                                               T           P               Y
                       σ = H(m)s = H(m)λ y = H(m) i∈T λi yi =                  H(m)λi yi
                                                                              i∈T

The H(m)yi computation resembles the standard BLS signing algorithm, using yi as the signing key for each
party; since yi is the secret share for party i, this is feasible to use as the per-party signing algorithm. λi is pub-
lic and can be recomputed knowing only which parties are signing the message, so that step of the signature
computation can be used to combine shares. This gives us the full BLS t-out-of-n threshold signing algorithm:

Definition 5.5 (BLS t-out-of-n threshold signature algorithm). The BLS t-out-of-n threshold signing
algorithm is defined as follows:

    • Setup: Choose a random BLS signing key k ← Fp . Using the Shamir secret sharing algorithm, split
      k into N shares (k1 ...kN ) ∈ Zp . Give party i share (i, ki ).

    • Sign((i, ki ), m): Let σi = mki . Output (i, σi ).

    • Aggregate({(x
                 Q 1 , σ1 ), ..., (xt , σt )): Compute the reconstuction coefficients λi using the xi values.
      Output σ = i∈[t] σiλi .
                                                                 P
The scheme is correct because σ = i∈[t] σiλi = i∈[t] mki λi = m i∈[t] ki λi = ms . Security follows from
                                   Q            Q
the Shamir secret sharing proof and from BLS signature security.




                                                         19


<!-- pdf-page: 23 -->
  CS 395T: Topics in Cryptography                                                        February 1, 2024

                             Lecture 6: Identity-Based Encryption
  Lecturer: David Wu                                                                 Scribe: Sidh Suchdev

In an ordinary public key encryption system, every user has their own public key and secret key. Com-
munication with many other users requires keeping track of all of those users’ public keys, which can take
up lots of space. Identity-based encryption is designed to reduce the amount of space needed to keep track
of many public keys by dynamically generating them from an arbitrary identifier (like an email address)
and a single master public key.

Definition 6.1 (Identity-based Encryption Scheme). An identity-based encryption scheme with message
space M is a tuple of efficient algorithms (Setup, KeyGen, Encrypt, Decrypt) with the following properties:

    • Setup(1λ ) → (mpk, msk): On input a security parameter λ, the setup algorithm outputs a master
      public key mpk (used for encryption) and a master secret key msk (used to issue keys).

    • KeyGen(msk, id) → skid : On input the master secret key msk and an identity id, the key-generation
      algorithm outputs an identity key skid .

    • Encrypt(mpk, id, m) → ct: On input the master public key mpk, a target identity id, and a message
      m ∈ M, the encryption algorithm outputs a ciphertext. (In some settings, this can be thought of as
      two separate algorithms: one that takes mpk and id and outputs a per-user public key, and a second
      that uses the per-user public key to encrypt a message.)

    • Decrypt(skid , ct) → m: On input an identity key skid and a ciphertext ct, the decryption algorithm
      either outputs a message m ∈ M.

Correctness. The scheme is correct if for all identities id and all messages m ∈ M, it holds that

                                                    (mpk, msk) ← Setup(1λ )
                                                                              

               Pr Decrypt(mpk, id, ct) = m : skid ← KeyGen(msk, id)  = 1.
                                                   ct ← Encrypt(mpk, id, m)

Security. We now define semantic security for an IBE scheme. Intuitively, security says that the adversary
cannot learn anything about a message encrypted to an identity id∗ if it does not possess a secret key for
id∗ . We now define this formally. As usual, the game is parameterized by a bit b ∈ {0, 1}.

    • Setup: At the beginning of the game, the challenger samples (mpk, msk) ← Setup(1λ ) and sends
      mpk to the adversary A.

    • Key-generation queries: The adversary A is now allowed to issue key-generation queries on
      identities id of its choosing. On each query, the challenger responds with the secret key skid ←
      KeyGen(msk, id).

    • Challenge query: When the adversary is done making key-generation queries, it outputs a challenge
      identity id∗ and two messages m∗0 , m∗1 . The challenger responds with ct∗b ← Encrypt(mpk, id∗ , m∗b ).


                                                     20


<!-- pdf-page: 24 -->
       • Key-generation queries: The challenger can continue to make key-generation queries on identities
         of its choosing. The challenger responds to each query exactly as before.

       • Output: At the end of the experiment, the adversary outputs a bit b′ ∈ {0, 1}.

We say the adversary A is admissible for the semantic security game if it does not make a key-generation
query on the challenge identity id∗ . Then, we say the IBE scheme is semantically secure if for every efficient
adversary A,
                           | Pr[b′ = 1 | b = 0] − Pr[b′ = 1 | b = 1]| ≤ negl(λ).
    (This scheme can also be extended to IND-CCA security by adding decryption queries for an arbitrary
identity and ciphertext. In the IND-CCA version, an attacker is admissible as long as it does not make any
decryption queries for ct∗ on id∗ .

Boneh-Franklin IBE. We now introduce the IBE scheme by Boneh and Franklin [BF01]. The structure
of this scheme shares many similarities with the BLS signature scheme (Construction 3.2). In particular,
the secret key for an identity id is a BLS signature on the identity. In this sense, the Boneh-Franklin IBE can
also be viewed as a “witness encryption” scheme [GGSW13] for the BLS signature language; decrypting
a ciphertext for an identity id requires knowledge of a BLS signature for id.1

Construction 6.2 (Boneh-Franklin Identity Based Encryption). Let (G, GT , e) be a (symmetric) pairing
group and let g be a generator of G. Let H : {0, 1}n → G be a hash function. We define the identity based
encryption scheme below:
                              r
       • Setup(1λ ): Sample k ← Zp and output mpk = g k , msk = k

       • KeyGen(msk, id): On input the master secret key msk = k, outputs skid = H(id)k
                                       r
       • Encrypt(mpk, id, m): Sample r ← Zp and output ct = (g r , e(mpk, H(id))r · m)

       • Decrypt(skid , ct): On input the secret key skid and the ciphertext ct = (u, v), output v/e(u, skid )

Correctness. We can verify the correctness by a simple calculation. Take any identity id and mes-
sage m. Let (mpk, msk) ← Setup(1λ ). Let ct ← Encrypt(mpk, id, m) and skid ← KeyGen(msk, id).
Write mpk = g k and msk = k. Then, skid = H(id)k . Next, write ct = (u, v) where u = g r and
v = e(g k , H(id))r · m. Then, using bilinearity, we have

                                               v         e(g k , H(id)r ) · m   e(g, H(id))kr
                   Decrypt(skid , ct) =                =                      =               · m = m.
                                           e(u, skid )     e(g r , H(id)k )     e(g, H(id))kr
Remark 6.3 (Parallels with ElGamal). The structure of the Boneh-Franklin IBE scheme shares many
similarities with that of ElGamal encryption. Recall first that in ElGamal encryption, the public key is
(g, h) and the secret key is the discrete log k ∈ Zp where h = g k . An encryption of m ∈ G is the pair
ct = (g r , hr · m). To decrypt, the user relies on the fact that (g r )k = hr , which suffices to recover m.
Knowledge of the key k ∈ Zp is used to “multiply-by-k in the exponent” (to translate from g r to g kr = hr ).
     In Boneh-Franklin, we can interpret the quantity e(mpk, H(id)) = e(g k , H(id)) as the public key
pkid associated with the identity id. Observe now that the encryption algorithm in Boneh-Franklin is
1
    Note that this high-level description does not map to a formal definition of witness encryption, but it does share conceptual
    similarities.


                                                                21


<!-- pdf-page: 25 -->
                                                                                      r
basically constructing an ElGamal ciphertext with respect to pkid : that is, sample r ← Zp and outputs
ct = (g , pkid · m). To decrypt, the pairing is used to implement the “multiply-by-k in the exponent”
        r    r

operation needed for the ElGamal-style decryption procedure:
                             e(g r , skid ) = e(g r , H(id)k ) = e(g k , H(id))r = pkrid .

Security. To prove security, we rely on the DBDH problem previously defined in Lecture 2, where we
                                                          r                                                 r
are to distinguish (g, g x , g y , g z , g xyz ), x, y, z ← Zp from (g, g x , g y , g z , g r ), x, y, z, r ← Zp .
    We will prove a stronger statement than semantic security. We will prove that the ciphertext generated
by the Boneh-Franklin scheme is indistinguishable from random under the random oracle model. Let D0
be the distribution of ciphertexts generated by the challenger and let D1 be the distribution of random
ciphertexts. An adversary wins if it can successfully distinguish between the two distributions.
    We will do this by a reduction to the DBDH problem. Let A be an adversary for the game described
before. Without loss of generality, we assume the following about A:
   1. A makes at most Q queries to the random oracle, where Q = poly(λ)
   2. A always queries the random oracle on id before asking for the key on id
   3. A always queries the random oracle on id∗ before outputting the challenge
   4. A always queries the random oracle any id at most once
Note, similarly to BLS signatures, that these assumptions follow naturally and that if any adversary does
not follow these, we can construct an adversary A′ where these assumptions hold.
    Now we construct adversary B as follows:
                                                                                      r
    • On input (g, u = g x , v = g y , w = g z , T ), algorithm B sets mpk = u and i∗ ← [Q], where i∗ is the
      guess of the challenge query index.
    • We run algorithm A with our mpk, and respond to the following queries
         – A makes a random oracle query on id:
               ∗ If i = i∗ , then output H(id) = skid = v
                                          r
               ∗ Otherwise, sample αid ←     Zp and output g αid .
         – A makes a key generation query on id:
               ∗ If i = i∗ , abort
               ∗ Otherwise, output uαid
         – A makes a challenge query m and id∗ :
               ∗ If i = i∗ , then output ct∗ = (w, T )
               ∗ Otherwise, abort
    • A outputs bit b′ ∈ {0, 1}, which B forwards to the challenger.
Suppose our guess of i∗ is correct and T = e(g, g)xyz . Then the following holds:
                                          T · m = e(g, g)xyz · m
                                                  = e(g x , g y )z · m
                                                  = e(mpk, H(id))z · m


                                                          22


<!-- pdf-page: 26 -->
We now analyze the advantage of our adversary B. Suppose AdvA = ϵ. Note that when i∗ is guessed
incorrectly, adversary B aborts, but when when i∗ is guessed correctly then the advantage of B is at least
ϵ. Thus, AdvB ≥ ϵ/Q > negl.

Remark 6.4 (Challenges in Proving Adaptive Security). The strategy to sidestep the paradox of an unknown
skid to prove adaptive security is known as partitioning. The other prominent method of showing adaptive
security is the dual-system, developed by Waters.

Limitations of IBE. Identity based encryption provides a neat solution to the issue of compressing
multiple public and secret keys for users. However, an important consideration when using identity based
encryption is that it changes the threat model in public key encryption. For example, suppose we have users
Alice and Bob. In standard public key cryptography, Alice generates (pkA , skB ), Bob generates (pkB , skB )
and they publish pkA , pkB . Note that only Alice knows her secret key skA and only Bob knows his secret
key skB . In identity based encryption, a third party authority generates the mpk, msk, sends Alice her
skA and Bob his skB , and publishes the mpk. In this case, the third party knows every user’s secret key.
This might be undesirable since the third party authority is a single point of failure, where if it were ever
compromised, all communications between parties could be decrypted. We can avoid this situation through
a scheme called registration-based encryption (RBE), where the authority instead aggregates identities and
public keys, with no knowledge of the secret keys associated with them.




                                                     23


<!-- pdf-page: 27 -->
  CS 395T: Topics in Cryptography                                                        February 6, 2024

                                Lecture 7: Broadcast Encryption
  Lecturer: David Wu                                                               Scribe: Matthew Healy

In the last lecture, we introduced identity-based encryption, a generalization of public-key encryption that
allows users to encrypt messages to an arbitrary identity. An IBE scheme can be viewed as “compressing”
an exponential number of public keys for different identities into a single set of public parameters. In this
lecture, we introduce the concept of broadcast encryption, which allows a broadcaster to encrypt a message
to a set of receivers with a ciphertext whose size scales sublinearly with the number of recipients.

Definition 7.1 (Broadcast Encryption). A broadcast encryption scheme with message space M is a tuple
of efficient algorithms (Setup, Encrypt, Decrypt) with the following properties:

    • Setup(1λ , 1N ): On input the security parameter λ and the number of users N , the setup algorithm
      outputs a master public key mpk and a collection of N decryption keys sk1 , . . . , skN .

    • Encrypt(mpk, S, m): On input the master public key mpk, a “broadcast set” S ⊆ [N ], and a message
      m, the encryption algorithm outputs a ciphertext ct.

    • Decrypt(ski , S, ct): On input a decryption key ski , the broadcast set S ⊆ [N ], and a ciphertext ct,
      the decryption algorithm outputs a message m.

Correctness. The scheme is correct if for all integers N ∈ N, all sets S ⊆ [N ], and all indices i ∈ S, it
holds that
                                           (mpk, sk1 , . . . , skN ) ← Setup(1λ , N )
                                                                                     
            Pr Decrypt(ski , S, ct) = m :                                               = 1.
                                                  ct ← Encrypt(mpk, S, m)

Succinctness. A trivial broadcast encryption scheme is to concatenate N ciphertexts (under N indepen-
dent public keys) together. The goal in broadcast encryption is to achieve short ciphertext. Specifically, we
say the broadcast encryption scheme satisfies succinctness if |ct| = o(N ) · poly(λ) where N is the number
of users and λ is the security parameter.

Security. We now define semantic security for a broadcast encryption scheme. Intuitively, security says
that the adversary cannot learn anything about a message encrypted to a set S ⊆ [N ] if it does not possess
a secret key for some index i ∈ S. We now define this formally. As usual, the game is parameterized by
a bit b ∈ {0, 1}.

    • Setup: At the beginning of the game, the adversary declares the number of users 1N . The challenger
      then samples (mpk, sk1 , . . . , skN ) ← Setup(1λ , N ) and sends mpk to the adversary A.

    • Key-generation queries: The adversary A can now ask for secret keys on indices i ∈ [N ] of its
      choosing. On each query i ∈ [N ], the challenger responds with ski .

    • Challenge query: When the adversary is done making key-generation queries, it outputs a set
      S ∗ ⊆ [N ] and two messages m∗0 , m∗1 . The challenger responds with ct∗b ← Encrypt(mpk, S ∗ , m∗b ).


                                                     24


<!-- pdf-page: 28 -->
    • Output: At the end of the experiment, the adversary outputs a bit b′ ∈ {0, 1}.

We say the adversary A is admissible for the semantic security game if it does not make a key-generation
query on any index i ∈ S ∗ Then, we say the broadcast encryption scheme is semantically secure if for
every efficient adversary A,

                              | Pr[b′ = 1 | b = 0] − Pr[b′ = 1 | b = 1]| ≤ negl(λ).

Boneh-Gentry-Waters broadcast encryption scheme. We now describe the broadcast encryption
scheme by Boneh, Gentry, and Waters [BGW05] The key idea underlying this scheme is to use powers in the
exponent. The “correlation” structure induced by the powers will play a role both in correctness and for argu-
ing security. We build this scheme up step-by-step before giving the formal description in Construction 7.2.

    • Public parameters: The public parameters in BGW will contain group elements of the form
                                                     2             N         N +2                  2N
                                          g, g α , g α , . . . , g α , g α          , . . . , gα        ,
                r                                                                       N
      where α ←    Zp is a random exponent. The first set of N powers g α , . . . , g α function as the “public
                                                                                                  N +2              2N 
      keys” associated with users 1, . . . , N respectively, while the latter set of elements g α      , . . . , gα
                                                                                               N +1
      are “helper components” that are used for decryption. Critically, there is a hole at g α       . The missing
      component will be used to “encrypt.”
                                                         r
    • Encryption: To encrypt a message m ∈ GT , sample r ← Zp and compute
                                                                       N
                                                 ct = g r , e(g α , g α )r · m .
                                                                              

                      N                                                                                                         N
      Here, e(g α , g α )r is the key-encapsulation mechanism (KEM) and can be rewritten as e(g α , g α ) =
              N +1                  N +1                                                                  N +1
      e(g, g α     ). Note that g α      cannot be given out, as otherwise anyone can compute e(g r , g α      ).

    • Decryption. However, with just the encryption construction stated above, we are unable to decrypt
      the ciphertext. We will need to include additional information in the ciphertext to allow a party to
                         N
      compute e(g α , g α )r in order to support decryption. We also want to ensure that a party i should
                                                                                                N +1 r
      only be able to decrypt if i ∈ S; if i ∈
                                             / S, it should not be possible to compute e(g, g α     ) . The
      approach to generating such a ciphertext is as follows:
                          i                                        i     j                         i j                   i+j
         – Let gi = g α . Observe that e(gi , gj ) = e(g α , g α ) = e(g, g)α α = e(g, g)α = e(g, gi+j ).
         – In the ciphertext, include j∈S gN  r
                                                +1−j . Now, take any index i ∈ S. By bilinearity, we now have
                                     Q

                                                     
                                        Y                    Y
                                               r
                              e gi ,         gN +1−j
                                                      =           e(gi , gN +1−j )r
                                        j∈S                  j∈S
                                                                                            Y
                                                          = e(gi , gN +1−i )r ·                             e(gi , gN +1−j )r   (7.1)
                                                                                          j∈S\{i}
                                                                                        Y
                                                                               r
                                                          = e(g, gN +1 ) ·                         e(g, gN +1−j+i )r
                                                                                     j∈S\{i}




                                                              25


<!-- pdf-page: 29 -->
         – Note that e(g, gN +1 )r is our quantity of interest and

                                             e(g, gN +1−j+i )r = e(g r , gN +1−j+i ).

           When i, j ∈ [N ], then 2 ≤ N + 1 − j + i ≤ 2N . Moreover, if i ̸= j, then N + 1 − j + i ̸= N + 1.
           This means gN +1−j+i is contained within the public parameters.
         – Conversely, if i ∈
                            / S, then e(gi , j∈S gN
                                                  r
                                                    +1−j ) does not contain the critical term e(g, gN +1 ) .
                                                                                                          r
                                            Q

    • Decryption keys. At this point, we have shown that knowledge of gi is sufficient to decrypt
      (whenever i ∈ S). However, gi is public so anyone could decrypt at this point. To address this, we
      introduce introduce an additioanl blinding factor to the ciphertexts that can only be removed by a
                                                                                            r
      user who possesses a secret key. Specifically, the setup algorithm now samples γ ←       Zp and sets the
                                         γ
      secret key for user i to be d :=
                               Q i r i g   . The public key will then contain v = g γ . Now, in the ciphertext,
      we replace the element j∈S gN +1−j with the element
                                                                 r
                                                      Y
                                                 v ·    gN +1−j  .
                                                           j∈S

      Consider the updated version of the decryption relation from Eq. (7.1):
                                       
                              Y                            Y
                e gi , v r ·    r
                                gN +1−j
                                         = e(gi , v r ) ·   e(gi , gN +1−j )r
                              j∈S                                 j∈S
                                                                                       Y
                                                = e(gi , v r ) · e(g, gN +1 )r ·              e(g, gN +1−j+i )r .
                                                                                    j∈S\{i}

      Notably, the decryption relation from Eq. (7.1) now has an additional term e(gi , v r ). Cancelling out
      this term will require knowledge of the ith user’s decryption key. Namely, observe that

                                    e(gi , v r ) = e(gi , g γr ) = e(giγ , g r ) = e(di , g r ).

      Since g r is part of the ciphertext, user i can compute e(di , g r ) and cancel out this term.
Putting all the pieces together, we now arrive at the full Boneh-Gentry-Waters construction:
Construction 7.2 (Boneh-Gentry-Waters Broadcast Encryption [BGW05]). Using the approach described
above, the broadcast encryption scheme is implemented as follows:
                                r          r                               i
    • Setup(1λ , 1N ): Sample α ← Zp and γ ← Zp . Let gi = g α and v = g γ . Output the master public key

                                    mpk = (g, g1 , g2 , . . . , gN , gN +2 , . . . , g2N , v),

      and the decryption keys ski = (i, gi , di ) where di = giγ .

    • Encrypt(mpk, S, m): On input the master public key mpk = (g, g1 , g2 , . . . , gN , gN +2 , . . . , g2N , v), a
                                                      r
      set S ⊆ [N ], and a message m ∈ GT , sample r ←   Zp and output the ciphertext
                                                                           
                                                 Y
                               ct = g r , v r ·    r
                                                   gN                   r
                                                      +1−j , e(g1 , gN ) · m .
                                                                            
                                                       j∈S


                                                             26


<!-- pdf-page: 30 -->
    • Decrypt(ski , S, ct): On input a decryption key ski = (i, gi , di ), the set S ⊆ [N ], and a ciphertext
      ct = (C1 , C2 , C3 ), output
                                                   Q                          
                                             e di · j∈S\{i},C1 gN +1−j+i
                                    z = C3 ·                                    .
                                                       e(gi , C2 )

Correctness. We now argue correctness. Let mpk = (g, g1 , . . . , gN , gN +2 , . . . , g2N , v), sk = (i, gi , di )
be the master public key and secret keys output by Setup(1λ , N ). Let ct = (C1 , C2 , C3 ) be an encryption
                                                                    i
of a message m to the set S under mpk. By construction, gi = g α , di = giγ , and v = g γ . Consider now
the decryption relation:

                                                                                  r
                                                                    Y
                                     e(gi , C2 ) = e gi , v ·             gN +1−j 
                                                                    j∈S
                                                                                                                    r
                                                                                                     Y
                                                   = e(gi , gN +1−i )r · e(gi , v)r · e gi ,                gN +1−j 
                                                                                                   j∈S\{i}
                                                                                        Y
                                                   = e(g, gN +1 )r · e(gi , v)r ·                e(gi , gN +1−j )r
                                                                                       j∈S\{i}
                                              
                    Y                                                  Y
           e di             gN +1−j+i , C1  = e(di , g r ) ·                 e(gN +1−j+i , g r )
                   j∈S\{i}                                           j∈S\{i}

                                                   = e(giγ , g)r ·
                                                                       Y
                                                                               e(gi , gN +1−j )r
                                                                     j∈S\{i}
                                                                      Y
                                                   = e(gi , v)r ·              e(gi , gN +1−j )r
                                                                     j∈S\{i}

Thus,
                                                  e(gi , C2 )
                                           Q                          = e(g, gN +1 )r .
                                   e di                g
                                               j∈S\{i} N +1−j+i , C1

Correspondingly,                       Q                               
                                e di       j∈S\{i} gN +1−j+i , C1              m · e(g, gN +1 )r
                        C3 ·                                               =                     = m.
                                               e(gi , C2 )                      e(g, gN +1 )r

Security. The security of this construction will rely on the N -bilinear Diffie-Hellman exponent (N -BDHE)
assumption. We will introduce this assumption and give its proof of security in the following lecture.




                                                               27


<!-- pdf-page: 31 -->
  CS 395T: Topics in Cryptography                                                                      February 8, 2024

                           Lecture 8: Distributed Broadcast Encryption
  Lecturer: David Wu                                                                               Scribe: Alex Huang

In the previous lecture, we introduced the Boneh-Gentry-Waters broadcast encryption scheme [BGW05].
In this lecture, we will prove the security of the scheme and show how to adapt it to obtain a distributed
broadcast encryption scheme where each recipient can choose their own key (instead of relying on a central
key distributor).

The N -bilinear Diffie-Hellman Exponent assumption. The security of the BGW broadcast encryption
scheme is based on the N -bilinear Diffie-Hellman exponent (N -BDHE) assumption which states that the
following two distributions are computationally indistinguishable:
               r           r
    • Sample α ← Zp and β ←    Zp . Output
                                                                                                
                                          2             N      N +2              2N         N +1
                        g, g β , g α , g α , . . . , g α , g α      , . . . , g α , e(g, g)α β     .

               r        r                 r
    • Sample α ← Zp , β ←  Zp and r ←        Zp . Output
                                             2             N      N +2              2N
                                                                                                 
                            g, g β , g α , g α , . . . , g α , g α      , . . . , g α , e(g, g)r   .


This assumption is similar to the DBDH problem defined in Lecture 2 except that the exponents are αN +1
                                                               2             N      N +2              2N
and β and the adversary is given additional powers g, g α , g α , . . . , g α , g α      , . . . , g α . It is often called
a “q-type assumption” since the size of the assumption depends on a scheme parameter, in this case the
number of users N .

Remark 8.1 (Hardness of N -BDHE). Note that if p − 1 (or p +p1) has a√factor t ≤ N , then there is an
                                            2             N
algorithm for computing α from (g, g α , g α , . . . , g α ) in time Õ( p/t + t) [BG04, Che06]. The generic
                                       √
discrete log algorithm runs in time Õ( p), so the hardness of the N -BDHE assumption degrades with the
size of the assumption.

Selective security. We will prove selective security of the BGW broadcast encryption scheme (Con-
struction 7.2). In the selective security game, the adversary has to declare its challenge set S ⊆ [N ] at
the beginning of the security game before it sees the public parameters. In the usual security game, the
adversary can adaptively choose the challenge set S after it sees the public parameters and the secret keys
(on users of its choosing). Selective security is a much weaker (and less natural) security notion, but enables
us to prove security. Intuitively, the scheme is selectively secure as long as the broadcast sets are chosen
“independently” of the public parameters and individual users’ decryption keys. We do not know how to
prove adaptive security of the BGW scheme. At the same time, we also do not know of any attacks on the
adaptive security of the BGW scheme.

Definition 8.2 (Selective Security for Broadcast Encryption). For a bit b ∈ {0, 1}, we define the selective
security game for broadcast encryption between a challenger and an adversary A as follows:

                                                            28


<!-- pdf-page: 32 -->
   1. The adversary starts by declaring its challenge set S ⊆ [N ] and sends it to the challenger.

   2. The challenger runs (mpk, sk1 , . . . , skN ) ← Setup(1λ , 1N ). The challenger gives mpk and {ski }i /∈S
      to the adversary.

   3. The adversary outputs two messages m0 and m1 .

   4. The challenger sends the encryption ctb ← Encrypt(mpk, S, mb ) to the adversary.

   5. The adversary outputs a bit b′ ∈ {0, 1}.
The scheme is said to be selectively secure if for all efficient adversaries A,

                             | Pr[b′ = 1 : b = 0] − Pr[b′ = 1 : b = 1]| = negl(λ).

Sketch of security proof. We now give a sketch of the proof of selective security for Construction 7.2
to the N -BDHE assumption. In our sketch, we will show that the challenge ciphertext ctb in the selective
security game (Definition 8.2)
                                                                          
                                              Y
                           ctb = g r , v r ·    r
                                                gN                   r
                                                   +1−j , e(g1 , gN ) · mb
                                                                           .                        (8.1)
                                                  j∈S

is computationally indistinguishable from
                                                                                          
                                                      Y
                                 ct′ = g r , v r ·          r
                                                            gN +1−j , e(g1 , gN )
                                                                                 t 
                                                                                     ,                         (8.2)
                                                      j∈S

         r
where t ←   Zp . In particular, ct′ is independent of m0 and m1 . This property implies selective security by
a hybrid argument. At the beginning of the game, the reduction algorithm is given the N -BDHE challenge:

                                     (h, g, g1 , . . . , gN , gN +2 , . . . , g2N , T ),
                        i                               N +1                    r
where h = g β , gi = g α , and T is either e(g, g)α β or e(g, g)t , and α, β, t ← Zp . At the beginning of the
game, the reduction algorithm runs the adversary A to receive the challenge set S ⊆ [N ]. The reduction
algorithm now needs to simulate the master public key mpk, the secret keys ski for all i ∈       / S, and the
challenge ciphertext ctb . Rather than simply give the reduction, we provide a step-by-step outline of how
the different pieces come together.
    • Write the challenge ciphertext as ct∗ = (ct∗1 , ct∗2 , ct∗3 ). The main difference between the ciphertext
      distribution in Eq. (8.1) and Eq. (8.2) is the distribution of ct∗3 . A natural choice then is to use the
      challenge term T to simulate ct∗3 . For instance, the reduction algorithm could set ct∗3 = mb · T . In
                                                       N +1
      this case, we would like to map T = e(g, g)α β to the distribution in Eq. (8.1) and T = e(g, g)t
      to the distribution in Eq. (8.2).
                      N +1
    • If mb · e(g, g)α β is supposed to coincide with the distribution in Eq. (8.1), then we also need
                                       β
      ct∗1 = g β and ct∗2 = v β · j∈S gN +1−j . Similarly, the components gi of the master public key mpk
                                 Q
                             i
      must satisfy gi = g α . Thus, we use the challenge terms g1 , . . . , gN , gN +2 , . . . , g2N to simulate the
      components of mpk and set ct∗1 = h = g β .

                                                               29


<!-- pdf-page: 33 -->
    • The question then is how to construct ct∗2 . The problem is the reduction algorithm does not know
      α or β (i.e., these are the exponents from the challenge). Luckily, we have one remaining degree of
      freedom! The reduction algorithm has not defined the value of v in the master public key yet. In the
      real scheme (Construction 7.2), the element v was a random element in G, so we have some
                                                                                           Q flexibility
                                                                                                   β
      in choosing v. The reduction will choose v so that it is able to simulate ct2 = v · j∈S gN
                                                                                   ∗     β
                                                                                                     +1−j
                                                                    r
      without knowledge of β. One way to do this is to sample ρ ←     Zp and set
                                                           gρ
                                                v=Q                 .                                      (8.3)
                                                        j∈S gN +1−j

      For this choice of v, the value of ct∗2 becomes
                                                               β
                                   Y β                Y
                      ct∗2 = v β ·    gN +1−j = v ·    gN +1−j  = g ρβ = (g β )ρ = hρ .
                                  j∈S                  j∈S

      Observe that the reduction can now simulate ct∗2 without knowledge of β. Moreover, v is still a
                                                                                    r
      uniformly random group element (since the reduction algorithm sampled ρ ←       Zp ). At this point,
      the reduction algorithm has fixed all of the components of the master public key (and the elements
      of the challenge ciphertext)
    • It remains to show that the reduction algorithm can simulate the decryption keys for all indices
      i ∈ [N ] \ S. From Construction 7.2, the decryption key for an index i has the form ski = (i, gi , di ),
      where di = giγ . Here γ is the discrete log of v base g (i.e., v = g γ ). This again seems problematic
      as the reduction algorithm constructed v without knowledge of its discrete log. Here, we make the
      following observation:
                                                      i           i      i
                                        di = giγ = g α γ = (g γ )α = v α .
      A priori, it may not seem that we have made much progress since the reduction algorithm also does
      not know α. However, using the definition of v from Eq. (8.3), we have

                                                                      giρ
                                                       i
                                          i        g ρα
                                  di = v α = Q        αi
                                                             = Q               .
                                                 j∈S gN +1−j     j∈S gN +1−j+i

      Since the reduction algorithm knows the exponent ρ as well as gi for all i ̸= N + 1, the reduction algo-
      rithm can compute di as long as N +1−j +i ̸= N +1 for all j ∈ S. This is true as long as i ̸= j for all
      j ∈ S, or equivalently, if i ∈
                                   / S. This is precisely the set of decryption keys the reduction needs to gen-
      erate. As such, the reduction algorithm is now able to generate decryption keys for every index i ∈   / S.
Before we present the formal reduction, it is instructive to take a step back and study the above reduction
strategy. First, we should affirm that the reduction algorithm is unable to generate decryption keys for
indices i ∈ S. Otherwise, the reduction algorithm could use the key ski to decrypt the challenge ciphertext
itself and trivially determine whether the ciphertext was distributed according to the distribution in Eq. (8.1)
or in Eq. (8.2). As we can see from the above analysis, the requirement i ∈   / S was critical for being able
to generate ski (specifically, generating the di component of ski ). The reduction algorithm in this case has
essentially programmed the challenge set S into the public parameters (without the adversary being able to
notice) in a way that allows it to generate decryption keys for all indices i ∈
                                                                              / S. This type of programming
is essential for completing the security proof (and also the reason why the current strategy only suffices
for proving selective security). We now state the formal theorem and security reduction.

                                                      30


<!-- pdf-page: 34 -->
Theorem 8.3 (Selective Security). If the N -BDHE assumption holds with respect to (G, GT , e), then Con-
struction 7.2 is selectively secure.

Proof. Take any bit b ∈ {0, 1}. Suppose there exists an efficient adversary A that breaks selective security
of Construction 7.2 with non-negligible advantage ε. We use A to construct a new adversary B for the
N -BDHE problem as follows:

   1. At the beginning of the game, algorithm B receives the N -BDHE challenge

                                        (h, g, g1 , . . . , gN , gN +2 , . . . , g2N , T ).

   2. Adversary B starts running A to receive a set S ⊆ [N ].
                            r                                              gρ
   3. Adversary B samples ρ ← Zp . It then computes v = Q                            , and sets the master public key to be
                                                                      j∈S gN +1−j

                                                                                          
                                   mpk = g, g1 , g2 , . . . , gN , gN +2 , . . . , g2N , v .

                                                                                        giρ
      Next, for each i ∈
                       / S, the reduction algorithm computes di = Q                              and sets ski = (i, gi , di ).
                                                                                   j∈S gN +1−j+i
      It sends mpk and {ski }i /∈S to A.

   4. After A outputs a pair of messages m0 , m1 , algorithm B sets ct∗1 = h, ct∗2 = hρ , and ct∗3 = T · mb
      and gives ct∗ = (ct∗1 , ct∗2 , ct∗3 ) to A.

   5. After A outputs a bit b′ ∈ {0, 1}, algorithm B outputs the same bit.

From our earlier analysis, we conclude that algorithm B perfectly simulates the selective security game with
                               N +1
bit b whenever T = e(g, g)α β and the selective security game with a message-independent ciphertext
(i.e., the distribution in Eq. (8.2)) if T = e(g, g)t . Correspondingly, algorithm B breaks the N -BDHE
assumption with the same advantage.

Remark 8.4 (Complexity Leveraging). Why can’t we just guess S beforehand and prove adaptive security?
This is an idea called complexity leveraging. In a setting like IBE, selective security implies adaptive security
by this very approach, because you can guess such an element correctly with 21λ , meaning the proof is still
sound due to subexponential hardness. However this does not hold in broadcast encryption because the
probability would be reduced by 21N . This could cause the reduction to become negligible, so we would
have to show that the algorithm does not allow the adversary to succeed even with ϵ/2N . This means we
would have to scale up the security parameter by at least N , to λ + N . The issue now is that the size of the
ciphertext grows, so it is no longer succinct. Recall that we can trivially implement broadcast encryption
with a linear size ciphertext.

Limitation of broadcast encryption. Another name for this construction of broadcast encryption
is Centralized Broadcast Encryption, because broadcast encryption changes the model familiar to us in
public-key encryption, in the sense that there is now a setup algorithm that generates mpk, sk1 , sk2 , · · · . In
order to run this setup algorithm, there must now be a central point of failure, where the central authority
that runs setup needs to be trusted. Instead of giving power to the end user, we have concentrated power
in a single entity, which some argue is a step backwards in the field of cryptography.



                                                           31


<!-- pdf-page: 35 -->
Distributed broadcast encryption. DBE is a notion that aims to solve the problem of having a central
point of failure. In ths model, there is a public key directory similar to a giant bulletin board. Users can
generate their own secret keys (and public keys), then post their public keys in the directory. It is trivial to
see that broadcast encryption can still be done in linear ciphertext size; however, we would like to achieve
broadcast encryption with sublinear ciphertext size. Specifically, we would like to broadcast to {pki }i∈S
with ciphertext ct of size |ct| = o(|S|). In fact, such a scheme was discovered a few months ago, which
uses the BGW construction to derive a distributed broadcast encryption construction.

Definition 8.5 (Distributed Broadcast Encryption). A distributed broadcast encryption scheme is an
encryption scheme with the following algorithms:

    • Setup() → pp: Generate some public parameters for the scheme to use.

    • KeyGen(pp, i) → (pki , ski ): Run by an individual user i, generates a keypair for the user based on
      the public parameters.

    • Encrypt(pp, (i, pki )i∈S , m) → ct: Given a set of users and their public keys, as well as the public
      parameters, encrypt a message to produce a ciphertext which should only be readable by users in S.

    • Decrypt((i, pki )i∈S , ski , ct) → m: Given a ciphertext, as well as the set of users it was encrypted
      for along with all their public keys, use the individual user’s secret key to decrypt the ciuphertext,
      returning the broadcasted message m.

Construction 8.6 (Kolonelos-Malavolta-Wee Distributed Broadcast Encryption Scheme [KMW23]). This
construction is similar to the BGW scheme, but instead of having a common γ, each user needs to choose
their own γ as all secrets must be introduced during KeyGen.
                         r
    • Setup(n): Sample α ← Zp . Output pp = (g, g1 , g2 , · · · , gN , gN +2 , · · · , g2N ).
                                                                                                      r
    • KeyGen(pp, i): Parse pp = (g, g1 , g2 , · · · , gN , gN +2 , · · · , g2N ). Sample γi ←            Zp . Generate the
      user’s secret key ski = (gi , giγ ) and public key pki = (g γi , g1γi , g2γi , · · · , gi−1
                                                                                              γi     γi
                                                                                                  , gi+1            γi
                                                                                                         , · · · , gN  ). Output
      (ski , pki ).

    • Encrypt(pp, (i, pki )i∈S , m): Parse pp =Q  (g, g1 , g2 , · · · , gN , gN +2 , · · · , g2N ), as well as (i, pki )i∈S =
      (i, g γi )i∈S . Compute the product vS =     i∈S g . Output the ciphertext
                                                          γi

      ct = (g r , (vS j∈S gN +1−j )r , e(g, gN )r m).
                        Q

    • Decrypt((i, pki )i∈S , ski , ct): Parse (i, pki )i∈S = (i, g γi )i∈S , parse ski = (gi , giγ ), as well as ct =
                                                       γ
                                        e(gi ,ct2 )/e(gi i
                                                             Q
                                                            j∈S\i gN +1−j+i ,ct1 )
      (ct1 , ct2 , ct3 ). Output ct−1
                                   3                Q           γj                   .
                                                       j∈S\i e(gi ,ct1 )




                                                                 32


<!-- pdf-page: 36 -->
Derivation. The following identities inform our decision for the Decrypt algorithm:
                             Y
                  e(gi , (vS   gN +1−j )r )
                                j∈S
                                                         Y
                     = e(gi , vS )r e(g1 , gN )r                e(g, gN +1−j+i )r
                                                      j∈S\{i}
                                Y                             Y
                     = e(gi ,         g γi )r e(g1 , gN )r             e(g, gN +1−j+i )r
                                j∈S                          j∈S\{i}

                     = e(giγi , g r )
                                        Y                                      Y
                                                e(gi , g γj )r e(g1 , gN )r             e(g, gN +1−j+i )r
                                        j∈S\i                                 j∈S\{i}
                                                      γ
                     = e(giγi , g r )
                                        Y                                      Y
                                                e(g, gi j )r e(g1 , gN )r             e(g, gN +1−j+i )r
                                        j∈S\i                               j∈S\{i}

Remark 8.7. Unlike in the BGW scheme, individual public keys now scale with N . This is because we
need to provide hints through each public key so that Decrypt for user i can successfully cancel out terms
which are dependent on user j ̸= i’s key.

Remark 8.8. The Setup algorithm still needs to be run by a trusted party which will not remember α after
the fact. In practice, such as for cryptocurrencies, this is usually done through a multiparty computation
during a physical ceremony. Afterwards, the hard drive which the algorithm was run on will be destroyed.




                                                               33


<!-- pdf-page: 37 -->
  CS 395T: Topics in Cryptography                                                        February 13, 2024

                            Lecture 9: Attribute-Based Encryption
  Lecturer: David Wu                                                                     Scribe: Phuc Dang

In an identity-based encryption, both secret keys and ciphertexts are associated with identities, and de-
cryption is successful if the identities match. In this setting, the decryption policy can be viewed as testing
for equality (of the identities associated with the secret key and the ciphertext). In this lecture, we study
a generalization of identity-based encryption to attribute-based encryption (ABE) [SW05, GPSW06] which
supports a broader class of decryption policies. For instance, in key-policy ABE, the ciphertext is associated
with a set of attributes S while the decryption keys are associated with a policy P . Decryption succeeds
whenever the set of attributes satisfy the policy (i.e., we can denote this by writing P (S) = 1).
    As an example, an encrypter might tag ciphertexts with a classification level (e.g., unclassified, se-
cret, or top secret) and the decryption policy associated with a key could be to allow decryption of all
ciphertexts that have the unclassified or secret attribute, but not ciphertexts with a top secret attribute.
In this way, attribute-based encryption provides fine-grained access control to encrypted data. The access
policies are encoded in the semantics of the encryption scheme itself.
Definition 9.1 (Attribute-Based Encryption). Let U be the universe of possible attributes and P be a family
of policies over U. We write 2U to denote the power set of U (i.e., the set of all subsets of U). Then each
policy P ∈ P is a mapping P : 2U → {0, 1} that takes as input a set of attributes S ⊆ U and outputs a bit
b ∈ {0, 1} indicating whether the set of attributes satisfy the policy (b = 1) or not (b = 0). A (key-policy)
attribute-based encryption scheme with attribute universe U, policy family P and message space M is a
tuple of efficient algorithms (Setup, KeyGen, Encrypt, Decrypt) with the following syntax:
    • Setup(1λ ) → (msk, mpk): On input the security parameter λ, the setup setup algorithm outputs the
      master public key mpk and the master secret key msk.

    • KeyGen(msk, P ): On input the master secret key msk and the policy P ∈ P, the key-generation
      algorithm outputs a secret key skP associated with this policy.

    • Encrypt(mpk, S, m) → ct: On input the master public key mpk, a set of attributes S ⊆ U, and a
      message m ∈ M, the encryption algorithm outputs a ciphertext ct.

    • Decrypt(sk, ct) → m: On receiving a secret key sk and a ciphertext ct, the decryption algorithm
      either outputs a message m ∈ M or a special symbol m = ⊥ (to indicate decryption failure).

Correctness. The scheme is correct if for some given some policy P and all sets S ⊆ U such that P(S) = 1,
then Pr[Decrypt(skP , ct) = m] = 1.

Security. We now define semantic security for an ABE scheme. Security says that the adversary cannot
learn anything about a message encrypted to the set of attributes S if it does not have a secret key skP
with a corresponding policy P where P(S) = 1. We will now define this formally. As usual, the game is
parameterized by a bit b ∈ {0, 1}.

    • Setup: At the beginning of the game, the challenger samples (mpk, msk) ← Setup() and sends mpk
      to the adversary A.

                                                      34


<!-- pdf-page: 38 -->
    • Key-generation queries: The adversary A is now allowed to issue key-generation queries on policies
      P of its choosing. On each query, the challenger responds with the secret key skP ← KeyGen(msk, P).

    • Challenge query: When the adversary is done making key-generation queries, it outputs a challenge
                                                                           r
      set S∗ and two messages (m∗0 , m∗1 ). The challenger samples a bit b ← {0, 1} and responds with
      ct∗b ← Encrypt(mpk, S∗ , m∗b )

    • Key-generation queries: The challenger can continue to make key-generation queries on identities
      of its choosing. The challenger responds to each query exactly as before.

    • Output: At the end of the experiment, the adversary outputs a bit b′ ∈ {0, 1}.

We say that adversary A is admissible for the semantic security game if it does not make a key-generation
query on the challenge set S ∗ . Then, we say that the ABE scheme is semantically secure if for every efficient
adversary A,
                           | Pr[b′ = 1 | b = 0] − Pr[b′ = 1 | b = 1]| ≤ negl(λ).

Goyal-Pandey-Sahai-Waters (GPSW). We now introduce the ABE scheme by Goyal et al [GPSW06].
It uses an El-Gamal style encryption. We will build this scheme firstly from a general construction. Then,
we will build a visualization of what a policy tree is and how it makes sense of the boolean formulas used
in generating the share matrix.

Construction 9.2. Assume that the number of attributes (or alternatively, the universe U) is polynomial,
labeling them by integers 1, 2, ..., n.
                                                 r                     r
    • Setup: For each i ∈ [n], sample ti ←           Zp . Sample γ ←       Zp . Then, output the attribute keys
      (T1 = g 1 , ..., Tn = g n , h = e(g, g) ). Let mpk = (T1 , ..., Tn , h) and msk = (t1 , ..., tn , γ).
             t               t               γ


    • Encryption: To encrypt a message m ∈ GT using the mpk and a set of attributes S ⊆ [n], sample
        r
      r←  Zp and output ct = (S, {Tir }i∈S , hr ∗ m).

    • Key Generation: Given the msk, generating a key for policy P is as follows:

         1. Secret share γ according to policy P.
         2. Let γi ∈ Zp be the share associated with attribute i.
         3. The secret key for P is the set g γi /ti for each attribute i that appears in the policy along with
            policy P

      There are still a few details in this key generation algorithm to go over. Namely, how one should
      secret share γ to the policy P. For this, we’ll need to describe the policy as a boolean formula. A
      policy can be visualized as a tree of AND gates and OR gates. For example, say we have a secret key
      skP according to some policy P. This policy in tree form looks like this:
      The leaves 1, 2, 3, 4, and 5 are attributes that a message encrypted to some set S must fulfill. More
      concretely, if a message was encrypted to S = (1, 2), this secret key with the corresponding policy
      P visualized above would be able to decrypt it. However, if the message was encrypted to S = (1, 4),
      then this secret key would not be able to decrypt.



                                                      35


<!-- pdf-page: 39 -->
                                              OR

                                  AND
                                                       AND
                                        OR

                              1     2        3     4         5

Figure 9.1: An example policy tree. Can also be represented as (1 ∧ (2 ∨ 3)) ∨ (4 ∧ 5).




                                             36


<!-- pdf-page: 40 -->
      This is hard to digest how exactly secret sharing works with this policy tree, so breaking it down
      further, let’s describe how γ is secret shared if the policy had just one gate:

                           AND                                                        OR

                       1          2                                               1         2
                                 r
      (a) Sample γ1 , γ2 ←               Zp such that             (b) Propagate the value γ to 1 and 2 such
      γ = γ1 + γ2 . This implies that we need                     that γ1 = γ2 = γ. This implies that we
      both γ1 AND γ2 to obtain γ. The resulting                   only need either γ1 OR γ2 to obtain γ. The
      key is skP = (g γ1 /t1 , g γ2 /t2 ).                        resulting key is skP = (g γ/t1 , g γ/t2 ).

     To simplify, skP can be referred to as K = (K1 , ..., Km ) = (g γ1 /t1 , ..., g γm /tm ) where m denotes the
     number of leaves in the policy tree.

   • Decryption: Given ct = (P, {Tir }i∈S , hr ∗ m) and skP , decryption succeeds if the attributes of set
     S satisfies the boolean formula specified by the policy of our secret key.
      For example, let our policy associated with our secret key be the one defined by the example tree
      [9.1] K = (K1 , K2 , K3 , K4 , K5 ), and let the ciphertext have the attribute set S = (2, 4, 5). This
      means that this part {Tir }i∈S of the ciphertext contains (g rt2 , g rt4 , g rt5 ) which will be instrumental
      in constructing the hr term needed to retrieve m.
      Pairing these terms e(Ki , Tir ) for i ∈ S, gets you e(g γi /ti , g rti ) = e(g, g)γi r . Notice here that the
      exponents of these results are secret shares of γr. More specifically, these secret shares are derived
      from a linear secret sharing scheme. With our example policy tree [9.1], we can use the result of
      e(g, g)γ4 r and e(g, g)γ5 r to reconstruct e(g, g)γr .
      The product of e(g, g)γ4 r ∗ e(g, g)γ5 r is e(g, g)(γ4 +γ5 )r . The exponent (γ4 + γ5 )r indeed perfectly
      reconstructs γr. Note then that we have constructed hr = e(g, g)γr = e(g, g)(γ4 +γ5 )r . Decryption
      is thus trivial.

Remark 9.3. The last thing for this construction is to show how to create a share generating matrix from
a boolean formula.
                                                                    r
   • AND gate: For an AND gate, we can secret share γ by sampling α ← Fp and setting γ1 = γ + α
     and γ2 = −α:                                    
                                        γ1      1 1        γ
                                            =           ·
                                        γ2      0 −1       α

   • OR gate: For an OR gate, we can secret share γ by setting γ1 = γ2 = γ:
                                                
                                              γ1      1  
                                                  =      · γ
                                              γ2      1




                                                        37


<!-- pdf-page: 41 -->
• General Procedure: To associate a policy tree with a share generating matrix:

    1. Associate vector [1] with root node and initialize counter c ← 1.
    2. Proceed down the tree.
          – If a node is an OR with label v, the children are associated with label v (i.e. they are identical
            to the parent).
          – If a node is an AND with label v, we label the children with label v∥0len(v)−c ∥1 and the other
            label with 0c ∥ − 1. Observe that the sum of the shares is v∥0len(v)−c . Finally, increment
            c ← c + 1.
    3. Pad all vectors with 0s to dimension c.

  For example, using the policy tree we’ve introduced above [9.1], we will label it accordingly to these
  steps.

                                                                [1], c = 1


                                                                  OR
                                              [1], c = 1

                                              AND                                     [1], c = 1
                                                              [0|−1], c = 2
                                                                              AND
                                                           OR

                                          A         B            C            D       E
                    [1|−1], c = 2                                                                  [1|0|−1], c = 3

                                    [0|−1], c = 2          [0|−1], c = 2          [1|0|−1], c = 3



                Figure 9.3: A labeled policy tree, now with alphabetic leaf labeling.

  The share-generation matrix follows suit from this tree, where the first row corresponds to the share
  held by A, the second corresponds to the share held by B and so on:
                                                                    
                                             1 1  0           γ + α1
                                           0 −1 0     γ       −α1 
                                                                    
                                           0 −1 0  · α1  =  −α1 
                                                                    
                                           1 0   1  α2       γ + α2 
                                             0 0 −1              −α2
                                           |   {z   }
                                                    MP

• Main observation: If the attributes of the ciphertext satisfy policy, then the vector eT1 = [1, 0, ..., 0]
  will be in the row span of Mp . Conversely, if the attributes do not satisfy policy, then the vector eT1
  is not in the row span of Mp . More generally, the boolean formula policy P on k attributes can be
  transformed into a share generating matrix M with k rows.




                                                                   38


<!-- pdf-page: 42 -->
Construction 9.4. We will now reconstruct the GPSW scheme with this share generating matrix M in
mind. Let n denote the attribute universe.
                                                     r           r
   • Setup(n) → (msk, mpk): Sample t1 , ..., tn ←       Zp and γ ← Zp . Set mpk = (T1 , ..., Tn , h) and
     msk = (t1 , ..., tn , γ) where Ti = g i and h = e(g, g) .
                                          t                 γ

                                       r
   • Encrypt(mpk, S, m) → ct: Sample r ← Zp and set ct = ({(i, Tir )}i∈S , hr m).

   • KeyGen(msk, M ) → sk: As shown before, M ∈ Zkxl   p is the share generating matrix associated with
                                       r
     the policy. Sample α1 , ..., αl−1 ← Zp and let N = [γ, α1 , α2 , ..., αl−1 ]. Compute the shares of λ:

                                                             γ
                                                                                
                                                   
                                                   s1       α1 
                                                               
                                                   ..     α2 
                                                   . =M ·     = M · NT
                                                            . 
                                                   sk       .. 
                                                                          αl−1

     Then, let p : [k] → [n] be the mapping from the row index of M to the attribute index in [n]. Output
     sk = (M, {(i, g si /tp(i) )}i∈[k] ).

   • Decrypt(sk, ct) → m: Parse sk = (M, {(i, Di )}i∈[k] ) and ct = ({(i, Ci )}i∈S , Z).
     If S satisfies the policy, then there exists a vector v ∈ Zkp such that v T M = [1, 0, ..., 0] and vi = 0
     for all p(i) ∈ S.
     Compute Y             Z
                                         .
                       e(Cp(i) ,Di )vi
               i∈[t]


Correctness. We can prove correctness as follows:

                               Y                            Y
                                       e(Cp(i) , Di )vi =           e(g rtp(i) , g si /tp(i) )vi
                               i∈[t]                        i∈[t]
                                                            Y
                                                      =             e(g, g)rsi vi
                                                            i∈[t]
                                                                           T       T
                                                      = e(g, g)rv M ·N = e(g, g)γr = hr

Security. Security proof to follow in the next lecture…




                                                                     39


<!-- pdf-page: 43 -->
  CS 395T: Topics in Cryptography                                                               February 15, 2024

                              Lecture 10: Attribute-Based Encryption
  Lecturer: David Wu                                                                        Scribe: Shafik Nassar


Last Lecture Review. In the last lecture, we started discussing the Goyal-Pandey-Sahai-Waters (GPSW)
Attribute-Based Encryption (ABE) scheme. Recall that the GPSW scheme is a key-policy ABE, mean-
ing that each secret key contains a policy and each message is encrypted to a certain set of attributes
which are labeled by integers 1, . . . , n. The correctness requirement states that a user with access policy
P : {0, 1}n → {0, 1} should be able to decrypt a ciphertext that was encrypted to a set S ∈ {0, 1}n (a
subset of [n] can be represented by an n bit string) if P (S) = 1.
    We also saw that a Boolean access formula over k attributes can be associated with a k × ℓ share-
generating matrix M , where ℓ is the number of AND gates in the formula. To share a secret γ ∈ Zp using
                                              r
M , we first sample uniform α1 , . . . , αℓ−1 ←  Zp and compute:
                                                        
                                                     γ         
                                                   α1        s1
                                                         s2 
                                              M ·  α2  =  . 
                                                          
                                                   ..   .. 
                                                   . 
                                                               sk
                                                    αℓ−1

The matrix M satisfies the following: if a set S ⊆ [k] satisfies the access policy then there exists a vector
v ∈ Zkp such that
                                v T · M = [1 0 0 . . . 0] and ∀i ∈
                                                                 / S : vi = 0.
The first condition allows us to reconstruct the secret, and the second condition guarantees that we only
need the attributes in the set S to do so. We can see that by examining the following equation:
                                                                     
                                                γ                     γ
                                              α1                 α1 
                                                                     
                               γ = v T · M ·  α2  = v T · M ·  α2 
                                                                     
                                              ..                  .. 
                                              .                   . 
                                                            
                                                            
                                              αℓ−1                  αℓ−1

Secret sharing security. The previous property guarantees correctness. Additionally, we want to
guarantee security. Consider the following property. If S ⊆ [k] does not satisfy the access policy then
the vector e1 = [1 0 0 . . . 0] is not spanned by the rows of M that are associated with S (rows i such that
i ∈ S). Clearly, this property is necessary for security: if the vector e1 is spanned by the rows associated
with S, then we can simply take the linear combination that gives us e1 , and reconstruct γ directly. We also
claim that this property is sufficient for security. Suppose v1 , . . . , vm ∈ Zℓp for m < ℓ and suppose that e1 ∈   /
span(v1 , . . . , vm ). Then e1 decomposes to two parts e1 = e1,V +e1,V ⊥ , such that e1,V is in span(v1 , . . . , vm )
and e1,V ⊥ is in the subspace that is orthogonal to span(v1 , . . . , vm ). This implies that there exists a w ∈ Zp
such that ∀i ∈ [n] : wT vi = 0 and wT e1 ̸= 0, and without loss of generality, the first coordinate of w can
be 1. This implies that the secret γ can never be “isolated” using the vectors v1 , . . . , vm , therefore we have
perfect secrecy. We will come back to this property later on when we prove the security of GPSW.

                                                          40


<!-- pdf-page: 44 -->
GPSW ABE scheme. Recall the GPSW scheme:
    • Setup(n) → (msk, mpk):
                               r
        1. Sample t1 , ..., tn ← Zp and set Ti = g ti for all i ∈ [n].
                    r
        2. Sample γ ← Zp and set h = e(g, g)γ .
        3. Output mpk = (T1 , ..., Tn , h) and msk = (t1 , ..., tn , γ).
                                        r
    • Encrypt(mpk, S, m) → ct: Sample r ← Zp and set ct = ({(i, Tir )}i∈S , hr m).

    • KeyGen(msk, M ) → sk: The matrix M ∈ Zk×ℓ
                                            p   is the share generating matrix, and k is the number
      of attributes that M depends on.
                                    r
        1. Sample α1 , . . . , αℓ−1 ← Zp , and secret share γ:
                                                                     
                                                                γ
                                                     s1          α1 
                                                    s2             
                                                    ..  ← M ·  α2 
                                                                   
                                                   .           .. 
                                                                 . 
                                                    sk
                                                                 αℓ−1

        2. Let ρ : [k] → [n] be a share labeling function that translates an index in the rows of M to an
           attribute. We can skip this, but then the size of M (and thus the secret keys) will grow with
           n instead of k.                        
                              n               o
        3. Output sk = M, i, g       si /tρ(i)
                                                    .
                                                 i∈[k]

    • Decrypt(sk, ct) → m: Parse sk = (M, {(i, Di )}i∈[k] ) and ct = ({(i, Ci )}i∈S , z). If S does not satisfy
      the policy, output ⊥.Otherwise, there exists a vector v ∈ Zkp such that v T M = [1, 0, ..., 0] and vi = 0
      for all ρ(i) ∈ S. Output
                                                        z
                                                Y                    .
                                                    e(Cρ(i) , Di )vi
                                                 i∈[k]

Correctness was proved in the previous lecture. We move on to security.

Selective Security. In the selective security game, the adversary commits to a set S ∗ ⊆ [n] ahead of
time. We actually show a stronger property than indistinguishability. We prove that the ciphertext is
indistinguishable from a distribution that does not depend on the message (almost that the ciphertexts are
pseudorandom). That is
                                                                               r
                     {(i, Tir )}i∈S , hr m ≈ {(i, Tir )}i∈S , e(g, g)α where α ←
                                                                                  
                                                                                 Zp .

We explicitly state the security game, which is parameterized by a bit b ∈ {0, 1}.
   1. Set declaration: The adversary A sends the number of attributes 1n and a set S ∗ ⊆ [n].

   2. Setup: The challenger samples msk ← (t1 , . . . , tn , γ) and mpk ← (T1 , . . . , Tn , h) as in Setup and
      sends mpk to A.

                                                         41


<!-- pdf-page: 45 -->
   3. Key-generation queries: The adversary A is now allowed to issue key-generation queries on access
      policy matrices M ∈ Zk×ℓ
                           p    of its choosing. On each query, the challenger responds with the secret
      key skM ← (M, {(i, Di )}i∈[k] ) which is computed as in KeyGen.
   4. Challenge query: When the adversary is done making key-generation queries, it outputs a mes-
      sage m∗ . If b = 0 then the challenger computes ct∗ as an encryption of m∗ , that is ct∗ ←
                                          r
      ({(i, Tir )}i∈S ∗ , hr m∗ ) where r ← Zp . If b = 1 then the challenger samples additionally a ran-
                r
      dom α ← Zp and sets ct ← ({(i, Tir )}i∈S ∗ , e(g, g)α ). The challenger sends ct∗ to A.
                                   ∗


   5. Key-generation queries: The challenger can continue to make key-generation queries on identities
      of its choosing. The challenger responds to each query exactly as before.
   6. Output: At the end of the experiment, the adversary outputs a bit b′ ∈ {0, 1}.

Security reduction. Recall the Decisional Bilinear Diffie Hellman (DBDH) assumption:
                                                       c                            
                        g, g a , g b , g c , e(g, g)abc ≈ g, g a , g b , g c , e(g, g)d ,
                  r
where a, b, c, d ←   Zp . The challenging part is that the reduction algorithm needs to generate secret keys
for all policies except the ones that are able to decrypt (ciphertexts for) S ∗ . Recall that this is a good sanity
check: if the reduction can beat the security game without the help of the adversary then there is something
wrong. This is similar to the case of identity based encryption, but it is harder for policies!
    Assume A is an adversary for the selective security game. Here is a reduction strategy to DBDH:
   1. The reduction receives the tuple (g, A, B, C, U ).
   2. Adversary A declares set S ∗ ⊆ [n].
   3. The reduction algorithm needs to do the following:
        (a) Construct mpk, namely construct T1 , . . . , Tn and h = e(g, g)γ .
        (b) Construct ct∗ , namely construct {Tir }i∈S ∗ and the blinding factor e(g, g)γr . Note that if b = 1
            in the experiment then the blinding factor is a random element in the target group.
        (c) Answer key generation queries. This is the hardest part.
   4. Eventually, when A makes a guess, the reduction outputs that same guess.
The reduction needs to map γ and r to a, b, c. Let us use r ← c and γ ← ab.
                                     h ← e(A, B) = e(g, g)ab = e(g, g)γ .                                    (10.1)
Since the reduction wants to use the guess of A regarding the encryption in order to distinguish between
the case where U = e(g, g)abc and U is a random element in the target group, then it better be the case
that the blinding factor e(g, g)γr that is constructed in the ciphertext is U . This means that the reduction
does not know r, therefore it must know ti for all i ∈ S ∗ .
                                                       r
                                  For all i ∈ S ∗ : ti ← Zp and set Ti ← g ti .                              (10.2)


                                        For all i ∈ S ∗ : Ti ← C ti = Tir .                                  (10.3)
We still need to choose Ti for i ∈
                                 / S ∗ . We will do that as we figure out how answer key-generation queries.

                                                        42


<!-- pdf-page: 46 -->
Answering key-generation queries. Let M ∈ Zk×ℓ           p    be the policy (matrix) that A queries. Denote row
i of M by mi . Let ρ : [k] → [n] be the index translation function. Normally, the ABE challenger would
              T

sample uniform α1 , . . . , αℓ−1 , set f = [ab α1 . . . αℓ−1 ]T and compute the shares s1 , . . . , sk using M · f .
Finally, the secret key would consist of (M, {(i, Di )}i∈[k] ), where Di = g si /tρ(i) . Our reduction will have
to construct Di differently. First, we can decompose f as follows
                                                                                  
                                                                1                0
                                                              w2             α1 
                            f = b · z + ab · w where w =  .  and z =  . 
                                                                                  
                                                               ..            .. 
                                                                    wℓ              αℓ−1

Specifically, because we know that the queried policy M is not satisfied by S ∗ , we can choose w, as in the
discussion about the secret sharing scheme, to be orthogonal to {mTi }i∈S ∗ (the rows of M that correspond
to S ∗ ). Now we split to two cases. The easiest one is if ρ(i) ∈ S ∗ . In this case, we know tρ(i) and additionally
have mTi w = 0. This last cancellation is what saves us. This allows us to simplify the exponent:

                                           si         bmTi z + abmTi w   bmTi z
                                                  =                    =        .
                                          tρ(i)              tρ(i)        tρ(i)

                                                                                                              mT
                                                                                                               iz
                               mT z
The reduction can compute t i , and g b = B, therefore the reduction can compute Di = g si /tρ(i) = B tρ(i) .
                               ρ(i)
If ρ(i) ∈
        / S ∗ , then the problem here is that we do not have tρ(i) . To solves the problem, we choose tρ(i) = δi ·b
for some random δi . This preserves the distribution of tρ(i) . The exponent can be simplified again

                                   si           bmTi z + abmTi w  mT z + amTi w
                                           =                     = i            .
                                  tρ(i)                tρ(i)            δi

                               mTiz   mT
                                       iw
The reduction can compute       δi and δi . Again, g is simply A. This allows the reduction to compute
                                                    a

        mT
         iz    mT
                iw
Di = g δi A δi . Note that by setting tρ(i) for i ∈ / S ∗ we have also set the corresponding Tρ(i) = g bδi ,
and thus we have completed the construction of mpk. In total, the reduction can perfectly simulate the
security game for A and answers 0 if U = e(g, g)abc and answers 1 if U = e(g, g)d .
Note that we have implicitly used the perfect secrecy of the secret sharing scheme when constructing Di .




                                                              43


<!-- pdf-page: 47 -->
  CS 395T: Topics in Cryptography                                                         February 20, 2024

                      Lecture 11: Somewhat Homomorphic Encryption
  Lecturer: David Wu                                                                    Scribe: Zhiyi Huang

In the previous lectures, we mainly focused on topics of different applications of pairing-based encryption
schemes. From now on we will turn to the topics of proof systems. We will start by a question: Can we
compute on encrypted data? This will lead to the idea of Homomorphic Encryption. While Fully Homo-
morphic Encryption(FHE) is allowing us to do arbitrary computation on ciphertexts using only the public
key, we will start by a simpler version which only allows us to do limited computation on the ciphertext.

Additively homomorphic encryption.              We start by describing a variant of classic ElGamal encryption
which is additively homomorphic:
                                    r
    • Setup() → pk, sk: We sample x ← Zp and set pk = (g, h = g x ), sk = x.
                                    r
    • Encrypt(pk, m) → ct: Sample r ← Zp and set ct = (g r , u = hr · m).

    • Decrypt(sk, ct) → m: Output m = (gur )x

      In order to support addition, we need to modify this scheme a little bit: where we set the ciphertext ct =
(g r , u = hr · g m ), where we assume the message m ∈ Z. However, now in the decryption stage, we only get
g m . So we need to ensure the message m to be small (poly-size) in order to get m using brute force logarithm.
      Here is how we support addition on the modified version of ElGamal:

    • Input: ct1 = (g r1 , u1 = hr1 · g m1 ) and ct2 = (g r2 , u2 = hr2 · g m2 ).

    • Output: ct = (g r1 +r2 , u = u1 · u2 = hr1 +r2 · g m1 +m2 ).

    Notice if ct1 and ct2 are encrypted using the same public key, then we can use the corresponding
secret key to decrypt ct. This scheme which supports addition is also known as Additively Homomorphic
Encryption.
    Notice that using addition with multiplication, we will be able to support any function we want to
compute. However, we need a different approach to support multiplication.

Definition 11.1 (Composite-order pairing groups). We call a symmetric pairing group (G, GT , e) with
order N as a symmetric composite-order pairing group if N = pq where p and q are two large primes.

Remark 11.2. Recall those important properties of composite-order pairing groups:

    • N is public while p and q are secret.

    • Let g be a generator of G. Define gp = g q , then the order of gp is p. And we can define Gp as the
      subgroup of order p generated by gp .

    • Similarly, we can define gq = g p with order q as well as the subgroup Gq .




                                                         44


<!-- pdf-page: 48 -->
Boneh-Goh-Nissim (BGN). We now introduce the Boneh-Goh-Nissim (BGN) scheme [BGN05], which
supports multiple additions and one multiplication on the ciphertexts.

    • KeyGen() → pk, sk: Sample N = pq and a composite-order pairing groups (G, GT , e). Also Sample
        r
      x←  ZN and set pk = (g, h = gqx ), sk = q.
                                    r
    • Encrypt(pk, m) → ct: Sample r ← Zp and set ct = (g r , u = hr · g m ).

    • Decrypt(sk, ct) → m: Compute uq = g mq and find m such that gpm = uq

    Here is how we support addition, it is exactly the same as what we do for Modified ElGamal:

    • Input: ct1 = (g r1 , u1 = hr1 · g m1 ) and ct2 = (g r2 , u2 = hr2 · g m2 ).

    • Output: ct = (g r1 +r2 , u = u1 · u2 = hr1 +r2 · g m1 +m2 ).

    Here is how we support multiplication:

    • Input: ct1 = (g r1 , u1 = hr1 · g m1 ) and ct2 = (g r2 , u2 = hr2 · g m2 ).

    • Output: ct = (g r1 +r2 , u) where u = e(hr1 g m1 , hr2 g m2 ).

Notice that we need to pair two messages to output the ciphertext for multiplication, which means we are
only allowed to do 1 multiplication.

Correctness. We actually need to prove correctness for the encryption scheme as well as addition and
multiplication. While the correctness for the encryption scheme and the addition is trivial, we will only
prove the correctness for multiplication.
Assume we encrypt ct1 and ct2 using the same public key, now with the corresponding secret key q.

                                uq = e(hr1 g m1 , hr2 g m2 )q
                                   = e(hr1 , hr2 g m2 )q e(g m1 , hr2 )q e(g m1 , g m2 )q
                                   = e(g m1 , g m2 )q
                                   = e(g, g)m1 m2 q


The third equation is because e(hr1 , hr2 g m2 ) and (g m1 , hr2 ) are elements in order q subgroup of GT since
h = gq . Thus we can use brute force logarithm to find m1 · m2 where e(g, gp )m1 ·m2 = uq .


Security. We will use the same context of semantic security as the one we used for ElGamal encryption
scheme. And the proof of semantic security for BGN scheme will be very similar to the proof for semantic
security for ElGamal, except we need to rely on a different security assumption.




                                                          45


<!-- pdf-page: 49 -->
Subgroup decision assumption. For a composite-order group G with order N = pq, the subgroup
decision hardness is:                         c
                                 g, gqs , gqr ≈ g, gqs , g r ,
                                                            

            r
where r, s ←   Zp . And we don’t know either p or q or gp .
    Now, we are switching context to Integrity of Computations by introducing the concept of Non-
interactive zero-knowledge (NIZK) proof systems. In this context, zero-knowledge proof stands for proving
a statement x is true without revealing anything more about x.

Definition 11.3 (NP Languages). We call L as an NP language if there exists an efficient relation R such that:

                                      x ∈ L ⇐⇒ ∃w : R(x, w) = 1

Sketch of proof systems for NP languages.

    • The prover takes x, w as input and produce a “proof” π.

    • The verifier takes x as input and receives the “proof” π. It outputs 1/0 depending on whether
      R(x, w) = 1 or not.

Definition 11.4 (NIZK proof for an NP language L). A NIZK proof for an NP language L is a tuple of
three efficient algorithms (Setup, Prove, Verify) with the following syntax:

    • Setup(1λ ) → crs: On input the security parameter λ, the setup algorithm outputs the common
      reference string crs.

    • Prove(crs, x, w) → π: On input the common reference string crs, the statement x, and a witness w,
      the prove algorithm outputs a proof π.

    • Verify(crs, x, π) → 1/0: Output the verified result of proof π.


Requirements. As we have correctness and security requirements for encryption scheme, we will have
two requirements for a proof system:

    • Completeness: Suppose R(x, w) = 1. If crs ← Setup() and π ← Prove(crs, x, w), we have
      Verify(crs, x, π) = 1.

    • Soundness: For all adversary A (we don’t assume efficiency here):

              Pr[x ∈
                   / L ∩ Verify(crs, x, π) = 1 : crs ← Setup(), π ← Prove(crs, x, w)] ≤ negl(λ)

   Above is only the requirements for a valid proof system, we still need a definition for zero-knowledge.

Definition 11.5 (Zero-Knowledge). There exists an efficient simulator S = (S0 , S1 ) such that for all
efficient A:
                                     |w0 − w1 | ≤ negl(λ)
where w0 and w1 are defined as follows:


                                                     46


<!-- pdf-page: 50 -->
   • Real distribution
                                w0 = Pr[AOo (crs,·,·) (crs) = 1 : crs ← Setup()]

   • Ideal distribution
                                 w1 = Pr[AO1 (st,·,·) (crs) = 1 : (crs, st) ← S0 ]

O0 and O1 are oracles defined as:

   • O0 (crs, x, w): If R(x, w) = 1: output Prove(crs, x, w), otherwise: output ⊥

   • O1 (st, x, w): If R(x, w) = 1: output S1 (st, x), otherwise: output ⊥

Groth-Ostrovsky-Sahai (GOS) NIZK proof system sketch [GOS06]. The GOS NIZK proof system
reduces the task of constructing a NIZK for a general NP language to constructing a NIZK for a related
boolean circuit consisting of only NAND gates as follows.

   1. Let C be a boolean circuit which computes an NP relation R, assuming without loss of generality
      that C consists only of NAND gates (which are universal).

   2. Firstly, the prover encrypts (or rather commits to) the values of each wire in C.

   3. Next, the prover provides the verifier with the randomness for the statement and output wires
      (allowing the verifier to observe that the output of the circuit was “1” and that the correct statement
      was used; both of these are public pieces of information).

   4. Finally, the prover argues that each of the NAND gates was computed correctly, which is sometimes
      referred to as “internal consistency”.




                                                     47


<!-- pdf-page: 51 -->
  CS 395T: Topics in Cryptography                                                         February 22, 2024

                       Lecture 12: Non-Interactive Zero Knowledge
  Lecturer: David Wu                                                                  Scribe: Zeki Gurbuz

Recall at the end of the previous lecture that we covered the high-level ideas behind the Groth-Ostrovsky-
Sahai (GOS) Non-interactive Zero Knowledge (NIZK) proof system, which reduces the task of constructing
a NIZK for a general NP language to constructing a NIZK for a related boolean circuit consisting of only
NAND gates as follows [GOS06]:

   1. Let C be a boolean circuit which computes an NP relation R, assuming without loss of generality
      that C consists only of NAND gates (which are universal).

   2. Firstly, the prover encrypts (or rather commits to) the values of each wire in C.

   3. Next, the prover provides the verifier with the randomness for the statement and output wires
      (allowing the verifier to observe that the output of the circuit was “1” and that the correct statement
      was used; both of these are public pieces of information).

   4. Finally, the prover argues that each of the NAND gates was computed correctly, which is sometimes
      referred to as “internal consistency”.

    In this lecture, we will introduce the “commit and prove” paradigm, give a more detailed description
of GOS, which will make use of the Boneh-Goh-Nissim (BGN) encryption scheme and its homomorphic
properties which we covered previously, and finally motivate the idea of batch arguments (BARGs), the
topic of our next lecture.

The commit-and-prove paradigm. In terms of the boolean circuit C defined above, the commit and
prove paradigm describes proof systems that follow the following general protocol:

   1. The prover commits to a statement x and a witness w.

   2. Next, the prover proves that the commited values satisfy the relation C(x, w) = 1.

   While we haven’t formally covered commitments in this course, a helpful intuitive notion are “sealed
envelopes”, which physically give the relevant guarantees that:

    • Once a message is written down and put into the sealed envelope, the message can’t be altered (that
      is, once the envelope is opened, the message observed will be the same message which was originally
      written down).

    • Until the envelope is unsealed, its contents are hidden from the outside world.

    One example of the commit and prove paradigm is the prototypical interactive zero-knowledge proof
system example of graph 3-coloring:

   1. The prover will commit to the color of each node in the graph.


                                                     48


<!-- pdf-page: 52 -->
   2. The verifier will ask to observe the colors of two nodes incident to a particular edge.

    If the graph is indeed 3-colorable, then the verifier will always observe consistency. Otherwise, at least
one edge in the graph would reveal a contradiction. As such, repeating the above protocol many times
(while the prover repeatedly permutes the three colors it uses as to maintain zero-knowledge) can give
a verifier which chooses a random edge each time strong confidence that the graph is indeed 3-colorable.

The Groth-Ostrovsky-Sahai (GOS) construction. We now turn our attention back to the GOS con-
struction. Throughout the following description, C : {0, 1}n × {0, 1}h → {0, 1} will represent a boolean
circuit, consisting solely of NAND gates, which computes an NP relation R. C takes as input an n-bit
statement as well as an h-bit witness and produces a single bit corresponding to R(x, w). As an example,
C might look like so (where here n = h = 2):

                                        x1 , 1
                                                                  5
                                                   1, 2, 5

                                        x2 , 2
                                                                      5, 6, 7   7
                                        w1 , 3
                                                   3, 4, 6
                                                                  6
                                        w2 , 4

    Notice in particular that each wire has been given an index. Let s denote the total number of wires in
C. The indices 1, 2, . . . , n will then index the statement, the indices n + 1, n + 2, . . . , n + h will index the
witness, and finally the indices n + h + 1, n + h + 2, . . . , s will index the non-input wires. Furthermore,
we will assume that all of the wires are indexed in a topological ordering. In particular, the prover can
always compute the value of wire i by knowing the values of the wires 1, 2, . . . , i − 1 and the structure
of the circuit. Clearly, this forces wire s to be the output wire. Notice that each NAND gate is also labeled
with a triple of wire indices, the first two being the input wires and the last being the output wire.
    Next, the prover will compute C(x, w). We denote t1 , t2 , . . . , ts ∈ {0, 1} to be the values of the wires
during the computation. The prover now commits to the values t1 , t2 , . . . , tn . To do so, it will use the
                                                                              r
BGN encryption scheme, that is, for each i ∈ [s], the prover samples ri ←        ZN and sets ci ← g ti · hri . The
following tasks remain for the prover:

    • It must show that cs commits to the value 1 (proving that C(x, w) = 1).

    • It must show that c1 , c2 , . . . , cn commits to the statement x.

    • It must show “internal consistency”, that is:

         – It must show that for all i ∈ [s], ci commits to either 0 or 1.
         – It must show that each NAND gate is computed correctly.

     The first two requirements are simple; the fact that C(x, w) should evaluate to 1 and the statement
itself are public information, so the prover can include r1 , r2 , . . . , rn and rs in the common reference string.
From there, the verifier can itself check for consistency. The challenge is to show internal consistency.

                                                             49


<!-- pdf-page: 53 -->
Commitments to 0/1. The main remaining task is to show that for all i ∈ [s], ci commits to either 0 or 1.
Let us first consider a fixed index i ∈ [s]. Then our BGN commitment is of the form c = g t · hr . If t ∈ {0, 1},
then either c = hr or c · g −1 = hr . We now introduce a composite-order pairing group (G, GT , e) where
|G| = N = pq where p, q are large primes. By the “projection” property of composite-order pairing groups,
then for an honest prover, e(c, c · g −1 ) lives in an order-q subgroup of GT , since one of c and c · g −1 live
in Gq . This implies that e(c, c · g −1 ) = e(h, u) for some u ∈ G, since ⟨h⟩ = Gq .
    In particular, we can explicitly calculate this value u ∈ G for when t = 0 and when t = 1:

    • If t = 0, then e(c, c · g −1 ) = e(hr , hr · g −1 ) = e(h, (hr · g −1 )r ), implying that u = (hr · g −1 )r .
    • If t = 1, then e(c, c · g −1 ) = e(g · hr , hr ) = e(h, (hr · g)r ), so u = (hr · g)r .

    More generally, u = (hr ·g 2t−1 )r for t ∈ {0, 1}. Our initial approach, which will have a specific flaw, will
be for the prover to provide ui for each i ∈ [s], and then have the verifier check that e(ci , ci · g −1 ) = e(h, ui )
for each i ∈ [s]. To see why this is sound, we will argue that if c = g t · hr for some t ̸∈ {0, 1}, then such
a u does not even exist. As a slight aside, note that expressing c in this form binds the value of t mod p; it
                                               ′    ′
is not possible to have that c = g t · hr = g t · hr since h is in the order-q subgroup. Then, we compute that

           e(c, c · g −1 ) = e(g t · hr , g t−1 · hr ) = e(g, g)t·(t−1) · e(g t , hr ) · e(g t−1 , hr ) · e(hr , hr ).
    Notice that the latter three terms in this expression all live in the order-q subgroup of GT , whereas
e(g, g)t·(t−1) lives in the full group GT . In particular, if t ̸∈ {0, 1}, then t · (t − 1) ̸= 0, so e(c, c · g −1 ) is
non-identity in the order-p subgroup. On the other hand, e(h, u) would live in the order-q subgroup, so
the verification relation can never be satisfied.
    As mentioned, this approach does have a flaw – it is not zero knowledge! This is because of the fact
that there is no randomness. The intuition for why this is is similar to the idea that no deterministic
encryption scheme can be semantically secure. We need to randomize somehow, and to do so we will
                                                                                                       r
pair with hα (where α is chosen randomly) instead of pairing with h. Suppose we pick α ←                  Z∗N . Then
                      −1 mod N
                α
e(h, u) = e(h , u   α          ), and we can replace our verification relation accordingly.
                                                                           −1
    We will begin to build our proof as π1 ← hα and π2 ← hα , and use the verification relation
               ?
e(c, c · g −1 ) = e(π1 , π2 ) = e(h, u). But now we have introduced another problem – this change to our
verification relation breaks soundness! The adversary could simply pick π1 to be an element of the order-p
subgroup, trivializing the verification relation. As such, we will also include in our proof π3 ← g α . Then,
                                     ?
we additionally check e(π1 , g) = e(π3 , h). Since g and π3 do not live in the order-q subgroup and h does,
this forces π1 to live in the order-q subgroup as desired.
     The informal argument for why this randomized version of our original idea is indeed zero knowledge
is that we can “lift” h to the full group using the assumed hardness of the subgroup decision problem. Then,
it becomes true that π1 fully determines the values of π2 and π3 .

Commitments to NAND consistency. The other remaining task to show internal consistency is to
argue that each NAND gate is computed correctly. We can describe each NAND gate as a tuple of three
elements (i, j, k) where i, j, k ∈ [s] and i < j < k. The first two values of the tuple represent the indices
of the input wires to the NAND gate, and the third value represents the index of the output wire. As such,
our goal will be to show that tk = NAND(ti , tj ).
     The convenient position we find ourselves in is that we have already shown that ti , tj , tk ∈ {0, 1}. In
particular, for tk = NAND(ti , tj ) if and only if tk = 1 − ti · tj , which for ti , tj , tk ∈ {0, 1}, is if and only
if ti + tj − 2 · tk + 2 ∈ {0, 1}. This can be seen via case analysis, but we do not include a proof.

                                                               50


<!-- pdf-page: 54 -->
    Our strategy will be to derive a commitment to ti + tj − 2 · tk + 2 using the linear homomorphism
of BGN encryption, and then use our same strategy to argue that this commitment is to either zero or one.
We compute ci · cj · c−2      2
                       k ·g = g
                                   ti +tj −2·tk +2 · hri +rj −2·rk , the desired commitment. In particular, we do

not prepare this commitment using multiplicative homomorphism, since this would leave us stuck in the
target group with no hope of using our previous strategy.
    Finally, we will give a formal description of GOS:

Construction 12.1 (The Groth-Ostrovsky-Sahai (GOS) NIZK Proof System).


    • Setup(): The common reference string is prepared as crs ← ((G, GT , e), N = pq, g, h ∈ Gq , C) for
      a composite-order pairing group of order N = pq where p, q are large primes, ⟨g⟩ = G, ⟨h⟩ = Gq ,
      and C : {0, 1}n × {0, 1}h → {0, 1} a circuit consisting of solely NAND gates which computes the
      NP relation R(x, w).

    • Prove(crs, x ∈ {0, 1}n , w ∈ {0, 1}h ) :

         1. Let t1 , t2 , . . . , ts be the wires of C(x, w) in topological ordering.
                                        r
         2. For each i ∈ [s], sample ri ← ZN and let ci ← g ti · hri .
         3. For each i ∈ [s],
                            r
              (a) Sample αi ← Z∗N .
                          (1)              (2)          −1           (3)
             (b) Let πi   ← hαi , πi ← hαi , and πi                        ← g αi .
                                          
                             (1)   (2) (3)
              (c) Let πi ← πi , πi , πi .
         4. For each (i, j, k) ∈ C,
                                  r
              (a) Sample α(i,j,k) ← Z∗N .
             (b) Let c(i,j,k) ← ci · cj · c−2
                                           k ·g .
                                               2

                                (1)                  (2)                −1            (3)
              (c) Let Let πi   ← hα(i,j,k) , πi ← hα(i,j,k) , and πi                        ← g α(i,j,k) .
                                                             
                                  (1)         (2)      (3)
             (d) Let π(i,j,k) ← π(i,j,k) , π(i,j,k) , π(i,j,k) .
         5. Output π ← (c1 , c2 , . . . , cs , {c(i,j,k) }(i,j,k)∈C , r1 , r2 , . . . , rn , rs , {πi }i∈[s] , {π(i,j,k) }(i,j,k)∈C ).

    • Verify(crs, x ∈ {0, 1}n , π) :

         1. Parse π as (c1 , c2 , . . . , cs , {c(i,j,k) }(i,j,k)∈C , r1 , r2 , . . . , rn , rs , {πi }i∈[s] , {π(i,j,k) }(i,j,k)∈C ).
                     
                                         ri
                     0 ci = h
                     
         2. Let ti ← 1 ci = g · hri for each i ∈ [n] ∪ {s}.
                        ⊥ otherwise
                     
                     

         3. If ⊥ ∈ {t1 , t2 , . . . , tn , ts }, or t1 ||t2 || . . . ||tn ̸= x, or ts = 0, output 0.
                                                                                                        
                                                                      (1)   (2)          (1)            (3)
         4. For each i ∈ [s], if e(ci , ci · g −1 ) ̸= e πi , πi                  or e πi , g ̸= e πi , h , output 0.
                                                                                                                         
                                                                                   (1)     (2)           (1)          (3)
         5. For each (i, j, k) ∈ C, e(c(i,j,k) , c(i,j,k) ·g −1 ) ̸= e π(i,j,k) , π(i,j,k) or e π(i,j,k) , g ̸= e π(i,j,k) , h ,
            output 0.
         6. Otherwise, as no verification relations have failed, output 1.

                                                                   51


<!-- pdf-page: 55 -->
Batch arguments (BARGs). Finally, we introduce the concept of batch arguments (BARGs). In this
setting, we have T many statements x1 , x2 , . . . , xT , and the goal is to prove that there exists witnesses
w1 , w2 , . . . , wT such that C(xi , wi ) = 1 ∀ i ∈ [T ]. The interesting quality that we ask for is “succintness”,
that |π| is independent on the value of T . In the next lecture, we will show how to achieve |π| = poly(λ, |C|).




                                                        52


<!-- pdf-page: 56 -->
  CS 395T: Topics in Cryptography                                                           February 27, 2024

                                    Lecture 13: Batch Arguments
  Lecturer: David Wu                                                                      Scribe: Alex Huang

Up until this point in the course, we have focused on using cryptography to achieve privacy. For the next
few lectures, we will instead focus on using cryptography to achieve efficiency/succinctness.

Motivation: Verifiable Computation In the case where a the computation of program P on some
value x would be computationally expensive, we would like to ask a more powerful server to perform the
computation. We can model this as a client with the program and value as parameters C(P, x). However,
we want to verify that the server’s computation is legitimate so we can trust the output of the server.
Therefore, the verifiable computation procedure can be described as:

   1. Client sends (P, x) to the server.

   2. Server responds with (y = P (x), π), where π is a proof that the computation is correct.

Verifying the proof A trivial way to verify the computation would be to compute P (x) locally. However,
this defeats the purpose of using the server for the computation. Therefore, we would like to enforce the
property that verifying the proof π is a much easier computation than computing P (x).

Requirements We will have three requirements for our computation verification system:

   1. Efficiency/Succinctness: Checking the proof must be much easier than computing P (x). Formally,
      we require that TVerify = poly(λ, log TP ), where TP is the running time of program P .

   2. Completeness: If y = P (x), then the verifier should accept the proof π on value y with respect to
      (P, x).

   3. Soundness: If y ̸= P (x), then the verifier should reject the proof π with probability 1 − negl.

    It turns out that verifiable computation requires an intermediate notion to first be achieved, so we will
delay describing the full construction until the next lecture. In fact, verifiable computation was not realized
until 2021, but it makes use of previous primitives, one of which is the concept of a batch argument.

Batch Arguments for NP (BARG) BARG is an aggregation system for proofs, analogous to how BLS
signatures aggregate signatures or BGW broadcast encryption aggregates ciphertexts. The setting for a
BARG is a collection of T statements in an NP language x1 , . . . , xT , and a circuit C. We would like to
prove that for all i ∈ [T ], there exists a witness wi such that C(xi , wi ) = 1. This can be accomplished
trivially by sending (w1 , w2 , . . . , wT ), just like in a NIZK, but it renders the construction useless. Unlike
in the zero-knowledge construction, the requirement for a BARG is succinctness.




                                                       53


<!-- pdf-page: 57 -->
Succintness for a BARG The proof π for a BARG is succinct if |π| = poly(λ, C). This notion of suc-
cinctness is hiding and actually implies NIZK. Informally, this is because since the proof has fewer than
T bits, it is necessarily a compression which loses information and therefore cannot contain knowledge
of the witnesses. This implication is a relatively recent discovery.

Remark 13.1. It is also possible to achieve |π| = poly(λ), where the proof is independent of the circuit
size. However, this construction is much harder to achieve and beyond the scope of this lecture, requiring
more advanced cryptographic tools.

Construction 13.2 (Waters-Wu BARG [WW22]). The construction of our BARG system will be based
off the same principles as the GOS proof system from the previous lecture. Namely, we will employ a
commit-and-prove system. Unlike GOS, though, we will need the committment scheme to be compressing.
Since the GOS commitment depends on T , we cannot use it, as it will scale with the size.

Ingredients for the BARG construction

   1. A succinct way to commit: In our setting where we have T copies or instances of a circuit, we
      would like to compress our proof to be independent of T . For a circuit such as the following, we
                                   (1) (2)           (T )
      want to commit the vectors (xi , xi , . . . , xi ) for i ∈ [4].

                                            x1


                                            x2
                                            x3


                                            x4

      In the GOS construction, to aggregate proofs we committed to the value g xi hr . Here, we can use
      multiplication to instead commit to a vector. We define the common reference string crs to include
                                                                                r
      the generator g, as well as T random group elements h1 , h2 , . . . , hT ←   G (where hi denotes g αi for
      some random αi ), instead of just one random group element inQ        the GOS construction. To commit
      to a vector v = (v1 , v2 , . . . , vT ), we define the commitment c = i∈[T ] hvi i , giving us a single group
      element whose size is independent of T .
                                                                                        (1)   (2)      (T )
   2. Committing across instances: For each wire j in the circuit C, we let (tj , tj , . . . , tj ) be the
                                                                          (i)
                                                                         t
      values across the T instances. Then, we can commit to cj ← i∈[T ] hij for all j.
                                                                Q

Together, these ingredients inform us of the structure of the common reference string and an individual
                                                                       (i)
                                                                      t
commitment, where crs = (g, h1 , h2 , . . . , hT ) and a cj = i∈[T ] hij for all j ∈ [S].
                                                             Q


Internal consistency properties Similarly to the GOS construction, we want to be able to show the
following two properties for parts of the circuit:



                                                       54


<!-- pdf-page: 58 -->
                                                               (i)
1. Completeness: For all i ∈ [T ] and j ∈ [S], tj ∈ {0, 1}.
   Suppose c = i∈[T ] hvi i ; then, we want to show that vi ∈ {0, 1} for all i ∈ [T ]. As before in the GOS
                Q

   construction, we can use the property that vi ∈ {0, 1} ↔ vi · (vi − 1) = 0 ↔ vi2 = vi . Then we have
                                           Y v Y v
                              e(c, c) = e(    hi i ,  hi i )
                                                i∈[T ]         i∈[T ]
                                                 P                        P
                                          = e(g     i∈[T ] αi vi     ,g        i∈[T ] αi vi   )
                                                         ( i∈[T ] αi vi )2
                                                          P
                                          = e(g, g)
                                                                         2 2
                                                          P                        P              P
                                   = e(g, g)( i∈[T ] αi vi )+( i∈[T ] j̸=i αi αj vi vj )
   If we have that vi2 = vi , then i∈[T ] αi2 vi2 = i∈[T ] αi2 vi . We can compute this in the exponent
                                  P                P
   using pairings based on the following derivation:
                                Y             P               P
                         e(c,      hi ) = e(g i∈[T ] αi vi , g i∈[T ] αi )
                                 i∈[T ]
                                                                   P                  P
                                              = e(g, g)(               i∈[T ] αi vi )(     i∈[T ] αi )

                                                                               2
                                                                   P                       P            P
                                              = e(g, g)(               i∈[T ] αi vi )+(        i∈[T ]       j̸=i αi αj vi )


  Taking these two facts together, we can now produce the verification relation
                                ?
                                                         P      P
                                           hi ) · e(g, g) i∈[T ] j̸=i αi αj (vi vj −vi )
                                       Y
                        e(c, c) = e(c,
                                                i∈[T ]

   The first two pairings can be computed by the verifier, but the last pairing requires knowledge
   of certain exponents which we do not know a priori. Therefore, we can     Padd P the group elements
   uij = g αi αj for all i ̸= j to the common reference string. Then, e(g, g) i∈[T ] j̸=i αi αj (vi vj −vi ) =
                        v v −v
   e(g, i∈[T ] j̸=i uiji j i ), which is now a pairing computable by the verifier with the additional
        Q       Q
   common reference string elements.
2. Gate consistency: All NAND gates should be correctly computed.
  Take any three wires v1,i , v2,i , v3,i . For this check, if we assume we passed the first check, then
                                                                                    ?
  vj,i ∈ {0, 1} for j ∈ {1, 2, 3}. Therefore, an equivalent formulation for v3,i = v1,i ˜ ∧v2,i is to check
  that v1,i + v2,i − 2v3,i + 2 ∈ {0, 1}. To do this, note that we have access to the commitments c1 =
             v1 ,i              v2 ,i                     v3 ,i
     i∈[T ] hi , c2 =   i∈[T ] hi , and c3 =      i∈[T ] hi . By simply multiplying these together, we get
  Q                   Q                         Q

                                                Y
                         c∗ = c1 · c2 · c−23  ·     h2i
                                                     i∈[T ]
                                            v                        v                        −2v1,i
                                   Y                      Y                        Y                            Y
                             =(            hi 1,i ) · (            hi 2,i ) · (            hi           )·(             h2i )
                                  i∈[T ]                  i∈[T ]                  i∈[T ]                       i∈[T ]
                                           v +v −2v +2
                                  Y
                             =            hi 1,i 2,i 3,i
                                 i∈[T ]

  This allows us to verify the relation in the exponent. Note that this derivation also implies that c∗
  is a commitment to v1,i + v2,i − 2v3,i + 2 for all i ∈ [T ]. We can now check that this value is 0 or
  1 using the technique described above.

                                                                   55


<!-- pdf-page: 59 -->
Soundness How do we argue soundness? For this proof, we only know how to achieve a weaker no-
tion of soundness, non-adaptive soundness, which is analogous to selective security. For non-adaptive
security, the adversary commits to a false statement (x1 , . . . , xT ) before seeing the common reference
string. Our approach for this proof will be to program a secret index i∗ ∈ [T ] into the common reference
string. Then, when given a valid proof for (x1 , . . . , xT ), we can extract a witness wi∗ for the xi∗ such that
C(xi∗ , wi∗ ) = 1, which suffices for non-adaptive soundness as long as i∗ is hidden from the adversary,
since it implies that the adversary’s behavior will not change based on the choiec of i∗ . This property of
being statistically sound on one instance is called somewhere-soundness.

Remark 13.3. It is actually possible to use this to also prove adaptive soundness through a technique
known as complexity leveraging, when complexity leveraging for index hiding.

Programming the CRS The normal CRS for this construction has (g, hi = g αi , uij = g αi αj ) for all
i ∈ [T ] and j ̸= i. For the proof, we want to view all of these group elements as elements in a composite-
                                       αα
order group (g, hi = gpαi , uij = gp i j ) for all i ∈ [T ] and j ̸= i. To bind the CRS, we replace hi∗ with
                     α                  α∗
g αi∗ , ui∗ j with hi∗j and uiu∗ with hi i , essentially ”lifting” the index of interest to the full group. Using
the subgroup decision problem, we can argue that this binding CRS is indistinguishable from the nor-
mal CRS.
       Q Now,       we can extract from every commitment. When we bind the CRS,       Q a commitment       is now
                 vi     vi∗ Q       vi               vi∗                                      vi
c = i∈[T ] hi = hi∗ · i̸=i∗ hi . Note that hi∗ is in the full group, whole i̸=i∗ hi is in the order p
                                                v∗
subgroup. Then, the pairing e(c, gq ) = e(hi∗i , gq ) holds, so we can solve discrete log to retrieve vi∗ .

Remark 13.4. The construction only ever uses elements from the order p subgroup. However, even though
its existence is never used, we require the order q subgroup to exist for the security proof.

The full construction [WW22]
                                 r
    • To generate crs: Sample αi ←   Zp for all i ∈ [T ]. Set crs ← (g, {hi }i∈[T ] , {uij }i̸=j ), where hi = g αi
      and uij = g αi αj .

    • To commit to a vector v = (v1 , . . . , vT ): Output c ← i∈[T ] hvi i .
                                                               Q

                                                                   vi vj −ui
    • To prove vi ∈ {0, 1}: Output π ←                                       .
                                            Q            Q
                                                i∈[T ]       j̸=i uij

                                                  ?                                                          vi vj −vi
    • To check a proof π, verify that e(c, c) = e(c,
                                                             Q                        Q            Q
                                                                 i∈[T ] hi ) · e(g,       i∈[T ]       j̸=i uij        ).




                                                              56


<!-- pdf-page: 60 -->
  CS 395T: Topics in Cryptography                                                        February 29, 2024

                                     Lecture 14: RAM Delegation
  Lecturer: David Wu                                                                   Scribe: Nate Mikosh

So far, we have focused on proving properties in a privacy-preserving manner. Next, we will look at
achieving short proofs that are efficient to verify.

Verifiable Computation In verifiable computation, the client provides a program P , and input x to
some server. The server responds with a proof y = P (x). The client needs to be able to check that this
proof is correct, but checking this correctness should be much faster than if the client were to compute
P (x) itself. This process of using a server to run a program that the client can check for correctness is
called delegation, or a succinct non-interactive argument (SNARG).
     Our goal is to check that y = P (x) was evaluated correctly. A reasonable approach is to break the
program P up into individual instructions and use a batch argument to check that each instruction was
executed properly. Before we can do this though, we should define P ’s structure. We will assume that P
is a RAM program.

RAM Programs         A RAM (random access machine) program is defined as follows:

    • The program has access to some vary large M bits of memory and a small number of bits of local
      state st

    • Memory is initialized as the input to the program x, with all other bits as 0s

    • The program consists of a sequence of only reads and write, defined as follows:

         – Read a single bit of memory and update state
         – Write a single bit of memory and update state

    • The program outputs the contents of memory at the end of computation

    Now that P ’s structure is clear, we can break it up in order to use a batch argument. A simple way
to do this is to separate the program into sequence of state and memory values. (st0 , M0 ) represent the
initial values of state and memory, (st1 , M1 ) are the values after one instruction has been executed, and
(stT , MT ) are the final values where T is the length of the program. To check that each instruction in the
program was executed properly, we can check that each consecutive pair of state and memory makes sense.
We can now construct our batch argument as follows:

    • IsValid: on inputs ((sti , Mi ), (sti+1 , Mi+1 )), output 1 if the transition is valid according to some
      criteria
      The exact criteria will vary, but for example:

         – For a read, checking that memory is unchanged
         – For a write, checking that at most one bit of memory was changed

    • Statements: ((st0 , M0 ), (st1 , M1 )), ...((stT −1 , MT −1 ), (stT , MT ))

                                                         57


<!-- pdf-page: 61 -->
    • Proof: BARG proof that IsValid holds for all statements

     While this initially seems like an effective argument, there is no succinctness here. The goal of a SNARG
is to verify correctness of a program much faster than actually running it, and this argument fails to achieve
that. This issue can partially be solved by compressing our statements. While hashing would normally
obscure the information we need for our argument, we will introduce a new method of hashing, Merkle
hashing, to solve this problem.

Merkle Hashing Merkle hashing is a hashing technique that hashes several values in such a way that an
”opening” can be used to reveal the value of an input without revealing any other inputs. To demonstrate
this let’s look at a Merkle hash on the inputs (x1 , x2 , x3 , x4 ) where H(x) is some collision-resistant hash
function.
The inputs to a Merkle hash can be thought of as leaves of a binary tree, as we step through the hash, the
tree will be built.
                                                x1 , x2 , x3 , x4


Each step of the Merkle hash generates another layer of the tree. A new ”node” is generated for every pair
of inputs.
                                  h12 = H(x1 ||x2 ), h34 = H(x3 ||x4 )


This process continues until we arrive at one final hash.

                                             h14 = H(h12 ||h34 )


The final value of the hash, in this case h14 , is referred to as the root of the Merkle hash.
The utility of a Merkle hash is that we can we can create short local openings to prove the value of an
input y = xi with respect to the root h. Once again think of the Merkle hash as a tree. By providing the
necessary nodes, we re-create the root and verify that y = xi . Using the same example as before, let’s
say we want to verify the value of x1 . The opening to x1 would be the values of x2 and h34 . We can then
compute h12 and h14 ourselves and check that it matches the given root h. The size of these openings will
only be λlog(n) + l where λ is the length of the hash function output and l is the length of each input.

Improved BARG With this new hash function, we can construct a more succinct BARG. We can Merkle
hash on ((st0 , M0 ), ..., (stT , MT )) to create a hash of all our statements ”hstate”. With hstate, we can
construct a more succinct BARG as follows:

    • IsValid: on i ∈ [T ]

         – Witnesses: Merkle openings with repsect to hstate in order to get (sti , Mi ), (sti+1 , Mi+1 )
         – Checks that transition is valid according to criteria like in our previous version

    • Statements: i ∈ [T ]

    • Proof: BARG proof that IsValid holds for all statements

    The runtime of this argument is as follows:

                                                      58


<!-- pdf-page: 62 -->
    • |πBARG| = poly(λ, log(T ), |IsV alid|)

    • |IsV alid| = poly(λ, log(T ), M )

    While this argument is slightly improved, the runtime of IsValid is based on the size of the program’s
memory. Memory for RAM programs is significantly large, therefore this argument still lacks succinctness.
The solution is to use yet another Merkle hash, this time on each value of memory. Every state (sti , Mi ),
can be translated into (sti , hi ) by Merkle hashing Mi . We then hash every (sti , hi ) pairing into hstate like
we did in the previous version.
    After this change, our final BARG proof is complete:

    • IsValid: on i ∈ [T ]

         – Witnesses: Merkle openings with respect to hstate in order to open (sti , hi ), (sti+1 , hi+1 )
         – To check a read, we check the Merkle opening with respect to hi for bit j to check that it is
           correctly computed
         – For a write, we similarly check bit j, but then we can use this same opening to reconstruct hi+1
           and check that it is also valid

    • Statements: i ∈ [T ]

    • Proof: BARG proof that IsValid holds for all statements

    This BARG is much faster. Opening each (sti , hi ) with respect to hstate is O(λlog(T )), opening a bit
with respect to some hi is O(λlog(M )). Therefore, |IsV alid| = poly(λlog(T ) + λlog(M )) and |πBARG|
remains unchanged at poly(λ, log(T ), |IsV alid|).

Security Merkle hashing on each memory state is acceptable, but a Merkle hash on all the states to
generate hstate is actually not strong enough to guarantee security. For full security, we would need a
somewhere extractable hash function which works similarly to a Merkle hash, but is stronger.

Extensions There are a couple interesting extensions of being able to produce SNARG for P , we’ll look
at two of them

    • Homomorphic signature
      Given a signature on a message m, we can derive a signature on f (m) for an arbitrary f . We sign
      m, the hash h(m). The signature on f (m) is the hash, the signature on the hash, the value y = h(m)
      and a proof that that y = h(m) with respect to h(m).

    • Functional Commitments
      With functional commitments, we can prove that a single function f is being used rather than using
      different functions for different values. We commit to an input x and then open to f (x).




                                                       59


<!-- pdf-page: 63 -->
  CS 395T: Topics in Cryptography                                                            March 5, 2024

                            Lecture 15: Polynomial Commitments
  Lecturer: David Wu                                                                     Scribe: Noel Elias

Previously, we showed how to construct verifiable computation/delegation - suitable for when the client
knows the program P and input x. The client wants to learn P(x) and verify that this value was computed
correctly in less time than it takes to compute P(x). This construction is a succinct non-interactive argument
(SNARG) for a deterministic polynomial-time computation (SNARG for P).
    In many cases however, the full input might not be known to the verifier. For example, suppose a server
publishes a hash of some database. The client performs a query and wants a proof that the query was
performed correctly relative to the hash of the database. Note the key difference in this setting is that the
client does not know the entirety of the database, it only knows the hash. The trivial construction has no
notion of soundness which binds the server’s response to a database D.
    So for this setting we need a SNARG for NP. Namely, we consider the following NP relation:

    • Statement: Takes hash h of the database contents as well as y, the output of the query

    • Witness: database (D)

    • Relation: Checks that h=Hash(D) and y is output of query algorithm on D. Outputs 1 if all these
      properties hold.

    • In particular, we want a proof size |π| = poly(λ).

    In this lecture, we will construct a SNARG for NP where the size of the proof is a constant number of
group elements, regardless of the complexity of the NP relation. As a result, this construction will rely more
assumptions including the random oracle (RO) as well generic group model. Recall, SNARGs rely on two
components: a functional commitment scheme + informational-theoretic component. In this construction
we will use a polynomial commitment scheme and a polynomial IOP.

Polynomial Commitment Scheme We will work specifically over Fp (integers modulo p). A polynomial
commitment scheme over Fp consists of four algorithms:

    • Setup (d): Takes the (max) degree of the polynomial and outputs a common reference string (crs)

    • Commit(crs, f ) → c: Commits to the polynomial f of degree at most d.

    • Eval(crs, c, f, x) → π: Computes an opening π to the evaluation y = f(x).

    • Verify(crs, c, x, y, π) → 0/1: : Checks whether opening is valid or not.

We can show some properties of a polynomial commitment scheme as follows:

    • Succinctness: The size of both |c| and |π| are O(1) group elements, regardless of the degree of f.

    • Correctness: Let f(X)=f0 + f1 X + ... + fd X d be a polynomial and x ∈ Fp be a point. If crs ←Setup(d),
      c ←Commit(crs, f ), π ←Eval(crs, c, x), then Verify(crs, c, x, f (x), π)=1.



                                                     60


<!-- pdf-page: 64 -->
    • Binding: Given crs, difficult to come up with commitment c, a point x, and value/opening pairs
      (y0 , π0 ), (y1 , π1 ) where if y0 ̸= y1 and Verify(crs, c, x, y0 , π0 )=1=Verify(crs, c, x, y1 , π1 ). Note that
      this definition allows us to open to 2d points where no degree d polynomial goes through all these
      points. So for applications, we often need a stronger knowledge soundness property =. This property
      states that if an efficient A can open a commitment c at k points, there exists an efficient extractor that
      outputs a polynomial f of degree at most d such that f (xi ) = yi (as we focus more on succinctness
      knowledge soundness will not be too important for understanding the construction).

   Using this general framework for polynomial commitment scheme, we can define the Kate-Zaverucha-
Goldberg (KZG) polynomial commitment scheme construction.

Construction 15.1. (Kate-Zaverucha-Goldberg (KZG) Polynomial Commitment Scheme [KZG10]):
                          r
    • Setup (d): Sample α ← Fp where p is the order of the group and the scheme supports polynomials
                                           2         d
      over Fp . Output crs = (g, g α , g α , ..., g α )

    • Commit(crs, f ): Commitment is the element g f (α)

         – Suppose f(X)=f0 + f1 X + ... + fd X d
                                                          i
         – Let crs = (g0 , g1 , ..., gd ) where gi = g α .
                                                           i   i
         – The commitment c= di=0 gifi = di=0 g fi α = g fi α = g f (α)
                                    Q            Q           P



    • Eval(crs, c, f, x∗): Let y=f(x). The goal is to construct a proof π that y=f(x*) where f is the polynomial
      associated with c.

         – Define the polynomial fˆ(X) = f (X) − y. Observe that f(x*)=y if and only if fˆ(x*)=0, or equiv-
           alently, if x* is a root of f. This means there exists a polynomial q(X) such that fˆ(X)=(X-x*)q(X).
                                                                           Pd−1
         – The opening will be a commitment to the polynomial q(X)= i=0           qi X i
                                               d−1            d−1
                                                                        i            qi αi
                                                                                 P
                                                     giqi =
                                               Y              Y
                                          π=                        g qi α = g               = g q(α)
                                               i=0            i=0


    • Verify(crs, c, x∗, y, π): Verifier will essentially check that the polynomials fˆ and (X-x*)q(X) are equal
      at X=α.

         – Recall that if these polynomials are equal at the random point α, they are equal. Suppose f is
           a polynomial of degree at most d and is not identically 0. Then, P rx←
                                                                                r
                                                                                  F
                                                                                    [f (x) = 0] ≤ d/p.
                                                                                                        p

         – Normally, we have that c = g f (α) and π = g q(α) .
                                                                                 ˆ
         – From c=g f (α) , verifier computes c · g −y = g f (α)−y = g f (α) .
         – From π = g q(α) , verifier computes e(g1 g −x∗ , π) = e(g α−x∗ , g q(α) ) = e(g, g)(α−x∗)q(α)
         – Verification relation thus checks if e(g, c · g −y ) = e(g1 g −x∗ , π). =

   In general, it is true that if two polynomials f,g of degree at most d such that f(x)=g(x) at a random
        r
point x ← Fg , then with probability 1 − d/p we can say that f=g. This generalizes to the Schwartz–Zippel
lemma for multi-variate polynomials.

                                                              61


<!-- pdf-page: 65 -->
KZG Binding We can show the binding property of the KZG scheme by relying on the d-strong Diffie-
                                          2      d                                         1
Hellman assumption (given g, g α , g α , ..., g α ), it is hard to come up with (c, g α+c ) for any c ̸= −α.
    Now suppose an adversary produces a commitment c = g S and opens c to two different values y1 and
y2 at x* with proof π1 = g t1 and π2 = g t2 (note that the reduction does not know s, t1 , t2 ). Then by the
verification relation; e(g, c · g −y1 ) = e(g α−x∗ , π1 ) and e(g, c · g −y2 ) = e(g α−x∗ , π2 ). In the exponent, this
means that s − y1 = t1 (α − x∗) and s − y2 = t2 (α − x∗). This allows for the following:

                                       t1 (α − x∗) + y1 − y2 = t2 (α − x∗)
                                            (t1 − t2 )(α − x∗) = y2 − y1
                                                       t1 − t2      1
                                                               =
                                                       y2 − y1   α − x∗
          1        t1 −t2               1
Thus, g α−x∗ = g y2 −y1 = (π1 /π2 ) y2 −y1 . Note y1 ̸= y2 since the adversary needs to open c two different
ways. If the adversary outputs x*=α, then the reduction trivially breaks the assumption. We will develop
protocols to prove additional properties on committed polynomials. To motivate this, we first sketch the
ideas underlying the PLONK scheme.

Arithmetic Circuits For the PLONK construction, the computational model will be arithmetic circuits.
Gates will be addition or multiplication and wires will be labeled by a field element. This can be used
for boolean circuits where we can implement AND and OR gates using multiplication and addition. An
illustration is shown in Figure 15.1:

                                                           3
                                                          MULT
                                               1                      2
                                              ADD                    ADD

                                             x1 , x2                 x2 , x3

                                                       Figure 15.1

    For any choice of input (x, x2 , x3 ), we can define an execution trace. Every gate has a left input and
a right input. Suppose x1 = 1, x2 = 2, x3 = 3. Then the trace can be shown in Table 15.1:

                                    Gate     Left Input    Right Input         Output
                                     1            1             2                 3
                                     2            2             3                 5
                                     3            3             5                15

                                                       Table 15.1


PLONK The idea is for the PLONK system [GWC19] is that the prover will choose a polynomial that
interpolates the entire execution trace.



                                                           62


<!-- pdf-page: 66 -->
    More specifically, suppose we take a point w ∈ Fp . Let m be a bound on the number of gates in the
circuit and let n be the number of public inputs (i.e., the statement) that is known to the verifier. We require
ord(w)>3m+n. Namely, the following elements are all distinct in Fp : w−n , w−n+1 , ..., w0 , w1 , ..., w3m .
The prover will interpolate the trace polynomial T where:

    • T (w−i ) = value of ith public input

    • T (w3j ) = value of left input to the jth gate

    • T (w3j+1 ) = value of right input to the jth gate

    • T (w3j+2 ) = value of output of jth gate

    The polynomial T encodes the entire execution of C. The prover commits to C using a polynomial
commitment scheme. The commitment is a single group element. Now the prover needs to show the
following four checks to convince the verifier that the commitment of C is a valid trace for the computation:

   1. Input Consistency: T (w−i ) = value of ith public input

   2. Gate Consistency: Every gate is correctly implemented

   3. Wire Consistency: If output of gate j is left input of gate k, then T (w3j+2 ) = T (w3k )

   4. Output Consistency: Output gate has the correct value.

    In the next lecture we will dive into the details of implementing these checks for the PLONK construc-
tion.




                                                       63


<!-- pdf-page: 67 -->
  CS 395T: Topics in Cryptography                                                               March 7, 2024

              Lecture 16: Succinct Non-Interactive Arguments (SNARGs)
  Lecturer: David Wu                                                                        Scribe: Noel Elias

Recall in the previous lecture we described the KZG polynomial commitment scheme and gave an overview
of the PLONK construction. In this lecture we will discuss the details of the PLONK construction [GWC19].
     To review, we will examine the arithmetic circuit defined in the previous lecture in Figure 15.1. Our goal
is to interpolate a polynomial that defines the execution trace of this arithmetic circuit as shown in Table 15.1.
     To do this, we associate a field element with each value in the execution trace. Moreover, remember
that n=length of statement while m=number of gates. The trace polynomial has the structure w ∈ Fp where
ord(w)>3m+n. In addition, the following elements are all distinct in Fp : w−n , w−n+1 , ..., w0 , w1 , ..., w3m .
The prover will interpolate the trace polynomial T where:

    • T (w−i ) = value of ith public input

    • T (w3j ) = value of left input to the jth gate

    • T (w3j+1 ) = value of right input to the jth gate

    • T (w3j+2 ) = value of output of jth gate

    To illustrate this polynomial structure we can label the execution trace with their equivalent polynomial
as shown in Table 16.1:

                                Gate    Left Input      Right Input     Output
                                 1      1 (T (w0 ))     2 (T (w1 ))   2 (T (w2 ))
                                 2      2 (T (w3 ))     3 (T (w4 ))   5 (T (w5 ))
                                 3      3 (T (w6 ))     5 (T (w7 ))   15 (T (w8 ))

                                                      Table 16.1

    Lastly, the prover must show that the commitment of this polynomial T satisfies the following checks
to convince the verifier that this commitment of C is a valid trace for the computation. Ideally we want
to do this with a constant number of group elements:

   1. Input Consistency: T (w−i ) = value of ith public input

   2. Gate Consistency: Every gate is correctly implemented

   3. Wire Consistency: If output of gate j is left input of gate k, then T (w3j+2 ) = T (w3k )

   4. Output Consistency: Output gate has the correct value.

Output Consistency We can begin by showing how we check for output consistency in PLONK. Proving
that the output gate has the correct value is just opening the polynomial commitment at w3|c|−1 .



                                                         64


<!-- pdf-page: 68 -->
Zero-Testing Gadget To prove consistency for the other three checks we will utilize a zero-testing
gadget which shows that a polynomial f(X) is zero on a set SQgiven only a polynomial commitment to f.
     First, define the vanishing polynomial for S:ZS (X) = i∈S (X − i). Then f is zero on S if and only
if there exists a polynomial q(X) such that f (X) = ZS (X) · q(X). The prover has the polynomial f and can
derive q(X) by dividing f (X)/ZS (X) (verifier knows ZS (X)). Suppose the verifier only has a commitment
to f. To prove that f is zero on S, we can use the following protocol:

   1. Prover commits to the polynomial q of degree at most d-—S— where f(X)=ZS (X) · q(X).
                                  r
   2. Verifier samples a random r ← Fp

   3. Prover opens commitments to f and q at r

   4. Verifier checks that f(r) = ZS (r)q(r)

   To see why this is sound suppose f(X) is not zero on S. Then, there does not exist a polynomial
g(X) such that f(X) = ZS (X) · g(X). Consider the polynomial h(X) = f (X) − ZS (X) · q(X). This is
a polynomial of degree at most d and is not the zero polynomial. Thus, it has at most d roots. Then,
                                                            f
P rr←Fp [h(r) = 0] = d/p = negl. Note that h(r) = 0 ←         → (r) = ZS (r)q(r). In other words, if f is not zero
on all points S, then h(x) is a non-zero polynomial as well.
     Also note that this proof consists of 3 group elements and 3 field elements. As long as the degree of the
protocol is small relative to the size of the field, this protocol will be sound. This can be made non-interactive
using the Fiat-Shamir Heuristic which hashes the inputs (commitments to f and q) to get the randomness
r. So using the random oracle model we can make the proof non-interactive as well as only consist of three
group elements: commitment to g, openings for f and q.

Input Consistency Now we can go back to the PLONK scheme where the prover has committed to a
trace polynomial T. We can now analyze the input consistency.

    • Suppose the public input is x=(x1 , ..., xn ). Then, the prover should show that T (w−i ) = x for all
      i ∈ [n].

    • To do so, prover (and verifier) interpolate polynomial v(X) where v(w−i ) = xi .

    • Then, the polynomial T(X)-v(X) is zero on the set S=w−1 , ..., w−n . The prover and the verifier now
      run the zero-testing protocol described above.

    • Note that in the zero-testing protocol, the prover needs to reveal T(r)=v(r). It does so by revealing
      T(r) and the verifer can then compute T(r)-v(r) itself.

    • Thus, we can prove input consistency with a constant number of group elements.

Gate Consistency . For gate consistency we can define the following procedure:

    • Define a selector polynomial v(X) where v(w3j )=1 if the gate j is an addition gate and v(w3j )=0 if
      the gate j is a multiplication gate.

    • Suppose all the gates are implemented correctly. Then if gate j is an addition gate, T (w3j+2 ) =
      T (w3j ) + T (w3j+1 ). If gate j is a multiplication gate T (w3j+2 ) = T (w3j ) · T (w3j+1 ).


                                                       65


<!-- pdf-page: 69 -->
    • Combining both of these gates into one equation we get T (w3j+2 ) = [T (w3j ) + T (w3j+1 )] · v(w3j ) +
      [T (w3j ) · T (w3j+1 )] · (1 − v(w3j )).

    • So if gate constraints are satisfied, then for all X ∈ [w0 , w3 , ..., w3|c|−3 ], T (w2 X) = v(S)[T(X)+T((wX)]+(1-
      v(S))[T(X)*T(wX)]).

    • This reduces to the zero-test protocol on the set [w0 , w3 , ..., w3|c|−3 ].

    • Note the implement this protocol, the verifier needs to evaluate polynomial T (w2 X) = v(S)[T(X)+T((wX)]+(1-
      v(S))[T(X)*T(wX)]) at a random point r.

    • In particular this can be implement using KZG by having the prover open T(r), T(wr), and T(w2 r)
      where the verifier can compute T(r) itself.

    • Thus, gate consistency can be proven with a constant number of group/field elements as well.

Wire Consistency Recall the arithmetic circuit shown in Figure 15.1. We can rewrite the table trace
with inputs 1(w−1 ), 2(w−2 ), 3(w−3 ) as shown in Table 16.2. We will show wire consistency as an example
rather than a generic protocol:

                                  Gate    Left Input    Right Input     Output
                                   1       1 (w0 )        2 (w1 )        2 (w2 )
                                   2       2 (w3 )        3 (w4 )        5 (w5 )
                                   3       3 (w6 )        5 (w7 )       15 (w8 )

                                                    Table 16.2

    In this example we require that T (w−1 ) = T (w0 ), T (w−2 ) = T (w1 ) = T (w3 ), T (w−3 ) = T (w4 ),
T (w2 ) = T (w6 ), and T (w5 ) = T (w7 ). Whenever a wire value is used multiple times, we introduce a
constraint. Every wire value participates in at most one constraint group. We can view this replication
pattern as inducing a permutation P on the set [w−3 , w−2 , .., w8 ]. For each input, wi , P (wi ) sends it to is
where j is the index of the next copy of the wire associated with index i. P can be described by a polynomial
of degree 3m+n (just like T). Checking equality of the wire constraints then boils down to checking T(X) =
T(P(X)) for all X ∈ [w−3 , w−2 , .., w8 ]. The polynomial P is known to the verifier so this can again be done
using the zero-testing protocol.
    However note that the this proof requires a quadratic sized circuit as well as a quadratic sized crs. To
solve this in practice, we work with a bi-variate polynomial.

Summary To summarize to prove that C(x,w)=1, the prover commits to the execution trace T(X) of C
and then proves the following checks: input consistency, gate consistency, wire consistency, and output
consistency. Each proof requires revealing a constant number of group elements (i.e., commitments and
openings to the polynomial commitment scheme). Soundness requires the random oracle (to make the
interactive protocol non-interactive) and the algebraic group model (or generic group model) to argue
soundness of the KZG scheme. Additionally, the crs of PLONK does not depend on the circuit and is thus
known as having a universal setup. Properties like zero-knowledge can be easily added to the PLONK
construction by making the KZG polynomial commitments implement hiding.



                                                        66


<!-- pdf-page: 70 -->
    There are many extensions to the PLONK protocol. First, one can modify the base protocol so the prover
complexity is quasi-linear in |C| rather than quadratic. Second, one can consider working with multi-linear
polynomials over the vector space F2 to support linear-time provers (HyperPlonk [CBBZ22]). Lastly, one
can support more general gates by extending gate consistency checks with tools like look-up arguments.




                                                    67


<!-- pdf-page: 71 -->
  CS 395T: Topics in Cryptography                                                          March 19, 2024

                                Lecture 17: Introduction to Lattices
  Lecturer: David Wu                                                                  Scribe: Zeki Gurbuz

Pairings Recap. Until now, we studied pairing-based cryptography, which gave us algebraic properties
that led to numerous useful constructions such as the following:

    • Short (BLS) Signatures,

    • Identity-based Encryption (IBE),

    • Broadcast Encryption,

    • Attribute-based Encryption,

    • Somewhat-homomorphic Encryption,

    • Non-interactive Zero-knowledge (NIZK),

    • and Succinct Non-interactive Arguments (SNARG),

    many of which we did not know how to realize without pairings. At this point in the course, we’ll pivot
to lattice-based cryptography.

Lattices. There are many differences and trade-offs between lattice-based and pairing-based cryptography,
and yet there are many subtle similarities as well. We’ll see that lattices allow us to construct many of the
same notions:

    • IBE,

    • ABE for circuits (hence arbitrary policies),

    • Fully-homomorphic Encryption (FHE),

    • NIZK,

    • SNARG (which is a recent development),

    • and more.

     On the other hand, it is quite challenging to build, for example, broadcast encryption from standard
lattice-based cryptographic assumptions! Only recent developments from new lattice-based assumptions
have yielded broadcast encryption constructions. We also don’t know how to build short signatures from
lattices (it may not even be a well-defined notion), and these are major open topics of research.
     Lattices have different algebraic properties/structure than pairings. A lot of pairing-based proofs re-
quired group-theoretic arguments, whereas lattices will revolve more around linear algebra. Moreover, our
lattice calculations will generally be more in-the-weeds, requiring more notation, whereas pairing-based con-
structions did not have to manipulate e.g. elliptic curve operations, treating the pairing map as a black box.

                                                     68


<!-- pdf-page: 72 -->
Why Lattices? Lattices are conjectured to provide post-quantum security. We know of quantum al-
gorithms, such as Shor’s for integer factorization and Simon’s for discrete log, which would break many
discrete log-based (and hence pairing-based) “classical” schemes that are used in real-world applications. An
important property of cryptographic systems is “forward secrecy”. For example, if a large group or nation
records encrypted messages of users in the present, and some time in the future large-scale quantum com-
puters come online, those encrypted messages may become compromised. As such, so-called post-quantum
cryptography revolving around lattice-based assumptions is relevant even to cryptographers today.
    As real-world evidence of this idea, the National Institute of Standards (NIST) has standardized post-
quantum key agreement protocols such as Kyber and Dilithium (among others) which are lattice-based.
There is also ongoing work to standardize post-quantum signature schemes. Additionally, Apple has begun
using Kyber alongside elliptic curve methods to secure iMessage messages. Cloudflare and Google also
use post-quantum key agreement alongside their classical algorithms.
    Another advantage of lattices is that their security is based on worst-case hardness. In contrast with
discrete log, which is an average-case assumption where an adversary sees a random instance, lattice
assumptions only rely on the existence of a single challenging instance for any particular adversarial
algorithm. This is conceptually related to basing cryptography purely on the hardness of NP problems.
For example, we could ask, if P ̸= NP, is it possible to construct cryptographic systems based on 3-SAT?
Unfortunately, we don’t know the answer to this, that is, we don’t know how to base cryptography purely
on the existence of hard problems, but lattices do seem to push us in the right direction.
    Finally, lattices have nice algebraic structure and properties that give us powerful functionality. The
crowning achievement to date of lattice-based cryptography is the realization of FHE, something which
was previously thought to be impossible.

Definition 17.1 (Lattices). An n-dimensional lattice L ⊂ Rn is a discrete additive subgroup of Rn .

    • Discrete: For each x ∈ L, there exists a neighborhood U ⊆ Rn about x such that U ∩ L = {x}.

    • Additive Subgroup: ∀ x, y ∈ L, x + y ∈ L and −x ∈ L.

    A neighborhood is typically thought of as a ball about a particular point, that is, all points which are
sufficiently “close” to a reference point, in terms of a norm (usually ℓp or ℓ∞ ).
    As an example, Z2 ⊂ R2 is a two-dimensional lattice. Z2 is clearly an additive subgroup of R2 , and
for each point (x, y) ∈ Z2 , we can consider a neighborhood of points whose distance from (x, y) (in terms
of ℓ∞ ) norm is at most 12 . Another example: Qn ⊂ Rn is not a lattice. Since Q is dense in R, Qn is not
discrete. Some other examples of lattices are Zn and (qZ)n for q ∈ N. The latter is called a q-ary lattice.
We typically stray away from using visual interpretations of lattices, since we can only usually visualize
one and two-dimensional lattices, but our visual intuition does not always carry over to higher dimensions.

Mathematical Properties. Lattices are typically infinite, but they can be finitely generated. We do so by
writing down a basis, with elements of the lattice being expressed as integer linear combinations of basis
elements. For a matrix representing a basis
                                                           
                                            | |           |
                                   B = b1 b2 . . . bk  ∈ Rn×k ,
                                            | |           |




                                                     69


<!-- pdf-page: 73 -->
we denote the lattice generated by the basis as
                                         ( k                              )
                                           X
                               L(B) :=          αi · bi | αi ∈ Z ∀ i ∈ [k] .
                                               i=1

We will also sometimes write B · Zk to mean L(B). It is important that the columns b1 , b2 , . . . , bk of B are
linearly independent
                    over
                         R , not just Z . Moreover, every lattice has a basis. For example, Z = L(I ),
                            n            n                                                           n        n

               1
              ..
where I = 
        n
                   . . A basis for a lattice generally is not unique, that is, lattices can have many bases.
                        

                      1
For example,                                         
                                        1    0              1    2
                                           ,      and          ,
                                        0    1              2    1
are two different bases for Z2 . So which basis should we use to represent a given lattice? It turns out that
this is a very important question, as the hardness of many lattice problems varies greatly based on the
choice of basis. Certain problems are much easier with a “good” basis than they are with a “bad” basis.
    “Good” bases are those whose basis
                                     qPvectors have small norm (l2 norm or l∞ norm). The l2 norm of a
                                          n
vector v ∈ Zn is defined as ∥v∥2 =        i=1 vi , whereas the l∞ norm of v is defined as ∥v∥∞ = maxi |vi |.
                                               2

In many cases, the public parameters for lattice-based schemes will include a “bad” basis, and the secret
key will be a “good” basis.

Definition 17.2 (Minimum Distance). Let L be an n-dimensional lattice. The minimum distance of L,
λ1 (L), is defined as
                                     λ1 (L) := min ∥v∥.
                                                       v∈L\{0}

Equivalently, the minimum distance is the norm of the shortest non-zero vector in L.

Computational Problems.

    • Shortest Vector Problem (SVP): Given a basis B for a lattice L, find v ∈ L such that ∥v∥ = λ1 (L).

    • Approximate SVP (SVPγ ): Given a basis B for a lattice L, find v ∈ L such that ∥v∥ ≤ γ · λ1 (L).

    • Decisional approximate SVP (GapSVPγ ): Given a basis B for a lattice L, decided if λ1 (L) ≤ 1 or
      if λ1 (L) ≥ γ (it is guaranteed that exactly one of these is true).

     SVP is NP-hard (intuitively it would be hard to even verify if a vector was truly the shortest), but not
known to be in NP (hence not NP-complete). For a reasonable value of γ, SVPγ is still not in NP. As such, we
defer to the third and easiest problem, GapSVPγ , which is in NP (the witness being a vector with appropriate
norm). When building cryptographic schemes using lattice assumptions, we actually do use average-case
assumptions, but we will see that these assumptions each reduce to the worst-case hardness of GapSVPγ .
     It seems intuitively true that GapSVPγ should get progressively easier as γ gets larger and larger, and
it turns out that this intuition is indeed correct. The complexity of GapSVPγ in terms of γ is as follows:

    • Between 1 and O(1): NP-hard (based on a randomized reduction).
                                  1−ε
    • Between O(1) and 2(log n)         : Quasi-NP-hard (based on a randomized reduction).

                                                       70


<!-- pdf-page: 74 -->
    •  n/ log n: Both NP and coAM (based on a quasi-polynomial-time randomized reduction).
     p

     √
    • n: Both NP and coNP (which is the same class as problems such as factoring).

    • O(n): Here we get an implication of one-way functions. There is a gap at which point we get PKE
      and FHE, etc.

    • 2n log log n/ log n : BPP (polynomial-time).

   Moreover, known GapSVPγ algorithms run in nearly exponential time in terms of lattice dimension.

Problems used in Practice. As mentioned previously, we do not generally speaking reduce directly
to GapSVPγ when coming up with cryptographic systems. Instead, we will reduce to average-case lattice
problems which themselves reduce to the worst-case hardness of GapSVPγ . The two most common as-
sumptions are the short integer solutions (SIS) assumption and the learning-with-errors (LWE) assumption.
Here we will cover SIS, deferring the discussion of LWE to a future lecture.

Definition 17.3 (SISn,m,q,β ). For a lattice of dimension n, a number of samples m, a modulus q, and a
norm bound β, the SISn,m,q,β assumption states that there is no polynomial-time adversary A such that
         r
given A ←  Zn×m
            q    , A produces non-zero x ∈ Zm such that Ax = 0 (mod q) and ∥x∥ ≤ β.

    It will typically be the case that m ≫ n. Generally, it is the case that Ax = 0 has plenty of solutions,
but finding short solutions is conjectured to be hard for certain norm bounds. Setting β = q/2 makes the
problem trivial (one could simply use Gaussian elimination). In particular, we care about the case where
                           √
β ≪ q, for example β = q.




                                                     71


<!-- pdf-page: 75 -->
  CS 395T: Topics in Cryptography                                                             March 21, 2024

                               Lecture 18: Short Integer Solutions
  Lecturer: David Wu                                                                        Scribe: Jeriah Yu


SIS Recap     In the previous lecture, we introduced the Short Integer Solutions problem on lattices.

Definition 18.1 (Short Integer Solution Problem (SISn,m,q,β )). The problem is defined in terms of lattice
                                                                                 r
dimension n, number of instances m, modulus q, and norm bound β. Given A ←         Zn×m
                                                                                     q  , find an x ∈ Zmq
such that x ̸= 0, Ax ≡ 0 (mod q), and ∥x∥ ≤ β.
                                                      qP
   We generally define ∥x∥ to be the ℓ2 norm, ∥x∥2 =         i∈[m] xi . With this norm definition, we can
                                                                    2
                                                    √
show a solution always exists if m > n log q and β ≥ m.

Proof. Take y ∈ {0, 1}m . There are 2m values of y, 2m > 2n log q = q n . The number of possible values for
Ay ≤ q n . Therefore, by the pigeonhole principle, there must exist y1 ̸= y2 such that Ay1 = Ay2 , thus we
have a solution to SIS.

SIS and SVP SIS is an average-case SVP on lattice A ∈ Zn×m
                                                       q   . If L⊥ (A) = {x ∈ Zm : Ax ≡ 0 (mod q)},
then SIS is equivalent to approximate SVP in L⊥ (A).

Theorem 18.2. For any m = poly(n), any β > 0, and sufficiently large q ≥ β ·poly(n), there is a randomized
reduction from solving GapSVPγ in the worst case to solving SISn,m,q,β where γ = β · poly(n).

Inhomogeneous SIS A parallel to the SIS problem for finding x where Ax = 0, the ISIS problem is to
find x where Ax = b for a random target vector b ∈ Znq .

Definition 18.3 (Inhomogeneous Short Integer Solution Problem (ISISn,m,q,β )). The problem is defined
                                                                                             r
in terms of lattice dimension n, number of instances m, modulus q, and norm bound β. Given A ← Zn×m
                                                                                                 q
       r
and b ← Zq , find an x ∈ Zq such that Ax ≡ b (mod q), and ∥x∥ ≤ β.
           n                m



Keyed Collision-Resistant Hash Functions (CRHF) from SIS Using the SIS hardness assumption,
we can construct a collision resistant hash function. We recall the definition of a keyed CRHF.

Definition 18.4 (Collision-Resistant Hash Function). A keyed family of hash functions H : K × X → Y ,
where K is the key space, X is the input space, and Y is the output space, is collision resistant if it satisfies
the following properties:

    • Compression: |Y | < |X|
                                         r
    • Collision Resistance: for some k ←   K, an efficient adversary should have negligible advantage
      in finding x1 ̸= x2 ∈ X such that H(k, x1 ) = H(k, x2 ).
                                                                                                      r
    We can derive a CRHF directly from SIS. For H : Zn×m q     × {0, 1}m → Znq , randomly sample A ←     K,
and define H(A, x) = Ax (mod q). The compression property is satisfied by setting m > n log q, and
                                                                           r
the collision resistance property follows directly from SIS: suppose for A ←  Zn×m
                                                                                 q   an efficient adversary
outputs x1 ̸= x2 ∈ {0, 1} s.t. H(A, x1 ) = H(A, x2 ). Then A(x1 − x2 ) = 0, thus solving SIS.
                           m



                                                       72


<!-- pdf-page: 76 -->
Local Updates For most cryptographic hash functions such as Merkle-Damgard constructions, changing
a small part of the input requires rerunning the hash function on the entire input. For the SIS CRHF, this
is unnecessary for small changes to x.
    Suppose y = H(A, x)   P where x ∈ {0, 1} . Let x be updated at a single bit index i from xi to xi∗ .
                                               m                                         ∗        ∗
                                                                                                        ′

Since H(A, x) = Ax = i∈[m] ai xi , where ai are the column vectors of A, we can easily find the updated
hash by adding ai∗ · (x′i∗ − xi∗ to the original hash.

Universality and Leftover Hash Lemma
Definition 18.5 (Universality). Let H : K × X → Y be a keyed hash function. H is universal if for all
x0 ̸= x1 , Pr[H(k, x0 ) = H(k, x1 )] ≤ |Y1 | for a randomly sampled key k.
     This is an information-theoretic property, and does not rely on computational assumptions of regarding
efficient adversaries.
Theorem 18.6. The SIS CRHF is universal.
                                      r
Proof. Let x1 ̸= x2 ∈ {0, 1}m and A ←    Zn×m  . Ax1 = Ax2 =⇒ A(x1 −x2 ) = i∈[m] ai (x1,i −x2,i ) = 0.
                                                                                 P
                                           q
Since x1 ̸= x2 , there must be some index i∗ where they differ: x1,i∗P̸= x2,i∗ =⇒ (x1,i∗ − x2,i∗ ) ∈ {−1, 1}.
Then P r[Ax1 = Ax2 (mod q)] = P r[ai∗ = −(x1,i∗ − x2,i∗ )−1 · i̸=i∗ ai (x1,i − x2,i )] = q1n = |Y1 | . Thus,
the SIS CRHF is universal by definition.

   We now define guessing probability and min-entropy.
Definition 18.7 (Guessing Probability and Min-entropy). Let X be a random variable which takes val-
ues from a finite set S. The guessing probability of X is maxs∈S P r[X = s]. The min-entropy of X is
− log guessing probability, or − log(maxs∈S P r[X = s]). Essentially, a random variable with k bits of
min-entropy can be treated as a random bit string of length k.
Definition 18.8 (Leftover Hash Lemma). Let H : K × X → Y be a universal hash. Let x ∈ X be a random
variable with t bits of min-entropy. Define distributions:
               r
    • D0 := (k ← K, y ← H(k, x))
               r      r
    • D1 := (k ← K, y ← Y)
                                                                    q
                                                                        |Y |
Then the statistical distance between D0 and D1 is bounded by 12         2t .

     For security parameter λ, we want to set t = 2λ + log |Y | to achieve a statistical distance < 21λ .
     Note that statistical distance is different than computational advantage. Any adversary, without any ef-
ficiency requirement, cannot distinguish between D0 and D1 with advantage greater than ϵ if the statistical
distance between D0 and D1 is ϵ.
     For lattices, m is commonly set to be 3n log q as this achieves negligible distinguishing advantage
against uniform random sampling.
                      r                                             r
Claim 18.9. Let A ←     Zn×m
                          q    where m > 3n log q. Then for any r ←     {0, 1}m , Ar is statistically close to
               n
uniform over Zq .
                                                        q        q n           q n
Proof. |Y | = |Znq | = q n . The statistical distance is |Y2t| =     q
                                                                  23n log q
                                                                            =       q
                                                                                  (q n )3
                                                                                          = q1n . This is the
equivalent probability to uniformly sampling Znq .

                                                     73


<!-- pdf-page: 77 -->
Commitment from LHL

Definition 18.10 (Commitment). Recall the definition of commitment schemes using three functions:
Setup, Commit, and Verify.

   • Setup(1λ ) → crs: create a common reference string relative to the security parameter.

   • Commit(crs, m, r) → c: commit to message m using random element r.

   • Verify(crs, c, r, m) → 0/1: check if c is a valid commitment to m with opening r.

A secure commitment scheme should satisfy the following two properties:

   • Hiding: Adversaries have negligible advantage distinguishing between commitments of different
     messages.

   • Binding: For a random crs, adversaries have negligible advantage in computing (m1 , r1 ) and (m2 , r2 )
     where m1 ̸= m2 such that c1 = c2 .

Definition 18.11 (Pedersen commitment from discrete log). Recall the Pedersen commitment using discrete
log:
                     r
   • Setup: sample s ← Zp , output (g, h = g s ).
                                 r
   • Commit((g, h), m): sample r ← Zp , output c = g r hm , with opening r.
                                         ?
   • Verify((g, h), c, r, m): check if c = g r hm .

   • Hiding: the Pedersen commitment satisfies the hiding property as g r is indistinguishable from a
     uniform random group element and obscures hm .
                                                                                         ′        ′
   • Binding: the binding property is satisfied as an adversary that finds g r hm = g r hm with m ̸= m′
     can solve the discrete log problem by solving s = (r − r′ )(m − m′ )−1 mod q.

   We can construct a parallel commitment scheme from SIS.

Definition 18.12 (Commitment from SIS). Let n, q be lattice parameters and m > 3n log q. We define the
following commitment functions:
               r           r
   • Setup: A1 ← Zn×m
                  q   , A2 ← Zn×m
                              q   , output crs = (A1 , A2 )
                                                                                                
                                                                                             p
                                                r
   • Commit((A1 , A2 ), p ∈ {0, 1}m ): sample r ← {0, 1}m , output c = A1
                                                                                    
                                                                                  A2             = A1 p + A2 r
                                                                                             r
                                                             ?
   • Verify((A1 , A2 ), c, r, p)): check p, r ∈ {0, 1}m and c = A1 p + A2 r

We can now prove the properties for commitment schemes:

   • Hiding: since m > 3n log q, A2 r is statistically indistinguishable from a uniform random value in
     Znq by the Leftover Hash Lemma. It therefore acts as a blinding element obscuring A1 m.


                                                      74


<!-- pdf-page: 78 -->
• Binding: Assume there exists an efficient adversary that can break the binding property. It can be
  used to construct an adversary to solve SISn,2m,q,√2m :
                                            r
    1. SIS challenger samples A = [A1 |A2 ] ← Zn×2m
                                               q    and sends to SIS adversary.
    2. The SIS adversary provides crs = (A1 , A2 ) to binding adversary.
    3. The binding adversary responds with (m1 , r1 ), (m2 , r2 ) such thatA1 m1 +A2 r1 = A1 m2 +A2 r2 .
                                                                 m1 − m2
       Or alternatively, A1 (m1 − m2 ) + A2 (r1 − r2 ) = A                   =0
                                                                  r1 − r2
                                                 
                                        m1 − m2
    4. The SIS adversary outputs x =
                                        r1 − r2
  If the binding adversary succeeds, we show above that the SIS adversary succeeds
                                                                            √      in finding x such
  that Ax = 0, and x ̸= 0 since m1 ̸= m2 . Since x ∈ {−1, 0, 1}2m , ∥x∥2 ≤ 2m. Thus, x is a valid
  solution to the SIS problem.




                                                 75


<!-- pdf-page: 79 -->
  CS 395T: Topics in Cryptography                                                           March 26, 2024

                                  Lecture 19: Lattice Trapdoors
  Lecturer: David Wu                                                                      Scribe: Jeriah Yu


Lattice Trapdoors from ISIS Recall the definition of Inhomogeneous SIS:
Definition 19.1 (Inhomogeneous Short Integer Solution Problem (ISISn,m,q,β )). The problem is defined
                                                                                             r
in terms of lattice dimension n, number of instances m, modulus q, and norm bound β. Given A ← Zn×m
                                                                                                 q
       r
and b ←  Znq , find an x ∈ Zm
                            q such that Ax ≡ b (mod q), and ∥x∥ ≤ β.

    Our eventual goal is to create digital signatures in lattices. To accomplish this, we first need to create
trapdoor functions using the ISIS problem.
Definition 19.2 (Trapdoor Function). A trapdoor function is a function f that is easy to compute in one
direction but hard to compute an inverse unless given additional information. This information is called
                                                               td
the trapdoor. f (x) → y is easy, f −1 (y) → x is hard, f −1 (y) → x is easy.
Definition 19.3 (Lattice Trapdoor). A lattice trapdoor is defined with the following procedures:
    • TrapGen(n, m, q, β) → (A, tdA ): given lattice parameters, the algorithm outputs matrix A and
      trapdoor tdA , where A ∈ Zn×m
                                q   . A should be statistically close to uniform over Zqn×m .

    • fA (x): for input x ∈ Zm
                             q , output Ax.

    • fA−1 (tdA , y): for input y ∈ Znq , output x such that Ax = y and ∥x∥ ≤ β.
   To make a trapdoor for the ISIS problem, we will make use of a powers-of-two ”gadget” matrix.
                                                             n×n⌊log q⌋
Definition 19.4 (Gadget Matrix). The gadget matrix G ∈ Zq       is a sparse matrix, where ℓ = ⌊log q⌋:

                                   1 2 4 . . . 2ℓ
                                                                        

                           G=
                                                     1 2 4 . . . 2ℓ 
                                                                    ..
                                                                         
                                                                       .

This is equivalent to the tensor product In ⊗ 1 2 4 . . . 2ℓ , where In is the identity matrix. Since
                                                              

generally m > n⌊log q⌋, G can be padded with columns of 0 to achieve G ∈ Zn×m
                                                                          q   .
    Inhomogeneous SIS is easy if A = G, as x can be set to the bitwise binary decomposition of y. This
yields Gx = y, and since x only contains 0 and 1, ∥x∥ = 1 for the infinity norm. We can refer to the bit
decomposition function as G−1 : Znq → {0, 1}m .
    We now want to hide G in relation to A in the ISIS problem, which is uniformly sampled. Thus, our
secret trapdoor for a specific instance of ISIS should be a ”short” matrix with small entries R such that
AR = G. Assuming we have this matrix, we can define fA−1 (tdA = R, y) : outputx = RG−1 (y). Then we
see that Ax = ARG−1 (y) = GG−1 (y) = y. Then since ∥G−1 (y)∥ = 1, then ∥x∥ ≤ m · ∥R∥, so if ∥R∥
is small enough, we can ensure ∥x∥ ≤ β.
    How do we find A and R such that AR = G, A is statistically close to uniform, and R is short? We
can define TrapGen(n, m, q, β) as follows:

                                                     76


<!-- pdf-page: 80 -->
                r           r
   1. Sample Ā ← Zn×m
                   q   , R̄ ← {0, 1}m×m .
                                                       
                                               −R̄
   2. Compute A = Ā          ĀR̄ + G and R =
                                      
                                               Im
   3. Output A and tdA = R.

By construction, AR = G and ∥R∥ = 1. By Leftover Hash Lemma, if m ≥ 3n log q, then Ar where
   r
r←    {0, 1}m is statistically close to a uniform element of Znq given A. We repeat this claim for each column
of R̄ to show that ĀR̄ is statistically close to uniform in Zn×mq    given Ā, thus A is statistically close to
uniform in Zqn×2m   .

Digital Signatures from Lattice Trapdoors With lattice trapdoors, we can develop a digital signature
scheme in the random oracle model that is analogous to RSA.
   We start by defining a candidate signature scheme using the gadget trapdoor defined above:

    • KeyGen(1λ ) : (A, tdA = R) ← TrapGen(n, m, q, β). Output vk = A, sk = tdA = R where
      AR = G.

    • Sign(sk, m) : σ ← fA−1 (sk, H(m)) = sk · G−1 (H(m)), where H(m) : {0, 1}∗ → Znq is a random
      oracle hash.

    • Verify(vk, mσ) : Check ∥σ∥ ≤ β and fA (σ) = Aσ = H(m).

We can see that this signature is correct by inspection. With regards to security, a forgery requires the
adversary to find v such that Av = H(m). Since A is statistically close to uniform and H(m) is uniform,
this is equivalent to solving ISIS. However, in the security reduction, we need to answer signing queries
for the signature adversary. Every signing query leaks information about R. This is because H(m) = y
and G−1 (y) are both computable. Thus an adversary can reconstruct R by making multiple signing queries
to construct and solve a linear system.
    To remedy this issue, we introduce randomness into the signing algorithm using a preimage sampleable
trapdoor function.

Definition 19.5. A function f : X → Y is a preimage-sampleable trapdoor function if there exists an
efficiently-sampleable distribution D over X and a trapdoor inversion algorithm SamplePre with the
following properties:

    • For x ← D, f (x) is uniform in Y .
            r
    • For y ← Y , SamplePre(td, y) outputs a preimage x from D where f (x) = y.
                                                                                    r
    • {x ← D, y ← f (x) : (x, y)} (a forward sampling) is statistically close to {y ← Y, x ← SamplePre(td, y) :
      (x, y) (a backward sampling).
                      r
    • Given f and y ←    Y , an efficient adversary has negligible advantage in computing x such that
      F (x) = y without td.

   Replacing the gadget trapdoor G−1 with a preimage-sampleable trapdoor SamplePre allows us to
develop a security proof analogous to RSA-FDH.



                                                       77


<!-- pdf-page: 81 -->
Proof. We will construct adversary B to break the trapdoor function security given an efficient signature
adversary A. Without loss of generality, assume A queries the random oracle H on message m before
making a signing query on m.
                               r
   1. Adversary B receives y ∗ ← Y from the challenger, and randomly chooses a query i∗ to program y ∗ to.

   2. For a random oracle query, respond with y ← y ∗ for query i∗ , otherwise forward sample and add
      m 7→ (x, y) to the random oracle table.

   3. For a signing query, if m has an entry in the table, respond with x. Otherwise, abort.

   4. Adversary A completes with m∗ , σ ∗ . If m∗ is the message used in random oracle query i∗ , output
      σ ∗ . Otherwise, abort.

If adversary A makes Q random oracle queries and has non-negligible advantage ϵ, B succeeds with
advantage Qϵ , which is non-negligible because Q is polynomially-bounded since A is efficient. Random
oracle queries are properly distributed by preimage sampling and signature queries are properly distributed,
so if A succeeds and i∗ is a correct guess, f (σ ∗ ) = H(m∗ ) = y ∗ , allowing B to break the one-wayness of
the trapdoor function.

Preimage-Sampleable Trapdoor from SIS Recall the hash function from SIS: fA (x) = Ax (mod q),
where A ∈ Zn×m q    and x ∈ Zmq . We wish to construct a preimage-sampelable trapdoor, which requires a
sufficient distribution on Zm
                            q to sample preimages. For lattices, we use the discrete Gaussian distribution.

                                                                                             −π∥x∥22
                                                                                                    
Definition 19.6 (Discrete Gaussian Distribution). Define the mass function ρs (x) = exp        s2
                                                                                                       , with
width s. Then the discrete Gaussian distribution DZm ,s over Zm is the distribution with probability mass
function P r[x = z] = P ρsm(z)ρs (x) ∀z ∈ Zm .
                         x∈Z


    For A ∈ Zn×m
             q   and y ∈ Zm
                          q , we will denote x ← As (y) as the distribution x ← DZm ,s conditioned
                                                  −1

on Ax = y. Now we want to ensure we can perform efficient preimage-sampling on this distribution.

Theorem 19.7. Suppose AR = G and s ≥ ∥R∥∞ · log n. Then there exists an efficient algorithm SamplePre
such that the distributions {x ← SamplePre(A, R, y, s)} and {x ← A−1
                                                                  s (y)} are statistically close (within
2−n ) for all y ∈ Znq .
                                                 r
    If we ensure that m ≥ 2n log q, s ≥ log m, A ← Zn×m
                                                    q   , and x ← DZm ,s , Ax will be statistically close
to uniform.




                                                     78


<!-- pdf-page: 82 -->
  CS 395T: Topics in Cryptography                                                        March 28, 2024

        Lecture 20: Lattice-based Signatures and Learning with Errors (LWE)
  Lecturer: David Wu                                                               Scribe: Sidh Suchdev


Lattice-based Signatures Recap Recall from last lecture the definition of a preimage-sampleable trap-
door function:

Definition 20.1. A function f : X → Y is a preimage-sampleable trapdoor function if there exists
an efficiently-sampleable distribution D and an inversion algorithm SamplePre where:
                                                          r                    
                          x←D                 s            y←   Y
                                     : (x, y) ≈                          : (x, y)
                        y ← f (x)                  x ← SamplePre(td, x)

    We define the preimage sampling theorem for the ISIS trapdoor:

Theorem 20.2. Let A ∈ Zn×m
                        q    , R small, where AR = G and s ≥ ∥R∥∞ · log n. Then there exists an efficient
algorithm SamplePre such that
                                                             s
                            {x ← SamplePre(A, R, y, s)} ≈ {x ← A−1
                                                                s (y)}

for all y ∈ Znq .

Corollary 20.3. Using the preimage-sampling theorem, we can see that:
                                                                                    
                                                 (A, R) ← TrapGen
                (A, R) ← TrapGen                  s
                                                                                     
                                                                r
                                    : (A, x, Ax) ≈           y←   Zmq    : (A, x, y)
                    x ← DZ,s
                                                         x ← fA−1 (R, y)
                                                                                    


Learning With Errors (LWE) Learning with Errors, like SIS, is a fundamental assumption in lattice-based
cryptography. It can be viewed as the dual to the Diffie-Hellman assumption for lattice-based cryptography.

Definition 20.4 (LWE assumption). The LWEn,m,q,χ assumption states that:
                                                         c
                                        (A, sT A + eT ) ≈ (A, rT ),
           r         r         r        r
where A ←    Zn×m
              q   ,s ← Znq , e ← χm , r ←  q . LWE is parameterized by n, m, q, χ. Typical parameter
                                          Zm
values are:

    • n ≈ 1024

    • q ≈ 232

    • m ∼ n log q ≈ 215

    • χ = DZ,s where s ≈ 3




                                                    79


<!-- pdf-page: 83 -->
    It is not obvious that this assumption is hard. However, Regev showed that LWE reduces to GapSVP
using a quantum reduction. More formally, he showed that for any m = poly(n), modulus q < 2poly(n) and
χ = DZ,s where χ is β-bounded (Pr[x ← χ : |x| < β] = 1), then solving LWEn,m,q,χ is as hard as solving
GapSVPγ , where γ = Õ(n · βq ).
    Additionally, it can be shown that the hardness of LWE implies the hardness of SIS. We can construct
an informal proof showing this. Suppose we have an adversary A for the SIS problem. We will construct
an adversary B for the LWE game.
                                                                                       ?
   1. The challenger gives B an LWE challenge (A, tT ). B must decide whether tT = sT A + eT (b = 0) or
           ?             r
      if tT = uT where u ←  q (b = 1).
                           Zm

   2. B sends A to A and receives a vector z ∈ Zm such that Az = 0 mod q and ||z|| is ”small”.

   3. B computes tT · z.

         • If tT = sT A + eT , then tT · z = sT A · z + eT · z = eT · z. Observe that eT · z is ”small” since
           e ∈ χm and z are both ”small”.
         • If tT = uT , then tT · z = uT · z. Observe this value is likely ”large” since u is sampled uniformly
           randomly from Zq .

   4. B sends the guess b′ = 0 if ||tT · z|| is ”small” and b′ = 1 otherwise.

Definition 20.5 (Regev Symmetric Encryption Scheme). The definition of the scheme follows below:
                           r
    • Setup(1λ ): Output s ← Znq
                                       r           r
    • Encrypt(s, µ ∈ {0, 1}): Sample a ← Znq and e ← χ. Output ct = (a, sT a + e + µ⌊ 2q ⌋)

    • Decrypt(s, ct = (c1 , c2 )) : Output ⌊c2 − sT c1 (mod q)⌉q,2 , where ⌊·⌉ is the rounding operation and
               j       m
      ⌊x⌉q,2 := 2q · x

Correctness Let ct = (c1 , c2 ) ← Encrypt(s, µ). It follows that
                                             j              jq k               m
               ⌊c2 − sT c1 (mod q)⌉q,2 = sT a + e + µ            − sT a (mod q)
                                                              2                  q,2
                                             j        jq k           m
                                          = e+µ              (mod q)
                                                        2              q,2
                                                                 
                                               2
                                          ≈      e + µ (mod q)
                                               q


Note that if |e| < 4q , then we can see that the result of the rounding operation is unchanged by e, and thus
rounds to the value of µ.




                                                     80


<!-- pdf-page: 84 -->
Security We can see security directly from the LWE assumption. We will show each encryption is
computationally indistinguishable from a uniformly random sample:
                                     c
   • Encrypt(s, 0) = (a, sT a + e) ≈ (a, r)
                                             c               c
   • Encrypt(s, 1) = (a, sT a + e + ⌊ 2q ⌋) ≈ (a, r + ⌊ 2q ⌋) ≈ (a, r)




                                                      81


<!-- pdf-page: 85 -->
  CS 395T: Topics in Cryptography                                                             April 2, 2024

         Lecture 21: Regev Encryption and Fully Homomorphic Encryption
  Lecturer: David Wu                                                                   Scribe: Eli Bradley

    In the previous lecture, we introduced the Regev symmetric-key encryption scheme. In this lecture,
we show the scheme can be extended to a public-key encryption scheme [Reg05] and a fully homomorphic
encryption (FHE) scheme [GSW13], and introduce the intermediate notion of somewhat homomorphic
encryption (SWHE).
                                                                              j m
Notation 21.1. We will use ⌊·⌉ : R → Z to denote rounding, and define ⌊x⌉q,2 : 2q x . When x is a vector,
this applies elementwise.

Regev encryption.      Recall the Regev encryption scheme:
                                      r
    • Setup(1λ ): Sample and output s ← Znq .
                                       r                                              q
    • Encrypt(s, µ ∈ {0, 1}): Sample a ← Znq , e ← χ. Output ct = (a, sT a + e + µ     2 ).

    • Decrypt(s, (c0 , c1 )): Output ⌊c1 − sT c0 (mod q)⌉q,2 .

              Let                                         T a + e + µ q ). If |e| < q , then c − sT c =
                                                                      
Correctness.       ct = (c1 , c0 ) = Encrypt(s, µ) = (a, s            2             4         1      0
e + µ 2q rounds to µ, and the decrypted value Decrypt(s, ct) is correct.
      


Security. The scheme is CPA-secure assuming the hardness of the LWE problem, which we recall here.
                                       r                r         r
Definition 21.2 (LWE Problem). Given a ← Znq , e ← χ, s ← Znq , u ← Zq , distinguish (a, sT a + e) and
(a, u).
    By this assumption, in the security argument, we can replace the ciphertexts with (a, u + µ⌊ 2q ⌋). Then,
the encryption scheme becomes a one-time pad.
    Extending the Regev encryption scheme to a public-key encryption scheme will rely on the observation
that it is additively homomorphic. That is, for ciphertexts ct1 ← Encrypt(s, µ1 ) and ct2 ← Encrypt(s, µ2 ),
ct1 + ct2 is an encryption of µ1 + µ2 . In fact, these techniques will work to derive public-key encryption
from any additively homomorphic secret-key encryption scheme.

Showing additive homomorphism. To see that Regev encryption is additively homomorphic, consider
two ciphertexts:                                                 jq k
                                     ct1 = (a1 , sT a1 + e1 + µ1       ).
                                                                 j 2q k
                                     ct2 = (a2 , sT a2 + e2 + µ2       ).
                                                                   2
Their sum is the following.
                                                                                j q k
                   ct1 + ct2 = a1 + a2 , sT (a1 + a2 ) + (e1 + e2 ) + (µ1 + µ2 )        .
                                                                                   2
Assuming small enough errors, it follows that ct1+ct2 isan encryption of µ1 + µ2 (mod 2) if µ1 = 0
or µ2 = 0. If µ1 = µ2 = 1, we observe (µ1 + µ2 ) 2q = 2 2q ∈ {q − 1, q} = {−1, 0}. This is small and
can be added into the error term, so ct1 + ct2 is an encryption of µ1 + µ2 (mod 2) in this case as well.

                                                     82


<!-- pdf-page: 86 -->
Regev public-key encryption [Reg05]. In the public-key encryption scheme, the public key will consist
of many encryptions of 0, (ai , sT ai + ei ) for i ∈ [m]. Notice this can be equivalently represented more
compactly by matrices, (A, sT A + eT ). To get a fresh encryption of 0, we take the sum of a random subset
of the encryptions of 0 in the public key. Then, we get an encryption of µ from this by adding µ 2q to
                                                                                                       

the second component.
                           r        r
    • Setup(1λ ): Sample A ← Zn×m
                              q   ,s← Znq , e ← χm . Output pk = (A, sT A + eT ), sk = s.
                                                             r                                           q
    • Encrypt(pk, µ ∈ {0, 1}): Parse pk = (A, bT ). Sample r ← {0, 1}m . Output ct = (Ar, bT r + µ        2 ).

    • Decrypt(s, (c0 , c1 )): Output ⌊c1 − sT c0 (mod q)⌉q,2 .

Correctness. We will need the following notion.

Definition 21.3 (B-bounded). A distribution χ is B-bounded if

                                         Pr[x ← χ : |x| ≤ B] = 1.

    Assume χ is B-bounded      and m · B ≤ 4q . Let ct = (c1 , c0 ) = Encrypt(s, µ) = (Ar, bT r + µ 2q ). Then,
                                                                                                    

c1 − sT c0 = eT r + µ 2q . Notice |eT r| ≤ m · B. If m · B ≤ 4q , then c1 − sT c0 rounds to µ, and the
                           

decrypted value Decrypt(s, ct) is correct.
    Notice m·B grows with the dimension m. It is important in LWE-based constructions for this reason that
errors are short. This is also why Gaussian distributions, which have vanishingly small tails, are often used.

Security. Our security argument proceeds in two steps.

   1. Note that under the LWE assumption, the public key is indistinguishable from random.
                                                                    r
                                                c                A←     Zn×m
                                            pk ≈ (A, bT ) :           r
                                                                         q
                                                                  b ← Zm   q


   2. The ciphertexts take the following form.
                                                                        
                                                        A             0 
                                             ct =            r +             .
                                                        bT         µ · 2q
             
            A
      But T is a uniformly random matrix and r is a random binary vector. By the leftover hash lemma,
           b
                                       
                                       A
      if m ≥ 3n log q, the first term T r is statistically close to uniformly random. The second term
                                       b
      involving µ is hidden as in a one-time pad.

    This procedure can be applied to get PKE from any additively homomorphic SKE scheme.




                                                          83


<!-- pdf-page: 87 -->
Fully homomorphic encryption. A fully homomorphic encryption (FHE) scheme is a scheme support-
ing arbitrary computation on ciphertexts. In other words, there exists a public algorithm for which for any
efficiently computable function f ,
                                                 public algorithm
                            Encrypt(pk, x) −−−−−−−−−−→ Encrypt(pk, f (x)).
   This notion goes back to the beginning of cryptography, and was speculated to exist by Whitfield Diffie
and Martin Helman. There were several partial successes before it was achieved.
    • ElGamal supported additively homomorphic encryption, but only addition. See lecture 6.
    • Boneh-Goh-Nissim supported an arbitrary number of additions, but only 1 multiplication [BGN05].
      This is a pairings-based construction. See lecture 11.
    Finally, Gentry showed in a 2009 PhD thesis that fully homomorphic encryption is possible [Gen09].
This was a surprising breakthrough result, and turned lattice-based cryptography from a niche field into
something very popular. This construction was initially very complicated, but was significantly simplified
by 2013 [GSW13].
    Gentry’s approach takes the following general blueprint:
   1. Build somewhat homomorphic encryption (SWHE), which supports many additions and multipli-
      cations but not arbitrarily many.
   2. Bootstrap from SWHE to FHE.
   In this lecture, we fully cover the first step and briefly describe the second.

Gentry-Sahai-Waters (GSW) somewhat homomorphic encryption [GSW13]. We will start by
presenting again the Regev public-key encryption scheme described above, slightly reframed.
                            r             r
    • Setup(1λ ): Sample A ←   Zn×m
                                q    ,s←    Znq , e ← χm .
                                   
                              A
      Output pk = A = T               , sk = s where sT = −sT               1 .
                                                                            
                          s A+e   T

                                                                                              
                                             r
    • Encrypt(A, µ ∈ {0, 1}): Sample r ← {0, 1}m . Output c = Ar +                        0q  .
                                                                                      µ    2

    • Decrypt(s, c): Output ⌊sT c⌉   q,2 .

   Note sT A = −sT A + sT A + eT = eT . Let c = Encrypt(A, µ) and consider the output Decrypt(s, c).
                                                       
                                  T      T             0
                                 s c=s        Ar + µ 
                                                       2
                                                             
                                                          0
                                     = eT r + −sT 1  µ 
                                               
                                                                        2
                                                           jµk
                                                   T
                                             =e r+µ                 .
                                                               2
    The encryption scheme works as before.
    For simplicity, we will write µ in place of µ 2q for the rest of this section. To additionally get a
                                                  

multiplicative homomorphism, we will try to make it so that for ciphertext matrix C, sT C = µsT + error
for some error term. Suppose we update the encryption scheme as follows:

                                                          84


<!-- pdf-page: 88 -->
                                       r
    • Encrypt(A, µ ∈ {0, 1}): Sample R ← {0, 1}m×m . Output C = AR + µI.
    This meets the desired property: sT C = µsT (AR + µI) = µsT + eT R.
    We will check for additive and multiplicative homomorphisms. Suppose we have ciphertexts C1 , C2 of
values µ1 , µ2 , so sT C1 = µ1 sT + eT1 and sT C2 = µ2 sT + eT2 . Additive homomorphism follows by linearity
as before. In addition, the following holds:
                                  sT C1 C2 = (µ1 sT + eT1 )C2
                                             = µ1 sT C2 + eT1 C2
                                             = µ1 µ2 sT + (µ1 eT2 + eT1 C2 )
    This almost works, except that the norm of the error term is too large, as C2 may be large. To contain
the norm of this term, we recall the gadget matrix G from lecture 19. This will be used to contain the norm
of C2 . We change the encryption algorithm once more:
                                       r
    • Encrypt(A, µ ∈ {0, 1}): Sample R ← {0, 1}m×m . Output C = AR + µG.
This meets a slightly different property: sT C = µsT (AR + µG) = eT R + µsT G. If the error term meets
∥eT R∥∞ ≤ 4q , we can successfully decrypt.
    We will check for a multiplicative homomorphism now. Suppose we have ciphertexts C1 = AR1 + µ1 G
and C2 = AR2 + µ2 G. Then, the following holds:
                            C1 G−1 (C2 ) = (AR1 + µ1 G)G−1 (C2 )
                                         = AR1 G−1 (C2 ) + µ1 GG−1 (C2 )
                                         = AR1 G−1 (C2 ) + µ1 C2
                                         = AR1 G−1 (C2 ) + µ1 AR2 + µ1 µ2 G
                                         = A(R1 G−1 (C2 ) + µ1 R2 ) + µ1 µ2 G.
Notice G−1 (C2 ) ∈ {0, 1}m×m . Then, the error R× = R1 G−1 (C2 ) + µ1 R2 now meets
                                     ∥R× ∥∞ ≤ m∥R1 ∥∞ + ∥R2 ∥∞ .
This is the somewhat homomorphic encryption scheme we will use.

Analysis. Consider an initial ciphertext C1 = AR1 + µ1 G with constant noise ∥R1 ∥∞ ≤ 1, and imagine
repeatedly squaring it.
                         C2 = C1 G−1 (C1 )                                 noise O(m)
                           ..                                                       ..
                            .                                                        .
                      Cd−1 = Cd−2 G−1 (Cd−2 )                            noise O(md ).
   The GSW construction supports circuits of multiplicative depth d if q > mO(d) .

Bootstrapping. In the next lecture, we will present a technique to “refresh” the randomness of a noisy
ciphertext, allowing for the evaluation of larger circuits and getting us fully homomorphic encryption.
Given a ciphertext C that encrypts µ with large noise, we will encrypt C and evaluate the decryption
circuit homomorphically on this new ciphertext. This is known as Gentry’s bootstrapping transformation.
    Note that we can set the parameters in this construction. We just need to choose q large enough to
support the decryption circuit in this case.

                                                      85


<!-- pdf-page: 89 -->
  CS 395T: Topics in Cryptography                                                        April 4, 2024

           Lecture 22: FHE Bootstrapping and Key Agreement from LWE
  Lecturer: David Wu                                                            Scribe: Matthew Healy


From SWHE to FHE. In the previous lecture, we saw how to construct a somewhat homomorphic
encryption (SWHE) scheme. The Gentry-Sahai-Waters (GSW) construction we introduced can support
bounded depth computation where the LWE modulus is q > mO(d) , with d as the multiplicative depth of
the computation. In this lecture we will show how to obtain fully homomorphic encryption (FHE) from
somewhat homomorphic encryption (SWHE) using Gentry’s brilliant insight of bootstrapping.

High-level idea. Imagine we have a SWHE scheme that supports d operations. Suppose decryp-
tion in this scheme requires at most (d − 1) operations. Then, we can build an FHE scheme as fol-
lows:

    The public key of the FHE scheme is the public key of the SWHE scheme (pk) and an encryption of
the SWHE decryption key under the SWHE public key (Encrypt(pk, sk)). We now describe a ciphertext-
refreshing procedure:

    • For each SWHE ciphertext we associate a “noise” level that keeps track of how many more ho-
      momorphic operations can be performed on the ciphertext, while maintaining correctness. For
      example, we can perform d homomorphic operations on fresh ciphertexts, but after evaluating a
      single multiplication we can only perform (d − 1) more operations. The encryption of the SWHE
      decryption key under the SWHE public key has noise level 0.

    • Suppose ctµ = Encrypt(pk, µ). Using the SWHE scheme, we can compute ct = Encrypt(pk, f (µ))
      with noise level d for any f computable using d homomorphic operations.

    • We homomorphically compute fct (sk) = Decrypt(sk, ct) which takes d − 1 operations to compute.

    • We homomorphically compute fct on Encrypt(pk, sk) → Encrypt(pk, fct (sk)) = Encrypt(pk, µ)
      with noise level (d − 1).

    After the refresh, the refreshed ciphertext can still support at least 1 more homomorphic operation
since its current noise level is only (d − 1). By repeating this refresh whenever our ciphertexts become
too noisy we can eventually perform unbounded depth computation. Thus, we have attained FHE.

Security. The security of this construction requires that this scheme should be secure even if the public
key includes a copy of the decryption key. This requires us to make a “circular security” assumption.
Obtaining FHE without circular security from LWE is currently an open problem.

Key Agreement from LWE. Analogous with the Diffie-Hellman key exchange protocol, we want to
define a protocol for key exchange derived from LWE. We start with an amortized version of Regev’s PKE
scheme where each ciphertext encrypts a vector of bits. Since it may seem wasteful to use a vector to
encrypt a single bit, we consider a simple variant where we reuse A to encrypt multiple bits.


                                                   86


<!-- pdf-page: 90 -->
Construction 22.1 (Encrypting multiple bits). We describe this scheme as follows:
                                    r           r
      • Setup(1λ , 1l ): Sample A ←   Zn×m
                                       q    ,S ←     q , E ← χ
                                                   Zn×l          m×l . Output pk = (A, B T = S T AE T ∈

        Zq ), sk = S. One can think of S as l secret keys concatenated together.
         l×m

                                             r
      • Encrypt(pk, µ ∈ {0, 1}l ): Sample r ←  {0, 1}m . Output ct = (Ar, B T r + µ 2q )
                                                                                    

      • Decrypt(sk, ct): Output ⌊ct2 − S T ct1 ⌉q,2 .

    Using this construction, we will define a protocol for key exchange relying on LWE which will operate
                                r
as follows: Alice samples A ←      Zn×n
                                     q   , S1 , E1 ← χn×k1 , B1T = S1T A + E1T ∈ Zkq 1 ×n and sends A, B1 to
Bob. Bob samples S2 , E2 ← χ 2 , B2 ← AS2 + E2 and sends B2 to Alice. Alice then computes ⌈S1T B2 ⌋2l
                                n×k

while Bob computes ⌈B1T S2 ⌋2l . The computation within ⌈·⌋ produces lk1 k2 bits and we take the most
significant l bits of the output as our shared key.

Correctness. To show correctness, observe that

                                  S1T B2 = S1T (AS2 + E2 ) = S1T AS2 + S1T E2

and
                                 B1T S2 = (S1T A + E1T )S2 = S1T AS2 + E1T S2
   We hope that ⌈S1T B2 ⌋ = ⌈B1T S2 ⌋, which holds as long as S1T B2 and B1T S2 are far from a rounding
boundary.

Security. We will not formally show the security of this scheme against passive eavesdroppers. At a high
level, the distribution of the shared key is computationally close to uniform random even given the public
messages, so Eve will only observe random matrices while Alice and Bob are performing the key exchange
protocol.




                                                        87


<!-- pdf-page: 91 -->
  CS 395T: Topics in Cryptography                                                             April 9, 2024

                             Lecture 23: Homomorphic Signatures
  Lecturer: David Wu                                                                    Scribe: Eli Bradley

    In this lecture, we give a lattice-based construction of a homomorphic signature scheme [GPV08] and
introduce key lattice equations from which many lattice-based constructions can be derived.
    Recall lecture 14, in which we previously constructed a homomorphic signature scheme from a digital
signature scheme, a CRHF and a SNARG for P. The construction we present today will be much lighter.

Homomorphic signatures. A homomorphic signature scheme is a digital signature scheme, with the
additional property that arbitrary functions can be evaluated on the signed input. It would enable the
following workflow:

                                       Client                                 Server
                                (vk, sk) ← KeyGen
                                 σ ← Sign(sk, x)
                                                                vk, x, σ
                                                               −−−−→
                                                              Later on…
                                                                   f
                                                                  −
                                                                  →
                                                              y=f (x), σy,f
                                                              ←−−−−−−−−
                                         ↓
                          Client checks if σy,f is a valid
                         signature of y with respect to f ,
                            without looking at x or σ.

   We require the scheme meet the following requirements:

    • Unforgeability: An efficient adversary given x cannot construct a signature on pair (y, f ) where
      y ̸= f (x).

    • Succinctness: For security parameter λ, |σy,f | = poly(λ.|y|).

   Note that without the requirement of succinctness, there is a trivial solution: Simply output σy,f = σ,
                               ?
and let the verifier check f (x) = y themselves. A similar observation can be made for the case of fully homo-
morphic encryption, where without a succinctness requirement, evaluation can be offloaded to the decrypter.

Upgrading succinctness. This succinctness requirement can be generically improved to remove depen-
dence on |y|. Here are two ways this might be done:
                                          (
                                           0 f (x′ ) ̸= y
   • Define indicator function fy (x′ ) =                 . Homomorphically compute the signature σ1,fy .
                                           1 f (x′ ) = y

    • For a hash function H, define g(x′ ) = H(f (x′ )). Homomorphically compute the signature σH(m),g .

   In the latter case, the function g is input-independent, which can be useful for precomputing.

                                                     88


<!-- pdf-page: 92 -->
Gentry-Peikert-Vaikuntanathan (GPV) construction [GPV08]. Our signature scheme will be the
following. We assume without loss of generality the signing key sk contains vk.
                                                                 r
    • KeyGen: Sample (A, T ) ← TrapGen(n, q) and B1 , . . . , Bl ← Zqn×m .
      Output vk = (A, B1 , . . . , Bl ) and sk = T .

    • Sign(sk, x ∈ {0, 1}l ): For all i ∈ [l], sample Ri ← A−1 (Bi − xi G). That is, use trapdoor T to sample
      short Ri such that ARi = Bi − xi G.
      Output σ = (R1 , . . . , Rl ).
    To verify the signature on bit i ∈ [l], one would check ∥Ri ∥∞ is small and the verification relation
ARi = Bi − xi G holds.
    Recall the equation for GSW ciphertexts: Bi = ARi +xi G, where xi represented the message bit, Ri was
the encryption randomness, and Bi was the ciphertext. This is merely a rearrangement of that same equation.
This one equation or homomorphism, we will see, is the basis of most of lattice-based cryptography.

Homomorphic evaluation. We first consider the case of homomorphic evaluation of addition, f (x) :=
x1 + x2 . By construction, we know AR1 = B1 − x1 G and AR2 = B2 − x2 G. We can add these equations
to get A(R1 + R2 ) = (B1 + B2 ) − (x1 + x2 )G. Notice this has the form of the original verification relation.
We define the signature σf (x),f of f (x) with respect to f , and the verification key vkf , as follows.

                                   A(R1 + R2 ) = (B1 + B2 ) − (x1 + x2 )G
                                     | {z }       | {z }       | {z }
                                         σf (x),f           vkf          f (x)

   Now, consider the case of multiplication, f (x) := x1 x2 . Here, we use the dual view, B1 = AR1 + x1 G
and B2 = AR2 + x2 G. We proceed just as in the GSW construction.

                                       B1 G−1 (B2 ) = (AR1 + x1 G)G−1 (B2 )
                                                        = AR1 G−1 (B2 ) + x1 B2
                                                        = A(R1 G−1 (B2 ) + x1 R2 ) + x1 x2 G
                        A(R1 G−1 (B2 ) + x1 R2 ) = B1 G−1 (B2 ) − x1 x2 G.
                          |       {z         }     |   {z    } | {z }
                                   σf (x),f                      vkf     f (x)

Signatures and verification keys for arbitrary functions can be computed by combining these cases.

Example. As an example, we will compute the verification key for a circuit shown below.
   TODO
   This verification key vkf is input-independent; it can be precomputed from vk and f without x.

Verification. We can now give the verification algorithm.
                                                    f
    • Verify(vk, y, f, σ): Map (B1 , . . . , Bl ) 7−
                                                   → vkf = Bf as above.
      Check that AR = Bf − yG and ∥R∥∞ is small.
    In this case, allowing R not to be short would break security, as opposed to breaking correctness in
the GSW encryption scheme.

                                                            89


<!-- pdf-page: 93 -->
Signature evaluation. Observe the transformations applied to the signature are linear.
                                                              
                                                             Im
   • Addition (f (x) = xi + xj ): R+ = Ri + Rj = Ri Rj            .
                                                  
                                                              Im
                                                                       G−1 (Bj )
                                                                                  
   • Multiplication (f (x) = xi xj ): R× = Ri G (Bj ) + xi Rj = Ri Rj
                                               −1                                    .
                                                                
                                                                           xi Im
We assume Boolean circuits, so all wires have values xi ∈ {0, 1}. Then, the matrix multiplied on the right
is {0, 1}-valued in both cases. From this, we can conclude the following lattice homomorphism equation:
For every function f computed a depth-d circuit and input x, there exists an evaluation map Hf,x where
∥Hf,x ∥∞ ≤ mO(d) and                                        
                                       Rf,x = R1 · · · Rl Hf,x .

Lattice homomorphism equations. Here, we will derive two key lattice equations from which both
GSW scheme and the GPV scheme follow as corollaries.
    Let B = B1 · · · Bl . The verification key for f meets Bf = B ·Hf for a short matrix Hf depending
on f and B. We have shown the following verification relation.
                                                    ARf,x = Bf − f (x) · G
                                                   
                                      A R1 · · · Rl Hf,x =
                                                   
                                     AR1 · · · ARl Hf,x =
                                                   
                           B1 − x1 G · · · Bl − xl G Hf,x =
                                          (B − xT ⊗ G)Hf,x = Bf − f (x) · G.
   We get the following result.
Theorem 23.1. Given any B1 , . . . , Bl ∈ Zn×m
                                            q    , any function f computed by a circuit of depth d, and any
input x, there exists short matrices Hf and Hf,x where the following hold.
   1. B · Hf = Bf
   2. (B − xT ⊗ Hf,x ) = Bf − f (x) · G
    We can see the
                 homomorphism of the GSW construction from this theorem. Recall the ciphertext was
defined as C = C1 · · · Cl where Ci = ARi + xi G.
                          

                           C − xT ⊗ G = A R1 · · · Rl                                 (construction)
                                                         

                        (C − xT ⊗ G)Hf,x = Cf − f (x) · G                                     (equation 2)
                                             = CHf − f (x) · G                                (equation 1)
                                                         T
                                     C · Hf = (C − x ⊗ G)Hf,x + f (x) · G
                                                          
                                            = A R1 · · · Rl Hf,x +f (x) · G.
                                                |       {z     }
                                                   encryption randomness

   Thus, C · Hf is an encryption of f (x).

Security. In the next lecture, we will argue the security of this homomorphic signature scheme, and
discuss the dual notion of homomorphic commitments.

                                                    90


<!-- pdf-page: 94 -->
  CS 395T: Topics in Cryptography                                                                 April 11, 2024

                           Lecture 24: Homomorphic Commitments
  Lecturer: David Wu                                                                      Scribe: Elahe Sadeghi


Homomorphic Signatures. To recall the goal of a homomorphic signature schemes, it is to compute a
signature σx to sign a message x, such that given (f, σx ), one can evaluate σf,f (x) that verifies with respect
to the function f and the claim the value f (x) (i.e. the verification algorithm does not need to know x). It is
useful in the settings where the input x is sensitive. One application of this can be when someone outsources
a sensitive dataset, and other people can query the dataset, hoping to learn the output of the query, while the
dataset is hidden. The construction was introduces by adapting the GSW homomorphic encryption scheme.
Construction 24.1 (Homomorphic Signature). The homomorphic signature scheme (Setup, Sign, Eval, Verify)
adapting the GSW homomorphic encryption scheme has been constructed as follows:
    • Setup(1λ ) → (vk, sk): The setup algorithm takes a security parameter λ as input, and then obtains
              r                                                                    r
      (A, T) ←   TrapGen(n, q) and samples ℓ random n × m matrices B1 , . . . , Bℓ ← Zn×m
                                                                                        q   . It then sets
      vk := (A, B1 , . . . , Bℓ ) and sk := T.

    • Sign(sk, x) → σ: The signing algorithm takes as inputs a signing key sk = T and a message
      x ∈ {0, 1}ℓ as inputs. It then uses the trapdoor T to compute targeted pre-images Ri such that
      ARi = Bi − xi G (i.e. Ri ← A−1 (Bi − xi G)), and sets σ := (R1 , . . . , Rℓ ).

    • Eval(vk, σx , f ) → σf,f (x) : The evaluation algorithm takes a verification key vk = (A, B1 , . . . , Bℓ ),
      a signature σx = (R1 , . . . , Rℓ ), and a function f as inputs, and it computes σf,f (x) := R · Hf,x ,
      where R = [R1 | · · · | Rℓ ] and Hf,x is the evaluation matrix.

    • Verify(vk, f, y, σf,f (x) ) → 0/1: The verification algorithm takes a verification key vk = (A, B1 , . . . , Bℓ ),
      a function f , a value y, and a signature σf,f (x) = (R1 , . . . , Rℓ ) as inputs. If ||σf,f (x) ||∞ is small and
      Aσf,f (x) = Bf − y · G, the algorithm outputs 1, and 0 otherwise.
    Homomorphism or homomorphic evaluations in signature schemes relies on matrix evaluation. From
the signing algorithm, we have the key equation B = AR + x ⊗ G, where B = [B1 | · · · | Bℓ ] and
R = [R1 | · · · | Rℓ ]. Observe that x ⊗ G = [x1 G | · · · | xℓ G].
Let B1 , . . . , Bℓ ∈ Zn×m
                       q   be arbitrary matrices. We can define two homomorphic evaluation algorithms
as follows.
   1. For every function f : {0, 1}ℓ → {0, 1}, there exists a short matrix Hf such that

                                                     B · Hf = Bf

   2. For every f : {0, 1}ℓ → {0, 1} and every x ∈ {0, 1}ℓ , there exists a short matrix Hf,x such that

                                       (B − x ⊗ G) · Hf,x = Bf − f (x) · G

      Intuitively, (B − x ⊗ G) is an encoding of x with respect to B, in which applying the evaluation
      matrix Hf,x on it computes a new encoding Bf − f (x) · G of f (x) with respect to Bf , where Bf
      is a function depending only on public parameters.

                                                        91


<!-- pdf-page: 95 -->
Correctness:
             A · σf,f (x) = ARHf,x = (B − x ⊗ G) · Hf,x = Bf − f (x) · G = Bf − y · G
Since R is small (as it is sampled from the Gaussian distribution), and Hf,x is also small (and as said in
previous lectures, ||Hf ||∞ , ||Hf,x ||∞ ≤ mO(d) where d is the depth of the circuit that computes f ). Thus,
σf,f (x) = R · Hf,x is going to be small.

Security. We show that the above construction has selective security. Selective security is defined as
follows, and can be boosted to adaptive security without additional assumptions.
   1. The adversary A sends x ∈ {0, 1}ℓ to the selective security challenger.
   2. The challenger computes and sends vk and σx to the adversary A.
   3. The adversary A sends (f, y, σf,y ) to the challenger, and wins if Verify(vk, f, y, σf,y ) = 1 and
      y ̸= f (x).
Claim 24.2. The above construction Construction 24.1 is selective secure under SIS assumption.
Proof. A sketch of the reduction would be as follows:
Assume that A is an adversary breaking the selective security of the signature scheme. Construct B breaking
the SIS as follows:
                                        r
   1. B receives the challenge matrix A ← Zn×m
                                           q   from its SIS challenger, and x ∈ {0, 1}ℓ from the
      adversary A.
                                       r
   2. B then samples R1 , . . . , Rℓ ←   {0, 1}m×m , and computes Bi ← ARi + xi G for all i ∈ [ℓ]. Then, B
      sends vk := (A, B1 , . . . , Bℓ ) and σx := (R1 , . . . , Rℓ ) to A. Note that by the LHL, the distribution
      of Bi ’s are uniform, as A and Ri ’s are random. Therefore, the distributions match the real scheme.
   3. B receives (f, y, σf,y ) from A, and computes and sends (RHf,x − Rf,y ) G−1 (0) to its challenger.
If A succeeds with non-negligible probability ϵ, then we can show that (RHf,x − Rf,y ) G−1 (0) is a so-
lution to SIS problem with respect to A. First, observe that by LHL, Bi ’s are uniform (and of the right
distribution of the signature scheme). Thus, upon receiving (f, y ∈ {0, 1}, σf,y = Rf,y ), and assuming A
succeeds, one can conclude that ||Rf,y ||∞ is small and ARf,y = Bf − y · G, while y ̸= f (x).
Based on the correctness of the signature scheme, ARHf,x = Bf − f (x) · G where R = [R1 | · · · | Rℓ ].
From A, ARf,y = Bf − y · G. Thus,
                                   A (RHf,x − Rf,y ) = (y − f (x)) · G
Note that y − f (x) ̸= 0 implying that y − f (x) ∈ {−1, +1}. Therefore,
                                         A (RHf,x − Rf,y ) = ±G
implying that (RHf,x − Rf,y ) is the trapdoor w.r.t. A. Having the above equation, B can find the SIS
solution w.r.t. A by computing G−1 (0) having the trapdoor.
                                      A (RHf,x − Rf,y ) G−1 (0) = 0
So (RHf,x − Rf,y ) G−1 (0) is going to be the SIS solution. Since the pre-image sampling is outputting
a random vector, this value will be non-zero with high probability.


                                                       92


<!-- pdf-page: 96 -->
Privacy. In applications, there are times that we might want the signature σf,f (x) = RHf,x to hide
information about x. This is not the case in the current scheme as the evaluation matrix Hf,x depends on
x, and in fact, is a function of x. Observe that Ri ’s have Gaussian distributions, which multiplying it with
a matrix that depends on x, will leak information about x by looking at the covariance of the vectors that
is going to depend on Hf,x . So the question is

                               Is there a way to make the signature private?

In previous lectures, we faced a similar problem in our signature scheme, where the signature R ·
G−1 (H(m)), was deterministic. To solve this, we used R as input to the pre-image sampler (as a trapdoor)
to make the signature randomized (so that the signature does not depend on the trapdoor). We will take
a similar approach for randomization here:
From the signing algorithm, ARf,f (x) = Bf − f (x)G, where Rf,f (x) = R · Hf,x is the signature on f (x).
We can rewrite this as ARf,f (x) = Bf − y · G, where y = f (x) ∈ {0, 1}.
We change our verification relation as follows: define a verification matrix V = [A | Bf + (y − 1) · G].
Rewrite V as follows:

                                   V = [A | Bf + (y − 1) · G]
                                                                  
                                     = A | ARf,f (x) + (2y − 1) · G
                                                             
                                     = A | ARf,f (x) + (±G)

Thus, we can find a trapdoor for this matrix as follows:
                                                              
                                                   −Rf,f (x)
                           V = A | ARf,f (x) + (±G) ·            = ±G
                                                        I
                          
                −Rf,f (x)
implying that                is a trapdoor for V.
                     I
Therefore, to re-randomize the solution, we just need to find a fresh solution from this lattice. So we are
going to prove that we have a signature without revealing the trapdoor, and we use this to as a pre-image
sampler. So we say that we have a trapdoor for this lattice because we have a solution for the SIS problem.
This property is called ”context-hiding”. In particular, we show that we can find a short t such that Vt = 0,
which hides the trapdoor, and can be used to randomize. This gives us needed randomization for the
signature scheme, to hide the original input, and achieve privacy.

Construction 24.3 (Homomorphic Commitments). These primitives can be viewed as dual of ”homomor-
phic signatures”. The idea behind homomorphic commitments is to commit to a value x, and open to f (x).
A vanilla idea of the scheme is sketched in the following:
                              r
    • Public parameters pp: A ← Zn×m
                                 q   .
                                    r
    • Commit to x: Sample Ri ←        {0, 1}m×m , and compute Ci ← ARi + xi G for all i ∈ [ℓ]. Let
      C = [C1 | · · · | Cℓ ] and R = [R1 | · · · | Rℓ ], and thus, C = AR + x ⊗ G.

    • Open to f (x): Compute Rf,f (x) := R · Hf,x

    • Verification relation: Check the equality ARf,f (x) + yG = Cf



                                                     93


<!-- pdf-page: 97 -->
Correctness: If y = f (x), then

                            ARHf,f (x) = (C − x ⊗ G) Hf,x = Cf − f (x)G

Observe that the commitments in this scheme can be really large. In particular, if we commit to a ℓ-bit string,
the commitment contains of ℓ matrices. So we want to construct succinct commitments (aka ”functional
commitments”).
The question if

                                           How can we compress?

Idea: Suppose pp contains the extra information as follows:
                                                            
                                      A                  W1
                                         A              W2 
                                              .           ..  (G)
                                                            
                                     
                                               . .        . 
                                                      A Wℓ
        r             r
where A ← Zn×m
           q   and Wi ← Zn×m
                         q   for all i ∈ [ℓ]. For simplicity, define Bℓ as
                                                                     
                                            A                     W1
                                             A                   W2 
                                      Bℓ =     ..                 .. 
                                                                     
                                                  .                . 
                                                               A Wℓ


Definition 24.4 (ℓ-succinct SIS). SIS is hard even with respect to A given B−1
                                                                            ℓ (G).

    Note that B−1
               ℓ (G) is a trapdoor for Bℓ :
                                                             
                                 A                      W1       R1
                                      A                 W2   .. 
                                                                  . 
                                                              
                                            ..           ..  ·   = 0
                                
                                               .          .  R 
                                
                                                                   ℓ
                                                     A Wℓ         T

which gives us the following linear system
                                         
                                         AR1 + W1 T = 0
                                         
                                         
                                           ..
                                           .
                                         
                                         AR + W T = 0
                                              ℓ  ℓ

As Wi T has a uniform distribution, it is going to be hard to find a SIS solution w.r.t. A from this system.
In next lecture, we see how to use the structure of this trapdoor (i.e. this ℓ-succinct SIS problem) as a way
to get succinct homomorphic commitments, known as “functional commitments”, which gives us functional
commitments for all circuits.




                                                      94


<!-- pdf-page: 98 -->
  CS 395T: Topics in Cryptography                                                            April 16, 2024

                             Lecture 25: Functional Commitments
  Lecturer: David Wu                                                                 Scribe: Elahe Sadeghi


Recap (Lattice Homomorphism). Let A ∈ Zqn×mℓ , where m = Ω(n log(q)).

   1. For all functions f : {0, 1}ℓ → {0, 1} computable by circuit of depth d, we can construct a matrix
      Hf ∈ Zmℓ×m
               q     , where ||Hf ||∞ ≤ mO(d) .

   2. For all functions f : {0, 1}ℓ → {0, 1} and all x ∈ {0, 1}ℓ , we can construct a matrix Hf,x ∈ Zmℓ×m
                                                                                                     q    ,
      where ||Hf,x ||∞ ≤ m   O(d) .

    From these matrices, we get ”key equation” that is used in lattice-based cryptography:
                                          
                              A − xT ⊗ G · Hf,x = A · Hf − f (x) · G

where we denote Af := A · Hf and A − xT ⊗ G = [A1 − x1 G | · · · | Aℓ − xℓ G]. Intuitively, the
                                                        

left hand-side of the above equation is multiplying an ”encoding of x w.r.t. A” by an evaluation matrix
Hf,x , and derive an ”encoding of f (x) w.r.t. Af ” on the right hand-side.

Functional Commitments. One of the motivations/applications of these commitments is the scenario
that a bank wants to design a ”single” fair algorithm to apply it to every client requesting a loan. Then
the bank can commit to the algorithm to decide whether one is eligible for getting loans, take some input
(client’s loan application), and then prove to client that the output value is consistent with the algorithm.
These primitives have two dual purposes of 1. commit to x and open to evaluation f (x), and 2. commit
to f and open to a value at f (x). These two are equivalent and in fact, from 1, one can define a universal
circuit as Ux (f ) := f (x), to derive 2.
The goal of this primitive is to have succinctness in commitments and openings. (i.e. they both are sub-linear
in the length of the input).
In the previous lecture, we defined a construction of homomorphic commitments where the commitments
were large. The goal is to construct a functional commitment derived from the previous construction with
a compression technique on top! To recall, Construction 24.3 was defined as follows:
                                     r
    • Public parameters pp: Sample A ← Zn×m
                                        q   .
                                        r
    • Commit to x ∈ {0, 1}ℓ : Sample R ←   {0, 1}m×mℓ . Compute C = AR + xT ⊗ G , where C is the
                                                                               

      commitment and R = [R1 | · · · | Rℓ ] is the opening.

    • Opening to function f : {0,1}ℓ → {0, 1}: Compute C − xT ⊗ G Hf,x = CHf − f (x)G, where
                                                                    

      from above, C − xT ⊗ G = AR, which gives us the following:

                                          A (RHf,x ) + f (x)G = CHf

      Denote Rf := RHf,x ∈ Zm×m
                            q   and Cf := CHf , implying that Cf is the new commitment and Rf
      is the new opening.

                                                     95


<!-- pdf-page: 99 -->
    • Verification relation: Given (pp, C, f, y, Rf ), the verifier computes Hf as it only depends on f and
      is computable, and then computes Cf = CHf . It then checks if Cf = ARf + yG, and whether
      ||Rf ||∞ is small.
    Observe that the openings in this scheme are in Zm×m
                                                     q    , which considered to be sub-linear in the length
of the input, ℓ, while the commitments are in Zn×mℓ
                                               q     , which is large.
                                            r                               r
Definition 25.1 (ℓ-succinct SIS). Suppose A ← Zn×m
                                                q       and W1 , . . . , Wℓ ←  q . Let
                                                                              Zn×t
                                                                  
                                          A                  W1
                                             A              W2 
                                    B=           .            .. 
                                                                  
                                                   . .         . 
                                                           A Wℓ
ℓ-succinct SIS problem (aka ”SIS with hints”) states that given A, B, and B−1 (G) (a trapdoor for B), it
is hard to find a non-zero solution x ∈ Zm
                                         q , such that Ax = 0 mod q, and ||x||∞ ≤ β.
The choice of parameter t (the dimension of the hint matrices), is important to ensure that the hints will
not help with breaking the SIS. So if t > mℓ, then SIS implies ℓ-succinct SIS.
    Observe that the hints in the above assumption is not going to immediately help to break the SIS
assumption. Suppose B−1 (0) is given as
                                         
                                         T1
                                                 
                                         ..    AT1 + W1 U = 0
                                                 
                                                 
                                         .       .
                              B (0) =   ⇒ ..
                                −1
                                         Tℓ    
                                                 
                                                 AT + W U = 0
                                          U            ℓ     ℓ

which is not going to help with finding the SIS solution immediately as Wi U’s distribution is uniform.

Homomorphic Commitment Compression. The idea is to use a variant of ℓ-succinct SIS assumption
in which t = m, in order to compress the commitments in Construction 24.3. In that construction, a
commitment was represented as C = [C1 | · · · | Cℓ ], where
                                     
                                     C1 = AR1 + x1 G
                                     
                                     
                                       ..
                                       .
                                     
                                     C = AR + x G
                                          ℓ          ℓ   ℓ

The distribution of C was said to be uniform by LHL, as the matrices Ri ’s are chosen randomly. However,
compressing randomness, without losing information, is hard, and therefore, the idea is to define the
commitments Ci ’s correlated.
Suppose Ci = Wi C, for C ∈ Zm×m   q     . In this case, the commitment algorithm only needs to output C, as
all the commitments C1 , . . . , Cℓ are computable assuming Wi ’s are known publicly. Thus, the goal is to
compute such a C.
C should sastisfy the following system:
                                                                              
                                                  A                 W1        R1
                                                                                           
              W1 C = AR1 + x1 G                                               .      −x1 G
              
                                                       A            W2   .   . 
              
                ..                                                             . = . 
                                                                              
                 .                           ⇒             .        ..  ·             .
                                                
                                                            . .     .     Rℓ 
                                                                                      −x  ℓG
              
              W C = AR + x G
                   ℓ           ℓ    ℓ                             A Wℓ       −C


                                                    96


<!-- pdf-page: 100 -->
                                                                   
                                         A                      W1
                                          A                    W2 
Based on ℓ-succinct SIS assumption, B =     ..                  .. . Therefore, it suffices to publish the
                                                                   
                                               .                 . 
                                                             A Wℓ
trapdoor B−1 (G) in the public parameters pp.

Construction 25.2 (Functional Commitment). We can construct a functional commitment scheme which
is similar to Construction 24.3 with the following changes:
                             r
    • Public parameter pp: A ← Zn×m
                                q   , W1 , . . . , Wℓ , and B−1 (G)

    • Commit to x: Compute C, R1 , . . . , Rℓ by using the trapdoor B−1 (G).

   Security. The security experiment between the challenger and the adversary A as follows:

   1. The challenger sends A, W1 , . . . , Wℓ , B−1 (G) to the adversary.
                                                                  
                                                                  C1 = W1 C
                                                                  
                                                                  
                                                                    .
   2. The adversary will eventually send (C, f, R0 , R1 ), and for ..                and Cf = [C1 | · · · | Cℓ ],
                                                                  
                                                                  
                                                                  C − ℓ = W C
                                                                            ℓ
                            (
                              Cf = AR0
      the adversary wins if                         and R0 , R1 are small.
                              Cf = AR1 + G

We say a functional commitment scheme is secure if the advantage of any efficient adversary in above
experiment is negligible.

Claim 25.3. Construction 25.2 is secure under ℓ-succinct SIS assumption.

Proof. sketch: If there exists an adversary A against the security experiment of Construction 25.2 with
non-negligible advantage, then we can construct the following adversary B solving ℓ-succinct SIS with
non-negligible advantage (as A’s advantage):

   1. B receives A, W1 , . . . , Wℓ , B−1 (G) from its challenger and forwards it to aA.
                                                 (
                                                   Cf = AR0
   2. It receives (C, f, R0 , R1 ) from A where                         and R0 , R1 are small.
                                                   Cf = AR1 + G

   3. B computes A(R0 − R1 ) = G, and therefore a trapdoor with respect to A. B then uses the trapdoor
      to solve the SIS assumption.




Intro to Attribute-Based Encryption for circuits.        To recall the intuitive notion of ABEs, the scheme
contains the following algorithms:

    • Setup(1λ ) → (msk, mpk)

    • Encrypt(mpk, x, m) → ct

                                                    97


<!-- pdf-page: 101 -->
    • KeyGen(msk, f ) → skf

    • Decrypt(sk, ct) → m: If f (x) = 0, then the decryption algorithm is able to decrypt, and not
      otherwise.

From LWE assumption, we can construct an ABE scheme that supports arbitrary policies for the keys, and
support any circuit f . To start, we use the idea of the ”dual Regev encryption scheme”. The dual Regev
encryption scheme is as follows:

    • KeyGen(1λ ) → (pk, sk): Given the security parameter λ, the key generation algorithm samples
         r             r
      A←   Z1n×m and r ←  {0, 1}m , and sets pk := (A, b = Ar) and sk := r.

    • Encrypt(pk, µ ∈ {0, 1}) → ct: Given the public key pk and the message µ, the encryption algorithm
                      r         r             r
      first samples s ← Znq , e ← χm , and e′ ← χ. It then outputs ct := (sT A + eT , sT b + e′ + µ⌊ 2q ⌉).

    • Decrypt(sk, (ct1 , ct2 )) → µ: Given the secret key sk and the ciphertext (ct1 , ct2 ), the decryption
                                             q
      algorithm computes ct2 − ctT                  ′   T
                                    1 r = µ⌊ 2 ⌉ + e + e r.

A comparison of the ”dual Regev” and ”Primal Regev” encryption schemes is illustrated in Fig. 25.1.
The security of this scheme is based on LHL and LWE. Based on the leftover hash lemma, b = Ar is
uniformly random, and therefore, by LWE, we can show that µ gets blinded by a uniform string.
Observe that r is a special component in dual Regev construction as having and LWE instance (sT A + eT )
with respect to A, we get a new LWE instance by multiplying with r, as (sT A + eT )r = sT b + eT r, with
respect to b.

 Dual Regev                                           Primal Regev
                  r                                                  r              r             r
  • KeyGen: A ← Zn×mq    ,                            • KeyGen: A ←     Zqn×m , s ←   Znq , and e ← χm .
      r
    r←  {0, 1}m . pk := (A, b = Ar) and sk := r.        pk := (A, b = sT A + eT ) and sk := s.
               r         r                                         r
  • Encrypt: s ← Znq , e ← χm and                     • Encrypt: r ←  {0, 1}m . ct := (Ar, bT + µ⌊ 2q ⌉)
       r
    e ← χ. ct := (s A + eT , sT b + e′ + µ⌊ 2q ⌉)
     ′             T




             Figure 25.1: Comparison of Dual Regev and Primal Regev Encryption Schemes.




                                                    98


<!-- pdf-page: 102 -->
  CS 395T: Topics in Cryptography                                                              April 18, 2024

                            Lecture 26: Attribute Based Encryption
  Lecturer: David Wu                                                                     Scribe: Nate Mikosh


Recap (Dual Regev)
                r        r
    • KeyGen: A ← Zn×m
                   q   ,r← {0, 1}m . pk := (A, b = Ar) and sk := r.
                        r         r           r
    • Encrypt(pk, µ): s ← Znq , e ← χm and e′ ← χ. ct := (sT A + eT , sT b + e′ + µ⌊ 2q ⌉)

    Looking at this construction, we can consider the following equation using the first part of the cipher text.

                                        sT A + eT r = sT Ar + eT r
                                                   


    eT r is too small to be significant, and b = Ar so we can consider this equation as:

                                          sT A + eT r = sT b + noise
                                                   


    So effectively, this allows us to take an LWE instance with respect to A and translate it into an instance
with respect to b. This is actually a very useful property for encryption, we can use this to switch between
keys to create a scheme for ABE. We’ll start by looking at a sketch of the construction, then the formal
construction, and finally the security proof.

Preliminary Construction Suppose we want to construct ABE for an attribute x ∈ {0, 1}ℓ and a policy
f : {0, 1}ℓ → {0, 1} If f (x) = 0, we are allowed to decrypt and if f (x) = 1, we are not allowed. We
will consider key-policy ABE where the secret key is associated with the policy f and the cipher text is
associated with the attribute x.

Algebraic Structure In order to create this encryption scheme, we need some way to encode an attribute
and then we need to compute on them (homomorphically). Being able to compute on it will allow us to
determine if f (x) = 0 or 1. Consider the following construction:
           r              r
    pk: A ←   Zn×m
                q   ,B←      Zn×mℓ
                               q
    In order to embed the attributes we can use (B − x ⊗ G) Recall that using the tensor function, this
gives us [B1 − x1 G | · · · | Bℓ − xℓ G]
    To enable homomorphic encryption we can use a homomorphic evaluation matrix.

                               (B − x ⊗ G) × Hf,x = B × Hf − f (x) × G

    When f (x) = 0, we are left with Bf and when f (x) = 1 we are left with Bf − G and we cannot learn
Bf .We can create a ciphertext to be a dual regev encryption with respect to [A | Bf ]




                                                       99


<!-- pdf-page: 103 -->
Encryption Setup:
       r           r           r
   A←      Zn×m
            q   B←    Zn×mℓ
                       q    u←    Znq
   [(A, tdA) ← trapGen (n, q)]
   pk: (A, B, u) sk: tdA
                          r        r        r      r
   Encrypt (pk, x, µ) : s ← Znq e ←   χm e′ ← χR←    {0, 1}m×m
   ct: s A + e , s (B − x ⊗ G) + e R, s u + e + µ⌊ 2q ⌉
          T     T   T                  T    T     ′
                                                           

   KeyGen(sk, f ): we only want to recode u when f (x) = 0.
   we can try sT (B − x ⊗ G) + eT R − Hf,x = sT (Bf − f (x)G)
   we need to use [A | Bf ]−1 for recoding
   zf = [A | Bf ]−1 (u)
   There is a new issue now though, that we have a trapdoor for A, but not a trapdoor for this whole
matrix. We can change our secret key to instead be a trapdoor T ∈ Zm×m
                                                                     q    where AT = G. So now
             
              T
[A | Bf ] ×     =G
              0

                       Decrypt(sk, ct) where sk = zf and ct is (c1, c2, c3) : ⌊c3 − c1T | c2T Hf,x zf ⌉
                                                                                                  
Final
    Construction
    c1T | c2T Hf,x = sT [A | Bf − f (x)G] + eT | eT RHf,x
                                                                 

   f (x) = 0 : sT [A | Bf ] + eT | eT RHf,x
   ×zf
   = sT [A | Bf ] zf + eT | eT RHf,x = sT u + error
                                       


Security Our ciphertext components are similar to LWE, and we can try to prove security by reducing
to LWE
    In fact, it seems like the only significant difference is that eT R in c2 should have a fresh error. Otherwise,
this construction would directly follow from LWE. However we cannot actually rely entirely on LWE. ABE
also requires there to be key generation and therefore a trapdoor. LWE does not allow for a trapdoor. We
need to be able to generate a key for functions that cannot decrypt, and not be able to for those that can. We
need possibly exponentially many keys and to not have a trapdoor. We can make this problem simpler by
relaxing to selective security, not adaptive security. The adversary will tell us the attribute in advance, but
we still need to be able to generate keys for exponentially many functions where f (x) = 1. We can consider
that we only have to generate a key when f (x) = 1 to help        us. Suppose
                                                                                we have the following relation:
                                                                   RHf,x
    ARHf,x = Bf − G ARHf,x − Bf = −G [A | Bf ]                              = −G
                                                                     −I
    We have managed to find a trapdoor, not for A, but for [A | Bf ],but only when f (x) = 1.

Selective Security Game Adversary starts by committing to an attribute x∗ ∈ 0, 1ℓ and receives in
return the public keys, A, B, andu. The adversary then sends a function f wheref (x∗ ) = 1 and the
challenger will respond with zf . Next the adversary will send the challenge, a message, µ. The challenger
                                                                                 q 
then responds based with either s A + e , s (B − x ⊗ G) , s u + e + µ⌊ 2 ⌉ or simply something
                                     T       T    T                T       ′

uniformly random. The adversary can continuously make key-gen queries after this.
                                                                                                  r
    We need to modify this somewhat to arrive at our final proof for security. We can sample A ←    Zn×m
                                                                                                       q
and set B = AR + (x ⊗ G).
                       ∗

    In our final game we have an LWE challenger, a reduction, and the adversary. The challenger samples
    r             r                                                                  r               r
A ←    Zn×m
        q     ,u ←  Znq and then either t1 = sT A + eT andt2 = sT u + e′ or t1 ←       Znq andt2 =←      Znq .
This give us an LWE instance of (A, u, t1 , t2 ). The adversary again starts by committing to an attribute


                                                       100


<!-- pdf-page: 104 -->
x∗ ∈ 0, 1ℓ and gets back the public keys,A, B = AR + (x∗ ⊗ G), andu. The adversary can then make
a keygen query, sendingf wheref (x∗ ) = 1 and we respond with zf = [A | Bf ]−1 (u). Remember that
                          RHf,x
we can use our trapdoor             to compute this efficiently. And now for every message µ the adversary
                           −I
                                               q
sends, we can respond with tT     T
                             1 , t1 R, t2 + µ⌊ 2 ⌉




                                                   101


<!-- pdf-page: 105 -->
Bibliography

[Ber06]    Daniel J. Bernstein. Curve25519: New Diffie-Hellman speed records. In PKC, pages 207–228,
           2006.

[BF01]     Dan Boneh and Matthew K. Franklin. Identity-based encryption from the weil pairing. In
           CRYPTO, pages 213–229, 2001.

[BG04]     Daniel R. L. Brown and Robert P. Gallant. The static diffie-hellman problem. IACR Cryptol.
           ePrint Arch., page 306, 2004.

[BGLS03]   Dan Boneh, Craig Gentry, Ben Lynn, and Hovav Shacham. Aggregate and verifiably encrypted
           signatures from bilinear maps. In EUROCRYPT, pages 416–432, 2003.

[BGN05]    Dan Boneh, Eu-Jin Goh, and Kobbi Nissim. Evaluating 2-dnf formulas on ciphertexts. In TCC,
           pages 325–341, 2005.

[BGW05]    Dan Boneh, Craig Gentry, and Brent Waters. Collusion resistant broadcast encryption with
           short ciphertexts and private keys. In CRYPTO, pages 258–275, 2005.

[BLS01]    Dan Boneh, Ben Lynn, and Hovav Shacham. Short signatures from the weil pairing. In
           ASIACRYPT, pages 514–532, 2001.

[BLS02]    Paulo S. L. M. Barreto, Ben Lynn, and Michael Scott. Constructing elliptic curves with
           prescribed embedding degrees. In SCN, pages 257–267, 2002.

[CBBZ22] Binyi Chen, Benedikt Bünz, Dan Boneh, and Zhenfei Zhang. Hyperplonk: Plonk with
         linear-time prover and high-degree custom gates. Cryptology ePrint Archive, Paper 2022/1355,
         2022. https://eprint.iacr.org/2022/1355.

[Che06]    Jung Hee Cheon. Security analysis of the strong diffie-hellman problem. In EUROCRYPT, pages
           1–11, 2006.

[Gen09]    Craig Gentry. A fully homomorphic encryption scheme. PhD thesis, Stanford University, 2009.
           crypto.stanford.edu/craig.

[GGSW13] Sanjam Garg, Craig Gentry, Amit Sahai, and Brent Waters. Witness encryption and its
         applications. In STOC, pages 467–476, 2013.

[GOS06]    Jens Groth, Rafail Ostrovsky, and Amit Sahai. Perfect non-interactive zero knowledge for NP.
           In EUROCRYPT, pages 339–358, 2006.



                                                 102


<!-- pdf-page: 106 -->
[GPSW06] Vipul Goyal, Omkant Pandey, Amit Sahai, and Brent Waters. Attribute-based encryption for
         fine-grained access control of encrypted data. In ACM CCS, pages 89–98, 2006.

[GPV08]    Craig Gentry, Chris Peikert, and Vinod Vaikuntanathan. Trapdoors for hard lattices and new
           cryptographic constructions. In Proceedings of the Fortieth Annual ACM Symposium on Theory
           of Computing, pages 197–206, 2008.

[GSW13]    Craig Gentry, Amit Sahai, and Brent Waters. Homomorphic encryption from learning with
           errors: Conceptually-simpler, asymptotically-faster, attribute-based. Cryptology ePrint
           Archive, Paper 2013/340, 2013. https://eprint.iacr.org/2013/340.

[GWC19]    Ariel Gabizon, Zachary J Williamson, and Oana Ciobotaru. Plonk: Permutations over lagrange-
           bases for oecumenical noninteractive arguments of knowledge. Cryptology ePrint Archive, 2019.

[Jou00]    Antoine Joux. A one round protocol for tripartite diffie-hellman. In ANTS, pages 385–394, 2000.

[KMW23] Dimitris Kolonelos, Giulio Malavolta, and Hoeteck Wee. Distributed broadcast encryption
        from bilinear groups. In ASIACRYPT, pages 407–441, 2023.

[KZG10]    Aniket Kate, Gregory M Zaverucha, and Ian Goldberg. Constant-size commitments to
           polynomials and their applications. In Advances in Cryptology-ASIACRYPT 2010: 16th
           International Conference on the Theory and Application of Cryptology and Information Security,
           Singapore, December 5-9, 2010. Proceedings 16, pages 177–194. Springer, 2010.

[MVO91]    Alfred Menezes, Scott A. Vanstone, and Tatsuaki Okamoto. Reducing elliptic curve logarithms
           to logarithms in a finite field. In STOC, pages 80–89, 1991.

[Reg05]    Oded Regev. On lattices, learning with errors, random linear codes, and cryptography. In
           Proceedings of the Thirty-Seventh Annual ACM Symposium on Theory of Computing, pages 84–93,
           2005.

[SW05]     Amit Sahai and Brent Waters. Fuzzy identity-based encryption. In EUROCRYPT, pages 457–473,
           2005.

[SW14]     Amit Sahai and Brent Waters. How to use indistinguishability obfuscation: deniable encryption,
           and more. In STOC, pages 475–484, 2014.

[WW22]     Brent Waters and David J. Wu. Batch arguments for np and more from standard bilinear group
           assumptions. In CRYPTO, pages 433–463, 2022.




                                                  103

