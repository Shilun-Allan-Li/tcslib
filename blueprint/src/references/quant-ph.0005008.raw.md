<!-- generated-by: proofmatch local extraction -->
<!-- source-pdf-sha256: 1ac7bb3b99ccdf62d030950bdeb31f5b8c6a3e1636142eadf899093d0203b829 -->
<!-- extractor: pdfminer.six v20260107 -->

<!-- pdf-page: 1 -->
0
0
0
2

y
a
M
1

1
v
8
0
0
5
0
0
0
/
h
p
-
t
n
a
u
q
:
v
i
X
r
a

Nonbinary Quantum Stabilizer Codes

Alexei Ashikhmin ∗

Emanuel Knill †

Abstract

We deﬁne and show how to construct nonbinary
quantum stabilizer codes. Our approach is based
It generalizes the rela-
on nonbinary error bases.
tionship between selforthogonal codes over F4 and
binary quantum codes to one between selforthogo-
nal codes over Fq2 and q-ary quantum codes for any
prime power q.

Index Terms — quantum stabilizer codes, nonbi-

nary quantum codes, selforthogonal codes.

prime) quantum stabilizer codes generalizing the F4
constructions for binary quantum codes.

Here we consider the problem of constructing
pm-ary quantum codes from classical selforthogo-
nal codes over Fp2m . The notion of selforthogonal-
ity arises naturally from the error bases of [10, 11]
and can be identiﬁed with that arising from a ﬁeld-
theoretically deﬁned simplectic form. Good self-
orthogonal codes with respect to this form have al-
ready been found by Bierbrauer and Edel [5], and our
construction can be used to obtain associated quan-
tum codes.

1

Introduction

2 Basic Deﬁnitions

Probably the most important class of binary quan-
tum codes are quantum stabilizer codes. They play
a role similar to the linear codes in classical coding
theory. Quantum stabilizer codes have simple encod-
ing algorithms, can be analyzed using classical coding
theory, and yield methods for fault tolerant quantum
computation. The ﬁrst examples of quantum codes
found by Shor [17], and Steane [19, 20] were quantum
stabilizer codes. General quantum stabilizer codes
were introduced by Gottesman [8] and Calderbank
et. al. [6]. Later Calderbank et. al. [7] gave the
now standard connection between quantum stabilizer
codes and classical selforthogonal codes, which was
used to construct a number of new good quantum
codes.

While the theory of binary quantum stabilizer
codes is now well developed, nonbinary codes have
been relatively ignored. A connection between clas-
sical codes over Zn and quantum codes is given
in [10, 11]. The connection is based on a stabilizer
construction derived from so-called nice error bases.
Raines [15] obtained a number of results for p-ary (p

∗Bell Laboratories, Lucent Technologies, 600 Mountain

Ave., Rm.: 2C-180, Murray Hill, NJ 07974.

†Los Alamos National Laboratory Group CIC-3, Mail Stop

B265, Los Alamos, NM 87545.

We start with the basic notions of classical and quan-
tum coding theory. Denote by Fpm the Galois ﬁeld
of pm elements, where p is a prime number and m is
an integer. Let α1, α1, . . . , αm denote the elements of
a basis of Fpm over Fp. We ﬁx a non-zero Fp-linear
Fp (called a trace function).
functional tr : Fpm
Thus tr satisﬁes

→

tr(a + b) = tr(a) + tr(b),

tr(αa) = αtr(a),

i

∈

∈

Fpm, α

Fp. Note that for x

Fpm ,
for all a, b
trx(a) = tr(xa) deﬁnes another trace function, and
that all such functions can be obtained this way. The
standard trace function is the one deﬁned by view-
ing Fpm as an extension of Fp and letting tr(a) =

∈

, [14, Chapter 2.3].

m−1
i=0 ap
Let t divide m. A classical pt-linear code C over a
P
ﬁeld Fpm of length n and size (pt)k, is a k dimensional
pt-linear subspace of the space Fn
pm. In other words,
for any a, b from C and any α, β
Fpt the vector
αa + βb is also from C. Let
be a Fpt -bilinear form
(an inner product ). A code C is selforthogonal for
if
for all vectors a and b from C the following property
holds

∈

∗

∗

b = 0.

a

∗

(1)

1

 
 
 
 


<!-- pdf-page: 2 -->
The code C⊥ =
dual of C with respect to (1).

v : v

{

∗

a = 0 for

a

∀

C

}

∈

is called

span of
operators of the form (2).

E

. For this reason it makes sense to focus on

Remark For an introduction to the theory of Ga-

lois Fields and classical codes see e.g. [14].

A q-ary quantum code Q of length n and size
K is a K-dimensional subspace of a qn-dimensional
Hilbert space. This Hilbert space is identiﬁed with
the n-fold tensor product of q-dimensional Hilbert
spaces. The q-dimensional spaces are thought of as
the state spaces of q-ary systems in the same way as
the values 0 and 1 can be thought of as the possible
states of a bit in a bit string. We identify the state
spaces with the q-dimensional complex linear space
Cq. An important characteristic of a quantum code
is its minimum distance. If a code has minimum dis-
1 and correct any
tance d then it can detect any d
errors. As a result it is desirable to keep d as
⌊
large as possible. A strict deﬁnition of the minimum
distance is given in the next section after introducing
error bases.

d−1
2 ⌋

−

Remark For introductions to the theory of quan-
tum error correcting codes see e.g. [12, 9, 13]. For a
reader with a background in classical coding theory
the papers [1, 2, 3] have brief introductions to the
ﬁeld.

3 Error Basis

i

A general quantum error of a pm-ary quantum sys-
tem, is a linear operator acting on the space Cpm. If
v
is a state (a unit vector in the space) of the sys-
|
tem, then the eﬀect of error E is to transform it to
the state E
. It is convenient to conﬁne ourselves
i
to errors that form a basis of the vector space of lin-
ear operators acting on Cpm . Let linear operators
e1, e2, . . . , ep2m form such a basis. If
represents
a state of n pm-ary systems it can be altered by an
error operator of the form

v

v

i

|

|

It is always possible to determine operators e1,
e2, . . . , ep2m in such a way that one of them, say e1,
is the identity operator Ipm . Deﬁne the weight of E
in (2) as

.

}|

(3)

= Ipm

wt(E) =

σi 6
|{
In the depolarizing channel model of errors [4], the
operators e2, e3, . . . satisfy Tr(e†
i ej) = pmδi,j, where
Tr is the trace of linear operators. When transmitting
a qubit through a depolarizing channel, the probabil-
ity that it is untouched (i.e. aﬀected by the identity
r and the probability that it is aﬀected
operator) is 1
by ei, i > 1, is r/(p2m
1). Thus, the probability of an
error operator decreases exponentially with weight, a
feature common to most realistic error models [13].
This explains why it is desirable to correct or detect
all error operators up to some given weight.

−

−

Let P be the orthogonal projection operator onto
Q. It can be shown that (see e.g. [10]) an error oper-
ator E is detectable by Q iﬀ

P EP = cEP.

(4)

The largest integer d such that every error of weight
d
1 or less can be detected by a code is called its
minimum distance.

−

We now deﬁne an explicit error basis for pm-ary
quantum codes. Let T and R be linear operators
acting on the space Cp deﬁned by the matrices with
entries

Ti,j = δi,j−1mod p and Ri,j = ξiδi,j,

where ξ = eι2π/p, ι = √
0 to p

−
1 [10]. It is easy to check that

1 and the indices range from

−

T R = ξRT

and therefore

σ2 ⊗
E = σ1 ⊗
e1, e2, . . . , ep2m

. . .

⊗

σn,

(2)

}

where σi ∈ {
. A general error oper-
ator is a linear operator acting on the n-fold tensor
product of Cpm. Any such operator can be written
down as a linear combination of error operators of the
form (2). It is well known from the general theory of
quantum codes that if a code can correct a given set
of error operators, then it can correct the linear

E

T iRj = ξij RjT i,
T kRl
T kRl

= ξil−jk
= ξ−jkT i+kRj+l.
(cid:1) (cid:0)
(cid:0)

T kRl

(cid:1)

T iRj
T iRj
(cid:0)

(cid:1) (cid:0)

T iRj

(5)
, (6)

(cid:1)

(7)

(cid:0)

(cid:1) (cid:0)
The Hermitian transposes of T i and Ri are obtained
by raising to the power p

1:

(cid:1)

−
(T i)† = (T i)p−1, (Ri)† = (Ri)p−1.

(8)

2



<!-- pdf-page: 3 -->
Note that

T p = Rp = Ip.

(9)

From (7) and (9) it follows that for p > 2

(T iRj)p = ξ−ij(1+2+...+(p−1)) = Ip.

(10)

Since Tr(T iRj) = 0 except when i = j = 0
mod p, the operators T iRj form an orthogonal oper-
ator basis under the usual inner product for operators
= Tr(A†B). Let a, b
Fpm. Using a
given by
basis of Fpm over Fp, we can write uniquely

A, B
h

∈

i

a = a1α1 + a2α2 + . . . + amαm,
b = b1α1 + b2α2 + . . . + bmαm,

with the ai and bi in Fp. Deﬁne

TaRb = (T a1

T a2

. . .

⊗

⊗

⊗

T am)(Rb1

Rb2

. . .

⊗

⊗

⊗

Rbm).

The operators TaRb then form an orthonormal basis.
The multiplication rules given above can be general-
ized. Deﬁne

a, b
h

i

=

m

i=1
X

aibi ∈

Fp.

(11)

From (7) and the identity (A
it follows that

⊗

B)(C

⊗

D) = AC

BD

⊗

(TaRb)(TcRd) = ξ−hb,ciTa+cRb+d.

(12)

(6) and (11) yield

(TaRb)(TcRd) = ξha,di−hb,ci(TcRd)(TaRb).

(13)

4 Nonbinary Stabilizer Codes

Let a† = (a(1), a(2), . . . , a(n)), b† = (b(1), b(2), . . . , b(n))
be vectors from the space Fn
(Throughout this
section we use superscripts to label the systems.) As
discussed in the previous section, it is enough to con-
sider the error operators given by

pm.

Ea,b = Ta(1) Rb(1)

Ta(2) Rb(2)

. . .

⊗

⊗

⊗

Ta(n)Rb(n) .

(14)

is generated by ξI and therefore has order p. For
vectors a, d

pm deﬁne an inner product by

Fn

∈

a, d
h

i

=

n

i=1
X

a(i), d(i)
h

,
i

(15)

where
(13) that

a(i), d(i)
h

i

is deﬁned in (11).

It follows from

Ea,bEc,d = ξha,di−hb,ciEc,dEa,b.

(16)

From (12) we have

Ea,bEc,d = ξ−hb,ciEa+c,b+d.

(17)

From (14) and (10) it follows that for any a and b
and p > 2,

Ep

a,b = Ipmn .

(18)

Quantum stabilizer codes are deﬁned as joint eigenspaces

|

|

S

Z

.
of the operators of a commutative subgroup S of
E
If
Without loss of generality, assume that
S.
Z ⊆
. The order of S
this is not the case, extend S by
= pr+1. The joint eigenspaces
is a power of p,
of S are associated with linear characters µ of the
group S whose value µ(E) is the eigenspace’s eigen-
value with respect to E. Clearly it must be the case
that µ(ξI) = ξ. Let µ be any one of the pr characters
of S which satisfy this constraint. We deﬁne a quan-
tum stabilizer code Q as the eigenspace associated
with µ. To determine the dimension of Q, consider
the orthogonal projection operator P on Q, which
can be written in the form

P =

1
S

|

| XE∈S

¯µ(E)E.

Since for E

∈ E \ Z

, Tr E = 0, we have

dim Q = Tr P

p−1

¯µ(ξiI) Tr(ξiI)

=

=

1
S

|

|
1
pr+1

i=0
X

p−1

i=0
X

= pmn−r.

pmn

The set of operators
≤
E
form a group of order p2mn+1. The center

=

≤

ξiEa,b

{

0

i

|

p

Z

−
of

1

}
E

Hence Q is an [[n, mn

−

r]]pm quantum stabilizer code.

We next establish a connection between quantum
stabilizer and classical selforthogonal codes. Note

3



<!-- pdf-page: 4 -->
that since the error basis is obtained as a tensor prod-
uct of p-ary error bases, stabilizer codes can be viewed
as standard p-ary stabilizer codes. This situation is
essentially the same as for classical linear codes over
Fpm . However, since the goal is to protect against
errors on pm-ary systems, we wish to usefully relate
pm-ary stabilizer codes to classical codes over Fp2m.
First we show how to construct a classical code
from a quantum code. Let ϕ be an isomorphism of the
vector space Fm
Ea,b
p . Clearly the set C =
is an Fp-linear code of length 2n and size pr.
S
Moreover, since all operators from S commute the
following property holds for any two vectors (a, b)
and (a′, b′) from C

(a, ϕ−1b)
|

{

}

a, ϕ(b′)
h

a′, ϕ(b)
i

i − h

= 0.

(19)

Thus C is selforthogonal with respect to the inner
product deﬁned by (a, b)
i −
a′, ϕ(b)
. Later we will choose ϕ to relate the in-
h
i
ner product to the structure of Fpm.

a, ϕ(b′)
h

(a′, b′) =

∗

The minimum distance of a stabilizer code deﬁned
by S is related to the classical minimum distance of
C⊥
C, where C⊥ is the dual code of C with respect
to (19). Deﬁne the weight of v = (a, b)

F2n

\

pm as

wt(v) =

|{

i : a(i)

= 0 or b(i)

∈
= 0

.

}|

Using arguments similar to ones from [6], one can
show that the minimum distance of a stabilizer code
. For complete-
of S equals min
ness we give a general proof of this fact.

wt(v) : v

C⊥

C

∈

{

\

}

Denote by S⊥ the group of operators in

that
commute with all operators from S. Thus S⊥ is given
by S⊥ =
ξiEa,b : (a, b)
. The desired fact
{
follows from the observation that E′
is detectable
iﬀ E′
S⊥
S. Let P be as deﬁned earlier. We
consider three cases.

C⊥

∈ E

∈

6∈

E

\

}

1. Let E′

S. Then

∈
E′P =

|

=

1
S

1
S

¯µ(E)E′E

| XE∈S

¯µ((E′)†E)E

|

| XE∈S
= µ(E′)P ,

6∈
E

S⊥. Let Si, 0

2. Let E′
Si =
and the assumption, it follows that
Thus

i < p, be deﬁned by
. Then from (16)
/p.
Si|

S : E′E = ξiEE′

≤

=

∈

S

{

}

|

|

|

∈

S

|

|

P E′P =

¯µ(E)EE′P

XE∈S
= E′

p−1

ξi ¯µ(E)EP

i=0
X
p−1

XE∈Si

= E′

ξiP

i=0
X
p−1

XE∈Si

ξiP

/p

S

|

|

= E′

= 0,

i=0
X

(21)

(22)

where we used (20) in the third to last step.
Again, E′ is detectable.

3. Let E′

S⊥

\

∈

S. By taking T to be the com-
mutative subgroup generated by S and E′ and
extending the character µ to T , a subcode Q′
of Q is obtained corresponding to the extended
character. The dimension of Q′ is smaller by
a factor of p, which implies that Q is not an
eigenspace of E′. Since E′ commutes with S,
E′ preserves Q. All of this implies that P E′P
is not proportional to P .

The inner product deﬁned in (19) depends on the
isomorphism ϕ. Clearly, the set of codes obtained
does not depend on ϕ, so the choice of ϕ is primarily
one of convenience. We now standardize this choice
to simplify the construction of large minimum dis-
tance codes. With respect to our distinguished basis
m matrix M over Fp.
of Fpm, ϕ is given by an m
Choose M by deﬁning

×

Mi,j = tr(αiαj).
With aT = (a1, a2, . . . , am), bT = (b1, b2, . . . , bm)
Fpm, we compute

∈

aT M b =

m

m

i=1
X
m

j=1
X
m

aibj tr(αiαj)

(20)

=

tr(aibjαiαj)

where the last equality follows from linearity of
µ. Thus

P E′P = µ(E′)P

and hence E′ is detectable.

i=1
X

j=1
X

m

= tr

aiαi

i=1
X

= tr(ab),

m

!  

i=1
X

biαi

!!

4

6
6
  


<!-- pdf-page: 5 -->
where the product in the trace is multiplication in
Fpm . For vectors a and b in Fn
i∗ =
i a(i)b(i). With this choice of ϕ, C is therefore self-
orthogonal with respect to the inner product deﬁned
P
by

a, b
h

pm ,

let

(a, b)

a, b′
(a′, b′) = tr(
h

∗

a′, b

i∗ − h

i∗).

(23)

|

|

r

C

−

≤

≤

We can now construct a quantum stabilizer code
= pr. Let
from a classical selforthogonal code C,
vectors vi = (ai, bi), 0
1 form a basis of
i
C over Fp. Then the pr operators Eai,φ(bi) together
with ξIpmn generate a group of commuting operators
of order pr+1, which deﬁnes [[n, mn
r]]pm stabilizer
wt(v) : v
codes with minimum distance d = min
{
C⊥

\
In [5] a number of families of good classical codes
that are selforthogonal with respect to the inner prod-
uct

−

C

∈

}

.

∗

i∗

(24)

a′, b

(a, b)

i∗ − h

(a′, b′) =

a, b′
h
where constructed. Since a code that is selforthogo-
nal with respect to (24) is also selforthogonal with
respect to (23), our results establish a previously
missing connection between the classical codes de-
ﬁned in [5] and quantum codes. Thus we already
have many good nonbinary stabilizer codes. For in-
stance from [5] we can obtain quantum stabilizer
[[q2 +
codes with parameters [[qr, qr
1, q2
1)/(q2
[[(qr+2
−
(r + 2), 3]]q (r is even) ,
1)
1), q3(qr−1
others.

−
−
(r + 2), 3]]q (r is odd) , and

(r + 2), 3]]q,
−
1), (qr+2
−
[[q3(qr−1

1)/(q2
1)/(q2

1)/(q2

3, 3]]q,

−
−

1)

−

−

−

−

−

In conclusion, we note that if a code is Fpm -linear
and is selforthogonal with respect to (23) then it is au-
tomatically selforthogonal with respect to (24). Since
this does not hold for general Fp-linear codes, one ex-
pects to ﬁnd better codes selforthogonal with respect
to (23) in this class.

Acknowledgements. E. K. was supported by fund-
ing from NSA and DOE.

References

[1] A. Ashikhmin and S. Litsyn, “Upper bounds of
the size of quantum codes,” IEEE Trans. Info.
Theory, vol 45, no. 4, pp.1205-1215, 1999.

5

[2] A. Ashikhmin, A. Barg, E. Knill, and S. Litsyn,
“Quantum Error Detection I: Statement of the
Problem ,” IEEE Trans. Info. Theory, to appear
.

[3] A. Ashikhmin, A. Barg, E. Knill, and S. Litsyn,
“Quantum Error Detection II: Bounds ,” IEEE
Trans. Info. Theory, to appear .

[4] C. H. Bennett, D. P. DiVincenzo, J. A. Smolin
and W. K. Wootters, “Mixed state entanglement
and quantum error-correcting codes,” Phys. Rev.
A, vol. 54, pp. 3824–, 1996.

[5] J. Bierbrauer and Y. Edel, “Quantum Twisted
Codes,” preprint, 1998. (The paper is available
at “http://www.math.mtu.edu/

jbierbra/”.)

∼

[6] A.R. Calderbank, E.M. Rains, P.W. Shor and
N.J.A. Sloane, “Quantum error correction and
orthogonal geometry,” Phys. Rev. Lett., vol. 78,
pp. 405-409, 1997.

[7] A.R. Calderbank, E.M. Rains, P.W. Shor and
N.J.A. Sloane, “Quantum errors correction via
codes over GF (4),”IEEE Trans. Info. Theory,
vol. 44, pp.1369 –1387, 1998.

[8] D. Gottesman, “A class of quantum error-
correcting codes saturating the quantum Ham-
ming bound,” Phys. Rev. A, vol.54, pp. 1862-
1868, 1996.

[9] D. Gottesman, “Stabilizer Codes and Quan-
tum Error Correction,” Ph.D. Thesis, Califor-
nia Institute of Technology, Pasadena, Califor-
nia, 1997.

[10] E. Knill, “Non-binary Unitary Error Bases
and Quantum Codes,” LANL Preprint, quant-
ph/9608048, 1996.

[11] E. Knill, “Group Representations, Error Bases
and Quantum Codes,” LANL Preprint, quant-
ph/9608049, 1996.

[12] E. Knill and R. Laﬂamme, “A theory of quantum
error correcting codes,” Phys. Rev. A, vol. 55,
pp. 900-911, 1997.

[13] E. Knill, R. Laﬂamme and L. Viola, “Theory
of quantum error correction for general noise”,
Phys. Rev. Lett., vol. 84, pp. 2525-2528, 2000.



<!-- pdf-page: 6 -->
[14] F. J. MacWilliams and N. J. A. Sloane, The The-
ory of Error-Correcting Codes, New York:
North-Holland, 1977.

[15] E. Rains, Nonbinary quantum codes, LANL e-

print quant-ph/9703048.

[16] P.W. Shor, “Polynomial-time algorithms for
prime factorization and discrete logarithms on
a quantum computer,” Proceedings of the 35th
Annual Symposium on the Foundations of Com-
puter Science, S.Goldwasser, Editor, IEEE Com-
puter Society Press, Los Alamitos, CA, p.124,
1994.

[17] P.W. Shor, “Scheme for reducing decoherence in
quantum memory,” Phys. Rev. A, 52, p. 2493,
1995.

[18] P.W. Shor and R. Laﬂamme, “Quantum analog
of the MacWilliams identities in classical coding
theory,” Phys. Rev. Lett., vol. 78, pp. 1600-1602,
1997.

[19] A. M. Steane, ”Simple quantum error correct-
ing codes,” Phys. Rev. Lett.,vol. 77, pp. 793-797,
1996.

[20] A. M. Steane, ”Multiple particle interference and
quantum error correction,” Proc. Roy. Soc. Lon-
don A, vol. 452, pp. 2551-2577, 1996.

6


