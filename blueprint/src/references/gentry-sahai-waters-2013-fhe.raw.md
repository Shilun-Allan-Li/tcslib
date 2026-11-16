<!-- generated-by: scoped Poppler extraction of the passages used (DW-7) -->
<!-- source-pdf-sha256: 8edb94cfd852a88a8684adbf81b73e78bd21466514b7bb7000d7df1e4431bf00 -->
<!-- extractor: pdftotext version 24.02.0; -layout; scoped to the line ranges listed below -->
<!-- scope (physical page: lines of the -layout text): p1: 1-5; p4: 153-199; p5: 200-248; p6: 249-286; p8: 374-394; p9: 395-447; p10: 448-495; p11: 496-544; p12: 545-578 -->
<!-- note: physical page = printed page -->

<!-- pdf-page: 1 -->
        Homomorphic Encryption from Learning with Errors:
     Conceptually-Simpler, Asymptotically-Faster, Attribute-Based
                          Craig Gentry∗                Amit Sahai†               Brent Waters‡

                                                      June 8, 2013

<!-- pdf-page: 4 -->
    As with all current FHE schemes without bootstrapping, the parameters and per-gate complex-
ity of evaluation depend on the multiplicative depth L of the circuit. “Bootstrapping” [Gen09],
together with an assumption of circular security, remains the only known way of making these
performance metrics independent of L, and while the overhead of bootstrapping is high, it becomes
an attractive option once L passes some threshold. However, our scheme loses some of its advan-
tages once bootstrapping is used. First, to apply bootstrapping, the evaluator needs to obtain the
user’s secret key encrypted under its public key – in effect, an evaluation key – and therefore we no
longer achieve identity-based/attribute-based FHE in this context. Second, this encrypted secret
key has quasi-cubic size in our scheme, and while this can be mitigated by public key compres-
sion techniques [CNT12], it eliminates the space complexity advantages of our scheme. Essentially,
bootstrapping returns us to the realm of “unnatural” operations, with all of its disadvantages.
It remains a fascinating open problem to find some “natural” alternative to bootstrapping, and
(relatedly) to achieve “pure” FHE without an assumption of circular security.

1.3     An Overview of Our FHE Scheme
Our main insight is that we can achieve LWE-based homomorphic encryption where homomorphic
addition and multiplication correspond directly to matrix addition and multiplication.

1.3.1     Homomorphic Operations
Let us skip key generation and encryption for the moment, and jump directly to the homomorphic
operations (and decryption).
    In our scheme, for some modulus q and dimension parameter N to be specified later, a ciphertext
C is a N × N matrix over Zq , with “small” entries (much smaller than q) and the secret key ~v is a
N -dimensional vector over Zq with at least one “big” coefficient vi . We restrict the message µ to
be a “small” integer. We say C encrypts µ when C · ~v = µ · ~v + ~e, where ~e is a “small” error vector.
To decrypt, we extract the i-th row Ci from C, compute x ← hCi , ~v i = µ · vi + ei , and output
µ = bx/vi e. In a nutshell, the essence of our scheme is that the secret key ~v is an approximate
eigenvector of the ciphertext matrix C, and the message µ is the eigenvalue.
    Now, let us see why matrix addition and multiplication are correct homomorphic operations.
Suppose C1 and C2 encrypt µ1 and µ2 in that Ci · ~v = µi · ~v + ~ei for small ~ei . Let C + = C1 + C2
and C × = C1 · C2 . For addition, we have C + · ~v = (µ1 + µ2 ) · ~v + (~e1 + ~e2 ), where the error likely
has grown a little, as usual in FHE schemes. But assuming the error is still “small”, the sum of
the ciphertext matrices encrypts the sum of the messages. For multiplication, we have

        C × · ~v = C1 · (µ2 · ~v + ~e2 ) = µ2 · (µ1 · ~v + ~e1 ) + C1 · ~e2 = µ1 · µ2 · ~v + µ2 · ~e1 + C1 · ~e2
                 = µ1 · µ2 · ~v + small

where the final error vector is hopefully “small”, since µ2 , C1 , ~e1 , and ~e2 are all small. If so, the
product of the ciphertext matrices encrypts the product of the messages. Interestingly, C2 · C1 is
also an encryption of µ1 · µ2 , even though matrix multiplication is not commutative.
    To simplify further, it might be helpful to imagine an error-free version of the scheme, where
Ci · ~v = µi · ~v exactly. In this case, the key ~v is an (exact) eigenvector of ciphertext matrices, and
the message µi is the eigenvalue. In general, if matrices C1 and C2 have a common eigenvector ~v
with eigenvalues µ1 and µ2 , then C1 · C2 and C2 · C1 have eigenvector ~v with eigenvalue µ1 · µ2 .


                                                           4

<!-- pdf-page: 5 -->
    Of course, in our scheme, the secret key ~v is only an approximate eigenvector, not an exact one.
Introducing error is necessary to base the security of our scheme on LWE. The cost of making ~v
only an approximate eigenvector is that certain terms in our scheme must be “small” to ensure
that homomorphic operations do not disrupt the essential form of the ciphertexts. We call our new
approach to LWE-based (homomorphic) encryption the approximate eigenvector method.

1.3.2     Bounding the Error and Somewhat Homomorphic Encryption
Although we have not fully specified the scheme, let us go ahead and estimate how homomorphic
it is. The scheme above works correctly until the coefficients of the error vector begin to approach
q in magnitude. How many homomorphic operations can we perform before that happens?
     Suppose C1 and C2 are B-bounded ciphertexts, in the sense that µi and the coefficients of Ci
and ~ei all have magnitude at most some bound B. Then, C + is 2B-bounded, and C × is (N + 1)B 2 -
                                                         L
bounded. In short, the error level grows worse than B 2 , doubly exponentially with the multiplicative
depth L of the circuit being evaluated. Alternatively, if one wants to consider the degree (rather than
depth) of functions that can be evaluated, if we evaluate a multivariate polynomial P (x1 , . . . , xt ) of
total degree d, on B-bounded ciphertexts as input, the final ciphertext is |P |(N +1)d−1 B d -bounded,
where |P | is the `1 -norm of P ’s coefficient vector. Taking q to comfortably exceed this bound, we
(roughly) can evaluate polynomials of degree logN B q. Since q/B must be subexponential (at most)
in N for security reasons, our scheme-so-far can only evaluate polynomials of (sublinear) polynomial
degree in N (only logarithmic depth). In short, our scheme-so-far is a somewhat homomorphic
encryption (SWHE) scheme [Gen09] that can evaluate log-depth or polynomial degree. Though
not yet fully homomorphic, it is by far the most homomorphic LWE-based encryption scheme that
uses only “natural” homomorphic operations.

1.3.3     Flattening Ciphertexts and Fully Homomorphic Encryption
To obtain a leveled FHE scheme that can evaluate circuits of polynomial depth without bootstrap-
ping or techniques like relinearization, we need to ensure better bounds on the growth of the error.
Let us say that a ciphertext C is B-strongly-bounded if its associated µ and the coefficients of
C all have magnitude at most 1, while the coefficients of its ~e all have magnitude at most B. If
we evaluate a NAND gate on B-strongly-bounded ciphertexts C1 , C2 to obtain a new ciphertext
C3 ← IN − C1 · C2 (where IN is the N -dimensional identity matrix), then the message remains in
{0, 1}, and the coefficients of C3 ’s error vector have magnitude at most (N + 1)B. If we could some-
how additionally ensure that C3 ’s coefficients have magnitude at most 1 so that strong-boundedness
is preserved, then we could evaluate a circuit of depth L while keeping the error magnitude at most
(N + 1)L B. Setting q/B to be subexponential in N , we could evaluate a circuit of polynomial depth
rather than merely polynomial degree. In short, we would have a leveled FHE scheme.
     Here we describe a operation called ciphertext flattening that keeps ciphertexts strongly bounded,
so that we obtain leveled FHE.
     Flattening uses some simple transformations from [BV11b, BGV12, Bra12] that modify vectors
without affecting dot products. Let ~a, ~b be vectors of some dimension k over Zq . Let ` = blog2 qc+1
and N = k · `. Let BitDecomp(~a) be the N -dimensional vector (a1,0 , . . . , a1,`−1 , . . . , ak,0 , . . . , ak,`−1 ),
where ai,j is the j-th bit in ai ’s binary representation, bits ordered least significant                  to most signif-
icant. For ~a0 = (a1,0 , . . . , a1,`−1 , . . . , ak,0 , . . . , ak,`−1 ), let BitDecomp−1 (~a0 ) = ( 2j · a1,j , . . . , 2j ·
                                                                                                     P                   P
ak,j ) be the inverse of BitDecomp, but well-defined even when the input is not a 0/1 vector. For


                                                             5

<!-- pdf-page: 6 -->
N -dimensional ~a0 , let Flatten(~a0 ) = BitDecomp(BitDecomp−1 (~a0 )), a N -dimensional vector with
0/1 coefficients. When A is a matrix, let BitDecomp(A), BitDecomp−1 , or Flatten(A) be the ma-
trix formed by applying the operation to each row of A separately. Finally, let Powersof2(~b) =
(b1 , 2b1 , . . . , 2`−1 b1 , . . . , bk , 2bk , . . . , 2`−1 bk ), a N -dimensional vector. Here are some obvious facts:
    • hBitDecomp(~a), Powersof2(~b)i = h~a, ~bi.
    • For any N -dimensional ~a0 , h~a0 , Powersof2(~b)i = hBitDecomp−1 (~a0 ), ~bi = hFlatten(~a0 ), Powersof2(~b)i.
 An interesting feature of Flatten is that it makes the coefficients of a vector or matrix small, without
 affecting its product with Powersof2(~b), and without knowing ~b.
     To facilitate ciphertext flattening, we give a special form to our secret key ~v . Specifically, we set
~v = Powersof2(~s) for some secret vector ~s (to be specified later). This form is consistent with our
 earlier requirement that ~v have some big coefficient vi for decryption; indeed, since ~v ’s coefficients
 go up by blog2 qc powers of 2, it must have a big coefficient suitable to recover µ ∈ {0, 1}.
     Now, for any N × N matrix C, we have Flatten(C) · ~v = C · ~v . So, after we compute an
 initial ciphertext C3 ← IN − C1 · C2 for the NAND gate, we set C NAND = Flatten(C3 ) to obtain a
 ciphertext that has 0/1 coefficients and is strongly bounded. Thus, we obtain leveled FHE without
 relinearization, under a fixed approximate eigenvector secret key.

1.3.4    Key Generation, Encryption, and Reduction to LWE
Let us finally circle back to key generation and encryption. We want to base security on LWE. So,
for key generation, we generate an LWE instance. For suitable parameters q, n, m = O(n log q), an
LWE instance over Zq consists of a m×(n+1) matrix A such that there exists a (n+1)-dimensional
vector ~s whose first coefficient is 1 where ~e = A · ~s is a “small” error vector. (See Section 2 for
a formal definition of LWE.) In our scheme, A is public and ~s is secret. We set our approximate
eigenvector to be ~v = Powersof2(~s), a vector of dimension N = (n + 1) · ` for ` = blog2 qc + 1.
    To encrypt µ ∈ Zq , the encrypter generates a random N × m matrix R with 0/1 entries, and
sets C = Flatten(µ · IN + BitDecomp(R · A)), where IN is the N -dimensional identity matrix. Since
Flatten does not affect the product with ~v , we have:

               C · ~v = µ · ~v + BitDecomp(R · A) · ~v = µ · ~v + R · A · ~s = µ · ~v + small

Flatten ensures that the coefficients of C are small, and therefore that C has the proper form of a
ciphertext that permits our homomorphic operations. Decryption works as mentioned previously.
    To show that security is based on LWE, it is now enough to show that C is statistically inde-
pendent of µ when A is a uniformly random m × (n + 1) matrix over Zq . Let C 0 = BitDecomp−1 (C).
Recall that C is Flatten’d, and so C = Flatten(C) = BitDecomp(C 0 ). Therefore, C reveals nothing
more than C 0 . But C 0 = BitDecomp−1 (µ · IN ) + R · A, and R · A is statistically uniform by the
leftover hash lemma when m = O(n log q) is chosen appropriately.


<!-- pdf-page: 8 -->
2.3   Other Preliminaries
For n, q, and ` = blog qc + 1, we define the procedures BitDecomp, BitDecomp−1 , Flatten and
Powersof2 as described in the Introduction. IN denotes the N -dimensional identity matrix.


3     Our LWE-Based FHE Scheme
3.1   Basic Encryption Scheme
Here, we formally describe our basic encryption scheme (without homomorphic operations). This
description matches the description outlined in the Introduction. In our description, we split
up KeyGen into three parts Setup, SecretKeyGen and PublicKeyGen. We provide two decryption
algorithms Dec and MPDec. Dec is sufficient to recover the message µ when it is in a small space
(e.g., {0, 1}). MPDec is an algorithm by Micciancio and Peikert [MP12] that can recover any µ ∈ Zq .

    • Setup(1λ , 1L ): Choose a modulus q of κ = κ(λ, L) bits, lattice dimension parameter n =
      n(λ, L), and error distribution χ = χ(λ, L) appropriately for LWE that achieves at least 2λ
      security against known attacks. Also, choose parameter m = m(λ, L) = O(n log q). Let
      params = (n, q, χ, m). Let ` = blog qc + 1 and N = (n + 1) · `.



                                                    8

<!-- pdf-page: 9 -->
   • SecretKeyGen(params): Sample ~t ← Znq . Output sk = ~s ← (1, −t1 , . . . , −tn ) ∈ Zn+1
                                                                                         q   . Let
     ~v = Powersof2(~s).

   • PublicKeyGen(params, sk): Generate a matrix B ← Zm×n   q    uniformly and a vector ~e ← χm .
     Set ~b = B · ~t + ~e. Set A to be the (n + 1)-column matrix consisting of ~b followed by the n
     columns of B. Set the public key pk = A. (Remark: Observe that A · ~s = ~e.)

   • Enc(params, pk, µ): To encrypt a message µ ∈ Zq , sample a uniform matrix R ∈ {0, 1}N ×m
     and output the ciphertext C given below.

                                                                         ×N
                              C = Flatten µ · IN + BitDecomp(R · A) ∈ ZN
                                                                   
                                                                       q    .

   • Dec(params, sk, C): Observe that the first ` coefficients of ~v are 1, 2, . . . , 2`−1 . Among these
     coefficients, let vi = 2i be in (q/4, q/2]. Let Ci be the i-th row of C. Compute xi ← hCi , ~v i.
     Output µ0 = bxi /vi e.

   • MPDec(params, sk, C) (for q a power of 2): Observe that q = 2`−1 and the first ` − 1
     coefficients of ~v are 1, 2, . . . , 2`−2 , and therefore if C · ~v = µ · ~v + small, then the first ` − 1
     coefficients of C · ~v are µ · ~g + small, where ~g = (1, 2, . . . , 2`−2 ). Recover LSB(µ) from
     µ · 2`−2 + small, then recover the next-least-significant-bit from (µ − LSB(µ)) · 2`−3 + small,
     etc. (See [MP12] for the general q case.)

   Dec is a BitDecomp’d version of Regev’s decryption procedure, applied to one row of the cipher-
text, which is a BitDecomp’d Regev ciphertext. (The extra rows will come into play in the homo-
morphic operations). If C is properly generated, then by the elementary properties of BitDecomp
and Powersof2, we have

                               C · ~v = µ · ~v + R · A · ~s = µ · ~v + R · ~e.

Dec only uses the i-th coefficient of the above expression, which is xi = µ · vi + hRi , ~ei. The error
hRi , ~ei has magnitude at most k~ek1 . In general, if xi = µ · vi + e0 for some error e0 of magnitude at
most q/8, and if vi ∈ (q/4, q/2], then xi /vi differs from µ by at most (q/8)/vi < 1/2, and Dec uses
rounding to output the correct value of µ. (In the basic scheme, we set χ to ensure that the error
is so bounded with overwhelming probability.)
    For the basic scheme (without homomorphic operations), one can take n to be quasi-linear in
the security parameter λ and κ = O(log n). When allowing homomorphic operations, L repre-
sents the circuit complexity of the functions that the scheme correctly evaluates (roughly, L is the
multiplicative depth); we provide a detailed analysis later of how L affects the other parameters.

3.2   Security
Observe that BitDecomp−1 (C) = µ · G + R · A, where G = BitDecomp−1 (IN ) is (the transpose
of) the “primitive matrix” used by Micciancio and Peikert [MP12] in their construction of lattice
trapdoors, and the rows of R · A are simply Regev [Reg05] encryptions of 0 for dimension n.
Assuming BitDecomp−1 (C) hides µ, C does as well, since C can be derived by applying BitDecomp.
Thus, the security of our basic encryption scheme follows directly from the following lemma, used
to prove the security of Regev’s encryption scheme [Reg05].


                                                        9

<!-- pdf-page: 10 -->
Lemma 1 (Implicit in [Reg05]). Let params = (n, q, χ, m) be such that the LWEn,q,χ assumption
holds. Then, for m = O(n log q) and A, R as generated above, the joint distribution (A, R · A) is
                                                     m×(n+1)    N ×(n+1)
computationally indistinguishable from uniform over Zq       × Zq        .
    Concretely, it suffices to take m > 2n log q [Reg05].
    Like Brakerski [Bra12], we can also base security on GapSVP via a classical reduction from
LWE [Pei09, BLP+ 13]. Specifically, Peikert [Pei09] gives a classical reduction of GapSVP to LWE,
with the caveat that q must be exponential in n. Brakerski notes that exponential q was unusable
in previous FHE schemes, since the ratio of q to the error level B of “fresh” ciphertexts cannot be
exponential in n for security reasons (since LLL [LLL82] could be used to break such a scheme), and
since B must be very small to permit many homomorphic operations. As in Brakerski’s scheme,
we do not have that problem. The error bound B of fresh ciphertexts in our scheme does not need
to be small to permit many homomorphic operations; we only require q/B to be sub-exponential,
and we can therefore permit q to be exponential. Alternatively, we can use a sub-exponential q and
base security on GapSVP via Brakerski et al.’s [BLP+ 13] recent classical reduction to LWE that
works even for polynomial-size moduli, with the caveat that, in their reduction, the dimension of
the GapSVP instances may be much smaller than the dimension of the LWE instances.

3.3   Homomorphic Operations
Recall that we already described some basic “homomorphic” operations BitDecomp, BitDecomp−1 ,
Flatten, and Powersof2. These will play an important role in analyzing the homomorphic operations
supported by our scheme. We remark that BitDecomp could alternatively decompose with respect
to bases other than 2, or according to the Chinese Remainder Theorem.
    We provide additional homomorphic operations MultConst, Add, Mult, NAND as follows.
   • MultConst(C, α): To multiply a ciphertext C ∈ ZN   ×N by known constant α ∈ Z , set M ←
                                                      q                           q       α
     Flatten(α · IN ) and output Flatten(Mα · C). Observe that:
              MultConst(C, α) · ~v = Mα · C · ~v = Mα · (µ · ~v + ~e) = µ · (Mα · ~v ) + Mα · ~e
                                       = α · µ · ~v + Mα · ~e
      Thus, the error increases by a factor of at most N , regardless of what element α ∈ Zq is
      used for multiplication. As in “classical” additively homomorphic encryption schemes, we
      could alternatively perform multiplication-by-constant α by recursively applying Add. But
      this multiplies the error size by at least α, whereas MultConst increases the error by at most
      a factor of N , regardless of α. An example application of MultConst is that we can perform
      homomorphic fast Fourier transformations (FFTs) natively over Zq without error growth
      dependent on q. Previously, the error growth depended on the size of the field underlying the
      FFT [GHS12a, GHS12b], restricting the choice of field.
   • Add(C1 , C2 ): To add ciphertexts C1 , C2 ∈ ZN ×N , output Flatten(C + C ). The correctness
                                                  q                      1   2
     of this operation is immediate. Note that the addition of messages is over the full base ring
     Zq .
   • Mult(C1 , C2 ): To multiply ciphertexts C1 , C2 ∈ ZN ×N , output Flatten(C · C ). Observe that:
                                                        q                      1   2

              Mult(C1 , C2 ) · ~v = C1 · C2 · ~v = C1 · (µ2 · ~v + ~e2 ) + µ2 · (µ1~v + ~e1 ) + C1 · ~e2
                                  = µ1 · µ2 · ~v + µ2 · ~e1 + C1 · ~e2

                                                      10

<!-- pdf-page: 11 -->
      As in Add, the multiplication operator is over the full base field Zq . In Mult, the new error
      depends on the old errors, the ciphertext C1 , and the message µ2 . The dependence on the
      old errors seems unavoidable (and normal for LWE-based HE schemes), and observe that C1
      contributes at most a factor N blowup of error, since all components of C1 are restricted to
      {0, 1}. The error growth based on the message µ2 , however, presents a concern. In general,
      we must address this concern by using homomorphic operations in a way that restricts the
      message space to small messages. One way to do this is to consider Boolean circuits using
      only NAND operations: this would restrict the message space to {0, 1}. We elaborate below.

   • NAND(C1 , C2 ): To NAND ciphertexts C1 , C2 ∈ ZN      ×N that are known to encrypt messages
                                                         q
     µ1 , µ2 ∈ {0, 1}, output Flatten(IN − C1 · C2 ). Observe that:

             NAND(C1 , C2 ) · ~v = (IN − C1 · C2 ) · ~v = (1 − µ1 · µ2 ) · ~v − µ2 · ~e1 − C1 · ~e2

      Note here that the NAND homomorphic operation maintains the invariant that if the input
      messages are in {0, 1}, then the output ciphertext will also encryption of {0, 1}, thus guar-
      anteeing small messages. Note that since µ2 ∈ {0, 1}, the error is increased by a factor of at
      most N + 1.

Circuits. By iteratively applying the homomorphic operations above, different types of (bounded-
depth) circuits may be homomorphically computed while maintaining correctness of decryption.
    The simplest case to analyze is the case of Boolean circuits computed over encryptions of
{0, 1} values. In this case, the circuit can be converted to use only NAND gates, and through
appropriate leveled application of the NAND homomorphic operation, the final ciphertext’s error
will be bounded by (N + 1)L · B, where L is the NAND-depth of the circuit, and B is the original
bound on the error of a fresh encryption of {0, 1}.
    More generally, with more care, we may consider arithmetic circuits over Zq that make use of
gates that perform addition, multiplication, or multiplication by a known constant. However, as
we have seen in the case of multiplication gates, the error growth may depend on the values being
encrypted in intermediate computations. One way to deal with this is to focus on situations where
(1) all input values are known to encrypt values bounded by some value T , and (2) the arithmetic
circuit is chosen to guarantee that all intermediate values are also bounded by T 0 whenever the
circuit inputs are constrained to values bounded by T . In such a situation, the final ciphertext’s
error will be bounded by (N + T 0 )L · B, where L is the depth of the arithmetic circuit, and B is the
original bound on the error of fresh encryptions of values smaller than T . For example, in this way,
we can homomorphically evaluate polynomials of degree d in this large-message-space variant when
the initial messages are bounded by roughly q 1/d , achieving a scheme that is “somewhat homomor-
phic” [Gen09]. Another example application would be to convert encryptions of a polynomially
bounded set of small values to encryptions of binary values, by using an appropriate arithmetic
circuit for the conversion. Once converted to encryptions of binary values, a NAND-based Boolean
circuit could be used for further computations.

3.4   Parameters, Performance and Optimizations
Suppose that Flatten’d ciphertexts C1 , C2 encrypt µ1 , µ2 ∈ {0, 1} under approximate eigenvector ~v
with B-bounded error – that is, Ci · ~v = µi · ~v + ~ei where |~ei |∞ ≤ B. Then C NAND ← NAND(C1 , C2 )
encrypts NAND(µ1 , µ2 ) ∈ {0, 1} under ~v with (N +1)B-bounded error. As long as q/B > 8(N +1)L ,

                                                     11

<!-- pdf-page: 12 -->
we can evaluate a depth-L circuit of NANDs over B-bounded ciphertexts to obtain a q/8-bounded
ciphertext, which Dec will decrypt correctly.
    As in previous LWE-based FHE schemes, n (hence N ) must increase linearly with log(q/B) to
maintain fixed 2λ security against known attacks, so q/B grows more like exp(L log L). We will
brush such issues under the rug and view n as a fixed parameter. Choosing χ so that B is not too
large, and since in practice there is no reason to have κ = log q grow super-linearly with n, we have
κ = O(L log N ) = O(L(log n + log κ)) = O(L log n), similar to [BGV12, Bra12]. Given that the
NAND procedure is dominated by multiplication of two N × N matrices for N = O(nκ) = Õ(nL),
we have the following theorem to characterize the performance of our FHE scheme.

Theorem 3. For dimension parameter n and depth parameter L, our FHE scheme evaluates depth-
L circuits of NAND gates with Õ((nL)ω ) field operations per gate, where ω < 2.3727 is the matrix
multiplication exponent.

This compares favorably with previous LWE-based FHE schemes, which all have at least Õ(n3 L)
field operations per gate [BV11b, BGV12, Bra12].
    Theorem 3 hides some factors, both good and bad. On the good size, it hides the fact that
ciphertext matrices in our scheme have 0/1 entries, and therefore can be multiplied faster than
if they were general matrices over Zq . In previous LWE-based FHE schemes, the field operations
involve multiplying a small number with a general number of Zq , which has complexity Õ(κ) =
Õ(L). So, previous LWE-based FHE schemes have real complexity Õ(n3 L2 ) whereas ours remains
Õ((nL)ω ). On the bad side, Theorem 3 hides logarithmic factors in the dimension of the ciphertext
matrices, since N = O(nκ) = O(nL log n). We note that typically n will dominate L, since for
very deep circuits, one would want to use Gentry’s bootstrapping technique [Gen09] to make the
per-gate computation independent of L.
    Since bootstrapping involves homomorphically evaluating the decryption function, and since
Dec is essentially Regev decryption [Reg05], bootstrapping works as in previous LWE-based FHE
schemes. In particular, we can use techniques from [BV11b] to reduce the dimension and modulus-
size of the ciphertext before bootstrapping, so that the complexity of decryption (and hence boot-
strapping) is completely independent of the depth L of the circuit that was evaluated to arrive
at that ciphertext. Regev decryption can be evaluated in O(log n) depth. Due to the logarithmic
depth, one can take q/B to be quasi-polynomial in n, and base security on LWE for quasi-polynomial
factors.
