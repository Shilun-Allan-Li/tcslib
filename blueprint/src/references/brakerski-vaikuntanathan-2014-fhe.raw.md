<!-- generated-by: scoped Poppler extraction of the passages used (DW-7) -->
<!-- source-pdf-sha256: eab2d1667a8e8a07155968141c72d0ff0be15b1185dd0fd34f291fb41fb812ca -->
<!-- extractor: pdftotext version 24.02.0; -layout; scoped to the line ranges listed below -->
<!-- scope (physical page: lines of the -layout text): p1: 1-2; p1: 44-47; p2: 64-71; p5: 236-252; p6: 253-270; p7: 345-365; p8: 366-409; p9: 410-465; p10: 466-519; p11: 520-565; p12: 566-627; p13: 628-684; p14: 685-734; p15: 735-792; p16: 793-811; p19: 954-970; p20: 1001-1030 -->
<!-- note: physical page = printed page -->

<!-- pdf-page: 1 -->
                         Lattice-Based FHE as Secure as PKE
                            Zvika Brakerski∗            Vinod Vaikuntanathan†

[...]
    1
      Here, and in the rest of the introduction, when we say FHE, we mean a leveled FHE scheme that can evaluate
circuits of any a-priori bounded polynomial depth. The only known way to achieve non-leveled FHE schemes is to
make a circular security assumption, in addition.

<!-- pdf-page: 2 -->
    Our results are summarized in the following theorem.
Theorem 1.1. For every  > 0, there exists a leveled fully homomorphic encryption scheme based
on the DLWEn,q,α assumption (n-dimensional decisional LWE modulo q, with discrete Gaussian
                                               p
noise with parameter α), where α = 1/O(ne  · n log(q)).
    Thus, the scheme is secure based on either the quantum worst-case hardness of GapSVPO(n
                                                                                        e 1.5+ ) ,
or the classical worst-case hardness of GapSVPO(ne 2+ ) .

<!-- pdf-page: 5 -->
2.3    Vector Decomposition and Key Switching
We show how to decompose vectors in a way that makes their norm smaller, and yet preserves
certain inner products. Our notation is generally adopted from [BGV12].

Vector Decomposition.     We often break vectors into their bit representations as defined below:
                                                                     Pdlog qe−1 j
• BitDecompq (x): For x ∈ Zn , let wi,j ∈ {0, 1} be such that x[i] = j=0        2 · wi,j (mod q).
  Output the vector
                       (w1,dlog qe−1 , . . . , w1,0 , . . . , wn,dlog qe−1 , . . . , wn,0 ) ∈ {0, 1}n·dlog qe .

• PowersOfTwoq (y): For y ∈ Zn , output
         h                                                                                      i
          (2dlog qe−1 y[1], . . . , 2y[1], y[1], . . . , 2dlog qe−1 · y[n], . . . , 2y[n], y[n]) ∈ Zqn·dlog qe .
                                                                                                       q


                                                                5

<!-- pdf-page: 6 -->
We will usually omit the subscript q when it is clear from the context.

Claim 2.7. For all q ∈ N and x, y ∈ Zn , it holds that

                        hx, yi = hBitDecompq (x), PowersOfTwoq (y)i        (mod q) .

   Additionally, we define the procedure Flatten following [GSW13], along with the procedure
Combine. Let g = (2dlog(q)e−1 , 2dlog(q)e−2 . . . , 4, 2, 1) ∈ Zdlog qe and let G := g ⊗ In ∈ Zn×(n·dlog qe)
denote the tensor product of g with the n-by-n identity matrix In .

• Combineq (z): For z ∈ Zn·dlog qe , output [G · z]q ∈ Znq .

• Flattenq (z): For z ∈ Zn·dlog qe , output BitDecompq (Combine(z)) ∈ {0, 1}n·dlog qe .

Claim 2.8. For all q ∈ N, and x, z ∈ Zn·dlog qe , it holds that

                    hPowersOfTwo(x), zi = hPowersOfTwo(x), Flatten(z)i (mod q) .


<!-- pdf-page: 7 -->
2.5      Homomorphic Encryption and Bootstrapping
We now define homomorphic encryption and introduce Gentry’s bootstrapping theorem. Our defi-
nitions are mostly taken from [BV11, BGV12].
    A homomorphic (public-key) encryption scheme HE = (HE.Keygen, HE.Enc, HE.Dec, HE.Eval) is
a quadruple of ppt algorithms as follows (κ is the security parameter):
      • Key generation (pk, evk, sk)←HE.Keygen(1κ ): Outputs a public encryption key pk, a public
        evaluation key evk and a secret decryption key sk.2

      • Encryption c←HE.Encpk (µ): Using the public key pk, encrypts a single bit message µ ∈
        {0, 1} into a ciphertext c.

      • Decryption µ←HE.Decsk (c): Using the secret key sk, decrypts a ciphertext c to recover the
        message µ ∈ {0, 1}.

      • Homomorphic evaluation cf ←HE.Evalevk (f, c1 , . . . , c` ): Using the evaluation key evk, ap-
        plies a function f : {0, 1}` → {0, 1} to c1 , . . . , c` , and outputs a ciphertext cf .
  2
      We adopt the terminology of [BV11] that treats the evaluation key as a separate entity from the public key.


                                                          7

<!-- pdf-page: 8 -->
   A homomorphic encryption scheme is said to be secure if it is semantically secure (note that
the adversary is given both pk and evk).
   Homomorphism w.r.t depth-bounded circuits and full homomorphism are defined next:
Definition 2.12 (compactness and full homomorphism). A homomorphic encryption scheme is
compact if its decryption circuit is independent of the evaluated function. A compact scheme is
(pure) fully homomorphic if it can evaluate any efficiently computable function. The scheme is
leveled fully homomorphic if it takes 1L as additional input in key generation, and can only evaluate
depth L Boolean circuits.
    Gentry’s bootstrapping theorem shows how to go from limited amount of homomorphism to
full homomorphism. This method has to do with the augmented decryption circuit.
Definition 2.13. Consider a homomorphic encryption scheme HE. Let (sk, pk, evk) be properly
generated keys and let C be the set of properly decryptable ciphertexts. Then the set of augmented
decryption functions, {fc1 ,c2 }c1 ,c2 ∈C is defined by fc1 ,c2 (x) = HE.Decx (c1 ) ∧ HE.Decx (c2 ). Namely,
the function that uses its input as secret key, decrypts c1 , c2 and returns the NAND of the results.
    The bootstrapping theorem is thus as follows.
Theorem 2.14 (bootstrapping [Gen09b, Gen09a]). A scheme that can homomorphically evaluate
its family of augmented decryption circuits can be transformed into a leveled fully homomorphic
encryption scheme with the same decryption circuit, ciphertext space and public key.
    Furthermore, if the aforementioned scheme is also weak circular secure (remains secure even
against an adversary who gets encryptions of the bits of the secret key), then it can be made into a
pure fully homomorphic encryption scheme.


3     Our FHE Scheme
In this section, we describe an FHE scheme secure under a polynomial LWE assumption which,
using known reductions [Reg05, Pei09], translates to the worst-case hardness of solving various
lattice problems to within polynomial approximation factors. We start with the basic encryption
scheme in Section 3.1, and describe “proto-homomorphic” addition and multiplication subroutines
in Section 3.2. Departing from the “conventional wisdom” in FHE, our circuit evaluation procedure
in Section 3.3 will not be a naive combination of these proto-homomorphic operations, but rather
a carefully designed procedure that manages the noise growth effectively.
    Finally, in Section 3.4, we put this all together to get our FHE scheme under the decisional
LWE assumption DLWEn,q,α with α = n−c for some constant c > 0. This polynomial factor is
rather large: thus, in Section 4, we apply a carefully designed variant of the dimension-modulus
reduction procedure of [BV11]pto obtain our final FHE scheme that is secure under the hardness of
DLWEn,q,α with α ≤ 1/O  eκ (n · n log(q)) which is weakest LWE hardness assumption that underlies
the (non-homomorphic) lattice-based PKE schemes [AD97, Reg04, Reg05, Pei09, BLP+ 13].

3.1    The Basic Encryption Scheme
Our basic encryption scheme closely follows the Gentry-Sahai-Waters FHE scheme [GSW13]. We
refer the reader to Section 2.3 for the description of the vector decomposition routines PowersOfTwo,
BitDecomp and Flatten used in the scheme below.

                                                     8

<!-- pdf-page: 9 -->
System Parameters. Let n be the LWE dimension and q be an LWE modulus. Define N :=
(n + 1) · dlog qe. Let d denote the maximal homomorphism depth that is allowed by the scheme.
Let χ be an error distribution over Z. Typically χ will be a discrete Gaussian DZ,αq for α =
       p
1/Oeκ ( n log(q) · 4d ). Recall that we identify Zq with the set (−q/2, q/2] ∩ Z.

                                                      $
   • NCCrypt.Keygen(1n , q, 4d ): Sample a vector s ← Znq . Let m , (n + 1) · (log q + O(1)). Sample
         $               $
      A ← Zm×n
           q   and e ← χm . Compute b:= [A · s + e]q , and define

                                        P:= [bk − A] ∈ Zm×(n+1)
                                                        q       .

      Output sk = s and pk = evk = P.

      We describe public-key as well as secret-key encryption algorithms. Looking ahead, we remark
      that a secret-key encryption of µ is somewhat less “noisy” than a public-key encryption of µ.

   • NCCrypt.PubEnc(pk, µ): To encrypt a bit µ ∈ {0, 1}, using the public key pk = P, we let
       $
     R ← {0, 1}N ×m , and output the ciphertext

                          C = Flatten (BitDecomp(R · P) + µ · I) ∈ {0, 1}N ×N .

   • NCCrypt.SecEnc(sk, µ): A symmetric encryption of a bit µ ∈ {0, 1}, using the secret key
                                          $     ×n and e ←$
     sk = s, is performed by sampling A ← ZN q              χN , computing b:= [A · s + e]q , and
     defining
                       C = Flatten (BitDecomp ([bk − A]) + µ · I) ∈ {0, 1}N ×N .

   • NCCrypt.Dec(sk, C): Let c be the second row of C. We use standard Regev decryption on c.
     Namely, we output µ∗ = 0 if [hc, PowersOfTwo(1, s)i]q < q/8, and µ∗ = 1 otherwise.

Correctness. In order to show correctness of this scheme, we analyze the noise magnitude of
ciphertexts produced by both the public-key and secret-key encryption algorithms. As we will
show shortly, for ciphertexts C produced by either encryption algorithm, we have

                   C · PowersOfTwo(1, s) = µ · PowersOfTwo(1, s) + e (mod q)

for a noise vector e of “small magnitude”. This motivates our definition of the noise in the ciphertext
C with respect to a secret key vector s and a message µ as follows.

Definition 3.1. For every C ∈ {0, 1}N ×N , s ∈ Znq and µ ∈ Z, we define

                     noises,µ (C) , k(C − µI) · PowersOfTwo(1, s)    (mod q)k∞

   The significance of this definition is captured by the following claims. The first claim shows
that any ciphertext with small noise is decrypted correctly.

Lemma 3.2. For every C ∈ {0, 1}N ×N , s ∈ Znq and µ ∈ Z such that noises,µ (C) < q/8,

                                       NCCrypt.Dec(s, C) = µ

                                                  9

<!-- pdf-page: 10 -->
Proof. Since noises,µ (C) < q/8, we have
                   C · PowersOfTwo(1, s) = η + µ · PowersOfTwo(1, s)      (mod q)
where kηk∞ < q/8. Thus, for the second row of C it holds that
                       hc, PowersOfTwo(1, s)i = η + 2dlog(q)e−2 · µ   (mod q)
where |η| < q/8. Thus, when µ = 0,

                               [hc, PowersOfTwo(1, s)i]q = |η| < q/8

When µ = 1,
                            [hc, PowersOfTwo(1, s)i]q ≥ q/4 − |η| ≥ q/8

since q/4 ≤ 2dlog(q)e−2 < q/2. This shows correctness of decryption for ciphertexts with small
noise.

   The next claim demonstrates parameter settings for which the (public key and secret key)
encryption algorithms produce ciphertexts with small noise.
Lemma 3.3. Let n be the LWE dimension, q be the LWE modulus and χ = DZ,αq be the discrete
Gaussian distribution. Then, for every s ∈ Znq and µ ∈ {0, 1},
                                                                 eκ (αq · √m).
  • for Cpub ← NCCrypt.PubEnc(pk, µ), we have noises,µ (Cpub ) = O

   • for Csec ← NCCrypt.SecEnc(sk, µ), we have noises,µ (Csec ) = O
                                                                  eκ (αq).

with all but negligible (in κ) probability over the coins of NCCrypt.Keygen.
                                                                                            e κ (√m),
   In particular, we have correctness of decryption for the public key encryption for α < 1/Ω
and for the secret key encryption for α < 1/Ω  e κ (1).

Proof. We first show the analysis for the public-key encryption.
                                                                 
       Cpub · PowersOfTwo(1, s) = Flatten BitDecomp(R · P) + µ · I · PowersOfTwo(1, s)
                                                             
                                 = BitDecomp(R · P) + µ · I · PowersOfTwo(1, s)

                                  = R · P · (1, s)T + µ · PowersOfTwo(1, s)
                                  = R · e + µ · PowersOfTwo(1, s)
Thus, by Proposition 2.3,
                                                            √
                              noise(Cpub ) = kR · ek∞ = O
                                                        eκ ( m · αq)

This is less than q/8 by the choice of α < 1/Ωe κ (√m).
   The analysis for the secret key encryption follows analogously, except that
                       Csec · PowersOfTwo(1, s) = e + µ · PowersOfTwo(1, s)
Thus,
                                   noise(Csec ) = kek∞ = O
                                                         eκ (αq)

which is less than q/8 by the choice of α < 1/Ω
                                              e κ (1).


                                                 10

<!-- pdf-page: 11 -->
Security. Semantic security of the scheme follows from the decisional LWE assumption DLWEn,q,α ,
similarly to Regev’s encryption scheme (see [Reg05, BV11, GSW13] for similar arguments).

Complexity of Decryption. Our decryption algorithm is essentially the same as the decryption
algorithm in Regev’s encryption scheme, the complexity of which has been thoroughly studied in
the context of FHE. The following is an immediate corollary from [BV11, Lemma 4.1].

Proposition 3.4. There exists a constant cdec such that the decryption circuit of the scheme
NCCrypt, with parameters n, q, has depth at most cdec · log(n log q).

3.2   Proto-Homomorphic Operations
We now describe proto-homomorphic addition and multiplication algorithms which will be used
in Section 3.3 for homomorphic circuit evaluation. Departing from the “conventional wisdom” in
FHE, our circuit evaluation procedure will not be a naive combination of homomorphic addition
and multiplication, but a carefully designed procedure that manages the noise growth effectively.
To further stress the fact that we do not intend for these procedures to be used independently, we
call them proto-homomorphic operations.

Proto-Homomorphic Addition. This is a simple addition of the ciphertext matrices.

   • NCCrypt.ProtoAdd(C1 , C2 ): Output C+ := Flatten(C1 + C2 ).

    Jumping ahead, we note that in our use of NCCrypt.ProtoAdd in Section 3.3, both C1 and C2
will be encryptions of bits, and at most one of them will be an encryption of 1. The following claim
analyzes the noise growth in homomorphic addition.

Claim 3.4.1 (Noise Growth in NCCrypt.ProtoAdd.). For every s ∈ Znq , µ1 , µ2 ∈ Z and C1 , C2 ∈
{0, 1}N ×N , we have

              noises,µ1 +µ2 (NCCrypt.ProtoAdd(C1 , C2 )) ≤ noises,µ1 (C1 ) + noises,µ2 (C2 )

Proof. Let C+ ← NCCrypt.ProtoAdd(C1 , C2 ). We note that

          C+ · PowersOfTwo(1, s) = Flatten(C1 + C2 ) · PowersOfTwo(1, s)
                                      = (C1 + C2 ) · PowersOfTwo(1, s)
                                      = C1 · PowersOfTwo(1, s) + C2 · PowersOfTwo(1, s)
                                      = (e1 + e2 ) + (µ1 + µ2 ) · I

Thus, by the definition of noises,µ1 +µ2 , we have

                          noises,µ1 +µ2 (C+ ) ≤ noises,µ1 (C1 ) + noises,µ2 (C2 )




                                                     11

<!-- pdf-page: 12 -->
Homomorphic Multiplication. This is essentially a multiplication of the ciphertext matrices,
except that we randomize the first ciphertext.

   • NCCrypt.ProtoMult(evk, C1 , C2 ):

        – Randomize C1 ∈ {0, 1}N ×N into a matrix C
                                                  e 1 ∈ {0, 1}N ×N by replacing each row c in
          C1 by the row
                                c ← BitDecomp(Rand(pk, Combine(c)))
                                e
          where Rand is the LWE randomization procedure from Section 2.4.
                                       
        – Output C× ← Flatten Ce 1 · C2 .

    Jumping ahead, we remark that when we use NCCrypt.ProtoMult in our homomorphic circuit
evaluation in Section 3.3, the first ciphertext will be an “evaluated ciphertext” (namely, a result
of previous homomorphic evaluations), whereas the second ciphertext will be a “fresh ciphertext”
(namely an output of the secret key encryption algorithm).
    The first new idea in this work is that while the order of the arguments does not matter in
homomorphic addition, the homomorphic multiplication algorithm NCCrypt.ProtoMult is inherently
asymmetric, since it is essentially the (non-commutative) matrix multiplication operation. This
asymmetry turns out to be the key to achieving improved noise growth, as Claim 3.4.2 below will
demonstrate.

Claim 3.4.2 (Noise Growth in NCCrypt.ProtoMult.). For every s ∈ Znq , µ1 , µ2 ∈ {0, 1} and C1 ∈
{0, 1}N ×N and C2 ← NCCrypt.SecEnc(sk, µ2 ), we have
                                                                                        p
         noises,µ1 µ2 (NCCrypt.ProtoMult(C1 , C2 )) ≤ |µ2 | · noises,µ1 (C1 ) + O
                                                                                eκ (αq · n log q)

with all but negligible probability over the randomness of NCCrypt.Keygen, NCCrypt.SecEnc and
NCCrypt.ProtoMult.

Remark. In words, Claim 3.4.2 says that if µ2 ∈ {0, 1} (as will be the case in our homomorphic
circuit evaluation in Section 3.3), the noise in C× is at most the noise in C1 , plus a fixed additive
term. What’s more, if µ2 = 0, then the noise in C× is independent of that in C1 ! These two facts
are the key new ideas that enable our main result.

Proof. (of Claim 3.4.2.) Let C× ← NCCrypt.ProtoMult(evk, C1 , C2 ). Note that

            C× · PowersOfTwo(1, s) = Flatten(Ce 1 · C2 ) · PowersOfTwo(1, s)
                                     e 1 · (C2 · PowersOfTwo(1, s))
                                   = C
                                         e 1 · (e2 + µ2 · PowersOfTwo(1, s))
                                       = C
                                         e 1 · e2 + µ2 · C
                                       = C               e 1 · PowersOfTwo(1, s)
                                         e 1 · e2 + µ2 · (e
                                       = C                e1 + µ1 · PowersOfTwo(1, s))
                                          e 1 · e2 + µ2 · e
                                       = (C               e1 ) + µ1 µ2 · PowersOfTwo(1, s)        (1)
            N
Since e2 ← DZ,αq                 e 1 ∈ {0, 1}N ×N is the result of Rand, by Lemma 2.11, we have
                 and each row of C

                                  e 1 · e2                   √
                                  C              ≤O
                                                  eκ (αq ·       n log q)                         (2)
                                             ∞


                                                   12

<!-- pdf-page: 13 -->
with all but negligible probability.
Also, by lemma 2.10, we have
                                                                  p
                                ke
                                 e1 k∞ ≤ ke1 k∞ + O
                                                  eκ (αq ·         n log q)                                       (3)

with all but negligible probability.
   Putting together Eq. (1),(2) and (3), we have
                                                                                                   p
       noises,µ1 µ2 (C× ) ≤ C
                            e 1 · e2       + |µ2 | · ke                                 eκ (αq ·
                                                      e1 k∞ ≤ |µ2 | · noises,µ1 (C1 ) + O              n log q)
                                       ∞

which finishes the proof.

3.3    Homomorphic Evaluation of Circuits
We now describe how to homomorphically evaluate a Boolean circuit Ψ with two-input NAND gates
that takes ` inputs, and has depth d. In particular, our scheme will be able to evaluate circuits
of depth c · log n (for any constant c) under a polynomial LWE assumption, namely DLWEn,q,χ
where χ = DZ,α and α = 1/nΘ(c) . Since the depth of the decryption circuit is cdec · log(n log(q)) ≤
2cdec · log(n) (for some constant cdec > 0), the scheme is bootstrappable, and by the bootstrapping
theorem (Theorem 2.14), we get a leveled FHE scheme under the same assumption.
    To evaluate a circuit, our scheme first turns it into a width-5 permutation branching pro-
gram [BDFP86, Bar89], a model of computation that we describe below.

Width-5 Permutation Branching Programs. A permutation branching program                  Π of length
                         `
                                                                                   
L with input space {0, 1} is a sequence of L tuples of the form var(t), σt,0 , σt,1 where

   • var : [L] → [`] is a function that associates the t-th tuple with an input bit xvar(t) .

   • σj,0 and σj,1 are permutations on 5 elements. We will think of σj,0 and σj,1 as bijective
     functions from the set {1, 2, 3, 4, 5} to itself.

    The computation of the program Π on input x = (x1 , . . . , x` ) proceeds as follows. The state of
the computation at any point in time t is a number ζt ∈ {1, 2, 3, 4, 5}. Computation starts with the
initial state ζ0 = 1. The state ζt is computed recursively as

                                               ζt = σt,var(t) (ζt−1 )

Finally, after L steps, our state is ζL . The output of the computation is 1 if ζL = 1, and 0 otherwise.
    To manage the growth of noise in homomorphic evaluation, we need to work with bits rather
than numbers. Thus, we prefer to represent the state ζt ∈ {1, 2, 3, 4, 5} by a 0-1 vector vt which is
the unit vector uζt in 5 dimensions.
    The computation then proceeds as follows. The idea is that vt [i] = 1 if and only if σt,var(t) (ζt−1 ) =
i. Turning this around, vt [i] = 1 if and only if either:
            −1
   • vt−1 [σt,0 (i)] = 1 and xvar(t) = 0; or
            −1
   • vt−1 [σt,1 (i)] = 1 and xvar(t) = 1.



                                                        13

<!-- pdf-page: 14 -->
   The following formula captures this condition. For t = 1, . . . , L, and i ∈ {1, 2, 3, 4, 5}, we have:
                                       −1                                 −1
                      vt [i] := vt−1 [σt,0 (i)] · (1 − xvar(t) ) + vt−1 [σt,1 (i)] · xvar(t)
                            = vt−1 [γt,i,0 ] · (1 − xvar(t) ) + vt−1 [γt,i,1 ] · xvar(t)             (4)
                 −1                   −1
where γt,i,0 , σt,0 (i) and γt,i,1 , σt,1 (i) are constants that are publicly computable given the
description of the branching program. It is this form that we will work with in our homomorphic
evaluation.
   The important property that we will use is that circuits of depth d can be simulated by branching
programs of depth L = 4d .

Theorem 3.5 (Barrington’s Theorem [Bar89]). Every Boolean NAND circuit Ψ that acts on `
inputs and has depth d can be computed by a width-5 permutation branching program Π of length
4d . Given the description of the circuit Ψ, the description of the branching program Π can be
computed in poly(`, 4d ) time.

Homomorphic Evaluation NCCrypt.Eval(Ψ, C1 , . . . , C` ). The homomorphic evaluation proce-
dure will first convert the depth-d circuit Ψ into a width-5 permutation branching program Π of
length L = 4d .

   • [Initialization] We will maintain the encrypted state of the computation of the branching
     program for every step t. We denote this by Vt = (Vt,1 , Vt,2 , Vt,3 , Vt,4 , Vt,5 ), where each
     Vt [i] ∈ {0, 1}N ×N will be an encryption of vt [i].

        – We initialize the state as follows. Compute V0,i := v0 [i] · I.
          Note that V0,i is in fact a valid encryption of the bit v0 [i] with zero noise.
        – We also compute encryptions of the complements of the input bits, for convenience.
          That is, set C̄k := I − Ck . Note that C̄k is an encryption of x̄k = 1 − xk with the same
          noise as Ck .

   • [Evaluation] The evaluation proceeds iteratively for t = 1, . . . , L, where L is the length of
     the branching program Π. Assuming that we have Vt−1 := (Vt−1,1 , Vt−1,2 , . . . , Vt−1,5 ), the
     encryption of the state of the branching program computation at time t − 1, we compute
     Vt := (Vt,1 , Vt,2 , . . . , Vt,5 ) by homomorphically evaluating Eq. (4) above.
     That is, for i ∈ {1, 2, 3, 4, 5}, we compute
                                                
                                                                                  
                     Vt,i := NCCrypt.ProtoAdd NCCrypt.ProtoMult Vt−1,γ0 ,C̄var(t) ,                  (5)
                                                                                
                                                                              
                                          NCCrypt.ProtoMult Vt−1,γ1 , Cvar(t)                        (6)


   • [Output] Upon finishing the evaluation stage, we have VL := (VL,1 , VL,2 , . . . , VL,5 ). Output
     VL,1 as the result of the homomorphic evaluation.

   We now show that the scheme correctly evaluates circuits.


                                                        14

<!-- pdf-page: 15 -->
Lemma 3.6 (Correctness of Homomorphic Evaluation). Let n be the LWE dimension, q the LWE
modulus, Ψ be any Boolean circuit of depth d, and
                                                    p
                                    α ≤ 1/Θe κ (4d · n log q)

For every x1 , . . . , x` ∈ {0, 1}, every Boolean circuit Ψ of depth at most d, and every secret key
sk, letting Ck ← NCCrypt.SecEnc(sk, xk ) be the secret key encryptions of the inputs, and CΨ ←
NCCrypt.Eval(evk, Ψ, C1 , . . . , Ck ) be the evaluated ciphertext, we have:

                               NCCrypt.Dec(sk, CΨ ) = Ψ(x1 , . . . , x` )

with overwhelming probability over the coin tosses of all the algorithms. NCCrypt.Eval runs in time
poly(4d , `, n, log q).

    Note that we stated the correctness of homomorphic evaluation on ciphertexts produced by
the secret-key encryption algorithm NCCrypt.SecEnc. A√similar lemma can be shown in the case
of public-key encryption, if α is smaller by a factor of n log q. However, in our “optimal FHE”
scheme in Section 4, we will only need to invoke this lemma with secret-key encryption.

Proof. It is easy to see that each step of the homomorphic evaluation algorithm, given by Eq. (5),
simulates the execution of the branching program, given by Eq. (4). It remains to bound the noise
growth during NCCrypt.Eval. We show this by induction.
     In the sequel, we will abbreviate the noise function noises,µ (C) to noise(C) since the secret key
is fixed throughout the evaluation, and the message µ is clear from the context.
     Clearly, noise(V0,i ) = 0, since they V0,i are just the messages, with no noise. Assume, as the
inductive hypothesis, that for all i ∈ {1, 2, 3, 4, 5},
                                                                   p
                                noise(Vt−1,i ) = (t − 1) · O
                                                           eκ (αq · n log q)

We will now bound noise(Vt,i ) for all i ∈ {1, 2, 3, 4, 5}. Note that
                                                                                                   
                                                                                                  
noise Vt,i ≤ noise NCCrypt.ProtoMult Vt−1,γ0 , C̄var(t) + noise NCCrypt.ProtoMult Vt−1,γ1 , Cvar(t)
                                                                                        p
            ≤ |1 − xvar(t) | · noise(Vt−1,γ0 ) + |xvar(t) | · noise(Vt−1,γ1 ) + O
                                                                                eκ (αq · n log q)

where the second inequality holds by Claim 3.4.2 since all the ciphertexts encrypt bits, Cvar(t) is a
fresh secret-key encryption, and C̄var(t) contains exactly the same noise as Cvar(t) .
    Since exactly one of xvar(t) and 1 − xvar(t) is non-zero, we have
                                                                           p
               noise Vt,i ≤ max(noise(Vt−1,γ0 ), noise(Vt−1,γ1 )) + O
                                                                    eκ (αq · n log q)
                                      p
                           ≤t·O
                              eκ (αq · n log q)

by the inductive hypothesis.
   Thus, in particular,
                                                             p
                      noise(VΨ ) = noise VL,1 ≤ 4d · O
                                             
                                                     eκ (αq · n log q) < q/8

by our setting of the parameter α.

                                                  15

<!-- pdf-page: 16 -->
3.4    Achieving Fully Homomorphic Encryption
We know by Lemma 3.4 that the depth of the decryption circuit of NCCrypt is cdec · log(n log q) =
cdec log N for some constant cdec >√ 0. Setting the depth d = c log N for some constant c > cdec
in Lemma 3.6 and α ≤ 1/Θ  e κ (4d · n log q) gives us a bootstrappable encryption scheme. By the
bootstrapping theorem (Theorem 2.14), this can be turned into a leveled FHE scheme, without
additional assumptions. We state this theorem below:

Theorem 3.7. Let n be the LWE dimension, q be the LWE modulus, N := (n + 1) · dlog qe,
and let c > cdec be a large enough constant (where cdec is the decryption depth constant from
Proposition 3.4), and
                                  α ≤ 1/Θe κ ((n log q)2c+1/2 )

Then, there is a leveled FHE scheme that is secure under the decisional LWE assumption DLWEn,q,α .

    In the next section, we will use a variant of the dimension-modulus reduction of [BV11], the
effect of which will be to reduce the constant c above to a very small  → 0, thus achieving a value
of α that matches the best known lattice-based PKE schemes.



<!-- pdf-page: 19 -->
Lemma 4.4. Let α(n) = 1/O      eκ ( n log(q) · n ), and let q(n) ≥ O(
of keys generated by (sk, pk, evk)←DimReduced.Keygen(1k ), and recall that sk = (s0 , sL ). Let
Ki ←DimReduced.SecEncsk (BitDecomp(s0 )[i]). Namely, Ki is the symmetric encryption of the ith
bit of s0 .
    Let f be an augmented decryption circuit as per Definition 2.13. Namely, let c, c0 ∈ Zkp and
µ, µ0 ∈ {0, 1} be such that
                                      [hc, s0 i]p = µ · τ p + e ,
where |e| < p/8, and similarly for c0 . The function f is the function that on input x, treats x as a
secret key and decrypts c, c0 , and outputs the NAND of their decryptions.
    Let
                                c0 ←DimReduced.Evalevk (f, K1 , K2 , . . .) ,
and note that this is syntactically well defined since f can be represented as a Boolean circuit of
depth cdec · log(k log(q(k))) + 1.
   Then with all but negl(κ) probability,
                                      [hc0 , s0 i]p = µ∗ · τ p + ef ,

where µ∗ = (µ ∧ µ0 ), |ef | < p/8 are as above.

<!-- pdf-page: 20 -->
   Finally, we derive the worst-case lattice approximation factor based on Corollary 2.6. We recall
that a bootstrappable homomorphic encryption scheme implies a leveled FHE scheme under the
same assumptions, and a pure FHE scheme with an additional circular security assumption.
Corollary 4.5. For all  > 0, there exist:
   • A bootstrappable homomorphic encryption scheme based on the worst-case quantum hardness
     of solving GapSVPO(n
                        e 1.5+) and SIVPO(n
                                         e 1.5+) .

   • A bootstrappable homomorphic encryption scheme based on the worst-case classical hardness
      of solving GapSVPO(n
                         e 2+) .
                                                                       √
   The first (quantum) case is derived from Lemma 4.4 by setting q(n) = n/α(n) = poly(n), and
the second (classical) case is derived by setting q(n) = 2n/2 .

Improving Key and Ciphertext sizes. The scheme DimReduced uses a ladder of LWE in-
stances, ranging from short (k, p) to polynomially larger (n, q). In the description above, the public
key of the scheme is derived from that of NCCrypt, and therefore depends on n and not on k.
Likewise, the “input ciphertexts” (the ones before homomorphic evaluation) also depend on n.
    We note here that this can be fixed in such a way that only the evk depends on n, and the rest
of the parameters are exactly the same as Regev’s scheme with parameters (k, p). This is done in
a standard way (used e.g. in [BV11]) as follows.
    We will generate the public key as a standard Regev public key with parameters (k, p), and
in the evaluation key we will encrypt the bits of the respective secret key using NCCrypt. This
will allow to perform homomorphic operations by evaluating the augmented decryption circuit.
Namely, the ciphertexts visible to the user of the scheme will always be short, but in the process of
homomorphic evaluation, larger ciphertexts are used to accommodate the homomorphic operation,
and once it is done dimension-modulus reduction will be used to shrink the output ciphertext back
to the original size. Since this is standard practice, we omit the technical description.
