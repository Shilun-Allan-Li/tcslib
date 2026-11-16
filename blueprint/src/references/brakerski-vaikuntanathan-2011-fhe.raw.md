<!-- generated-by: scoped Poppler extraction of the passages used (DW-7) -->
<!-- source-pdf-sha256: d3e95f9b9e017ea1133064bed227981ec21e38ee6fc6163eb08585dd238b0c00 -->
<!-- extractor: pdftotext version 24.02.0; -layout; scoped to the line ranges listed below -->
<!-- scope (physical page: lines of the -layout text): p1: 1-3; p12: 596-617; p13: 618-659; p14: 660-712; p15: 713-744; p29: 1491-1542 -->
<!-- note: physical page p is printed page p-1 (the title page is unnumbered) -->

<!-- pdf-page: 1 -->
   Efficient Fully Homomorphic Encryption from (Standard) LWE∗

                             Zvika Brakerski†               Vinod Vaikuntanathan‡

<!-- pdf-page: 12 -->
3     Homomorphic Encryption: Definitions and Tools
In this section we discuss the definition of homomorphic encryption and its properties as well as
some related subjects. We start by defining homomorphic and fully homomorphic encryption in
Section 3.1. Then, in Section 3.2 we discuss Gentry’s bootstrapping theorem.
    We note that there are a number of ways to define homomorphic encryption and to describe
the bootstrapping theorem. We chose the definitions that best fit the constructions and we urge
even the knowledgeable reader to go over them so as to avoid confusion in interpreting our results.

3.1   Homomorphic Encryption – Definitions
We now define homomorphic encryption and its desired properties. Throughout this section (and
this work) we use κ to indicate the security parameter. In addition, all schemes in this paper
encrypt bit-by-bit and therefore our definitions only refer to this case. The generalization to an
arbitrary message space is immediate.
    A homomorphic (public-key) encryption scheme HE = (HE.Keygen, HE.Enc, HE.Dec, HE.Eval) is
a quadruple of ppt algorithms as follows.

    • Key generation. The algorithm (pk, evk, sk)←HE.Keygen(1κ ) takes a unary representation
      of the security parameter and outputs a public encryption key pk, a public evaluation key
      evk and a secret decryption key sk.


                                                  11

<!-- pdf-page: 13 -->
   • Encryption. The algorithm c←HE.Encpk (µ) takes the public key pk and a single bit message
     µ ∈ {0, 1} and outputs a ciphertext c.
   • Decryption. The algorithm µ∗ ←HE.Decsk (c) takes the secret key sk and a ciphertext c and
     outputs a message µ∗ ∈ {0, 1}.
   • Homomorphic evaluation. The algorithm cf ←HE.Evalevk (f, c1 , . . . , c` ) takes the evalua-
     tion key evk, a function f : {0, 1}` → {0, 1} and a set of ` ciphertexts c1 , . . . , c` , and outputs
     a ciphertext cf .
      The representation of the function f is an important issue. Since the representation can vary
      between schemes, we leave this issue outside of this syntactic definition. We remark, however,
      that in this work, f will be represented by an arithmetic circuit over GF(2).
We note that while one can treat the evaluation key as a part of the public key, as has been done
in the literature so far, we feel that there is an expository value to treating it as a separate entity
and to distinguishing between the public elements that are used for encryption and those that are
used only for homomorphic evaluation.
    The only security notion we consider in this chapter is semantic security, namely security w.r.t.
passive adversaries. We use its widely known formulation as IND-CPA security, defined as follows.
Definition 3.1 (CPA security). A scheme HE is IND-CPA secure if for any polynomial time
adversary A it holds that
  AdvCPA [A] , |Pr[A(pk, evk, HE.Encpk (0)) = 1] − Pr[A(pk, evk, HE.Encpk (0)) = 1]| = negl(κ) ,
where (pk, evk, sk)←HE.Keygen(1κ ).
   In fact, based on the best known about lattices, the schemes we present in this paper will
be secure against even stronger adversaries. In order for our reductions to make sense for such
adversaries as well, we also consider a parameterized version of CPA security. There, we allow the
adversary to run in time t (which is typically super-polynomial) and succeed with probability 
(which is typically sub-polynomial).
Definition 3.2 ((t, )-CPA security). A scheme HE is (t, )-IND-CPA secure if for any adversary
A that runs in time t for t = t(κ) it holds that
  AdvCPA [A] , |Pr[A(pk, evk, HE.Encpk (0)) = 1] − Pr[A(pk, evk, HE.Encpk (0)) = 1]| ≤  = (κ) ,
where (pk, evk, sk)←HE.Keygen(1κ ).
    We move on to define the homomorphism property. Note that we do not define the “correctness”
of the scheme as a separate property, but rather (some form of) correctness will follow from our
homomorphism properties.
    We start by defining C-homomorphism, which is homomorphism with respect to a specified class
C of functions. This notion is sometimes also referred to as “somewhat homomorphism”.
Definition 3.3 (C-homomorphism). Let C = {Cκ }κ∈N be a class of functions (together with their
respective representations). A scheme HE is C-homomorphic (or, homomorphic for the class C) if
for any sequence of functions fκ ∈ Cκ and respective inputs µ1 , . . . , µ` ∈ {0, 1} (where ` = `(κ)), it
holds that
                 Pr [HE.Decsk (HE.Evalevk (f, c1 , . . . , c` )) 6= f (µ1 , . . . , µ` )] = negl(κ) ,
where (pk, evk, sk)←HE.Keygen(1κ ) and ci ←HE.Encpk (µi ).

                                                   12

<!-- pdf-page: 14 -->
     We point out two important properties that the above definition does not require. First of
all, we do not require that the ciphertexts ci are decryptable themselves, only that they become
decryptable after homomorphic evaluation.17 Secondly, we do not require that the output of HE.Eval
can undergo additional homomorphic evaluation.18
     Before we define full homomorphism, let us define the notion of compactness.

Definition 3.4 (compactness). A homomorphic scheme HE is compact if there exists a polynomial
s = s(κ) such that the output length of HE.Eval(· · · ) is at most s bits long (regardless of f or the
number of inputs).

    Note that a C-homomorphic scheme is not necessarily compact.
    We give the minimal definition of fully homomorphic encryption, which suffices for most appli-
cations.

Definition 3.5 (fully homomorphic encryption). A scheme HE is fully homomorphic if it is both
compact and homomorphic for the class of all arithmetic circuits over GF (2).

    As in the definition of C homomorphism, one can require that the outputs of HE.Eval can again
be used as inputs for homomorphic evaluation (“multi-hop homomorphism”). Indeed, all known
schemes have this additional property. However, due to the complexity of the formal definition in
this case, we refrain from describing a formal definition.
    An important relaxation of fully homomorphic encryption is the following.

Definition 3.6 (leveled fully homomorphic encryption). A leveled fully homomorphic encryp-
tion scheme is a homomorphic scheme where the HE.Keygen gets an additional input 1L (now
(pk, evk, sk)←HE.Keygen(1κ , 1L )) and the resulting scheme is homomorphic for all depth-L binary
arithmetic circuits. The bound s(κ) on the ciphertext length must remain independent of L.

    In most cases, the only parameter of the scheme that becomes dependent on L is the bit-length
of the evaluation key evk.

3.2    Gentry’s Bootstrapping Technique
In this section we formally define the notion of a bootstrappable encryption scheme and present
Gentry’s bootstrapping theorem [Gen09b, Gen09a] which implies that a bootstrappable scheme can
be converted into a fully homomorphic one.

Definition 3.7 (bootstrappable encryption scheme). Let HE be C-homomorphic, and Let fadd and
fmult be the the augmented decryption functions of the scheme defined as
 c1 ,c2                                                          c1 ,c2
fadd    (s) = HE.Decs (c1 ) XOR HE.Decs (c2 )         and       fmult   (s) = HE.Decs (c1 ) AND HE.Decs (c2 ) .

Then E is bootstrappable if                 c1 ,c2 c1 ,c2
                                            fadd , fmult c1 ,c2 ⊆ C .
Namely, the scheme can homomorphically evaluate fadd and fmult .
  17
     Jumping ahead, while this may seem strange at first, this notion of somewhat homomorphism is all that is really
required in order to bootstrap into full homomorphism and it also makes our schemes easier to describe. Lastly, note
that one can always perform a “blank” homomorphic operation and then decrypt, so functionality is not hurt.
  18
     This is termed “1-hop homomorphism” in [GHV10a].


                                                        13

<!-- pdf-page: 15 -->
    We describe two variants of Gentry’s bootstrapping theorem. The first implies leveled fully
homomorphic encryption but requires no additional assumption; where the second makes an ad-
ditional (weak) circular security assumption and achieves the stronger (non-leveled) variant of
Definition 3.5.
    The first variant follows.

Theorem 3.1 ([Gen09b, Gen09a]). Let HE be a bootstrappable scheme, then there exists a leveled
fully homomorphic encryption scheme as per Definition 3.6.

    Specifically, the leveled homomorphic scheme is such that only the length of the evaluation key
depends on the level L. All other parameters of the scheme are distributed identically regardless
of the value of L.
    For the second variant, we need to define circular security.

Definition 3.8 (weak circular security). A public key encryption scheme (Gen, Enc, Dec) is weakly
circular secure if it is IND-CPA secure even for an adversary with auxiliary information containing
encryptions of all secret key bits: {Encpk (sk[i])}i .

    Namely, no polynomial time adversary can distinguish an encryption of 0 from an encryption
of 1 even given the additional information.
    We can now state the second theorem.

Theorem 3.2 ([Gen09b, Gen09a]). Let HE be a bootstrappable scheme that is also weakly circular
secure. Then there is a fully homomorphic encryption scheme as per Definition 3.5.

   Finally, we want to make a statement regarding the ciphertext length of a bootstrapped scheme.
The following is implicit in [Gen09b, Gen09a].

Lemma 3.3. If a scheme FH is obtained from applying either Theorem 3.1 or Theorem 3.2 to a
bootstrappable scheme HE, then both FH.Enc and FH.Eval produce ciphertexts of the same length as
HE.Eval (regardless of the length of the ciphertext produced by HE.Enc).


<!-- pdf-page: 29 -->
4.5   Bootstrapping and Full Homomorphism
We now show how to apply Gentry’s bootstrapping theorem (Theorems 3.1, 3.2) to achieve full
homomorphism. In order to do this, we first need to bound the complexity of an augmented
decryption circuit. Since our decryption is essentially a computation of inner product, we bound
the complexity of this operation.

Lemma 4.5. Let (v̂, ŵ) ∈ Zkp × Zp . There exists an arithmetic circuit with fan-in 2 gates and
O(log k + log log p) depth, that on input ŝ ∈ Zkp (in binary representation) computes

                                  (ŵ − hv̂, ŝi (mod p))          (mod 2) .

Proof. We let ŝ[i](j) denote the j th bit of the binary representation of ŝ[i] ∈ Zp . We notice that
                                            k
                                            X
                     ŵ − hv̂, ŝi = ŵ −         ŝ[i]v̂[i]   (mod p)
                                            i=1
                                            k blog
                                            X  Xpc
                                  = ŵ −                  ŝ[i](j) · (2j · v̂[i])   (mod p) .
                                            i=1 j=0

Therefore computing ŵ − hv̂, ŝi (mod p) is equivalent to summing up k(1 + blog pc) + 1 numbers
in Zp , and then taking the result modulo p. The summation (over the integers) can be done in
depth O(log k + log log p). In order to take modulo p, one needs to subtract, in parallel, all possible
multiples of p (there are at most O(k log p) options) and check if the result is in Zp . This requires
depth O(log k + log log p) again. Then a selection tree of depth O(log k + log log p) is used to
choose the correct result. Once this is done, outputting the least significant bit implements the
final modulo 2 operation.
    The total depth is thus O(log k + log log p) as required.

   We can now apply the bootstrapping theorem to obtain a fully homomorphic scheme.

Lemma 4.6. There exists C ∈ N such that setting n = k C/ and the rest of the parameters as in
Theorem 4.2, BTS is bootstrappable as per Definition 3.7.

Proof. Lemma 4.5 guarantees that the decryption circuit is in Arith[O(log k), 1] (note that log log p =
o(log k)), since the augmented decryption circuit just adds 1 to the depth, it follows that the aug-
mented decryption circuits are also in Arith[O(log k), 1].
                                                                                             √
    Theorem 4.2, on the other hand, guarantees homomorphism for any Arith[Ω( log n), q] func-
                                                                                         √
tion. Taking a large enough C, it will hold that Arith[O(log k), 1] ⊆ Arith[Ω( log n), q] and the
lemma follows.

   Finally, we conclude that there exists an LWE based fully homomorphic encryption based on
Theorem 4.1 and Lemma 4.6.

Corollary 4.7. There exists a leveled fully homomorphic encryption based on the DLWEn,q,χ and
DLWEk,p,χ̂ assumptions.
   Furthermore, if BTS is weakly circular secure (see Definition 3.8), then there exists a fully
homomorphic encryption based on the same assumptions.
