<!-- generated-by: scoped Poppler extraction of the passages used (DW-8) -->
<!-- source-pdf-sha256: 9e7f32f1b8543416fc6c2fcbfedd5d2d69150226b9bbd2cccac57840a5db7b66 -->
<!-- extractor: pdftotext version 24.02.0; -layout; scoped to the line ranges listed below -->
<!-- scope (physical page: lines of the -layout text): p53: 1822-1845; p54: 1848-1885; p55: 1900-1925; p56: 1926-1967; p57: 1968-2015; p58: 2032-2054; p59: 2055-2071; p60: 2115-2140; p61: 2141-2183; p62: 2184-2200 -->
<!-- note: physical page p is printed page p-10 (p53 is printed page 43) -->

<!-- pdf-page: 53 -->
4.1     Leveled Fully Homomorphic Encryption from Bootstrap-
        pable Encryption, Generically
Assume we have an encryption scheme E that compactly evaluates some set of circuits
CE . We want to use E to construct a homomorphic encryption scheme that can handle
arbitrary circuits. In this Chapter we prove a fundamental result: that if CE contains
(slight augmentations of) E’s own decryption circuit DE – i.e., if E “compactly evaluates”
its (augmented) decryption circuit – then we can use E to construct an efficient scheme that
handles circuits of arbitrary depth.
   A bit more specifically, for any integer d, we use E to construct a scheme E (d) that can
compactly evaluate circuits of depth up to d. The decryption circuit for E (d) is still DE ; the
secret key and ciphertexts are the same size as in E. The public key in E (d) consists of d + 1
public keys from E, together with a chain of encrypted E secret keys – the first E secret key
encrypted under the second E public key, and so on. In short, the family of schemes {E (d) }
is leveled fully homomorphic. We base the semantic security of E (d) on that of E using a
hybrid argument; as usual with hybrid arguments, the reduction loses a factor linear in d.
In Chapter 4.3, we describe how one can obtain a fully homomorphic encryption scheme
(where the public key size does not depend on the maximum number of levels we want to
evaluate) by assuming key-dependent-message (KDM) security, specifically circular-security
– i.e., that one can safely encrypt a E secret key under its associated public key.




                                              43

<!-- pdf-page: 54 -->


    Since this critical property of E – that it can compactly evaluate (slight augmenta-
tions of) its own decryption circuit – is self-referential and universal, we give it the obvious
name: bootstrappability. Why should bootstrappability be such a powerful feature? At a
high level, the reason is that bootstrappability allows us periodically to “refresh” ciphertexts
associated to interior nodes in a circuit; we can refresh for an arbitrary number of levels
in the circuit, and thus can evaluate circuits of arbitrary depth. To “refresh” a ciphertext
that encrypts a plaintext π under E public key pki , we re-encrypt it under pki+1 and then
homomorphically apply the decryption circuit to the result, using the secret key ski that is
encrypted under pki+1 , thereby obtaining an encryption of π under pki+1 . Homomorphi-
cally evaluating the decryption circuit decrypts the inner ciphertext under pki , but within
homomorphic encryption under pki+1 . The implicit decryption “refreshes” the ciphertext,
but the plaintext is never revealed; the plaintext is always covered by at least one layer of
encryption. Now that the ciphertext is refreshed, we can “continue” correctly evaluating
the circuit.
    To see how this works mathematically, begin by considering the following algorithm,
called Recrypt. For simplicity, suppose the plaintext space P is {0, 1} and DE is a boolean
circuit in CE . Let (sk1 , pk1 ) and (sk2 , pk2 ) be two E key-pairs. Let ψ1 be an encryption of
π ∈ P under pk1 . Let sk1j be an encryption of the j-th bit of the first secret key sk1 under
the second public key pk2 . Recrypt takes as these things as input, and outputs an encryption
of π under pk2 .

Recrypt(pk2 , DE , hsk1j i, ψ1 ).

                              R
                    Set ψ1j ← EncryptE (pk2 , ψ1j ) where ψ1j is the j-th bit of ψ1
                    Set ψ2 ← EvaluateE (pk2 , DE , hhsk1j i, hψ1j ii)
                    Output ψ2

Above, the Evaluate algorithm takes in all of the bits of sk1 and all of the bits of ψ1 , each
encrypted under pk2 . Then, E is used to evaluate the decryption circuit homomorphically.
The output ψ2 is thus an encryption under pk2 of DecryptE (sk1 , ψ1 ) → π.

Remark 4.1.1. The Recrypt algorithm implies a proxy one-way re-encryption scheme [19].
Roughly speaking, a one-way proxy re-encryption scheme allows the owner of sk1 to generate
a tag that enables an untrusted proxy to convert an encryption of π under pk1 to an
encryption of π under pk2 , but not the reverse. In our case, the tag is hsk1j i, the encrypted

<!-- pdf-page: 55 -->

                   R
          Set ψ1j ← WeakEncryptE (pk2 , ψ1j ) where ψ1j is the j-th bit of ψ1

Let us call this relaxation Recrypt0E . The main point of this relaxation is that WeakEncrypt
does not need to be semantically secure for Recrypt0E to be a secure one-way proxy re-
encryption scheme, or for Recrypt0E to be useful toward bootstrapping (as we will see below).
Thus, depending on E, WeakEncryptE can be very simple – e.g., for some schemes, and in
particular for the ideal-lattice-based scheme that we describe later, WeakEncryptE might
leave the input “bits” entirely unmodified. This will unfortunately not help us much in
terms of making the encryption scheme bootstrappable; essentially, it will add one circuit
level to what E can evaluate. However, it will affect the eventual computational complexity
of our scheme, since it will require less computation to apply the decryption circuit homo-
morphically to ciphertexts in which the outer encryption is weak. Another way of viewing
this relaxation is that we only need to be able to evaluate non-uniform decryption circuits,
where the ciphertext is “hard-wired” into the circuit (making this circuit simpler than the
“normal” decryption circuit that takes the ciphertext (and secret key) as input.
   To be bootstrappable, E needs to be able to compactly evaluate not only its decryption
circuit, which merely allows recryptions of the same plaintext, but also slightly augmented
versions of it, so that we can perform binary operations on plaintexts and make actual
progress through a circuit.

Definition 4.1.2 (Augmented Decryption Circuit). Let DE be E’s decryption circuit, which
takes a secret key and ciphertext as input, each formatted as an element of P `(λ) , where P is
the plaintext space. Let Γ be a set of gates with inputs and output in P, which includes the
trivial gate (input and output are the same). We call a circuit composed of multiple copies

<!-- pdf-page: 56 -->
CHAPTER 4. BOOTSTRAPPABLE ENCRYPTION                                                          46



of DE connected by a single g gate (the number of copies equals the number of inputs to g)
a “g-augmented decryption circuit.” We denote the set of g-augmented decryption circuits,
g ∈ Γ, by DE (Γ).

Definition 4.1.3 (Bootstrappable Encryption Scheme). As before, let CE denote the set of
circuits that E can compactly evaluate. We say that E is bootstrappable with respect to Γ if

                                          DE (Γ) ⊆ CE .

   For example, if Γ includes the trivial gate and NAND, E is bootstrappable with respect
to Γ if CE contains DE and the circuit formed by joining two copies of DE with a NAND
gate. Remarkably, as we will show, if there is a scheme E that can compactly evaluate only
these two circuits, then there is a scheme that is leveled fully homomorphic.

Remark 4.1.4. We could relax the bootstrappability definition slightly to say that E only
needs to be able to homomorphically evaluate its (augmented) decryption circuit when
the input ciphertext is weakly encrypted, similar to the relaxation Recrypt0E above. But,
this makes the definition of bootstrappable more cumbersome; we will continue with the
definition above, and remind the reader occasionally that the relaxation can be used.

   From the informal description above, it should already be somewhat clear how to use
a bootstrappable encryption scheme to construct a leveled fully homomorphic one; below,
we give a more formal description. Let E be bootstrappable with respect to a set of gates
Γ. For any integer d ≥ 1, we use E to construct a scheme E (d) = (KeyGenE (d) , EncryptE (d) ,
EvaluateE (d) , DecryptE (d) ) that can handle all circuits of depth d with gates in Γ. Note that
in the description below we encrypt the secret keys in reverse order; the only reason is that
this ordering simplifies our description of the recursion in Evaluate. When we refer to the
level of a wire in C, we mean the level of the gate for which the wire is an input. We use
the notation DE (Γ, δ) to refer to the set of circuits that equal a δ-depth circuit with gates
in Γ augmented by DE (copies of DE become inputs to the δ-depth circuit).

KeyGenE (d) (λ, d). Takes as input a security parameter λ and a positive integer d. For
` = `(λ) as in Definition 4.1.2, it sets

                                   R
                        (ski , pki ) ← KeyGenE (λ)        for i ∈ [0, d]
                         R
                    skij ← EncryptE (pki−1 , skij )       for i ∈ [1, d], j ∈ [1, `]

<!-- pdf-page: 57 -->
CHAPTER 4. BOOTSTRAPPABLE ENCRYPTION                                                             47



where ski1 , . . . , ski` is the representation of ski as elements of P. It outputs the secret key
sk(d) ← sk0 and the public key pk(d) ← (hpki i, hskij i). Let E (δ) refer to the sub-system that
uses sk(δ) ← sk0 and pk(δ) ← (hpki ii∈[0,δ] , hskij ii∈[1,δ] ) for δ ≤ d.

EncryptE (d) (pk(d) , π). Takes as input a public key pk(d) and a plaintext π ∈ P. It outputs a
                 R
ciphertext ψ ← EncryptE (pkd , π).

DecryptE (d) (sk(d) , ψ). Takes as input a secret key sk(d) and a ciphertext ψ (which should be
an encryption under pk0 ). It outputs DecryptE (sk0 , ψ).

EvaluateE (δ) (pk(δ) , Cδ , Ψδ ). Takes as input a public key pk(δ) , a circuit Cδ of depth at most
δ with gates in Γ, and a tuple of input ciphertexts Ψδ (where each input ciphertext should
be under pkδ ). We assume that each wire in Cδ connects gates at consecutive levels; if not,
add trivial gates to make it so. If δ = 0, it outputs Ψ0 and terminates. Otherwise, it does
the following:
            †
   • Sets (Cδ−1 , Ψ†δ−1 ) ← AugmentE (δ) (pk(δ) , Cδ , Ψδ ).
                                                     †
   • Sets (Cδ−1 , Ψδ−1 ) ← ReduceE (δ−1) (pk(δ−1) , Cδ−1 , Ψ†δ−1 ).

   • Runs EvaluateE (δ−1) (pk(δ−1) , Cδ−1 , Ψδ−1 ).

AugmentE (δ) (pk(δ) , Cδ , Ψδ ). Takes as input a public key pk(δ) , a circuit Cδ of depth at most
δ with gates in Γ, and a tuple of input ciphertexts Ψδ (where each input ciphertext should
                                                                     †
be under pkδ ). It augments Cδ with DE ; call the resulting circuit Cδ−1 . Let Ψ†δ−1 be
the tuple of ciphertexts formed by replacing each input ciphertext ψ ∈ Ψδ by the tuple
hhskδj i, hψj ii, where ψj ← WeakEncryptE (δ−1) (pk(δ−1) , ψj ) and the ψj ’s form the properly-
                                                             †
formatted representation of ψ as elements of P. It outputs (Cδ−1 , Ψ†δ−1 ).

ReduceE (δ) (pk(δ) , Cδ† , Ψ†δ ). Takes as input a public key pk(δ) , a tuple of input ciphertexts
Ψ†δ (where each input ciphertext should be in the image of EncryptE (δ) ), and a circuit Cδ† ∈
DE (Γ, δ + 1). It sets Cδ to be the sub-circuit of Cδ† consisting of the first δ levels. It sets
                                                                            (w)
Ψδ to be the induced input ciphertexts of Cδ , where the ciphertext ψδ            associated to wire
                                         (w)  (w)          (w)
w at level δ is set to EvaluateE (pkδ , Cδ , Ψδ ), where Cδ is the sub-circuit of Cδ† with
                       (w)                               (w)
output wire w, and Ψδ are the input ciphertexts for Cδ . It outputs (Cδ , Ψδ ).

High-level review of the Evaluate algorithm. We are given a circuit Cd of, say, d levels
with gates in Γ. For each input wire w of Cd , there is an associated input ciphertext ψw

<!-- pdf-page: 58 -->
of ψ1 . We then showed that the ciphertext generated by ψ2 ← EvaluateE (pk2 , C2 , Ψ2 ), which
is also associated to wire w, also encrypts π, but now under pk2 .
   In the full scheme above, the ciphertexts that we associate to the decryption circuit
that was attached to wire w are analogous to the ones we used in Recrypt0E : the encrypted
secret key (skd under pkd−1 ), and the re-encryption ciphertexts of ψw under pkd−1 . By
the correctness of Recrypt, the ciphertext now associated to w (after performing EvaluateE )
should encrypt the same plaintext as ψw , but now under pkd−1 .
   The Reduce step simply performs this Evaluate up to the wire w, and one level beyond.
We know that Evaluate can correctly continue one level beyond the wire w, because (by
assumption) E can evaluate not just the decryption circuit attached to w, but can evaluate
a circuit containing one Γ-gate above w. Reduce outputs Cd−1 and ciphertexts associated
to Cd−1 ’s input wires. We have made progress, since Cd−1 is one level shallower than Cd .
We perform this entire process d − 1 more times to obtain the final output ciphertexts.

Remark 4.1.5. Previously, we said that Evaluate takes as input ciphertexts that are “fresh”
outputs of Encrypt. However, we note EvaluateE (δ) also operates correctly on ciphertexts
output by Evaluate. (For δ < d above, this is precisely what EvaluateE (δ) does.)


4.2     Correctness, Computational Complexity and Security of
        the Generic Construction
Here we state and prove some theorems regarding the generic construction. Regarding
correctness, we have the following theorem.

<!-- pdf-page: 59 -->
CHAPTER 4. BOOTSTRAPPABLE ENCRYPTION                                                                  49



Theorem 4.2.1. Let E be bootstrappable with respect to a set of gates Γ. Then E (d) com-
pactly evaluates all circuits of depth d with gates in Γ – i.e., if Γ is a universal set of gates,
the family E (d) is leveled fully homomorphic.

Proof. (Theorem 4.2.1) First, we define a convenient notation: let D(δ, w, C, Ψ) denote
the plaintext value for wire w in circuit C induced by the decryptions (under skδ ) of the
ciphertexts Ψ associated to C’s input wires. If C is empty (has no gates), then the input
wires are the same as the output wires, and D(δ, w, C, Ψ) just denotes the decryption of the
single ciphertext ψ ∈ Ψ associated to w. To prove correctness, it suffices to show that

                          D(d, wout , Cd , Ψd ) = D(0, wout , C0 , Ψ0 )                            (4.1)

for every output wire wout of C0 (at level 0).

<!-- pdf-page: 60 -->



   Finally, assuming the semantic security of E, we prove the semantic security of E (d) .

Theorem 4.2.3. Let A be an algorithm that (t, ²)-breaks the semantic security of E (d) .
Then, there is an algorithm B that (t0 , ²0 )-breaks the semantic security of E for t0 ≈ t · ` and
²0 ≥ ²/`(d + 1), for ` as in Definition 4.1.2.

Proof. (Theorem 4.2.3) Let (E)` be equivalent to E, but with plaintext space P ≤` , where
Encrypt(E)` involves up to ` invocations of E and a concatenation of the results. We use a
hybrid argument to show that B (t00 , ²00 )-breaks the semantic security of (E)` for t00 ≈ t and
²00 ≥ ²/(d + 1), from which the result follows.
   For k ∈ [0, d], let Game k denote a game against E (d) in which everything is exactly as
in the real-world game, except that for all i ∈ [1, k] the challenger sets

                         R                            R
              (sk0i , pk0i ) ← KeyGenE (λ) and skij ← EncryptE (pki−1 , sk0ij )

In other words, for i ∈ [1, k], skij is the encryption (under pki−1 ) of the j-th bit of a
random secret key sk0i unrelated to ski . Game d + 1 is identical to Game d, except that
the challenger ignores b and (π0 , π1 ), generates a random plaintext π of the appropriate
length, and encrypts π to construct the challenge ciphertext. Let ²k denote the adversary’s
advantage in Game k.
   Since Game 0 is identical to the real world attack, the adversary’s advantage is ² by
assumption. Also, ²d+1 = 0, since the challenge is independent of b. Consequently, for some

<!-- pdf-page: 61 -->
CHAPTER 4. BOOTSTRAPPABLE ENCRYPTION                                                          51



k ∈ [0, d], it must hold that |²k − ²k+1 | ≥ ²/(d + 1); fix this value of k.
   B uses A to break (E)` as follows. B receives from the challenger a public key pk.
B generates the secret and public values exactly as in Game k, except that it replaces its
                                                                                               R
original value of pkk with pk. Also, if k < d, it generates a dummy key pair (sk0k+1 , pk0k+1 ) ←
KeyGenE (λ), sets π0 ← skk+1 and π1 ← sk0k+1 , and requests a challenge ciphertext (under
                                                                   R
pk) encrypting either π0 , π1 ∈ P ` . The challenger generates β ← {0, 1} and sends a tuple of
ciphertexts hψj i encrypting the bits hπβj i. B replaces its original tuple hsk(k+1)j i with the
tuple hψj i. One can verify that the public values are generated exactly as in Game k + β.
B sends the public values to A.
                                                                               R
   Eventually, A requests a challenge ciphertext on π0 or π1 . B sets b ← {0, 1}. If k < d,
                        R                                                          R
B sends the values ψj ← EncryptE (pkd , πbj ). If k = d, B generates random π ← P and asks
                                                                                        R
the challenger for a challenge ciphertext on πb or π. The challenger generates β ← {0, 1}
and encrypts πb or π accordingly, and B forwards the challenge to A. A sends a bit b0 . B
sends bit β 0 ← b ⊕ b0 to the challenger. One can verify that the challenge is generated as in
Game k + β.
   Since B’s simulation has the same distribution as Game k + β, and the probability that
B outputs 0 is ²k+β . The result follows.




4.3     Fully Homomorphic Encryption from KDM-Secure Boot-
        strappable Encryption
The length of the public key in E (d) is proportional to d (the depth of the circuits that can
be evaluated). It would be preferable to have a construction E ∗ where the public key size
is completely independent of the circuit depth, a construction that is fully homomorphic
rather than merely leveled fully homomorphic. Here is the obvious way to make the public
key pk∗ of E ∗ short: for E key pair (sk, pk), pk∗ includes only pk and (the “bits” of) sk
encrypted under pk. In other words, we have a cycle (in fact, a self-loop in this example)
of encrypted secret keys rather than an acyclic chain. It is clear that E ∗ is correct: the
recursive algorithm EvaluateE ∗ works as before, except that the implicit recryptions generate
“refreshed” ciphertexts under the same public key.
   Why didn’t we present this construction in the first place? Using an acyclic chain of
encrypted secret keys allowed us to base the security of E (d) on E using a hybrid argument;

<!-- pdf-page: 62 -->
CHAPTER 4. BOOTSTRAPPABLE ENCRYPTION                                                             52



this hybrid argument breaks down when there is a cycle. In general, a semantically secure
encryption scheme is not guaranteed to be KDM-secure – i.e., secure when the adversary
can request the encryptions of key-dependent messages, such as the secret key itself. Typ-
ically, when we prove an encryption scheme semantically secure, there is not an obvious
attack when the adversary is given the encryption of a key-dependent message. However,
KDM-security is highly nontrivial to prove. The problem is precisely that the usual hybrid
argument breaks down.

Remark 4.3.1. Canetti [27] proposed the acyclic, leveled approach as a way to remove
the need for KDM-security. Our initial approach had actually been to use E ∗ (with the
self-loop), and assume, or try to prove, KDM-security.

   Let us review (a restriction of) the definition of KDM-security. We will say a scheme E is
