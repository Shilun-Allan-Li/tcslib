<!-- generated-by: scoped Poppler extraction of the passages used (DW-7) -->
<!-- source-pdf-sha256: 63c1c7b0817f36d6e558107bf281e22d2c454f821fadd533ced653e81a6a35de -->
<!-- extractor: pdftotext version 24.02.0; -layout; scoped to the line ranges listed below -->
<!-- scope (physical page: lines of the -layout text): p1: 1-11; p2: 93-104; p3: 105-151; p4: 152-198; p5: 199-207; p5: 236-251; p6: 252-313; p7: 314-375; p8: 376-397; p8: 405-412 -->
<!-- note: physical page = printed page -->

<!-- pdf-page: 1 -->
An extended abstract of this paper appears in C. Cachin and J. Camenisch, editors, Advances in Cryptology—
EUROCRYPT 2004, volume 3027 of Lecture Notes in Computer Science, pages 223–238, Berlin: Springer-
Verlag, 2004. This version is available from the cryptology archive at http://eprint.iacr.org/2004/172/.




             Efficient Selective-ID Secure Identity Based Encryption
                             Without Random Oracles
                                    Dan Boneh∗                     Xavier Boyen
                                Stanford University               Voltage Security

<!-- pdf-page: 2 -->
2     Preliminaries
Before presenting our results we briefly review the definition of security for an IBE system. We
also review the definition of groups equipped with a bilinear map.

2.1   Selective Identity Secure IBE and HIBE Systems
Recall that an Identity Based Encryption system (IBE) consists of four algorithms [Sha84, BF01]:
Setup, KeyGen, Encrypt, Decrypt. The Setup algorithm generates system parameters, denoted by
params, and a master key master-key. The KeyGen algorithm uses the master key to generate the
private key corresponding to a given identity. The encryption algorithm encrypts messages for a


                                                  2

<!-- pdf-page: 3 -->
given identity (using the system parameters) and the decryption algorithm decrypts ciphertexts
using the private key. In a Hierarchical IBE [HL02, GS02] identities are vectors. A vector of
dimension ` represents an identity at depth `. Algorithm KeyGen takes as input an identity
ID = (I1 , . . . , I` ) at depth ` and the private key dID |`−1 of the parent identity ID|`−1 = (I1 , . . . , I`−1 )
at depth ` − 1. It outputs the private key dID for identity ID. We refer to the master-key as the
private key at depth 0 and note that an IBE system is an HIBE where all identities are at depth 1.
    Boneh and Franklin [BF01, BF03] define chosen ciphertext security for IBE systems under a
chosen identity attack. In their model the adversary is allowed to adaptively chose the public
key it wishes to attack (the public key on which it will be challenged). Canetti, Halevi, and
Katz [CHK03, CHK04] define a weaker notion of security in which the adversary commits ahead of
time to the public key it will attack. We refer to this notion as selective identity, chosen ciphertext
secure IBE (IND-sID-CCA). More precisely, selective identity IBE and HIBE security is defined
using the following game:
      Init: The adversary outputs an identity ID∗ where it wishes to be challenged.
      Setup: The challenger runs the Setup algorithm. It gives the adversary the resulting system
          parameters params. It keeps the master-key to itself.
      Phase 1: The adversary issues queries q1 , . . . , qm where query qi is one of:
               – Private key query hIDi i where IDi 6= ID∗ and IDi is not a prefix of ID∗ . The challenger
                 responds by running algorithm KeyGen to generate the private key di corresponding
                 to the public key hIDi i. It sends di to the adversary.
               – Decryption query hCi i for identity ID∗ or any prefix of ID∗ . The challenger responds
                 by running algorithm KeyGen to generate the private key d corresponding to ID∗ (or
                 the relevant prefix thereof as requested). It then runs algorithm Decrypt to decrypt
                 the ciphertext Ci using the private key d. It sends the resulting plaintext to the
                 adversary.
            These queries may be asked adaptively, that is, each query qi may depend on the replies
            to q1 , . . . , qi−1 .
      Challenge: Once the adversary decides that Phase 1 is over it outputs two equal length
          plaintexts M0 , M1 ∈ M on which it wishes to be challenged. The challenger picks a
          random bit b ∈ {0, 1} and sets the challenge ciphertext to C = Encrypt(params, ID∗ , Mb ).
          It sends C as the challenge to the adversary.
      Phase 2: The adversary issues additional queries qm+1 , . . . , qn where qi is one of:
               – Private key query hIDi i where IDi 6= ID∗ and IDi is not a prefix of ID∗ . The challenger
                 responds as in Phase 1.
               – Decryption query hCi i 6= hCi for ID∗ or any prefix of ID∗ . The challenger responds
                 as in Phase 1.
            These queries may be asked adaptively as in Phase 1.
      Guess: Finally, the adversary outputs a guess b0 ∈ {0, 1}. The adversary wins if b = b0 .
We refer to such an adversary A as an IND-sID-CCA adversary. We define the advantage of the
adversary A in attacking the scheme E as
                                                                       1
                                            AdvE,A = Pr[b = b0 ] −
                                                                       2
The probability is over the random bits used by the challenger and the adversary.


                                                         3

<!-- pdf-page: 4 -->
Definition 2.1. We say that an IBE or HIBE system E is (t, qID , qC , )-selective identity, adaptive
chosen ciphertext secure if for any t-time IND-sID-CCA adversary A that makes at most qID chosen
private key queries and at most qC chosen decryption queries we have that AdvE,A < . As
shorthand, we say that E is (t, qID , qC , ) IND-sID-CCA secure.

Semantic Security. As usual, we define selective identity, chosen plaintext security for an IBE
system as in the preceding game, except that the adversary is not allowed to issue any decryption
queries. The adversary may still issue adaptive private key queries.

Definition 2.2. We say that an IBE or HIBE system E is (t, qID , )-selective identity, chosen
plaintext secure if E is (t, qID , 0, )-selective identity, chosen ciphertext secure. As shorthand, we say
that E is (t, qID , ) IND-sID-CPA secure.

2.2     Bilinear Groups
We briefly review the necessary facts about bilinear maps and bilinear map groups [Jou00, Mil04].
We use the following notation:
    1. G and G1 are two (multiplicative) cyclic groups of prime order p;
    2. g is a generator of G.
    3. e is a bilinear map e : G × G → G1 .
    Let G and G1 be two groups as above. A bilinear map is a map e : G × G → G1 with the
following properties:
    1. Bilinearity: for all u, v ∈ G and a, b ∈ Z, we have e(ua , v b ) = e(u, v)ab .
    2. Non-degeneracy: e(g, g) 6= 1.
     We say that G is a bilinear group if the group action in G can be computed efficiently and there
exists a group G1 and an efficiently computable bilinear map e : G × G → G1 as above. Note that
e(, ) is symmetric since e(g a , g b ) = e(g, g)ab = e(g b , g a ).
     Throughout the paper, for a prime order group G we use G∗ to denote the set G \ {1G } where
1G is the identity of G.


3     Complexity Assumptions
Let G be a bilinear group of prime order p. We review the standard Bilinear Diffie-Hellman (BDH)
assumption and define the Bilinear Diffie-Hellman Inversion (BDHI) assumption.

3.1     Bilinear Diffie-Hellman Assumption
The BDH problem [Jou00, SOK00, BF01] in G is as follows: given a tuple g, g a , g b , g c ∈ G as input,
output e(g, g)abc ∈ G1 . An algorithm A has advantage  in solving BDH in G if
                                    h                                 i
                                Pr A(g, g a , g b , g c ) = e(g, g)abc ≥ 

where the probability is over the random choice of generator g in G∗ , the random choice of a, b, c in
Zp , and the random bits used by A. Similarly, we say that an algorithm B that outputs b ∈ {0, 1}
has advantage  in solving the decision BDH problem in G if
                   h                                       i    h                              i
                 Pr B(g, g a , g b , g c , e(g, g)abc ) = 0 − Pr B(g, g a , g b , g c , T ) = 0 ≥ 

                                                      4

<!-- pdf-page: 5 -->
where the probability is over the random choice of generator g in G∗ , the random choice of a, b, c in
Zp , the random choice of T ∈ G1 , and the random bits consumed by B. We refer to the distribution
on the left as PBDH and the distribution on the right as RBDH .

Definition 3.1. We say that the (Decision) (t, )-BDH assumption holds in G if no t-time algorithm
has advantage at least  in solving the (Decision) BDH problem in G.

Occasionally we drop the t and  and refer to the BDH and Decision BDH assumptions in G.


[...]
4     Efficient Selective Identity IBE and HIBE Based on BDH
      Without Random Oracles
We construct an efficient HIBE system that is selective identity secure without random oracles
based on the Decision BDH assumption. In particular, this implies an efficient selective identity,
chosen ciphertext secure IBE based on Decision BDH without random oracles.

4.1    Construction
Let G be a bilinear group of prime order p (the security parameter determines the size of G). Let
e : G × G → G1 be the bilinear map. For now, we assume public keys (ID) of depth ` are vectors
of elements in Zp ` . We write ID = (I1 , . . . , I` ) ∈ Zp ` . The j-th component corresponds to the
identity at level j. We later extend the construction to public keys over {0, 1}∗ by first hashing
each component Ij using a collision resistant hash H : {0, 1}∗ → Zp . We also assume messages to
be encrypted are elements in G1 . The HIBE system works as follows:


                                                       5

<!-- pdf-page: 6 -->
Setup(`): To generate system parameters for an HIBE of maximum depth `, select a random
     generator g in G∗ , a random α ∈ Zp , and set g1 = g α . Next, pick random elements h1 , . . . , h` ∈
     G and a random element g2 ∈ G. The public parameters params and the secret master-key
     are given by
                           params = (g, g1 , g2 , h1 , . . . , h` ) , master-key = g2α

      For j = 1, . . . , `, we define Fj : Zp → G to be the function:                      Fj (x) = g1x hj .

KeyGen(dID |j−1 , ID): To generate the private key dID for an identity ID = (I1 , . . . , Ij ) ∈ Zp j of
    depth j ≤ `, pick random r1 , . . . , rj ∈ Zp and output
                                                         j
                                                                                                  !
                                                         Y
                                     dID =       g2α ·         Fk (Ik )rk , g r1 , . . . , g rj
                                                         k=1

      Note that the private key for ID can be generated just given a private key for ID|j−1 =
      (I1 , . . . , Ij−1 ) ∈ Zp j−1 , as required. Indeed, let dID |j−1 = (d0 , . . . , dj−1 ) be the private key for
      ID|j−1 . To generate dID pick a random rj ∈ Zp and output dID = (d0 ·Fj (Ij )rj , d1 , . . . , dj−1 , g rj ).

Encrypt(params, ID, M): To encrypt a message M ∈ G1 under the public key ID = (I1 , . . . , Ij ) ∈
    Zp j , pick a random s ∈ Zp and output
                                                                               
                                         s      s          s                  s
                          C = e(g1 , g2 ) · M, g , F1 (I1 ) , . . . , Fj (Ij )

      Note that e(g1 , g2 ) can be precomputed once and for all so that encryption does not require
      any pairing computations. Alternatively, e(g1 , g2 ) can be included in the system parameters,
      in which case g2 can be dropped.

Decrypt(dID , C): Consider an identity ID = (I1 , . . . , Ij ). To decrypt a given ciphertext C =
    (A, B, C1 , . . . , Cj ) using the private key dID = (d0 , d1 , . . . , dj ), output
                                                         Qj
                                                           k=1 e(Ck , dk )
                                                  A·                           =M
                                                               e(B, d0 )

      Indeed, for a valid ciphertext, we have
                         Qj                               Qj                 s rk
                           k=1 e(Ck , dk )                 k=1 e(Fk (Ik ), g)                  1
                                             =                   j
                                                                                         =            s
                              e(B, d0 )                    s α                     s r     e(g1 , g2 )
                                                               Q
                                                  e(g, g2 )      k=1 e(g, Fk (Ik ))
                                                                                       k




4.2   Security
The HIBE system above is reminiscent of the Gentry-Silverberg HIBE which is only known to be
secure in the random oracle model. Surprisingly, our choice of functions F1 , . . . , F` enables us to
prove security without random oracles. We prove security of our HIBE system under the standard
Decision BDH assumption in G.

Theorem 4.1. Suppose the (t, )-Decision BDH assumption holds in G. Then the previously defined
`-HIBE system is (t0 , qS , )-selective identity, chosen plaintext (IND-sID-CPA) secure for arbitrary `
and qS , and any t0 < t − Θ(τ ` qS ) where τ is the maximum time for an exponentiation in G.


                                                                 6

<!-- pdf-page: 7 -->
Proof. Suppose A has advantage  in attacking the HIBE system. We build an algorithm B
that solves the Decision BDH problem in G. Algorithm B is given as input a random 5-tuple
(g, g a , g b , g c , T ) that is either sampled from PBDH (where T = e(g, g)abc ) or from RBDH (where
T is uniform and independent in G1 ). Algorithm B’s goal is to output 1 if T = e(g, g)abc and 0
otherwise. Set g1 = g a , g2 = g b , g3 = g c . Algorithm B works by interacting with A in a selective
identity game as follows:
Initialization. The selective identity game begins with A first outputting an identity ID∗ =
      (I∗1 , . . . , I∗k ) ∈ Zp k of depth k ≤ ` that it intends to attack. If necessary, B appends ran-
      dom elements in Zp to ID∗ so that ID∗ is a vector of length `.
Setup. To generate the system parameters, algorithm B picks α1 , . . . , α` ∈ Zp at random and
                          −I∗
      defines hj = g1 j g αj ∈ G for j = 1, . . . , `. It gives A the system parameters params =
      (g, g1 , g2 , h1 , . . . , h` ). Note that the corresponding master key, which is unknown to B, is
      g2a = g ab ∈ G. As before, for j = 1, . . . , ` we define Fj : Zp → G to be the function
                                                                                       x−I∗j α
                                                          Fj (x) = g1x hj = g1                gj



Phase 1. A issues up to qS private key queries. Consider a query for the private key corresponding
    to ID = (I1 , . . . , Iu ) ∈ Zp u where u ≤ `. The only restriction is that ID is not a prefix of ID∗ .
    Let j be the smallest index such that Ij 6= I∗j . Necessarily 1 ≤ j ≤ u. To respond to the
    query, algorithm B first derives a private key for the identity (I1 , . . . , Ij ) from which it then
    constructs a private key for the requested identity ID = (I1 , . . . , Ij , . . . , Iu ). Algorithm B picks
    random elements r1 , . . . , rj ∈ Zp and sets
                         −αj      j                                                                                             −1
                        Ij −I∗    Y                                                                                           Ij −I∗
                                                   rv                r1                              rj−1
               d0 = g2       j
                                          Fv (Iv ) ,      d1 = g ,              ...,   dj−1 = g             ,       d j = g2       j
                                                                                                                                       g rj
                                  v=1

      We claim that (d0 , d1 , . . . , dj ) is a valid random private key for (I1 , . . . , Ij ). To see this, let
      r̃j = rj − b/(Ij − I∗j ). Then we have that
                      −αj                            −αj
                                                                                                               b
                    (Ij −I∗
                          j)                       (Ij −I∗
                                                         j)     Ij −I∗                    Ij −I∗        rj − I −I∗
                                        rj
                  g2           Fj (Ij )      = g2             (g1    j
                                                                         g αj )rj = g2a (g1    j
                                                                                                   g αj )       j     j   = g2a Fj (Ij )r̃j
      It follows that the private key (d0 , d1 , . . . , dj ) defined above satisfies
                                  j−1
                                  Y
                 d0 = g2a · (             Fv (Iv )rv ) · Fj (Ij )r̃j ,         d1 = g r1 , . . . , dj−1 = g rj−1 ,              dj = g r̃j
                                  v=1

      where r1 , . . . , rj−1 , r̃j are uniform in Zp . This matches the definition for a private key for
      (I1 , . . . , Ij ). Hence, (d0 , d1 , . . . , dj ) is a valid private key for (I1 , . . . , Ij ). Algorithm B derives
      a private key for the requested ID from the private key (d0 , d1 , . . . , dj ) and gives A the result.
Challenge. When A decides that Phase 1 is over, it outputs two messages M0 , M1 ∈ G1 on which
    it wishes to be challenged. Algorithm B picks a random bit b ∈ {0, 1} and responds with the
    ciphertext C = (Mb · T, g3 , g3α1 , . . . , g3αk ). Since Fi (I∗i ) = g αi for all i, we have that
                                              C = (Mb · T, g c , F1 (I∗1 )c , . . . , Fk (I∗k )c )
      Hence, if T = e(g, g)abc = e(g1 , g2 )c then C is a valid encryption of Mb under the public key
      ID∗ = (I∗1 , . . . , I∗k ). On the other hand, when T is uniform and independent in G1 (when the
      input 5-tuple is sampled from RBDH ) then C is independent of b in the adversary’s view.

                                                                           7

<!-- pdf-page: 8 -->
Phase 2. A continues to issue queries not issued in Phase 1. Algorithm B responds as before.

Guess. Finally, A outputs a guess b0 ∈ {0, 1}. Algorithm B concludes its own game by outputting
    a guess as follows. If b = b0 then B outputs 1 meaning T = e(g, g)abc . Otherwise, it outputs
    0 meaning T 6= e(g, g)abc .

    When the input 5-tuple is sampled from PBDH (where T = e(g, g)abc ) then A’s view is identical
to its view in a real attack game and therefore A must satisfy | Pr[b = b0 ] − 1/2| > . On the
other hand, when the input 5-tuple is sampled from RBDH (where T is uniform in G1 ) then
Pr[b = b0 ] = 1/2. Therefore, with g uniform in G∗ , a, b, c uniform in Zp , and T uniform in G1 we
have that
                                                                                
       h
               a b c            abc
                                      i    h
                                                  a b c
                                                                    i        1       1
     Pr B(g, g , g , g , e(g, g) ) = 0 − Pr B(g, g , g , g , T ) = 0 ≥         ± −      = 
                                                                             2       2

as required. This completes the proof of Theorem 4.1.


[...]
4.4   Arbitrary Identities
We can extend our HIBE above to handle identities ID = (I1 , . . . , I` ) with Ij ∈ {0, 1}∗ (as opposed
to Ij ∈ Zp ) by first hashing each Ij using a collision resistant hash function H : {0, 1}∗ → Zp prior
to key generation and encryption. A standard argument shows that if the scheme above is selective
identity, chosen ciphertext secure then so is the scheme with the additional hash function. We note
that there is no need for a full domain hash into Zp ; for example, a collision resistant hash function
H : {0, 1}∗ → {1, . . . , 2b } where 2b < p is sufficient for the security proof.
