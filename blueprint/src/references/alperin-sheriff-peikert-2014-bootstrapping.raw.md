<!-- generated-by: scoped Poppler extraction of the passages used (DW-7) -->
<!-- source-pdf-sha256: cecd346d2e879ff865c23fe977e172e1068f20b01c7f555a419d2f3d5ec2c0da -->
<!-- extractor: pdftotext version 24.02.0; -layout; scoped to the line ranges listed below -->
<!-- scope (physical page: lines of the -layout text): p1: 1-4; p7: 285-338; p8: 339-392; p9: 393-443; p10: 444-493; p11: 494-542; p12: 543-582; p13: 613-636; p14: 637-685; p15: 686-735; p16: 736-750 -->
<!-- note: physical page p is printed page p-1 (the first page is unnumbered) -->

<!-- pdf-page: 1 -->
                       Faster Bootstrapping with Polynomial Error
                                    Jacob Alperin-Sheriff∗                   Chris Peikert†

                                                        June 13, 2014

<!-- pdf-page: 7 -->
2.2        Symmetric Groups and Zq -Embeddings
Here we recall some basic facts about symmetric groups, which can be found in most abstract algebra
textbooks, e.g., [Jac12]. Let Sr denote the symmetric group of order r, i.e., the group of permutations
(bijections) π : {1, . . . , r} → {1, . . . , r} with function composition as the group operation. The group Sr is
isomorphic to the multiplicative group of r-by-r permutation matrices (i.e., 0-1 matrices with exactly one
nonzero element in each row and each column), via the map that associates π ∈ Sr with the permutation
matrix Pπ = [eπ(1) eπ(2) · · · eπ(r) ], where ei ∈ {0, 1}r is the ith standard basis vector. For the remainder
of this work we identify permutations with their associated permutation matrices.
     The additive cyclic group (Zr , +) embeds into the symmetric group Sr via the injective homomorphism
that sends the generator 1 ∈ Zr to the “cyclic shift” permutation π ∈ Sr , defined as π(i) = i + 1 for
1 ≤ i < r and π(r) = 1.3 Clearly, this embedding and its inverse can be computed efficiently. Notice also
that the permutation matrices in the image of this embedding can be represented more compactly by just their
first column, because the remaining columns are just the successive cyclic shifts of this column. Similarly,
such permutation matrices can be multiplied in only O(r2 ) operations, since we only need to multiply one
matrix by the first column of the other.
     For our efficient bootstrapping algorithm, we need to efficiently embed a group (Zq , +), for some
sufficiently large q of our choice, into a symmetric group of order much smaller than q (e.g., polylogarithmic
in q). This can be done as follows: suppose that q = r1 r2 · · · rt , where the ri are pairwise coprime. Then by
the Chinese Remainder Theorem, the ring Zq is isomorphic to the direct product of rings Zr1 ×Zr2 ×· · ·×Zrt ,
and hence their additive groups are isomorphic as well. Combining this with the group embeddings of (Zri , +)
into Sri , we have an (efficient) group embedding from (Zq , +) into Sr1 × Sr2 × · · · × Srt .4
     Importantly for our purposes, q can be exponentially large in terms of maxi ri above. This can be shown
using lower bounds on the second Chebyshev function
                                                   X                Y
                                                                       pblogp xc ,
                                                                                
                                      ψ(x) :=           log p = log
                                                        pk ≤x                 p≤x


where the first summation is over all prime powers pk ≤ x, and the second is over all primes p ≤ x; note that
pblogp xc is the largest power of p not exceeding x. Therefore, the product q of all maximal prime powers
ri = pblogp xc ≤ x is exp(ψ(x)). Asymptotically, it is known that ψ(x) = x ± O(x/ log x), and we also
have the nonasymptotic bound ψ(x) ≥ 3x/4 for all x ≥ 7 [Sch76, Theorem 11]. In summary:

Lemma 2.2. For all x ≥ 7, the product of all maximal prime powers ri ≤ x is at least exp(3x/4).

For any given lower bound q0 ≥ 191 > exp(21/4), we can therefore efficiently find a q ≥ q0 whose maximal
prime-power divisors are all at most x = 43 log q0 ≥ 7.


3        GSW Cryptosystem
Here we present a variant of the Gentry-Sahai-Waters homomorphic encryption scheme [GSW13] (hereafter
called GSW), which we believe is simpler to understand at a technical level. We also give a tighter analysis
of its error growth under homomorphic operations.
    3
        This is just a special case of Cayley’s theorem, which saysPthat any group G embeds into the symmetric group S|G| .
    4
        The latter group can be seen as a subgroup of Sr for r = i ri , but it will be more efficient to retain the product structure.




                                                                     6

<!-- pdf-page: 8 -->
3.1   Background
We first recall some standard background (see, e.g., [MP12] for further details). For a modulus q, let
` = dlog2 qe and define the “gadget” (column) vector g = (1, 2, 4, . . . , 2`−1 ) ∈ Z`q . Note that the penultimate
entry 2`−2 of g is in the interval [q/4, q/2) mod q. It will be convenient to use the following randomized
“decomposition” function.

Claim 3.1 (Adapted from [MP12]). There is a randomized, efficiently computable function g−1 : Zq → Z`
such that x ← g−1 (a) is subgaussian with parameter O(1), and always satisfies hg, xi = a.

     Briefly, the algorithm described in the claim works as follows (though for our application it is not necessary
to understand its internals): let S ∈ Z`×` be the basis of the lattice Λ⊥ (gt ) = {z ∈ Z` : hg, zi = 0 ∈ Zq }
as constructed in [MP12], whose Gram-Schmidt vectors all have Euclidean norm O(1). Given a ∈ Zq ,
run a randomized version of the nearest-plane algorithm [Bab85] with basis S to sample from the coset
Λ⊥    t
  a (g ) = {x : hg, xi = a}, where in each iteration of the algorithm we choose the coefficient of the ith
basis vector to have expectation zero over {ci − 1, ci } for an appropriate ci ∈ 1q Z ∩ [0, 1). In particular, the
                                              √
coefficient is subgaussian with parameter 2π given any fixed values of the previous coefficients. The final
output x is the linear combination of the (orthogonal) Gram-Schmidt vectors of S with these coefficients, and
is therefore subgaussian with parameter O(1).
     For vectors and matrices over Zq , define the randomized function G−1 : Zn×m     q     → Zn`×m by apply-
ing g−1 independently to each entry. Notice that for any A ∈ Zn×m         q   , if X ← G−1 (A) then X has
subgaussian parameter O(1) and

                     G · X = A,       where G = gt ⊗ In = diag(gt , . . . , gt ) ∈ Zqn×n`                    (3.1)

is the block matrix with n copies of gt as diagonal blocks, and zeros elsewhere.

3.2   Cryptosystem and Homomorphic Operations
The GSW scheme is parameterized by a dimension n, a modulus q with ` = dlog2 qe, and some error
distribution χ over Z which we assume to be subgaussian. Formally, the message space is the ring of
integers Z, though for bootstrapping we only work with ciphertexts encrypting messages in {0, 1} ⊂ Z. The
ciphertext space is C = Zn×n`
                         q     . For simplicity we present just a symmetric-key scheme, which is sufficient for
our purposes (it can be converted to a public-key or even attribute-based scheme, as described in [GSW13]).
    Our GSW variant differs from the original scheme described in [GSW13] in two main ways:

   1. In [GSW13], a ciphertext is a square binary matrix C ∈ {0, 1}n` , a secret key is a “structured” mod-q
      vector s ∈ Zn`
                  q (having large entries), and s is an “approximate mod-q eigenvector” of C, in the sense
      that s C ≈ µst (mod q), where µ ∈ Z is the message.
            t

       In our variant, a ciphertext is a rectangular mod-q matrix C ∈ Zn×n`
                                                                       q     , a secret key is some (unstructured,
       short) integer vector s ∈ Zn , and st C ≈ µ · st G (mod q), i.e., s and Gt s are corresponding left- and
       right- “approximate singular vectors” of C.
      The difference between these two variants turns out to be purely syntactic, in that we can efficiently
      and “losslessly” switch between them (without needing the secret key). However, we believe that our
      variant leads to simpler notation and easier-to-understand operations and analysis.



                                                         7

<!-- pdf-page: 9 -->
   2. The second difference is more substantial: our homomorphic multiplication procedure uses the
      randomized G−1 (·) operation from Claim 3.1. This yields a few important advantages, such as a very
      tight and simple error analysis using subgaussianity (see Lemma 3.5), and the ability to completely
      re-randomize the error in a ciphertext (see Corollary 3.6).

We now describe the scheme formally.

GSW.Gen(): choose s̄ ← χn−1 and output secret key s = (s̄, 1) ∈ Zn .
                                                      (n−1)×n`
GSW.Enc((s̄, 1), µ ∈ Z): choose C̄ ← Zq                          and e ← χm , let bt = et − s̄t C̄ (mod q), and output
    the ciphertext                                          
                                                            C̄
                                                        C=     + µG ∈ C,
                                                            bt
       where G is as defined in Equation (3.1). Notice that st C = et + µ · st G (mod q).
GSW.Dec(s, C ∈ C): let c be the penultimate column of C, and output µ = bhs, cie2 , where b·e2 : Zq →
    {0, 1} indicates whether its argument is closer modulo q to 0 or to 2`−2 (the penultimate entry of g).5
Homomorphic addition is defined as C1 ‘ C2 = C1 + C2 .
Homomorphic multiplication is defined as C1 d C2 ← C1 · G−1 (C2 ), and is right associative. Notice
    that this is a randomized procedure, because G−1 is randomized.

    The IND-CPA security of the scheme follows immediately from the assumed hardness of LWEn−1,q,χ ,
where the entries of the secret are drawn from the error distribution χ (which is no easier than for a uniformly
random secret; see [ACPS09, Lemma 2]). This is because a fresh ciphertext is just µG plus a matrix of n`
independent LWE samples under secret s̄, which are pseudorandom by assumption and hence hide µG.

3.3    Analysis
Here we analyze the scheme’s correctness and homomorphic operations.

Definition 3.2. We say that a ciphertext C is designed to encrypt message µ ∈ Z (under a secret key s) if it
is a fresh encryption of µ, or if C = C1 ‘ C2 where C1 , C2 are respectively designed to encrypt µ1 , µ2 ∈ Z
and µ = µ1 + µ2 , or similarly for homomorphic multiplication.

Definition 3.3. We say that a ciphertext C that is designed to encrypt µ ∈ Z (under s) has error vector
et ∈ Zn` if st C − µ · st G = et (mod q).

     For convenience later on, we also say the matrix µG is designed to encrypt µ, and has error 0. (This is
essentially implied by the above definitions, since µG is indeed a fresh encryption of µ, assuming that zero is
in the support of χ.) The next claim on the correctness of decryption follows immediately from the fact that
s = (s̄, 1) and the penultimate column of G is (0, . . . , 0, 2`−2 ), where 2`−2 ∈ [q/4, q/2) mod q.

Claim 3.4. If C is designed to encrypt some µ ∈ {0, 1} ⊂ Z, and has error vector et whose penultimate
coordinate has magnitude less than q/8, then GSW.Dec(s, C) correctly outputs µ.

We now analyze the behavior of the error terms under homomorphic operations.
   5
     Note that we can decrypt messages in Z ∩ [− 2q , 2q ), or any other canonical set of representatives of Zq , by “decoding” st C to
the nearest multiple of st G. The above decryption algorithm will be sufficient for our purposes.


                                                                  8

<!-- pdf-page: 10 -->
Lemma 3.5. Suppose C1 , C2 are respectively designed to encrypt µ1 , µ2 ∈ Z and have error vectors et1 , et2 .
Then C1 ‘ C2 has error vector et1 + et2 , and C1 d C2 has error vector et1 X + µ1 et2 , where X ← G−1 (C2 )
is the matrix used in the evaluation of d. In particular, for any values of Ci , ei , µi , the latter error vector is
of the form et + µ1 et2 , where the entries of e are independent and subgaussian with parameter O(ke1 k).

    Importantly, the error in C1 d C2 is quasi-additive and asymmetric with respect to the errors in C1 , C2 :
while the first error vector et1 is multiplied by a short (subgaussian) matrix X, the second error vector et2 is
only multiplied by the (scalar) message µ1 , which we will ensure remains in {0, 1}.

Proof. The first claim is immediate, by linearity. For the second claim, because G · X = C2 we have

                                 st (C1 d C2 ) = st C1 · X
                                                = (et1 + µ1 · st G)X
                                                = et1 X + µ1 (et2 + µ2 · st G)
                                                = (et1 X + µ1 et2 ) + µ1 µ2 · st G.

    As observed in [BV14], the asymmetric noise growth allows for performing a long chain of homomorphic
multiplications while only incurring a polynomial-factor error growth, because d is defined to be right
associative. For convenience of analysis, in such a chain we always include the fixed ciphertext G, which
is designed to encrypt µ = 1 and has zero error, as the rightmost ciphertext in the chain. This ensures that
the error vector of the output ciphertext is subgaussian and essentially independent of the errors in the input
ciphertexts (apart from their lengths), which leads to a simpler and tighter analysis. (In [BV14] a weaker
independence guarantee was achieved by a separate “partial re-randomization” procedure, which requires
additional public key material.)

Corollary 3.6. Suppose that Ci for i ∈ [k] are respectively designed to encrypt µi ∈ {0, ±1} and have
error vectors eti . Then for any fixed values of these variables,
                                  ô
                           C←         Ci d G = C1 d (C2 d (· · · (Ck d G) · · · ))
                                 i∈[k]

has an error vector whose entries are mutually independent and subgaussian with parameter O(kek), where
et = (et1 , . . . , etk ) ∈ Zkn` is the concatenation of the individual error vectors.

Proof. By Lemma 3.5, the error vector in C is i eti Xi , where each eti Xi is a fresh independent vector that
                                              P
has mutually independent coordinates and is subgaussian with parameter O(kei k). The claim then follows by
Pythagorean additivity.


4    Homomomorphic Encryption for Symmetric Groups
Brakerski and Vaikuntanathan [BV14] showed how to use the GSW encryption scheme to homomorphically
compose permutations of five elements (i.e., to homomorphically compute the group operation in the
symmetric group S5 ) with small additive noise growth; the use of S5 comes from its essential role in
Barrington’s theorem [Bar86]. In [BV14], the homomorphic composition of permutations is intertwined with
the evaluation of a branching program given by Barrington’s theorem. Here we give, as a “first-class object,”
a homomorphic cryptosystem for any symmetric group Sr . The ability to use several different small values
of r, along with a homomorphic equality test that we design, will be central to our bootstrapping algorithm.

                                                         9

<!-- pdf-page: 11 -->
4.1      Encryption Scheme
We now describe our (symmetric-key) homomorphic encryption scheme for symmetric groups, called
HEPerm. Let C denote the ciphertext space for an appropriate instantiation of the GSW scheme, which we
treat as a “black box.” A secret key sk for HEPerm is simply a secret key for the GSW scheme.

       • HEPerm.Enc(sk, π ∈ Sr ): let P = (pi,j ) ∈ {0, 1}r×r be the permutation matrix associated with π.
         Output an entry-wise encryption of P, i.e., the ciphertext

                                         C = (ci,j ) ∈ C r×r , where ci,j ← Enc(sk, pi,j ).

    (Decryption follows in the obvious manner.) As with the GSW system, we say that a ciphertext C ∈ C r×r
is designed to encrypt a permutation π ∈ Sr (or its permutation matrix Pπ ) if its C-entries are designed
to encrypt the corresponding entries of Pπ . For convenience, we let J ∈ C r×r denote the ciphertext that
encrypts the identity permutation with zero noise, which is built in the expected way from the fixed zero-error
GSW ciphertexts that encrypt 0 and 1.
    We now show how to homomorphically compute two operations: the standard composition operation for
permutations, and an equality test.

Homomorphic composition Cπ e Cσ : on ciphertexts Cπ = (cπi,j ), Cσ = (cσi,j ) ∈ C r×r encrypting permu-
    tations π, σ ∈ Sr respectively, we compute one encrypting the permutation π ◦ σ by homomorphically
    evaluating the naı̈ve matrix-multiplication algorithm.6 That is, output C = (ci,j ) ∈ C r×r where
                                                 ð π
                                         ci,j ←      (ci,` d cσ`,j ) ∈ C.                             (4.1)
                                                              `∈[r]

         Just like d, we define e to be right associative.

Homomorphic equality test Eq?(Cπ = (cπi,j ), σ ∈ Sr ): given a ciphertext encrypting some permutation
    π ∈ Sr and a permutation σ ∈ Sr (in the clear), output a ciphertext c ∈ C encrypting 1 if π = σ and 0
    otherwise, as                               ô π
                                          c←         cσ(i),i d g,
                                                               i∈[r]

         where g ∈ C denotes the fixed zero-error encryption of 1. (Recall that d is right associative.)

    Observe that for the above two operations, the GSW ciphertext(s) in the output are designed to encrypt
the appropriate {0, 1}-message. For Compose this is simply by correctness of the matrix-multiplication
algorithm. For Eq? this is because the output ciphertext is designed to encrypt 1 if and only if every cσ(i),i is
designed to encrypt 1, which is the case if and only if Cπ is in fact designed to encrypt σ. All that remains is
to analyze the behavior of the error terms, which we do next.
   6
     Note that asymptotically faster algorithms (e.g., Strassen’s) do not appear suitable here, because the intermediate steps of these
algorithms can result in values having magnitude greater than one, which can cause the error in the ciphertexts to grow much faster.
In any case, this will not matter much in our application, since r will be small.




                                                                 10

<!-- pdf-page: 12 -->
4.2   Analysis
Recalling that the GSW scheme is parameterized by n and q, denote its space of error vectors by E = Zm
where m = ndlog2 qe. The Euclidean norm on E r = Zmr is defined in the expected way. In what follows it
is often convenient to consider vectors and matrices over E, i.e., each entry is itself a (row) vector in E = Zm ,
and we switch between E h×w and Zh×wm as is convenient.
     The following lemma describes the behavior of errors under the homomorphic composition operation e.
Note that working with vectors and matrices over E lets us write a statement that is syntactically very similar
to the one from Lemma 3.5, with a very similar proof.
Lemma 4.1. Let Cπ , Cσ ∈ C r×r respectively be designed to encrypt permutation matrices Pπ , Pσ ∈
{0, 1}r×r with error matrices Eπ , Eσ ∈ E r×r . Then for any fixed values of these variables, Cπ e Cσ has
error matrix E + Pπ · Eσ ∈ E r×r , where the Z-entries of E are mutually independent, and those in its ith
row are subgaussian with parameter O(keπi k), where eπi is the ith row of Eπ .

Proof. Let C ← Cπ e Cσ . It suffices to show that for all i, j, its (i, j)th entry ci,j ∈ C has error

                                          ei,j + eσπ−1 (i),j ∈ E = Zm ,

where all the Z-entries of all the ei,j ∈ Zm are mutually independent and subgaussian with parameter
O(keπi k), and eσ`,j is the (`, j)th entry of Eσ . This follows directly from Equation (4.1) and Lemma 3.5:
the error in each ciphertext cπi,` d cσ`,j is pπi,` · eσ`,j plus a fresh vector whose entries are independent and
subgaussian with parameter O(keπi,` k). Since pπi,` = 1 for ` = π −1 (i) and 0 otherwise, the claim follows by
Pythagorean additivity of independent subgaussians.

    Similarly to a multiplication chain of GSW ciphertexts, we can perform a (right-associative) chain of
compositions while incurring only small error growth. For convenience of analysis, we always include the
fixed zero-error ciphertext J ∈ C r×r (which encrypts the identity permutation) as the rightmost ciphertext
in the chain. The following corollary follows directly from Lemma 4.1 in the same way that Corollary 3.6
follows from Lemma 3.5.
Corollary 4.2. Suppose that Ci ∈ C r×r for i ∈ [k] are respectively designed to encrypt permutation matrices
Pi ∈ {0, 1}r×r and have error matrices Ei ∈ E r×r . Then for any fixed values of these variables,
                              õ
                        C←        Ci e J = C1 e (C2 e (· · · (Ck e J) · · · ))
                                 i∈[k]

has an error matrix whose Z-entries are mutually independent, and those in its ith row are subgaussian with
parameter O(kei k), where eti ∈ E kr is the ith row of the concatenated error matrices [E1 | · · · | Ek ].

    Finally, since the Eq? procedure simply performs a chain of (right-associative) multiplications of GSW
ciphertexts, Corollary 3.6 applies.


<!-- pdf-page: 13 -->
5     Bootstrapping
We now describe our bootstrapping procedure.

5.1   Specification and Usage
We start by specifying the abstract preconditions and output guarantees of our bootstrapping algorithm,
and describe how to use it (with some additional pre- and post-processing) to bootstrap known LWE-based
encryption schemes.
    The scheme to be bootstrapped must have binary ciphertexts in {0, 1}d and secret keys in Zdq for some
dimension d and modulus q that should be made as small as possible (q, d = Õ(λ) are possible), and a
decryption function of the form Decs (c) = f (hs, ci) ∈ {0, 1} for some arbitrary function f : Zq → {0, 1}.
We rely on an appropriate instantiation of the GSW cryptosystem, as described in further detail in Section 5.2
below.

BootGen(s ∈ Zdq , sk) takes as input a secret key vector s ∈ Zdq from the scheme to be bootstrapped, and a
     secret key sk for GSW. It outputs a bootstrapping key bk, which appropriately encrypts s under sk.

Bootstrap(bk, c ∈ {0, 1}d ) takes as input the bootstrapping key bk and a ciphertext vector c ∈ {0, 1}d
     (which decrypts under the secret key s). It outputs a GSW ciphertext which decrypts (under sk) to the
     same bit as c does (under s), but with less error.




                                                     12

<!-- pdf-page: 14 -->
Pre- and post-processing. We can bootstrap all known LWE-based bit-encryption schemes using the above
algorithms as follows. In all LWE-based encryption schemes, decryption can be expressed as a “rounded
inner product” bhs, cie2 for some appropriate rounding function b·e2 : Zq → {0, 1}, as required. Note that
a GSW ciphertext can trivially be put in this form by just taking its penultimate column (see GSW.Dec
in Section 3.2). As for the other conditions we need (binary ciphertexts and small d, q), LWE encryption
schemes are not always presented in a way that fulfills them, but fortunately there are standard transformations
that do so, as we now describe. (See [BV11, BLP+ 13] for further details.)
    First, since we do not need to perform any further homomorphic operations on the ciphertext, we can use
dimension- and modulus-reduction [BV11] to get a ciphertext c̄ (over Zq ) of dimension Õ(λ) and modulus
q = Õ(λ), while preserving correct decryption. These steps can be implemented with 2λ security under
conventional lattice assumptions.7 Then, we can obtain a binary ciphertext c using “bit decomposition:” let
G be as defined in Section 3.1, and for the ciphertext c̄ over Zq under secret key s̄, let c be a {0, 1}-vector
such that Gc = c̄, and let s = Gt s̄ so that hs, ci = hs̄, c̄i ∈ Zq . (The secret key s is therefore the one we
need to provide to BootGen.)
    After bootstrapping, the output is a GSW ciphertext C encrypted under sk (which is just an integer
vector). If desired, we can convert this ciphertext back to one for the original LWE cryptosystem, simply by
taking the penultimate column of C. We can also key-switch from sk back to the original secret key s. (As
usual in bootstrapping, going “full circle” in this way requires an appropriate circular security assumption.)

5.2      Procedures
Our algorithms rely on instantiations of GSW and HEPerm with parameters n, Q, χ. Importantly, the
ciphertext modulus Q is not the modulus q of the scheme we are bootstrapping, but rather some Q  q that
                                                      Q ciphertext. Let C denote the GSW ciphertext space.
is sufficiently larger than the error in Bootstrap’s output
     Our procedures need q to be of the form q = i∈[t] ri where the ri are small and powers of distinct
primes (and hence pairwise coprime). Specifically, using Lemma 2.2 we can choose q = Õ(λ) to be large
enough by letting it be the product of all maximal prime-powers ri that are bounded by O(log λ), of which
there are t = O(log λ/ log log λ). Let φ be the group embedding of (Zq , +) ∼  = (Zr1 × · · · × Zrt , +) into
S = Sr1 × · · · × Srt described in Section 2.2, and let φi denote the ith component of this embedding, i.e.,
the one from Zq into Sri .
BootGen(s ∈ Zdq , sk): given secret key s ∈ Zdq for the scheme to be bootstrapped and a secret key sk
     for HEPerm, embed each coordinate sj ∈ Zq of s as φ(sj ) ∈ S and encrypt the components under
     HEPerm. That is, generate and output the bootstrapping key
                                  bk = {Ci,j ← HEPerm.Enc(sk, φi (sj )) : i ∈ [t], j ∈ [d]}.

         Recalling that we are working with embeddings of Zri , each Ci,j ∈ C ri can be represented as a tuple
         of ri GSW ciphertexts encrypting an indicator vector (see Section 4.3). Because t, ri = O(log λ) and
         d = Õ(λ), the bootstrapping key consists of Õ(λ) GSW ciphertexts.
Bootstrap(bk, c ∈ {0, 1}d ): given a binary ciphertext c ∈ {0, 1}d , do the following:

         Inner Product: Homomorphically compute an encryption of
                                                        X
                                          v = hs, ci =       sj ∈ Zq
                                                                       j : cj =1
   7
       To make the modulus quasi-linear, we need to use randomized (subgaussian) rounding in the modulus-reduction step.


                                                                13

<!-- pdf-page: 15 -->
           using the encryptions of the sj ∈ Zq as embedded into the permutation group S, via a chain of
           compositions. Formally, for each i ∈ [t] compute (recalling that e is right associative, and J is
           the fixed HEPerm encryption of the identity permutation)
                                                       õ
                                              Ci ←           Ci,j e J.                                 (5.1)
                                                       j s.t. cj =1

           Again, because we are working with embeddings of Zri , each Ci ∈ C ri .
      Round: Homomorphically map v ∈ Zq to f (v) ∈ Z2 = {0, 1}: for each x ∈ Zq such that f (x) = 1,
                                               ?
           homomorphically test whether v = x by homomorphically multiplying the GSW ciphertexts
                                                   ?
           resulting from all the equality tests v = x (mod ri ). Then homomorphically sum the results of
                     ?
           all the v = x tests.
           Formally, compute and output the GSW ciphertext (recalling that d is right associative, and G is
           the fixed GSW encryption of 1)
                                            ð      ô                            
                                C←                      Eq?(Ci , φi (x)) d G .                         (5.2)
                                        x∈Zq s.t. f (x)=1 i∈[t]

           Note that since we are working with embeddings of Zri , each Eq?(Ci , φi (x)) is just some GSW
           ciphertext component of Ci ∈ C ri (see Section 4.3).

      Because t, ri = O(log λ) and d = Õ(λ) and by Equations (5.1) and (5.2), Bootstrap performs Õ(λ)
      homomorphic multiplications and additions on GSW ciphertexts.

5.3   Analysis
The following is our main theorem.
Theorem 5.1. The above bootstrapping scheme can be instantiated to be correct (with overwhelming
probability) and secure assuming that the decisional Shortest Vector Problem (GapSVP) and Shortest
Independent Vectors Problem (SIVP) are (quantumly) hard to approximate in the worst case to within Õ(n2 λ)
factors on n-dimensional lattices.

    Because all known (quantum) algorithms for poly(n)-factor approximations to GapSVP and SIVP on
n-dimensional lattices take 2Ω(n) time, for 2λ hardness we can take n = Θ(λ), yielding a final approximation
factor of Õ(n3 ). This comes quite close to the O(n3/2+ ) factors obtained in [BV14], but without any
expensive “dimension leveraging:” we use GSW ciphertexts of dimension only n = O(λ), rather than some
large polynomial in λ. Alternatively, at the cost of a larger dimension n = λ1/ , but without using the
successive dimension-reduction procedure from [BV14], we can obtain factors as small as Õ(n2+ ) for any
constant  > 0.
The remainder of this subsection is devoted to proving the above theorem.

Security. If the HEPerm key sk is generated independently of s, then IND-CPA security of the bootstrap-
ping key follows immediately from the security of HEPerm, hence from LWE with parameters n − 1, Q, χ,
and finally from worst-case lattice problems. (We instantiate these parameters below to obtain the claimed
approximation factors.) As usual, if the keys are not independent, then we need to make an appropriate
circular security assumption. (To date, such an assumption is the only known way to obtain unbounded FHE.)

                                                      14

<!-- pdf-page: 16 -->
Correctness and error analysis. For correctness, we first show that the ciphertext C output by Bootstrap
is designed to encrypt the appropriate bit. Then we quantify the error in C and instantiate the parameters so
that it indeed decrypts to the intended bit.
Lemma 5.2 (Correctness). For bk ← BootGen(s, sk), the GSW ciphertext C ← Bootstrap(bk, c) is
designed to encrypt Decs (c) = f (hs, ci) ∈ {0, 1}.

Proof. First, by construction the HEPerm ciphertext Ci,j is designed to encrypt φi (sj ). Therefore, because
    Zq → Sri is a group homomorphism, the ciphertext Ci as defined in Equation (5.1) is designed to encrypt
φi :P
φi ( j : cj =1 sj ) = φi (hs, ci) = φi (v). By correctness of Eq? and the isomorphism Zq ∼= Zr1 × · · · × Zrt
                                                                    Ô
given by Chinese Remainder Theorem, the homomorphic product i∈[t] Eq?(Ci , φi (x)) d G is designed to
encrypt 1 if and only if v = x. Finally, because the homomorphic sum is taken over every x ∈ Zq such that
f (x) = 1, it is designed to encrypt 1 if and only if f (v) = 1.
