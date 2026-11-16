# AP14: excerpts of the passages used (Gate 41)

**Reference.** J. Alperin-Sheriff, C. Peikert, *Faster Bootstrapping with Polynomial Error*, CRYPTO 2014; IACR ePrint 2014/094, version dated 13 June 2014 (18 pp.).

**Extraction.** `pdftotext -layout` (poppler) of the uploaded PDF, SHA-256 `cecd346d2e879ff865c23fe977e172e1068f20b01c7f555a419d2f3d5ec2c0da` (checked when this file was written); line numbers are those of the extracted text. The PDF itself is not committed (pairing ruling Q12; GSW ruling Q14 and the plan-section provenance). Only the passages below are quoted. Mathematical layout (sub- and superscripts, fraction bars) is flattened by the extraction; read formulas against the Lean statements and the PDF where needed.

**Passages.**

- lines 1–3: title
- lines 326–483: §3: §3.1 (gadget g, Claim 3.1, Equation (3.1)), §3.2 (the GSW variant: Gen, Enc, Dec, the operations, IND-CPA remark), §3.3 (Definitions 3.2–3.3, Claim 3.4, Lemma 3.5, Corollary 3.6)
- lines 484–581: §4 to Corollary 4.2: Equation (4.1) (cited by `Encrypts.sum`) and the permutation-matrix chains (phase-7 roadmap, ruled Q12 for BV14)

## Lines 1–3: title

```text
                       Faster Bootstrapping with Polynomial Error
                                    Jacob Alperin-Sheriff∗                   Chris Peikert†
```

## Lines 326–483: §3: §3.1 (gadget g, Claim 3.1, Equation (3.1)), §3.2 (the GSW variant: Gen, Enc, Dec, the operations, IND-CPA remark), §3.3 (Definitions 3.2–3.3, Claim 3.4, Lemma 3.5, Corollary 3.6)

```text
3        GSW Cryptosystem
Here we present a variant of the Gentry-Sahai-Waters homomorphic encryption scheme [GSW13] (hereafter
called GSW), which we believe is simpler to understand at a technical level. We also give a tighter analysis
of its error growth under homomorphic operations.
    3
        This is just a special case of Cayley’s theorem, which saysPthat any group G embeds into the symmetric group S|G| .
    4
        The latter group can be seen as a subgroup of Sr for r = i ri , but it will be more efficient to retain the product structure.




                                                                     6

[page break]
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

[page break]
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

[page break]
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
```

## Lines 484–581: §4 to Corollary 4.2: Equation (4.1) (cited by `Encrypts.sum`) and the permutation-matrix chains (phase-7 roadmap, ruled Q12 for BV14)

```text
4    Homomomorphic Encryption for Symmetric Groups
Brakerski and Vaikuntanathan [BV14] showed how to use the GSW encryption scheme to homomorphically
compose permutations of five elements (i.e., to homomorphically compute the group operation in the
symmetric group S5 ) with small additive noise growth; the use of S5 comes from its essential role in
Barrington’s theorem [Bar86]. In [BV14], the homomorphic composition of permutations is intertwined with
the evaluation of a branching program given by Barrington’s theorem. Here we give, as a “first-class object,”
a homomorphic cryptosystem for any symmetric group Sr . The ability to use several different small values
of r, along with a homomorphic equality test that we design, will be central to our bootstrapping algorithm.

                                                         9

[page break]
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

[page break]
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
```
