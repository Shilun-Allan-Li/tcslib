# Pei16: excerpts of the passages used (Gate 41)

**Reference.** C. Peikert, *A Decade of Lattice Cryptography*, author version dated 17 February 2016 (already ingested: `blueprint/src/references/peikert2016-lattice-survey{,.raw}.md`; the scoped `.md` covers Definitions 4.1.1, 4.2.1, 4.2.3 and SIS passages only, so §5.4.3 and §6.1.2–6.1.3 are quoted from the committed raw extraction).

**Extraction.** Lines of the committed file `blueprint/src/references/peikert2016-lattice-survey.raw.md` (blob 9aa84826712a65f261e9f374be4d45eccdb0bb27 at records e4302a5ee8756728a13c3b1e1398c207e66221a6), whose header names PDF SHA-256 `1a9802b66031a2b863fd498a5de4a71cdb1bd46ac1d47dc1f4a67ae341357488` and `pdftotext -layout`. The PDF itself is not committed (pairing ruling Q12; GSW ruling Q14 and the plan-section provenance). Only the passages below are quoted. Mathematical layout (sub- and superscripts, fraction bars) is flattened by the extraction; read formulas against the Lean statements and the PDF where needed.

**Passages.**

- lines 2530–2586: §5.4.3 "Gadgets": g, G = I_n ⊗ gᵗ, Equation (5.4.1), G · G⁻¹(u) = u
- lines 3374–3499: §6.1.2 (bootstrapping, circular security) and §6.1.3 (third-generation FHE: Equations (6.1.4)–(6.1.7), decryption, NAND, right-associative chains, Barrington)

## Lines 2530–2586: §5.4.3 "Gadgets": g, G = I_n ⊗ gᵗ, Equation (5.4.1), G · G⁻¹(u) = u

```text
5.4.3    Gadget Trapdoors
We now turn from short bases as generic lattice trapdoors, to the “gadget”-based trapdoors for q-ary SIS/LWE
lattices as developed in [MP12], building on techniques from several related works [Ajt99, AP09, PW08,
ABB10].

Gadgets. The first main idea is that there are special, structured matrices G, called “gadgets,” for which
solving SIS and LWE is easy. The simplest gadget is as follows: for a given a modulus q, define the vector

                                             g = (1, 2, 4, . . . , 2`−1 ) ∈ Z`q ,

where ` = dlog2 qe.8 Now observe that given any u ∈ Zq , we can find a short solution x ∈ Zm to

                                            hg, xi = gt · x = u (mod q);

for example, let x correspond to the base-two representation of u’s canonical representative in {0, . . . , q − 1}.
In other words, it is easy to solve the SIS problem with respect to the one-row parity-check “matrix” gt .
Moreover, it is easy to randomly sample from a discrete Gaussian over the lattice coset L⊥      t
                                                                                            u (g ) of solutions.
    A bit more thought reveals that solving LWE with respect to gt is also easy. For simplicity, suppose
that q = 2` ; then given any bt ≈ s · gt (mod q) with errors in the interval [− 4q , 4q ), we can recover the
most-significant bit of s ∈ Zq from

                                       b` ≈ s · 2`−1 = msb(s) · 2q         (mod q).

We can then recover the next-most-significant bit of s from b`−1 ≈ s · 2`−2 (mod q), etc. (This all generalizes
to non-power-of-two moduli as well, but is a bit more technically involved.)
    We extend all of the above to n-dimensional SIS and LWE with respect to the block-diagonal gadget
matrix
                               G := In ⊗ gt = diag(gt , . . . , gt ) ∈ Zn×n`
                                                                         q   ,

just by working blockwise: for LWE, given bt ≈ st G = (s1 g, . . . , sn g)t , just recover each si from the
corresponding block of b. For SIS, to find a short solution to Gx = u for a given u ∈ Znq , just find short
solutions to gt · xi = ui for each entry ui and concatenate the results. It is convenient to express this operation
in terms of the “decomposition” function

                               G−1 : Znq → Zn`                                                                      (5.4.1)
                                        u 7→ a short solution x to Gx = u (mod q),
   8
    This g can be generalized in a variety of ways, e.g., by using a base other than two, mixed bases, the Chinese Remainder
Theorem, etc.


                                                             50


<!-- pdf-page: 53 -->
where the choice of notation is explained by the relation

                                       G · G−1 (u) = u      (mod q).

We stress that G−1 is not a matrix, but rather a function that maps a mod-q input to a short integer vector.
Depending on the context, the G−1 operation may even be randomized, e.g., it could sample a Gaussian-
distribution solution.
    Finally, observe that given any invertible matrix H ∈ Zn×n
                                                            q   , SIS and LWE remain easy with respect to
the matrix HG ∈ Zq   n×n` . Specifically, to solve (HG)x = u, simply output x = G−1 (H−1 · u), and given
```

## Lines 3374–3499: §6.1.2 (bootstrapping, circular security) and §6.1.3 (third-generation FHE: Equations (6.1.4)–(6.1.7), decryption, NAND, right-associative chains, Barrington)

```text
6.1.2    Bootstrapping
Even with all of the above techniques, homomorphic operations still always increase the error rate of a
ciphertext, by as much as a polynomial factor per operation. Therefore, the schemes described so far can
only homomorphically evaluate circuits of an a-priori bounded depth; such systems are frequently called
“somewhat homomorphic” or “leveled” (we ignore the precise technical distinction between these terms).
     A beautiful idea from Gentry’s original work [Gen09b, Gen09a], called bootstrapping or sometimes
refreshing, makes it possible to reduce the error rate of a ciphertext, thus enabling unbounded homomorphic
computation. Suppose we have a ciphertext c that encrypts some (unknown) message µ under a secret key s,
where the error rate of c is too large to perform further homomorphic operations on it. The idea behind
bootstrapping is to homomorphically evaluate the decryption function on a low-error encryption cs = Enc(s)
of the secret key s, which is included as part of the public key. More specifically, we homomorphically
evaluate the function fc (·) = Dec(·, c) on the ciphertext cs . (Note that the ciphertext c to be refreshed is
“hard-coded” into the function fc (·), whereas the secret key is treated as the function argument.) Because
fc (s) = Dec(s, c) = µ, it follows that homomorphic evaluation of fc on an encryption of s (namely, cs )
produces an encryption of µ. Moreover, as long as the circuit depth of fc and the error rate of cs are small
enough, the error rate of the output ciphertext will be substantially smaller than that of the input ciphertext c,
as desired. In particular, decryption can be performed in O(log λ) depth, so it suffices for cs to have some
λ−O(log λ) error rate.
     Because bootstrapping involves the homomorphic evaluation of a somewhat complex function, it is not
very efficient (see, e.g., [GH11b]). However, bootstrapping has been intensively studied and improved in var-
ious ways [GH11a, BGV12], culminating in ring-LWE-based methods that run in only polylogarithmic Õ(1)
time per encrypted bit [GHS12a, AP13], where the hidden logO(1) (λ) factors are not exceedingly large.
     We conclude this discussion by noting that, in order to yield unbounded homomorphic operations,
bootstrapping requires a “circular” encryption of the secret key under itself. It is unknown whether it is
provably secure (under a standard assumption) to reveal such an encryption, but nor are any attacks known.
So to date, all unbounded FHE schemes require an additional assumption of circular security for the secret
key.




                                                       66


<!-- pdf-page: 69 -->
6.1.3   Third-Generation FHE
In 2013, Gentry, Sahai, and Waters (hereafter GSW) [GSW13] proposed an interesting LWE-based FHE
scheme that has some unique and advantageous properties. For example, homomorphic multiplication
does not require any key-switching step, and the scheme can be made identity-based. Moreover, as shown
in [BV14, AP14], the GSW scheme can be used to bootstrap with only a small polynomial-factor growth in
the error rate, as opposed to quasi-polynomial λΘ(log λ) growth for the system described above. This yields
unbounded FHE based on LWE with just an inverse-polynomial n−O(1) error rate (plus a circular-security
assumption). We describe these results in some detail next.

Homomorphic trapdoors. The GSW scheme is presented most simply in terms of the gadget-based trap-
doors described in Section 5.4.3. (The presentation here has evolved through [BGG+ 14, AP14, GVW15b].)
At the heart of GSW are the following additive and multiplicative homomorphisms for tags and trapdoors.
Let Ā ∈ Zn×
           q
              m̄ be arbitrary, and for i = 1, 2 let


                                             Ai = xi G − ĀRi                                            (6.1.4)
                                                                    R 
for some integer xi and short integer matrix Ri . In other words,     I
                                                                          i   is a trapdoor with tag xi (or more
accurately, tag xi I) for the matrix [Ā | Ai ].
    Applying Equation (6.1.4), it is easy to verify that

                                 A1 + A2 = (x1 + x2 )G − Ā(R1 + R2 ),                                   (6.1.5)

and

                          A1 · G−1 (A2 ) = (x1 G − ĀR1 ) · G−1 (A2 )
                                          = x1 A2 − Ā · R1 G−1 (A2 )
                                          = x1 x2 G − Ā (R1 G−1 (A2 ) + x1 R2 ) .                       (6.1.6)
                                                         |        {z          }
                                                                     R
                R +R                                                                      
In other words, 1 I 2 is a trapdoor with tag x1 + x2 for the matrix [Ā | A1 + A2 ], and R   I is a trapdoor
                                            −1
with tag x1 x2 for the matrix [Ā | A1 · G (A2 )]. Note that in the latter case, we need x1 to be a small
integer in order to get a good-quality trapdoor.
    One very important property of homomorphic multiplication is that the growth of the resulting trapdoor
matrix R is asymmetric and quasi-additive: while R1 is expanded by some polynomial factor due to the
multiplication by G−1 (A2 ), the R2 term is only multiplied by x1 . We discuss the implications of this below.

Fully homomorphic encryption. The GSW FHE scheme works as follows. As in prior systems, the public
key is a matrix Ā ∈ Zn×
                      q
                        m̄ whose columns are LWE samples with some secret s̄ ∈ Zn−1 , i.e.,


                                                  st Ā ≈ 0                                              (6.1.7)

where s = (−s̄, 1) is the secret key. An encryption of an integer x is a matrix

                                              A = xG − ĀR




                                                     67


<!-- pdf-page: 70 -->
for some sufficiently short random R. As usual, semantic security follows by a lossiness argument: encrypting
under a uniformly random (“malformed”) public key Ā statistically hides the message, because [Ā | ĀR] is
very close to uniformly distributed.
     To decrypt a ciphertext A using the secret key s, one just computes
                                                        st A ≈ x · st G,

where the approximation holds by Equation (6.1.7), and because R is short. Since it is easy to solve LWE
with respect to G, we can recover x · st and hence x (modulo q). In fact, if x is known to be just a bit, then
because one of the rightmost entries of st G is far from zero modulo q, we can recover x simply by testing
whether st · a ≈ 0 for an appropriate column a of A.
    To homomorphically add or multiply ciphertexts A1 , A2 that encrypt small messages, one just computes
A1 + A2 or A1 · G−1 (A2 ), respectively. As shown above in Equations (6.1.5) and (6.1.6), the resulting
ciphertext is a valid encryption for the sum or product of the messages, respectively. Because it is important
for noise growth that messages remain small integers, we typically only use operations that maintain the
messages as {0, 1}-values. For example, the binary NAND operation, which is sufficient for expressing
arbitrary computations, can be written as (x1 NAND x2 ) = 1 − x1 x2 .

Bootstrapping. As first shown by Brakerski and Vaikuntanathan [BV14], the asymmetric and quasi-
additive growth of the trapdoor matrices under homomorphic multiplication allows certain computations—in
particular, decryption for the purpose of bootstrapping—to be performed with rather small error growth.
The first main observation is that by Equation (6.1.6), any polynomial-length chain of homomorphic bit-
multiplications on fresh ciphertexts, if done in a right-associative manner, incurs only polynomial error
growth. The same also holds when multiplying a sequence of permutation matrices (or more generally,
orthonormal integer matrices), where each matrix is encrypted entry-wise.
    The second main idea is that by using Barrington’s Theorem [Bar86], any depth-d circuit can be converted
into a length-4d branching program of permutation matrices. In particular, the O(log λ)-depth decryption
circuit can be computed homomorphically in polynomial time and with polynomial error growth, albeit
for rather large polynomials. The subsequent work of Alperin-Sheriff and Peikert [AP14] significantly
improved the runtime and growth to small polynomials, by avoiding Barrington’s Theorem and instead
expressing decryption as an arithmetic function that can be embedded directly into permutation matrices.
```
