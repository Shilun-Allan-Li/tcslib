<!-- generated-by: scoped Poppler extraction -->
<!-- source-pdf-sha256: 74f48b0eff6f4a0afd52ffe2bfddc6bef006c241c458812bfe085ce85059752c -->
<!-- extractor: pdftotext version 26.10.0; -layout -f 33 -l 39 -->

<!-- pdf-page: 33 -->
B = {b1 , . . . , bd } ⊂ Rd :                 X                         
                                        Λ=                 ci bi : ci ∈ Z .
                                                   i∈[d]

In computational settings, it is standard to represent a lattice by a basis.
    Regev showed that for certain normal error distributions, the LWE problem is as hard as several standard
worst-case lattice problems, for quantum algorithms. We state a version of the main theorem here:
                                                                                                 √
Proposition 6.1 ([57]). Let α = α(d) ∈ (0, 1) and let q = q(d) be a prime such that α · q > 2 d. There
is a quantum polynomial-time reduction from solving either of the following two lattice problems in the
worst-case to solving LWEq,Ψ̄α :
      • SIVP: In any lattice of dimension d, find a set of d linearly independent lattice vectors, the longest of
        which has Euclidean norm within an Õ(d/α) factor of optimal.

      • GapSVP: In any lattice of dimension d, approximate the Euclidean length of a shortest nonzero lattice
        vector to within a Õ(d/α) factor.
    Proposition 6.1 has since been strengthened by Peikert in two ways: first [49], it also applies to the
SIVP and GapSVP problems in√any `p norm, 2 < p ≤ ∞, for essentially the same Õ(d/α) approximation
factors. Second [50], for αq ≥ d log d there is also a classical (non-quantum) reduction from a variant of
the GapSVP problem to LWE (and from GapSVP itself to LWE with modulus q = 2d , but such a large value
is not useful for our purposes).
    The SIVP and GapSVP problems appear to be quite hard in the worst case (even for quantum algorithms):
to obtain a poly(d) approximation factor, known algorithms require time and space that are exponential
in d [4]; known polynomial-time algorithms obtain approximation factors that are only slightly subexponential
in d [43, 61].
    We define our lossy and ABO functions in terms of the LWE problem, without explicitly taking into
account the connection to lattices (or the hypotheses on the parameters required by Proposition 6.1). Then
in Section 6.5 we instantiate the parameters appropriately, invoking Proposition 6.1 to obtain a worst-case
hardness guarantee.

6.2     Matrix Concealer
Here (as in Section 5.2) we describe a method for generating a special kind of pseudorandom “concealer”
matrix (with trapdoor) that is the foundation for our lossy and ABO TDFs. Similarly to our DDH-based
construction, the trapdoor is a description of a low-dimensional subspace, but unlike it, the rows of the
concealer matrix only lie near the subspace.
   The algorithm GenConcealχ (h, w) works as follows: given positive integer dimensions h, w = poly(d),
      • Choose A ← Zh×d
                    q   and S ← Zw×d
                                 q   uniformly at random, and E ← χh×w .

      • Output
                                        C = (A, B = ASt + E) ∈ Zqh×(d+w)
        as the concealer matrix, and S as the trapdoor.
Lemma 6.2. Let h, w = poly(d). Under the LWEq,χ assumption, the concealer matrix C = (A, B) output
                                      h×(d+w)
by GenConcealχ is pseudorandom over Zq        , i.e., computationally indistinguishable from the uniform
distribution.

                                                           33

<!-- pdf-page: 34 -->
Proof. The proof proceeds by a simple hybrid argument over the w columns of B. We define a sequence of
                                           h×(w+d)
hybrid distributions H0 , . . . , Hw over Zq        . In experiment Hj , the first j columns of B are as produced
by GenConcealχ (h, w), while the remainder are uniformly random and independent. Clearly Hw is the
output distribution of GenConcealχ (h, w) and H0 is the uniform distribution.
    We now show that for each j ∈ [w], Hj and Hj−1 are computationally indistinguishable under the
LWEq,χ assumption, which by transitivity proves the claim. To do so, we give a reduction from distinguishing
As,χ (for uniformly random s ← Zdq ) from the uniform distribution U over Zdq × Zq to distinguishing Hj
from Hj−1 . The reduction works as follows: given access to an unknown distribution D over Zdq × Zq , draw
h samples (ai , bi ) from D; form the matrix A ∈ Zh×d  q   whose ith rows is ai and the column vector b ∈ Zh×1q
whose ith entry is bi .
    Choose S ← Zw×d    q  uniformly at random and E ← χh×w , and let B0 = ASt + E. Form the matrix B
                      0
that agrees with B on its first j − 1 columns, whose jth column is b, and whose remaining columns are
uniformly random and independent. Output C = (A, B).
    It should be clear by inspection that if the reduction’s unknown distribution D is As,χ , then the reduction’s
output is distributed as Hj , whereas if D is uniformly random then the reduction’s output is distributed as
Hj−1 . This completes the proof.
   We now show a technical lemma that is needed for both the correctness and lossiness properties of our
constructions.
Lemma 6.3. Let h, w, p be positive integers. Let q ≥ 4ph, let 1/α ≥ 8p(h + g) for some g > 0, and let
χ = Ψ̄α . Then except with probability at most w · 2−g over the choice of E ← χh×w , the following holds:
for every x ∈ {0, 1}h , each entry of (xE)/q ∈ Tw has absolute value less than 4p
                                                                                1
                                                                                  .
Proof. By a union bound over all w columns of E, it suffices to show that for each column et ∈ Zh×1
                                                                                                q   of E,
                       1                   h                                                  −g
we have |hx, ei /q| < 4p for all x ∈ {0, 1} simultaneously, except with probability at most 2 over the
choice of e.
   Below we show that for any fixed x ∈ {0, 1}h ,
                                         h                i
                                    Pr |hx, ei /q| ≥ 4p1
                                                            ≤ 2−(h+g) .                               (2)
                                     e←χh

Taking a union bound over all x ∈ {0, 1}h , we conclude that |hx, ei /q| < 4p 1
                                                                                 for all x ∈ {0, 1}h simultane-
ously, except with probability at most 2−g .
    We now prove (2). By definition, ei = bqyi e mod q where yi ← Dα are independent for all i ∈ [h].
Then by the triangle inequality, the distance (modulo 1) between hx, ei /q ∈ T and hx, yi ∈ T is at most
h/(2q) ≤ 1/8p. Therefore, it suffices to show that |hx, yi| < 1/8p except with probability              −(h+g) .
                                                                                      0
                                                                                           √ at most√2
    Because the yi are independent and x is binary, hx, yi is distributed as Dα0 for α ≤ h · α ≤ h + g · α.
Then by hypothesis on α and the tail inequality on Gaussian variables,
         h              i          h                      p             i
                                                               h + g · α ≤ exp(−(h + g)) < 2−(h+g) .
                                               p
                      1
    Pr |hx, yi| ≥ 8p      ≤ Pr |hx, yi| ≥ h + g ·
     h
  y←Dα                          h
                             y←Dα


6.3     Lossy TDF
6.3.1   Overview
Our LWE-based lossy TDF is built upon the same main ideas as the DDH-based construction of Section 5.
In particular, a function index is a concealed matrix M, and the function is evaluated on x ∈ {0, 1}n by
homomorphically computing an encrypted linear product xM (where M = 0 in the lossy case).

                                                       34

<!-- pdf-page: 35 -->
     However, the use of LWE introduces several additional technical challenges. The chief difficulty is that the
function outputs now also include accumulated error terms, so there are many more outputs than there would
otherwise be if the error terms were not present. (The errors, of course, are necessary to securely conceal the
underlying matrix M.) The main challenge, therefore, is to limit the number of possible accumulated error
vectors, while simultaneously ensuring (in the injective case) that all n bits of the input x can be recovered
from the function output.
     To start, it is helpful to see why the straightforward approach taken in our DDH-based construction does
not yield a lossy function here. Recall that a lossy function index is simply an (unmodified) concealer matrix,
                                                               n×(d+n)
which in the case of LWE is C = (A, B = ASt +E) ∈ Zq                   . Then given the first component xA of the
function output (and even ignoring its q d possible values), the second component xB = (xA)St + xE ∈ Znq
uniquely determines x whenever E is invertible modulo q, which occurs often. Note that we do not have the
luxury of restricting the rows of E to a low-dimensional subspace, because our proof of pseudorandomness
(Lemma 6.2) requires the columns of E to be independent.
     Our solution instead conceals suitably chosen nonsquare matrices of dimension n × w, where n
 d + w,
to limit the number of outputs in the lossy case while still ensuring invertibility in the injective case. For the
lossy case, the number of outputs xC = (xA, xB) ∈ Zd+w       q    is bounded by q d times the number of possible
values for xE, which we can bound using Lemma 6.3. In principle, the input length n can then be made as
large as needed to obtain the desired amount of lossiness. (However, correct inversion will impose additional
constraints.)
     Of course, in the injective case we cannot conceal the identity matrix I because we are no longer using
square matrices. Instead, we conceal a (suitably encoded) special matrix G ∈ Zn×w , whose rows are
increasing power-of-2 multiples of each standard basis vector ei ∈ Zw . The idea is that we can easily recover
x ∈ {0, 1}n from xG via its base-2 representation. Of course, G is actually hidden by a concealer matrix
over Zq , and we need to be able to compute xG homomorphically and then decrypt it correctly. Computing
xG involves at most n row additions, and the entries of xG are bounded by 2(n/w) , so we need to choose the
parameters of the scheme to support such bounded homomorphism and message sizes. In the end, with a
careful balancing of the parameters we can support any constant lossiness rate with a poly(d) input length n
and modulus q, and a 1/poly(d) noise rate α. (See Theorem 6.4 and Section 6.5 for the precise instantiation).

6.3.2   Construction
We now describe the lossy TDF construction, which involves several parameters. The dimension d is the main
security parameter. As discussed above, our lossy TDF needs to support homomorphic operations resulting
in encrypted integers as large as some p. We consider the modulus p ≥ 2 (for simplicity, a power of 2) and
matrix width w ≥ 1 to be free variables, which will largely determine the lossiness of the functions. The
input length of the functions is n = w lg p. Finally, the modulus q and parameter α of the error distribution
χ = Ψ̄α of the underlying LWE problem will be instantiated later to ensure correct inversion. Looking ahead,
the quantity 1/α (which determines the worst-case approximation factor for lattice problems) will grow with
p, so our goal will be to make p as small as possible while still ensuring lossiness.
    Let I ∈ Zw×w be the w × w identity matrix over the integers, and define a special row vector

                                   p = (20 , 21 , . . . , 2lg(p)−1 = p/2) ∈ Zlg p

consisting of increasing powers of 2. Define the matrix G = I ⊗ pt ∈ Zn×w , where ⊗ denotes the tensor
(or Kronecker) product. Essentially, the tensor product replaces each entry ei,j of I with the column vector
ei,j · pt ∈ Zlg p×1 . Thus, the ((i − 1)(lg p) + j)th row of G is 2j−1 · ei , for i, j ∈ [w].


                                                        35

<!-- pdf-page: 36 -->
   To encrypt and operate homomorphically on integers as large as p using the LWE problem, we need to
encode elements of Zp suitably as elements of Zq . Define the encoding function c : Zp → Zq as
                                                   j     m
                                         c(m) = q · m  p ∈ Zq ,

where m
      p ∈ T, and extend c coordinate-wise to matrices over Zp . We also define a decoding function
 −1
c : Zq → Zp as                                j     m
                                         c−1 (v) = p · vq ∈ Zp ,

where again vq ∈ T and we extend c−1 coordinate-wise to matrices over Zq . (Formally, c−1 is not the inverse
function of c, but this abuse of notation evokes the intended use of the functions. For example, it can be
verified that c−1 (c(m)) = m for appropriate choices of p, q.)

   • Sampling an injective/lossy function. The function generators (for both the injective and lossy cases)
                                                                                                   n×(d+w)
     first invoke GenConcealχ (n, w) to generate a concealer matrix C = (A, B = ASt + E) ∈ Zq
     and trapdoor S.
                                                                                               n×(d+w)
      The injective function generator Sinj outputs function index Y = (A, B + M) ∈ Zq                   and
      trapdoor S, where M = c(G mod p).
      The lossy function generation algorithm Sloss simply outputs function index Y = C. There is no
      trapdoor output.

   • Evaluation algorithm. Fltdf takes as input (Y, x) where Y is a function index and x ∈ {0, 1}n is an
     n-bit input interpreted as a vector. The output is z = xY ∈ Zd+w
                                                                  q   .
      Note that if the function index Y was generated by Sinj , i.e., Y = (A, ASt + E + M), then

                                       z = (xA, (xA)St + x(E + M)).

      In contrast, if Y was generated by Sloss , i.e., Y = (A, ASt + E), then z = (xA, (xA)St + xE).
                             −1
   • Inversion algorithm. Fltdf  takes as input (S, z), where S is the trapdoor and z = (z1 , z2 ) ∈ Zdq × Zw
                                                                                                            q
     is the function output. It computes v = z2 − z1 St , and lets m = c−1 (v) ∈ Zw   p . Finally, the output
     x ∈ {0, 1}n is computed as the unique binary solution to xG = m̄, where m̄ ∈ Zw is the unique
     integral vector congruent to m modulo p having entries in {0, . . . , p − 1}. (The solution x may be
     found efficiently by computing the base-2 representation of m̄.)

Theorem 6.4. Let q ≥ 4pn = 4wp lg p and χ = Ψ̄α where 1/α ≥ 16pn = 16wp lg p. Then the algorithms
described above define a collection of almost-always (n, k)-lossy TDFs under the LWEq,χ assumption, where
the residual leakage r = n − k is
                                                                   
                                              d     d
                                   r ≤n·        +      + 1 logp (q/p) .
                                             w      w

   Note that in order for the residual leakage rate to be less than 1, we need both w > d and q < p2 .




                                                    36

<!-- pdf-page: 37 -->
Proof. First, it follows directly from Lemma 6.2 that lossy function indices are computationally indistin-
guishable from injective ones, because both types are indistinguishable from uniform.
     Now we show that with overwhelming probability over the choice of Y = (A, B = ASt + E + M) by
Sinj , the inversion algorithm is correct for all z = (z1 , z2 ) = Fltdf (Y, x) = xY where x ∈ {0, 1}n . By the
remarks accompanying the evaluation and inversion algorithms, we have
                                                                            j      m
                                              t                                  G
                              v = z2 − z1 S = x(E + M) = xE + x q · p .

Define the closed interval I = [− 12 , 21 ] ⊂ R. We have
                                            j            j       m m
                         c−1 (v) = p · xE + x q · G             p    /q
                                            j                                m
                                    ∈ p · (xE)/q + (p/q) · x I n×w + q · G  p
                                            1 w                  n×w
                                                                          
                                    ∈            · I + (p/q) · xI     + xG                                 (3)
                                             32 w        
                                    ∈          4 · I + xG                                                  (4)
                                   = xG mod p,

where (3) holds for all x simultaneously except with probability at most w · 2−n over the choice of E by
Lemma 6.3, and (4) is by the triangle inequality (yielding xI n×w ∈ n · I w ) and by the hypothesis that
q ≥ 4pn. Then because all the entries of xG ∈ Zw are in {0, . . . , p − 1} by definition of G, the inversion
algorithm successfully recovers xG and outputs the correct x ∈ {0, 1}n .
    We now analyze the lossy functions. Let Y = (A, B = ASt + E) be a function index produced by Sloss .
Then for any input x ∈ {0, 1}n ,

                        Fltdf (Y, x) = (z1 , z2 ) = (xA, (xA)St + xE) ∈ Zdq × Zw
                                                                               q.

The number of possible values for z1 ∈ Zdq is at most q d , and given z1 , the number of possible values for z2
is exactly the number of possible values for xE (recall that S is fixed by the function index). By Lemma 6.3,
the latter quantity is at most (1 + q/2p)w ≤ (q/p)w . The total number of outputs of the function is therefore
at most q d · (q/p)w . The base-2 logarithm of this quantity is a bound on the residual leakage r = n − k:

                               r ≤ d · lg q + w · lg(q/p)
                                        d lg q     n
                                 = n·          +      · lg(q/p)
                                        w lg p lg p
                                                               
                                          d      d
                                 = n·        +      + 1 logp (q/p) .
                                          w      w

6.4   All-But-One TDF
Our all-but-one TDF construction relies on all the ideas from the prior constructions, plus one additional
technique. As always, evaluating the ABO function on x ∈ {0, 1}n involves computing an encrypted product
xM, where M depends on the branch of the function being evaluated (and M = 0 on the lossy branch).
    In our DDH-based ABO function, the matrix M is some scalar multiple (b − b∗ )I of the identity matrix,
where b, b∗ ∈ Zp . Because the matrices M are over the very large cyclic group Zp (where p is the order of the
DDH-hard group), the construction naturally supports a very large (super-polynomial) number of branches.


                                                      37

<!-- pdf-page: 38 -->
     In the LWE setting, our matrices M may also be viewed over a group Zp . For correctness, however,
the inverse error parameter 1/α of the relevant LWE problem needs to grow with p, and the strength of the
underlying complexity assumption (specifically, the approximation factor for worst-case lattice problems)
in turn grows with 1/α. Consequently, simply using scalar multiples of the identity matrix I to get a large
number of branches would induce a strong assumption, which is undesirable.
     Instead, we generalize the set of branches to be a certain large linear family of integral matrices, for which
every nonzero matrix in the family has full rank (i.e., its rows are linearly independent). The construction
of such a family involves a simple linear encoding trick (a variant of which was used in [18] for different
purposes) that maps a vector v ∈ Zw to a matrix V ∈ Zw×w          q     such that V = 0 when v = 0, and V
                                 9
is full-rank whenever v 6= 0. The full-rank property allows us to (efficiently) recover x from xV and
knowledge of v. Just as in the lossy TDF, the ABO function index conceals an “expanded” version of V,
namely V ⊗ pt ∈ Zw lg p×w , to achieve lossiness by way of increasing the input length. A final small detail
is that for binary x, the entries of xV can be as large as w(p − 1), rather than just p − 1 when V = I ⊗ pt ,
so we must enlarge the message space of the scheme accordingly.

Construction. Let the parameters p ≥ 2 and w ≥ 2 be free, assuming for simplicity that both p and w are
powers of 2, and let n = w lg p as before. Again, the parameters q and α will be instantiated later to ensure
correctness. The branch set B = Bd = {0, 1}w .
    For an integral vector v = (v1 , . . . , vw ) ∈ Zw , define the “anti-cyclic” shift operation

                                          s(v) = (−vw , v1 , . . . , vw−1 ) ∈ Zw .

(Note that the element vw is negated in the output.) Also define the (anti-cyclic) shift matrix V = S(v) ∈
Zw×w whose ith row vi = s(i−1) (v) is the vector v shifted i − 1 times. Clearly s (and hence S) is a linear
operation, i.e., s(v + v0 ) = s(v) + s(v0 ) and s(c · v) = c · s(v), so in particular s(0) = 0. It is also
the case that for any nonzero v ∈ Zw , the matrix S(v) is full-rank. The proof is as follows: because w
is a power of 2, the polynomial f (x) = xw + 1 is irreducible over Q[x]. (This may be seen by applying
Eisenstein’s criterion with prime p = 2 to the shifted polynomial f (x + 1), or by noting that f (x) is the 2mth
cyclotomic polynomial.) Then the vectors v ∈ Zw are in bijective correspondence with the polynomials
v(x) = v1 + v2 x + · · · + vw xw−1 ∈ Z[x]/f (x), and s(v) corresponds to x · v(x) mod f (x). Because the
rows of S(v) correspond to v(x), x · v(x) . . . , xw−1 · v(x) mod f (x) and f (x) is irreducible, the rows are
linearly independent when v 6= 0.
    As in the lossy TDF construction from Section 6.3.2 above, let p = (1, 2, . . . , p/2) ∈ Zlg p have
increasing power-of-2 entries. Similarly, let c : Zp0 → Zq and c−1 : Zq → Zp0 be (respectively) the
encoding and decoding functions, where we now use the modulus p0 = 2pw. For notational simplicity, let
r : {0, 1}w → Zn×wq    be the function mapping a branch value to its encoded matrix over Zq :

                                             r(v) = c(S(v) ⊗ pt mod p0 ).

       • Sampling an ABO function. The function generator Sabo takes as input the desired lossy branch v∗ ∈
                                                                                                    n×(d+w)
         {0, 1}w . It runs GenConcealχ (n, w) to generate a concealer C = (A, B = ASt + E) ∈ Zq
         and trapdoor S.
                                                                n×(d+w)
         The function index is Y = (A, B − r(v∗ )) ∈ Zq                   . The trapdoor information is t = (S, v∗ ).
   9
     We thank Daniele Micciancio for pointing out this avenue, which simplifies and slightly tightens the ABO construction from
prior versions of this work.


                                                              38

<!-- pdf-page: 39 -->
    • Evaluation algorithm. Gabo takes as input (Y, v, x) where Y = (A, B0 ) is a function index, v ∈
      {0, 1}w is the desired branch, and x ∈ {0, 1}n is an n-bit input interpreted as a vector. The output is
      x(A, B0 + r(v)) ∈ Zd+wq   .
      Note that if Y was generated to have lossy branch v∗ , then we have

               (A, B0 + r(v)) = (A, ASt + E + (r(v) − r(v∗ ))) ≈ (A, ASt + E + r(v − v∗ )),

      with equality when v = v∗ . (We may have only a close approximation otherwise, because the function
      c : Zp0 → Zq is not quite linear due to rounding.)

    • Inversion algorithm. G−1                              ∗
                              abo takes as input (t = (S, v ), v, z), where t is the trapdoor information,
             ∗
      v 6= v is the evaluated branch, and z = (z1 , z2 ) ∈ Zdq × Zw     q is the function output. It computes
      v = z2 − z1 S and lets m = c (v) ∈ Zp0 . The output x ∈ {0, 1}n is computed as the unique binary
                     t               −1         w

      solution to x · (S(v − v∗ ) ⊗ pt ) = m̄, where m̄ ∈ Zw is the unique integral vector congruent to m
      modulo p0 = 2pw having entries in {−w(p − 1), . . . , 0, . . . , w(p − 1)}.
      (The solution x may be found efficiently by solving the full-rank system w · S(v − v∗ ) = m̄, whose
      solution will be some integral w ∈ {0, . . . , p − 1}w , and then computing w in base 2.)

Theorem 6.5. Let q ≥ 8p0 n = 16w2 p lg p and χ = Ψ̄α where 1/α ≥ 16p0 n = 32w2 p lg p. Then the
algorithms described above define a collection of almost-always (n, k)-ABO TDFs with branch set {0, 1}w
under the LWEq,χ assumption, where the residual leakage r = n − k is
                                                                   
                                           d       d
                                r ≤n·         +      + 1 logp0 (q/p0 ) .
                                           w       w

Proof. The hidden lossy branch property (under the LWEq,χ assumption) follows directly from Lemma 6.2:
by an elementary reduction, for any branch v∗ the first output of Sabo (v∗ ) is computationally indistinguishable
                                     n×(d+w)
from the uniform distribution over Zq        .
    Proving correct inversion on branch v 6= v∗ is very similar to the correctness proof for Theorem 6.4. Let
Y = (A, B0 = ASt + E − r(v∗ )) be a function index generated by Sabo (v∗ ), and let

                     z = (z1 , z2 ) = Gabo (Y, v, x) = x(A, ASt + E + r(v) − r(v∗ )).

Then we have

         v = z2 − z1 St = xE + x(r(v) − r(v∗ )) ∈ xE + {−n, . . . , n}w + x · r(v − v∗ ) ∈ Zw
                                                                                            q,

where we have used the fact that r(v) − r(v∗ ) ∈ r(v − v∗ ) + {0, ±1}n×w and the triangle inequality.
Following the analysis from the proof of Theorem 6.4 (with the additional error terms of magnitude at most
n ≤ 8pq 0 ), it can be shown that
                                     c−1 (v) = x · r(v − v∗ ) mod p0
except with negligible probability over the choice of E. Because v − v∗ has entries from {0, ±1}, the integer
entries of x · r(v − v∗ ) lie in {−w(p − 1), . . . , w(p − 1)}, so the inversion algorithm successfully recovers
x · r(v − v∗ ) ∈ Zw and outputs the correct x.
     Finally, the analysis of the residual leakage on the lossy branch is essentially identical to that in the proof
of Theorem 6.4, with p replaced by p0 .


                                                        39
