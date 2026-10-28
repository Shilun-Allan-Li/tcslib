Appendix A

Background Concepts

Basic Probability
  • Events A and B are said to be independent if

                        Pr [ A ∩ B] = Pr [ A] · Pr [ B]

  • The conditional probability of event A given event B, written
    as Pr[ A | B] is defined as
                                          Pr[ A ∩ B]
                          Pr[ A | B] =
                                            Pr[ B]

  • Bayes theorem relates the Pr[ A | B] with Pr[ B | A] as follows:
                                     Pr[ B | A] Pr[ A]
                      Pr[ A | B] =
                                           Pr[ B]

  • Events A1 , A2 , . . . , An are said to be pairwise independent if
    for every i and every j 6= i, Ai and A j are independent.
  • Union Bound: Let A1 , A2 , . . . , An be events. Then,
      Pr[ A1 ∪ A2 ∪ . . . ∪ An ] ≤ Pr[ A1 ] + Pr[ A2 ] + . . . + Pr[ An ]

  • Let X be a random variable with range Ω. The expectation
    of X is the value:
                         E[ X ] = ∑ x Pr[ X = x ]
                                   x ∈Ω

                                 187
 188                                      chapter a. background concepts


         The variance is given by,

                             Var [ X ] = E[ X 2 ] − ( E[ X ])2

       • Let X1 , X2 , . . . , Xn be random variables. Then,

            E [ X1 + X2 + · · · + X n ] = E [ X1 ] + E [ X2 ] + · · · + E [ X n ]

       • If X and Y are independent random variables, then

                                 E[ XY ] = E[ X ] · E[Y ]
                          Var [ X + Y ] = Var [ X ] + Var [Y ]


 Markov’s Inequality
 If X is a positive random variable with expectation E( X ) and
 a > 0, then
                                     E( X )
                        Pr[ X ≥ a] ≤
                                       a

 Chebyshev’s Inequality
 Let X be a random variable with expectation E( X ) and variance
 σ2 , then for any k > 0,

                                                       σ2
                          Pr[| X − E( X )| ≥ k ] ≤
                                                       k2

 Chernoff’s inequality
.Theorem 188.7 Let X1 , X2 , . . . , Xn denote independent random vari-
 ables, such that for all i, E( Xi ) = µ and | Xi | ≤ 1.

                     Pr ∑ Xi − µn ≥ e ≤ 2−e n
                                                     2




 The constants in this statement have been specifically chosen for
 simplicity; they can be further optimized for tighter analysis.
     A useful application of this inequality is the Majority voting
 lemma. Assume you can get independent and identically dis-
 tributed, but biased, samples of a bit b; that is, these samples are
 Background Concepts                                                189


 correct only with probability 12 + poly1(n) . Then, given poly(n)
 samples, compute the most frequent value b0 of the samples; it
 holds with high probability that b = b0 .

.Lemma 189.8 (Majority vote) Let b ∈ {0, 1} be a bit and let X1 , . . . , X`
 denote independent random variables such that Pr[ Xi = b] ≥ 12 + p(1n)
 for some polynomial p. Then if ` > p(n)2 ,
               Pr[majority( X1 , . . . , X` ) = b] > 1 − 2??

 Proof. Without loss of generality, assume that b = 1. (Similar
 analysis will apply in the case b = 0.) In this case, µ = E[ Xi ] =
 1     1                    1     1
 2 + p(n) , and so µ ` = `( 2 + p(n) ) > ` /2 + p ( n ). In order for
 the majority procedure to err, less than `/2 of the samples must
 agree with b; i.e. ∑ Xi < `/2. Applying the Chernoff bound, we
 have that ...
                                                                   

 Pairwise-independent sampling inequality
 Let X1 , X2 , . . . , Xn denote pair-wise independent random vari-
 ables, such that for all i, E( Xi ) = µ and | Xi | ≤ 1.
                             ∑ Xi             1 − µ2
                                         
                        Pr        −µ ≥ e ≤
                              n                 ne2
 Note that this is a Chernoff like bound when the random vari-
 ables are only pairwise independent. The inequality follows as a
 corollary of Chebyshev’s inequality.


 Cauchy-Schwarz Inequality
 In this course, we will only need Cauchy’s version of this inequal-
 ity from 1821 for the case of real numbers. This inequality states
 that
.Theorem 189.9 (Cauchy-Schwarz) For real numbers xi and yi ,
                         !2
                         n              n      n
                        ∑ xi yi     ≤ ∑ xi2 · ∑ y2i
                         i              i       i
 Appendix B

 Basic Complexity Classes

 We recall the definitions of the basic complexity classes DP, NP
 and BPP.

 The Complexity Class DP. We start by recalling the definition
 of the class DP, i.e., the class of languages that can be decided in
 (deterministic) polynomial-time.
.Definition 191.10 (Complexity Class DP) A language L is recog-
 nizable in (deterministic) polynomial-time if there exists a deterministic
 polynomial-time algorithm M such that M ( x ) = 1 if and only if x ∈ L.
 DP is the class of languages recognizable in polynomial time.

 The Complexity Class NP. We recall the class NP, i.e., the class
 of languages for which there exists a proof of membership that
 can be verified in polynomial-time.
.Definition 191.11 (Complexity Class NP) A language L is in NP
 if there exists a Boolean relation R L ⊆ {0, 1}∗ × {0, 1}∗ and a polyno-
 mial p(·) such that R L is recognizable in polynomial-time, and x ∈ L
 if and only if there exists a string y ∈ {0, 1}∗ such that |y| ≤ p(| x |)
 and ( x, y) ∈ R L .
 The relation R L is called a witness relation for L. We say that y is a
 witness for the membership x ∈ L if ( x, y) ∈ R L . We will also let
 R L ( x ) denote the set of witnesses for the membership x ∈ L, i.e.,

                        R L ( x ) = {y : ( x, y) ∈ L}

                                    191
 192                              chapter b. basic complexity classes


 We let co-NP denote the complement of the class NP, i.e., a
 language L is in co-NP if the complement to L is in NP.

 The Complexity Class BPP. The class BPP contains the lan-
 guages that can be decided in probabilistic polynomial-time (with
 two-sided error).

.Definition 192.12 (Complexity Class BPP) A language L is recog-
 nizable in probabilistic polynomial-time if there exists a probabilistic
 polynomial-time algorithm M such that

       • ∀ x ∈ L, Pr[ M ( x ) = 1] ≥ 2/3

       • ∀ x 6∈ L, Pr[ M( x ) = 0] ≥ 2/3

 BPP is the class of languages recognizable in probabilistic polynomial
 time.
