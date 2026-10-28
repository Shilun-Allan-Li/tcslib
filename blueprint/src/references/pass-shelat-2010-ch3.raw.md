Chapter 3

Indistinguishability &
Pseudo-Randomness

Recall that one main drawback of the One-time pad encryption
scheme—and its simple encryption operation Enck (m) = m ⊕ k—
is that the key k needs to be as long as the message m. A natural
approach for making the scheme more efficient would be to start
off with a short random key k and then try to use some pseudo-
random generator g to expand it into a longer “random-looking”
key k0 = g(k ), and finally use k0 as the key in the One-time pad.
    Can this be done? We start by noting that there can not exist
pseudo-random generators g that on input k generate a perfectly
random string k0 , as this would contradict Shannon’s theorem
(show this). However, remember that Shannon’s lower bound
relied on the premise that the adversary Eve is computationally
unbounded. Thus, if we restrict our attention to efficient adver-
saries, it might be possible to devise pseudo-random generators
that output strings which are “sufficiently” random-looking for
our encryption application.
    To approach this problem, we must first understand what
it means for a string to be “sufficiently random-looking” to a
polynomial time adversary. Possible answers include:

  — Roughly as many 0 as 1.
  — Roughly as many 00 as 11
  — Each particular bit is roughly unbiased.

                               67
68          chapter 3. indistinguishability & pseudo-randomness


  — Each sequence of bits occurs with roughly the same proba-
    bility.
  — Given any prefix, it is hard to guess the next bit.
  — Given any prefix, it is hard to guess the next sequence.

    All of the above answers are examples of specific statistical
tests—and many more such test exist in the literature. For specific
simulations, it may be enough to use strings that pass some
specific statistical tests. However, for cryptography, we require
the use of strings that pass all (efficient) statistical tests. At first,
it seems quite overwhelming to test a candidate pseudo-random
generator against all efficient tests. To do so requires some more
abstract concepts which we now introduce.


3.1 Computational Indistinguishability
We introduce the notion of computational indistinguishability to for-
malize what it means for two probability distributions to “appear”
the same from the perspective of a computationally bounded test.
This notion is one of the cornerstones of modern cryptography.
To begin our discussion, we present two games that illustrate
important ideas in the notion of indistinguishability.

Game 1 Flip the page and spend no more than two seconds
looking at Fig. 1 that appears on the next page. Do the two boxes
contain the same arrangement of circles?
   Now suppose you repeat the experiment but spend 10 sec-
onds instead of two. Imagine spending 10 minutes instead of 10
seconds. If you are only given a short amount of time, the two
boxes appear indistinguishable from one another. As you take
more and more time to analyze the images, you are able to tease
apart subtle differences between the left and right. Generalizing,
even if two probability distrubutions are completely disjoint, it
may be that an observer who is only given limited processing
time cannot distinguish between the two distributions.

Game 2 A second issue concerns the size of a problem instance.
Consider the following sequence of games parameterized by the
 3.1. Computational Indistinguishability                         69




      Figure 69.1: Are the two boxes the same or different?


 value n in Fig. 2. The point of the game is to determine if the
 number of overlapping boxes is even or odd. An example of each
 case is given on the extreme left. The parameter n indicates the
 number of boxes in the puzzle. Notice that small instances of
 the puzzle are easy to solve, and thus “odd” instances are easily
 distinguishable from “even” ones. However, by considering a
 sequence of puzzles, as n increases, a human’s ability to solve
 the puzzle correctly rapidly approaches 1/2—i.e., no better than
 guessing.
     As our treatment is asymptotic, the actual formalization of
 this notion considers sequences—called ensembles—of probability
 distributions (or growing output length).

.Definition 69.3 (Ensembles of Probability Distributions) A se-
 quence { Xn }n∈N is called an ensemble if for each n ∈ N, Xn is a
 probability distribution over {0, 1}∗ .

    Normally, ensembles are indexed by the natural numbers
 n ∈ N. Thus, for the rest of this book, unless otherwise specified,
 we use { Xn }n to represent such an ensemble.

.Definition 69.4 (Computational Indistinguishability). Let { Xn }n
 and {Yn }n be ensembles where Xn , Yn are distributions over
70             chapter 3. indistinguishability & pseudo-randomness



         evens                    odds
     # of boxes that overlap   # of ... is odd
     another box is even




          (a) Description of Game                (b) n = 9: Even or Odd?




         (c) n = 22: Even or Odd?                (d) n > 80: Even or Odd?

                 Figure 70.2: A game parameterized by n


{0, 1}`(n) for some polynomial `(·). We say that { Xn }n and
{Yn }n are computationally indistinguishable (abbr. { Xn }n ≈ {Yn }n )
if for all non-uniform p.p.t. D (called the “distinguisher”), there
exists a negligible function e(·) such that ∀n ∈ N


      Pr [t ← Xn , D (t) = 1] − Pr [t ← Yn , D (t) = 1] < e(n).


In other words, two (ensembles of) probability distributions are
computationally indistinguishable if no efficient distinguisher D
can tell them apart better than with a negligible advantage.
    To simplify notation, we say that D distinguishes the distribu-
tions Xn and Yn with probability e if


         Pr [t ← Xn , D (t) = 1] − Pr [t ← Yn , D (t) = 1] > e.


Additionally, we say D distinguishes the ensembles { Xn }n and
{Yn }n with probability µ(·) if ∀n ∈ N, D distinguishes Xn and
Yn with probability µ(n).
 3.1. Computational Indistinguishability                            71


 3.1.1   Properties of Computational Indistinguishability
 We highlight some important (and natural) properties of the
 notion of indistinguishability. This properties will be used over
 and over again in the remainder of the course.

 Closure Under Efficient Opertations
 The first property formalizes the statement “If two distributions
 look the same, then they look the same no matter how you pro-
 cess them” (as long as the processing is efficient). More formally,
 if two distributions are indistinguishable, then they remain indis-
 tinguishable even after one applies a p.p.t. computable operation
 to them.

.Lemma 71.5 (Closure Under Efficient Operations) If the pair of
 ensembles { Xn }n ≈ {Yn }n , then for any n.u.p.p.t M, { M ( Xn )}n ≈
 { M(Yn )}n .
 Proof. Suppose there exists a non-uniform p.p.t. D and non-
 negligible function µ(n) such that D distinguishes { M( Xn )}n
 from { M(Yn )}n with probability µ(n). That is,

 | Pr[t ← M( Xn ) : D (t) = 1] − Pr[t ← M(Yn ) : D (t) = 1]| > µ(n)

 It then follows that

 | Pr[t ← Xn : D ( M(t)) = 1] − Pr[t ← Yn : D ( M(t)) = 1]| > µ(n).

 In that case, the non-uniform p.p.t. machine D 0 (·) = D ( M(·))
 also distinguishes { Xn }n , {Yn }n with probability µ(n), which
 contradicts that the assumption that { Xn }n ≈ {Yn }n .        

 Transitivity - The Hybrid Lemma
 We next show that the notion of computational indistinguishabil-
 ity is transitive; namely, if { An }n ≈ { Bn }n and { Bn }n ≈ {Cn }n ,
 then { An }n ≈ {Cn }n . In fact, we prove a generalization of this
 statement which considers m = poly(n) distributions.

.Lemma 71.6 (Hybrid Lemma) Let X 1 , X 2 , . . . , X m be a sequence of
 probability distributions. Assume that the machine D distinguishes X 1
 72          chapter 3. indistinguishability & pseudo-randomness


 and X m with probability e. Then there exists some i ∈ [1, . . . , m − 1]
 s.t. D distinguishes X i and X i+1 with probability me .

 Proof. Assume D distinguishes X 1 , X m with probability e. That
 is,
          h                 i
      | Pr t ← X : D (t) = 1 − Pr [t ← X m : D (t) = 1] | > e
                1



 Let gi = Pr t ← X i : D (t) = 1 . Thus, | g1 − gm | > e. This im-
                               

 plies,

             | g1 − g2 | + | g2 − g3 | + · · · + | g m − 1 − g m |
                 ≥ | g1 − g2 + g2 − g3 + · · · + g m − 1 − g m |
                 = | g1 − gm | > e.

 Therefore, there must exist i such that | gi − gi+1 | > me .          

.Remark 72.7 (A geometric interpretation) Note that the probabil-
 ity with which D outputs 1 induces a metric space over probability
 distributions over strings t. Given this view the hybrid lemma is just a
 restatement of the triangle inequality over this metric spaces; in other
 words, if the distance between two consecutive probability distributions
 is small, then the distance between the extremal distributions is also
 small.

 Note that because we lose a factor of m when we have a sequence
 of m distributions, the hybrid lemma can only be used to deduce
 transitivity when m is polynomially-related to the security pa-
 rameter n. (In fact, it is easy to construct a “long” sequence of
 probability distributions in which each adjacent pair of distribu-
 tions are indistinguishable, but where the extremal distributions
 are distinguishable.)

 Example
 Let { Xn }n , {Yn }n and { Zn }n be pairwise indistinguishable prob-
 ability ensembles, where Xn , Yn , and Zn are distributions over
 {0, 1}n . Assume further that we can efficiently sample from
 all three ensembles. Consider the n.u. p.p.t. machine M(t)
 that samples y ← Yn where n = |t| and outputs t ⊕ y. Since
 3.1. Computational Indistinguishability                                73


 { Xn }n ≈c { Zn }n , closure under efficient operations directly im-
 plies that

     { x ← Xn ; y ← Yn : x ⊕ y}n ≈c {y ← Yn ; z ← Zn : z ⊕ y}n


 Distinguishing versus Predicting

 The notion of computational indistinguishability requires that
 no efficient distinguisher can tell apart two distributions with
 more than a negligible advantage. As a consequence of this
 property, no efficient machine can predict which distribution a
 sample comes from with probability 12 + poly1(n) ; any such predic-
 tor would be a valid distinguisher (show this!). As the following
 useful lemma shows, the converse also holds: if it is not possible
 to predict which distribution a sample comes from with proba-
 bility significantly better than 12 , then the distributions must be
 indistinguishable.

.Lemma 73.8 (The Prediction Lemma) Let { Xn0 }n and { Xn1 }n be
 two ensembles where Xn0 and Xn1 are probability distributions over
 {0, 1}`(n) for some polynomial `(·), and let D be a n.u. p.p.t. machine
 that distinguishes between { Xn0 }n and { Xn1 }n with probability µ(·) for
 infinitely many n ∈ N. Then there exists a n.u. p.p.t. A such that

             h                              i 1 µ(n)
           Pr b ← {0, 1}; t ← Xnb : A(t) = b ≥ +     .
                                              2  2

 for infinitely many n ∈ N.

 Proof. Assume without loss of generality that D outputs 1 with
 higher probability when receiving a sample from Xn1 than when
 receiving a sample from Xn0 , i.e.,

    Pr[t ← Xn1 : D (t) = 1] − Pr[t ← Xn0 : D (t) = 1] > µ(n)        (73.2)

 This is without loss of generality since otherwise, D can be
 replaced with D 0 (·) = 1 − D (·); one of these distinguishers
 works for infinitely many n ∈ N. We show that D is also a
 74         chapter 3. indistinguishability & pseudo-randomness


“predictor”:
    h                               i
 Pr b ← {0, 1}; t ← Xnb : D (t) = b
      1 h                      i                         
         Pr t ← Xn1 : D (t) = 1 + Pr t ← Xn0 : D (t) 6= 1
                                        
   =
      2
      1 h                      i                            
         Pr t ← Xn1 : D (t) = 1 + 1 − Pr t ← Xn0 : D (t) = 1
                                          
   =
      2
      1 1 h                          i                      
             Pr t ← Xn1 : D (t) = 1 − Pr t ← Xn0 : D (t) = 1
                                           
   = +
      2 2
         1 µ(n)
   = > +
         2     2
                                                                   


 3.2 Pseudo-randomness
 Using the notion of computational indistinguishability, we next
 turn to defining pseudo-random distributions.

 3.2.1 Definition of Pseudo-random Distributions
 Let Un denote the uniform distribution over {0, 1}n , i.e, Un =
 {t ← {0, 1}n : t}. We say that a distribution is pseudo-random if
 it is indistinguishable from the uniform distribution.

.Definition 74.1 (Pseudo-random Ensembles). The probability
 ensemble { Xn }n , where Xn is a probability distribution over
 {0, 1}l (n) for some polynomial l (·), is said to be pseudorandom if
 { Xn }n ≈ {Ul (n) }n .

     Note that this definition effectively says that a pseudorandom
 distribution needs to pass all efficiently computable statistical
 tests that the uniform distribution would have passesd; otherwise
 the statistical test would distinguish the distributions.
     Thus, at first sight it might seem very hard to check or prove
 that a distribution is pseudorandom. As it turns out, there
 are complete statistical tests; such a test has the property that
 if a distribution passes only that test, it will also pass all other
 efficient tests. We proceed to present such a test.
 3.2. Pseudo-randomness                                                     75


 3.2.2    A complete statistical test: The next-bit test
 We say that a distribution passes the next-bit test if no efficient
 adversary can, given any prefix of a sequence sampled from the
 distribution, predict the next bit in the sequence with probability
 significantely better than 12 (recall that this was one of the test
 originally suggested in the introduction of this chapter).

.Definition 75.2 An ensemble { Xn }n where Xn is a probability dis-
 tribution over {0, 1}`(n) for some polynomial l (n) is said to pass the
 Next-Bit Test if for every non-uniform p.p.t. A, there exists a negligible
 function e(n) such that ∀n ∈ N and ∀i ∈ [0, · · · , `(n)], it holds that

                                                             1
           Pr [t ← Xn : A(1n , t1 t2 . . . ti ) = ti+1 ] <     + e ( n ).
                                                             2
 Here, ti denotes the i’th bit of t.

.Remark 75.3 Note that we provide A with the additional input 1n .
 This is simply allow A to have size and running-time that is polynomial
 in n and not simply in the (potentially) short prefix t0 . . . ti .

.Theorem 75.4 (Completeness of the Next-Bit Test) If a probabil-
 ity ensemble { Xn }n passes the next-bit test then { Xn }n is pseudo-
 random.

 Proof. Assume for the sake of contradiction that there exists a
 non-uniform p.p.t. distinguisher D, and a polynomial p(·) such
 that for infinitely many n ∈ N, D distinguishes Xn and U`(n)
 with probability p(1n) . We contruct a machine A that predicts
 the next bit of Xn for every such n. Define a sequence of hybrid
 distributions as follows.
            n                                                        o
     Hni = x ← Xn : u ← U`(n) : x0 x1 . . . xi ui+1 ui+2 . . . u`(n)

                                       `(n)
 Note that Hn0 = U`(n) and Hn
                           = Xn . Thus, D distinguishes
                 `(n)
 between Hn and Hn with probability p(1n) . It follows from
          0

 the hybrid lemma that there exists some i ∈ [0, `(n)] such that
 D distinguishes between Hni and Hni+1 with probability p(n)`(
                                                            1
                                                               n)
                                                                  .
 Recall, that the only difference between H i+1 and H i is that in
76           chapter 3. indistinguishability & pseudo-randomness


H i+1 the (i + 1)th bit is xi+1 , whereas in H i it is ui+1 . Thus,
intuitively, D—given only the prefix x1 . . . xi —can tell apart xi+1
from a uniformly chosen bit. This in turn means that D also can
tell apart xi+1 from x̄i+1 . More formally, consider the distribution
H̃ni defined as follows:
           n                                                            o
     H̃ni = x ← Xn : u ← U`(n) : x0 x1 . . . xi−1 x̄i ui+1 . . . ul (m)

Note that Hni can be sampled by drawing from Hni+1 with proba-
bility 1/2 and drawing from H̃ni+1 with probability 1/2. Substi-
tuting this identity into the last of term
         h                       i       h               i
      Pr t ← Hni+1 : D (t) = 1 − Pr t ← Hni : D (t) = 1

yields

   Pr t ← Hni+1 : D (t) = 1 −
                               
       1          i +1 : D ( t ) = 1] + 1 Pr[ t ← H̃ i +1 : D ( t ) = 1]
                                                                         
       2 Pr[ t ← Hn                     2           n

which simplifies to
     1   h                     i    h                       i
       Pr t ← Hni+1 : D (t) = 1 − Pr t ← H̃ni+1 : D (t) = 1
     2
Combining this equation with the observation above that D
distinguishes Hni and Hni+1 with probability p(n)`(
                                                1
                                                    n)
                                                       implies that
D distinguishes Hni+1 and H̃ni+1 with probability p(n)`(
                                                     2
                                                         n)
                                                            . By the
prediction lemma, there must therefore exist a machine A such
that
       h                                   i  1          1
     Pr b ← {0, 1}; t ← Hni+1,b : D (t) = b > +
                                              2    p(n)`(n)

where we let Hni+1,1 denote Hni+1 and Hni+1,0 denote H̃ni+1 . (i.e., A
predicts whether a sample came from Hni+1 or H̃ni+1 .) We can now
use A to construct a machine A0 predicts xi+1 (i.e., the (i + 1)th
bit in the pseudorandom sequence):
algorithm 76.5: A0 (1n , t1 , . . . , ti ): A next-bit predictor
  Pick `(n) − i random bits ui+1 . . . u`(n) ← U `(n)−1
  Run g ← A(t1 . . . ti ui+1 . . . u`(n) )
 3.3. Pseudo-random generators                                        77


   if g = 1 then
      Output ui+1
   else
      Output ūi+1 = 1 − ui+1
   end if
 Note that,

  Pr t ← Xn : A0 (1n , t1 . . . ti ) = ti+1
                                           
            h                                 i 1    1
     = Pr b ← {0, 1}; t ← Hni+1,b : A(t) = 1 > +
                                                2 p(n)`(n)

 which concludes the proof Theorem 75.4.                              


 3.3 Pseudo-random generators
 We now turn to definitions and constructions of pseudo-random
 generators.

 3.3.1   Definition of a Pseudo-random Generators
.Definition 77.1 (Pseudo-random Generator). A function G :
 {0, 1}∗ → {0, 1}∗ is a Pseudo-random Generator (PRG) if the fol-
 lowing holds.

   1. (efficiency): G can be computed in p.p.t.
   2. (expansion): | G ( x )| > | x |
   3. The ensemble { x ← Un : G ( x )}n is pseudo-random.

 3.3.2   An Initial Construction
 To provide some intuition for our construction, we start by con-
 sidering a simplified construction (originally suggested by Adi
 Shamir). The basic idea is to iterate a one-way permutation and
 then output, in reverse order, all the intermediary values. More
 precisely, let f be a one-way permutation, and define the genera-
 tor G (s) = f n (s) k f n−1 (s) k . . . k f (s) k s. We use the k symbol
 here to represent string concatentation.
     The idea behind the scheme is that given some prefix of the
 output of the generator, computing the next block is equivalent
 78         chapter 3. indistinguishability & pseudo-randomness


  G(s) =      f n (s)   f n−1 (s) f n−2 (s)   ...   f (s)     s



               Figure 78.2: Shamir’s proposed PRG


 to inverting the one-way permutation f . Indeed, this scheme
 results in a sequence of unpredictable numbers, but not necessarily
 unpredictable bits. In particular, a one-way permutation may
 never “change” the first two bits of its input, and thus those
 corresponding positions will always be predictable.
     The reason we need f to be a permutation, and not a gen-
 eral one-way function, is two-fold. First, we need the domain
 and range to be the same number of bits. Second, and more
 importantly, we require that the output of f k ( x ) be uniformly
 distributed if x is uniformly distributed. This holds if f is a
 permutation, but may not hold for a general one-way function.
     As we shall see, this construction can be modified to generate
 unpredictable bits as well. Doing so requires the new concept of
 a hard-core bit.

 3.3.3 Hard-core bits
 Intuitively, a predicate h is hard-core for a OWF f if h( x ) cannot
 be predicted significantly better than with probability 1/2, even
 given f ( x ). In other words, although a OWF might leak many
 bits of its inverse, it does not leak the hard-core bits—in fact, it
 essentially does not leak anything about the hard-core bits. Thus,
 hard-core bits are computationally unpredictable.

.Definition 78.3 (Hard-core Predicate). A predicate h : {0, 1}∗ →
 {0, 1} is a hard-core predicate for f ( x ) if h is efficiently com-
 putable given x, and for all nonuniform p.p.t. adversaries A,
 there exists a negligible e so that ∀k ∈ N
           h                                      i 1
         Pr x ← {0, 1}k : A(1n , f ( x )) = h( x ) ≤ + e(n)
                                                    2

 Examples The least significant bit of the RSA one-way function
 is known to be hardcore (under the RSA assumption). That
 3.3. Pseudo-random generators                                     79


 is, given N, e, and f RSA ( x ) = x e mod N, there is no efficient
 algorithm that predicts LSB( x ). A few other examples include:

    • The function half N ( x ) which is equal to 1 iff 0 ≤ x ≤ N2 is
      also hardcore for RSA, under the RSA assumption.

    • The function half p−1 ( x ) is a hardcore predicate for expo-
      nentiation to the power x mod p for a prime p under the
      DL assumption. (See §3.4.1 for this proof.)

     We now show how hard-core predicates can be used to con-
 struct a PRG.


 3.3.4   Constructions of a PRG
 Our idea for constructing a pseudo-random generator builds on
 Shamir’s construction above that outputs unpredictable numbers.
 Instead of outputting all intermediary numbers, however, we only
 output a “hard-core” bit of each of them. We start by providing
 a construction of a PRG that only expands the seed by one bit,
 and then give the full construction in Corollary 81.7.


.Theorem 79.4 Let f be a one-way permutation, and h a hard-core
 predicate for f . Then G (s) = f (s) k h(s) is a PRG.


 Proof. Assume for contradiction that there exists a nonuniform
 p.p.t. adversary A and a polynomial p(n) such that for infinitely
 many n, there exists an i such that A predicts the ith bit with
 probability p(1n) . Since the first n bits of G (s) are a permutation
 of a uniform distribution (and thus also uniformly distributed),
 A must predict bit n + 1 with advantage p(1n) . Formally,

                                            1    1
                  Pr[ A( f (s)) = h(s)] >     +
                                            2   p(n)

 This contradicts the assumption that b is hard-core for f . We
 conclude that G is a PRG.                                    
 80         chapter 3. indistinguishability & pseudo-randomness


 3.3.5   Expansion of a PRG
 The construction above from Thm. 79.4 only extends an n-bit
 seed to n + 1 output bits. The following theorem shows how a
 PRG that extends the seed by only 1 bit can be used to create a
 PRG that extends an n-bit seed to poly(n) output bits.

.Lemma 80.5 Let G : {0, 1}n → {0, 1}n+1 be a PRG. For any polyno-
 mial `, define G 0 : {0, 1}n → {0, 1}`(n) as follows (see Fig. 6):

                             G 0 (s) = b1 . . . b`(n) where
                                 X0 ← s
                      X i + 1 k bi + 1 ← G ( X i )

 Then G 0 is a PRG.


                                       s
                                     G(s)
                                      X0        b0
                                    G(X0 )

                                     X1        b1
                                    G(X1 )
                                     X2        b2

 Figure 80.6: Illustration of the PRG G 0 that expands a seed of
 length n to `(n). The function G is a PRG that expands by only 1
 bit.

 Proof. Consider the following recursive definition of G 0 (s) =
 G m ( s ):

             G0 ( x ) = ε
              Gi ( x ) = b|| Gi−1 ( x 0 ) where x 0 ||b ← G ( x )
 3.3. Pseudo-random generators                                                      81


 where ε denotes the empty string. Now, assume for contradic-
 tion that there exists a distinguisher D and a polynomial p(·)
 such that for infinitely many n, D distinguishes {Um(n) }n and
 { G 0 (Un )}n with probability p(1n) .
    Define the hybrid distributions Hni = Um(n)−i || Gi (Un ), for
                                                               m(n)
 i = 1, . . . , m(n). Note that Hn0 = Um(n) and Hn                    = G m(n) (Un ).
                                m(n)
 Thus, D distinguishes Hn0 and Hn    with probability p(1n) .      By
 the Hybrid Lemma, for each n, there exist some i such that D
 distinguishes Hni and Hni+1 with probability m(n)1p(n) . Recall that,

              Hni = Um−i k Gi (Un )
                   = Um−i−1 kU1 k Gi (Un )
             Hni+1 = Um−i−1 k Gi+1 (Un )
                   = Um−i−1 kbk Gi ( x ) where x kb ← G (Un )

  Consider the n.u. p.p.t. M(y) which outputs from the following
 experiment:
                      b prev ← Um−i−1
                      b ← y1
                      bnext ← Gi (y2 . . . yn+1 )
                      Output b prev kbkbnext
 Algorithm M (y) is non-uniform because for each input length n,
 it needs to know the appropriate i. Note that M (Un+1 ) = Hni and
 M ( G (Un )) = Hni+1 . Since (by the PRG property of G) {Un+1 }n ≈
 { G (Un )}n , it follows by closure under efficient operations that
 { Hni }n ≈ { Hni+1 }n , which is a contradiction.                
      By combining Theorem 79.4 and Lemma 80.5, we get the final
 construction of a PRG.

.Corollary 81.7 Let f be a OWP and h a hard core bit for f . Then

      G ( x ) = h( x ) k h( f ( x )) k h( f (2) ( x )) k . . . k h( f `(n) ( x ))

 is a PRG.

 Proof. Let G 0 ( x ) = f ( x ) k h( x ). By Theorem 79.4 G 0 is a PRG.
 Applying Lemma 80.5 to G 0 shows that G also is a PRG. See
 Fig. 8.                                                             
82           chapter 3. indistinguishability & pseudo-randomness


              s                     f (s)               f (2) ( s )            ...

                  h(s)                  h( f (s))              h( f (2) (s))
              b0                     b1                    b2


Figure 82.8: Illustration of a PRG based on a one-way permuta-
tion f and its hard-core bit h.

    Note that the above PRG can be computed in an “on-line”
fashion. Namely, we only need to remember xi to compute the
continuation of the output. This makes it possible to compute
an arbitrary long pseudo-random sequence using only a short
seed of a fixed length. (In other words, we do not need to know
an upper-bound on the length of the output when starting to
generate the pseudo-random sequence.)
    Furthermore, note that the PRG construction can be easily
adapted to work also with a collection of OWP, and not just a
OWP. If { f i } is a collection of OWP, simply consider G defined
as follows:
                                                         (2)
                  G (r1 , r2 ) = hi ( f i ( x )) k hi ( f i ( x )) k . . .

where r1 is used to sample i and r2 is used to sample x.

3.3.6 Concrete examples of PRGs
By using our concrete candidates of OWP (and their correspond-
ing hard-core bits), we get the following concrete instantiations
of PRGs.

Modular Exponentiation                 (Blum-Micali PRG)

     • Use the seed to generate p, g, x where p is a prime of the
       form 2q + 1 and q is also prime, g is a generator for Z∗p ,
       and x ∈ Z∗p .
                                                                                     x
     • Output half p−1 ( x ) k half p−1 ( g x mod p) k half p−1 ( g g mod
       p) k · · ·
3.4. Hard-Core Bits from Any OWF                                  83


RSA (RSA PRG)

   • Use the seed to generate p, q, e where p, q are random n-
     bit primes p, q, and e is a random element in Z∗N where
     N = pq.

   • Output LSB( x ) k LSB( x e mod N ) k LSB(( x e )e mod N ) k
     · · · where LSB( x ) is the least significant bit of x.

Rabin   (Blum-Blum-Schub)

   • Use seed to generate random k-bit primes p, q = 3 mod 4
     and x ∈ QRn , where n = pq.

   • Output LSB( x ) k LSB( x2 mod N ) k LSB(( x2 )2 mod N ) k
     . . . where LSB( x ) is the least significant bit of x.

   • This is efficient: given the state xi , only one modular multi-
     plication is needed to get the next bit. C.f. linear congruen-
     tial generators G ( xi+1 ) = axi + b.

   • We can efficiently compute the ith bit (i.e., LSB( x2 )i ) with-
     out needing to keep state ( x2 )i−1 , provided that the primes
     p and q are known. This is because we can easily compute
     Φ( pq).

In all the above PRGs, we can in fact output log n bits at each
iteration, while still remaining provably secure. Moreover, it is
conjectured that it is possible to output n2 bits at each iteration
and still remain secure (but this has not been proven).


3.4 Hard-Core Bits from Any OWF
We have previously shown that if f is a one-way permutation
and h is a hard-core predicate for f , then the function

                        G (s) = f (s) k h(s)

is a pseudo-random generator. One issue, however, is how to find
a hard-core predicate for a given one-way permutation. We have
illustrated examples for some of the well-known permutations.
 84            chapter 3. indistinguishability & pseudo-randomness


 Here, we show that every one-way function (permutation resp.)
 can be transformed into another one-way function (permutation
 resp.) which has a hard-core bit. Combined with our previous
 results, this shows that a PRG can be constructed from any one-
 way permutation.
     As a warm-up, we show that half p−1 is a hardcore predicate
 for exponentiation mod p (assuming the DL assumption).

 3.4.1 A Hard-core Bit from the Discrete Log problem
 Recall that halfn ( x ) is equal to 1 if and only iff 0 ≤ x ≤ n2 .

.Lemma 84.1 Under the DL assumption (52.2), the function half p−1
 is a hard-core predicate for the exponentiation function f p,g ( x ) = g x
 mod p from the discrete-log collection DL.

 Proof. First, note that it is easy to compute half p−1 () given x.
 Suppose, for the sake of contradiction, that there exists a n.u.
 p.p.t. algorithm A and a polynomial s(n) such that for infinitely
 many n ∈ N
         h                                                              i
     Pr f p,g ← DL(n); x ← Z p : A(1n , f p,g ( x )) = half( p−1) ( x )
               1   1
           >     +
               2 s(n)

 We show how to use the algorithm A to construct a new algo-
 rithm B which solves the discrete logarithm problem for the same
 n and therefore violates the discrete log assumption. To illustrate
 the idea, let us first assume that A is always correct. Later we
 remove this assumption. The algorithm B works as follows:
 algorithm 84.2: DiscreteLog( g, p, y) using A
  1: Set yk ← y and k = | p |
  2: while k > 0 do
  3:    if yk is a square mod p then
  4:       xk ← 0
  5:    else
  6:       xk ← 1
  7:       yk ← yk /g mod p to make a square
  8:    end if
3.4. Hard-Core Bits from Any OWF                                      85

                                             √
 9:   Compute the square root yk−1 ←             yk mod p
10:   Run b ← A(yk−1 )
11:   IF b = 0 THen yk−1 ← −yk−1
12:   Decrement k
13: end while
14: return x

      Recall from Thm. 58.2 and the related exercises on that page,
for every prime p, the modular square root operation can be
performed efficiently.
      Now if g is a generator, and y is square y = g2x , notice
that y has two square roots: g x and g x+ p/2 . (Recall that g p/2 =
−1 mod p.) The first of these two roots has a smaller discrete
log than y, and the other has a larger one. If it is possible to
determine which of the two roots is the smaller root—say by
using the adversary A to determine whether the exponent of the
root is in the “top half” [1, p/2] or not—then we can iteratively
divide, take square-roots, and then choose the root with smaller
discrete log until we eventually end up at 1. This is in fact the
procedure given above.
      Unfortunately, we are not guaranteed that A always outputs
the correct answer, but only that A is correct noticably more often
than not. In particular, A is correct with probability 12 + e where
e = s(n). To get around this problem, we can use self-reducibility
in the group Z p . In particular, we can choose ` random values
r1 , . . . , r` , and randomize the values that we feed to A in line 8 of
Alg. 84.2. Since A must be noticably more correct than incorrect,
we can use a “majority vote” to get an answer that is correct with
high probability.
      To formalize this intuition, we first demonstrate that the
procedure above can be used to solve the discrete log for instances
in which the discrete log is in the range [1, 2, . . . , e/4 · p]. As we
will show later, such an algorithm suffices to solve the discrete
log problem, since we can guess and map any instance into this
range. Consider the following alternative test in place of line 8
of Alg. 84.2.
    lo ← 0
    for i = 1, 2, . . . , ` do
        ri ← Z p
86          chapter 3. indistinguishability & pseudo-randomness


     z i ← y k −1 g r i
     bi ← A ( z i )
     Increment lo if (bi = 0 ∧ ri < p/2) or (bi = 1 ∧ ri ≥ p/2)
  end for
  Set b = 0 if lo > `/2 and 1 otherwise
Suppose the discrete log of yk is in the range [1, 2, . . . , s] where
s = e/4 · p. It follows that either the discrete log of yk−1 falls
within the range [1, 2, . . . , s/2] or in the range [ p/2, . . . p/2 + s/2].
In other words, the square root will either be slightly greater
than 0, or slightly greater than p/2. Let the event noinc represent
the case when the counter lo is not incremented in line 13. By
the Union Bound, we have that

Pr [noinc | low(yk−1 )] ≤ Pr[ A(zi ) errs]
                            + Pr[ri ∈ [ p/2 − s, p/2] ∪ [ p − s, p − 1]]

The last term on the right hand side arises from the error of re-
randomizing. That is, when ri ∈ [ p/2 − s, p/2], then the discrete
log of zi will be greater than p/2. Therefore, even if A answers
correctly, the test on line 13 will not increment the counter lo.
Although this error in unavoidable, since ri is chosen randomly,
we have that
                                      1               1 e
         Pr[noinc | low(yk−1 )] ≤       − e + 2(e/4) = −
                                      2               2 2
Conversely, the probability that lo is incremented is therefore
greater than 1/2 + e/2. By setting the number of samples ` =
(1/e)2 , then by the corollary of the Chernoff bound given in
Lemma 189.8, value b will be correct correct with probability
very close to 1.
                                                                
    In the above proof, we rely on specific properties of the OWP
f . We proceed to show how the existence of OWPs implies the
exitence of OWPs with a hard-core bit.

3.4.2 A General Hard-core Predicate from Any OWF
Let h x, r i denote the inner product of x and r, i.e., ∑ xi ri mod 2.
In other words, r decides which bits of x to take parity on.
 3.4. Hard-Core Bits from Any OWF                                          87


.Theorem 87.3 Let f be a OWF (OWP) and define function g( x, r ) =
 ( f ( x ), r ) where | x | = |r |. Then g is a OWF (OWP) and h( x, r ) =
 h x, r i is a hardcore predicate for f .

 3.4.3    *Proof of Theorem 87.3
 Proof. We show that if A, given g( x, r ) can compute h( x, r ) with
 probability non-negligibly better than 1/2, then there exists a
 p.p.t. adversary B that inverts f . More precisely, we use A to
 construct a machine B that on input y = f ( x ) recovers x with
 non-negligible probability, which contradicts the one-wayness
 of f . The proof is fairly involved. To provide intuition, we first
 consider two simplified cases.

 Oversimplified case: assume A always computes h( x, r ) cor-
 rectly. (Note that this is oversimplified as we only know that
 A computes h( x, r ) with probability non-negligibly better than
 1/2.) In this case the following simple procedure recovers x: B
 on input y lets xi = A(y, ei ) where ei = 00..010.. is an n bit string
 with the only 1 being in position i, and outputs x1 , x2 , . . . , xn .
 This clearly works, since by definition h x, ei i = xi and by our
 assumption A( f ( x ), r ) = h x, r i.

 Less simplified case: assume A computes h( x, r ) with proba-
 bility 43 + e(n) where e(n) = poly1(n) . In this case, the above
 algorithm of simply querying A with y, ei no longer work for
 two reasons:

    1. A might not work for all y’s,

    2. even if A predicts h( x, r ) with high probabiliy for a given
       y, but a random r, it might still fail on the particular r = ei .

 To get around the first problem, we show that for a reasonable
 fraction of x’s, A does work with high probability. We first define
 the “good set” of instances
                                                                      
                                n                                3 e
     S=       x | Pr [r ← {0, 1} : A( f ( x ), r ) = h( x, r )] > +
                                                                 4 2
 88           chapter 3. indistinguishability & pseudo-randomness


 Let us first argue that Pr [ x ∈ S] ≥ 2e . Suppose, for the sake of
 contradiction, that it is not. Then we have

          Pr [ x, r ← {0, 1}n : A( f ( x ), r ) = h( x, r )]
             ≤ (Pr [ x ∈ S] · 1)
               + (Pr [ x ∈
                         / S] · Pr [A( f ( x ), r ) = h( x, r )| x ∈
                                                                   / S])
               e                   
                                          3 e
                                                   
             <       + (1 − e/2) ·           +
                 2                        4 2
               3
             < +e
               4
which contradicts our assumption. The second term on the third
line of the derivation follows because by definition of S, when
x 6∈ S, then A succeeds with probability less than 34 + e/2.
    The second problem is more subtle. To get around it, we
“obfuscate” the queries y, ei and rely on the linearity of the inner
product operation. The following simple fact is useful.

.Fact 88.4 h a, b ⊕ ci = h a, bi ⊕ h a, ci mod 2
 Proof.

                h a, b ⊕ ci = Σai (bi + ci ) = Σai bi + Σai ci
                            = h a, bi + h a, ci mod 2

                                                                      
     Now, rather than asking A to recover h x, ei i, we instead pick
 a random string r and ask A to recover h x, r i and h x, r + e1 i, and
 compute the XOR of the answers. If A correctly answers both
 queries, then the i’th bit of x can be recovered. More precisely,
 B(y) proceeds as follows:
 algorithm 88.5: B(y)
   m ← poly(1/e)
   for i = 1, 2, . . . , n do
     for j = 1, 2, . . . , m do
        Pick random r ← {0, 1}n
        Set r 0 ← ei ⊕ r
        Compute a guess gi,j for xi as A(y, r ) ⊕ A(y, r 0 )
     end for
3.4. Hard-Core Bits from Any OWF                                      89


    xi ← majority( gi,1 , . . . , gi,m )
  end for
  Output x1 , . . . , xn .

Note that for a “good” x (i.e., x ∈ S) it holds that:

   • with probability at most 14 − 2e , A(y, r ) 6= h( x, r )

   • with probability at most 14 − 2e , A(y, r 0 ) 6= h( x, r )

It follows by the union bound that with probability at least 12 + e
both answers of A are correct. Since hy, r i ⊕ hy, r 0 i = hy, r ⊕ r 0 i =
hy, ei i, each guess gi is correct with probability 12 + e. Since
algorithm B attempts poly(1/e) independent guesses and finally
take a majority vote, it follows using the Chernoff Bound that
every bit is xi computed by B is correct with high probability.
Thus, for a non-negligible fraction of x’s, B inverts f , which is a
contradiction.

The general case. We proceed to the most general case. Here,
we simply assume that A, given random y = f ( x ) and random r
computes h( x, r ) with probability 12 + e (where e = poly1(n) ). As
before, define the set of good cases as
                                                        
                                                     1 e
           S = x | Pr [A( f ( x ), r ) = h( x, r )] > +
                                                     2 2

It again follows that Pr [ x ∈ S] ≥ 2e . To construct B , let us first as-
sume that B can call a subroutine C that on input f ( x ), produces
samples
              (b1 = h x, r1 i, r1 ), . . . , (bm = h x, rm i, rm )
where r1 , . . . , rm are independent and random. Consider the
following procedure B(y):
algorithm 89.6: B(y) for the General case
  m ← poly(1/e)
  for i = 1, 2, . . . , n do
    (b1 , r1 ), . . . , (bm , rm ) ← C (y)
    for j = 1, 2, . . . , m do
       Let r 0j = ei ⊕ r j
90           chapter 3. indistinguishability & pseudo-randomness


      Compute gi,j = b j ⊕ A(y, r 0 )
    end for
    Let xi ← majority( g1 , . . . , gm )
  end for
  Output x1 , . . . , xn .
      Given an x ∈ S, it follows that each guess gi,j is correct with
probability 12 + 2e = 12 + e0 . We can now again apply the the
Chernoff bound to show that xi is wrong with probability ≤
      02
2−e m . Thus, as long as m >> e102 , we can recover all xi . The only
problem is that B uses the magical subroutine C.
      Thus, it remains to show how C can be implemented. As
an intermediate step, suppose that C were to produce samples
(b1 , r1 ), . . . , (bn , rn ) that were only pairwise independent (instead
of being completely independent). It follows by the Pairwise-
Independent Sampling inequality that each xi is wrong with
                                 −4e02
probability at most 14me                       1
                                    02 ≤ me02 . By union bound, any of the
xi is wrong with probability at most n/me02 which is less than 1/2
when m ≥ e2n02 . Thus, if we could get 2n/e02 pairwise independent
samples, we would be done. So, where can we get them from?
A simple approach to generating these samples would be to pick
r1 , . . . , rm at random and guess b1 , . . . , bm randomly. However,
bi would be correct only with probability 2−m . A better idea
is to pick log(m) samples s1 , . . . , slog(m) and guess b10 , . . . , blog
                                                                         0
                                                                            (m) ;
here the guess is correct with probability 1/m. Now, gener-
ate r1 , r2 , . . . , rm−1 as all possible sums (modulo 2) of subsets of
s1 , . . . , slog(m) , and b1 , b2 , . . . , bm as the corresponding subsets of
bi0 . That is,
                         ri = ∑ s j j ∈ I iff i j = 1
                               j∈ Ii

                        bi = ∑ b0j
                               j∈ Ii

       It is not hard to show that these ri are pairwise independent
samples (show this!). Yet with probability 1/m, all guesses for
b10 , . . . , blog
               0
                   (m) are correct, which means that b1 , . . . , bm−1 are also
correct.
       Thus, for a fraction of e0 of x 0 it holds that with probability
1/m, the algorithm B inverts f with probability 1/2. That is, B
 3.5. Secure Encryption                                             91


 inverts f with probability

                           e0   e 03   (e/2)3
                              =      =
                          2m    4n       4n

 when m = 2n
          e2
             . This contradicts the one-wayness of f .


 3.5 Secure Encryption
 We next use the notion of indistinguishability to provide a com-
 putational definition of security of encryption schemes. As we
 shall see, the notion of a PRG will be instrumental in the con-
 struction of encryption schemes which permit the use of a short
 key to encrypt a long message.
     The intuition behind the definition of secure encryption is
 simple: instead of requiring that encryptions of any two messages
 are identically distributed (as in the definition of perfect secrecy),
 the computational notion of secure encryption requires only that
 encryptions of any two messages are indistinguishable.


.Definition 91.1 (Secure Encryption). The encryption scheme
 (Gen, Enc, Dec) is said to be single-message secure if ∀ non uniform
 p.p.t. D, there exists a negligible function e(·) such that for
 all n ∈ N, m0 , m1 ∈ {0, 1}n , D distinguishes between the the
 following distributions with probability at most e(n):

    • {k ← Gen(1n ) : Enck (m0 )}
    • {k ← Gen(1n ) : Enck (m1 )}


     The above definition is based on the indistinguishability of
 the distribution of ciphertexts created by encrypting two different
 messages. The above definition does not, however, explicitly cap-
 ture any a priori information that an adversary might have. Later
 in the course, we will see a definition which explicitly captures
 any a priori information that the adversary might have and in fact
 show that the indistinguishability definition is equivalent to it.
 92          chapter 3. indistinguishability & pseudo-randomness


 3.6 An Encryption Scheme with Short Keys
 Recall that perfectly secure encryption schemes require a key that
 is at least as long as the message to be encrypted. In this section
 we show how a short key can be used to construct a secure
 encryption scheme. The idea is to use a one-time pad encryption
 scheme in which the pad is the output of a pseudo-random
 generator (instead of being truly random). Since we know how
 to take a small seed and construct a long pseudorandom sequence
 using a PRG, we can encrypt long messages with a short key.
     More precisely, consider the following encryption scheme.
 Let G (s) be a length-doubling pseudo-random generator.
 algorithm 92.1: Encryption Scheme for n-bit message

  Gen(1n ): k ← Un/2
  Enck (m): Output m ⊕ G (k )
  Deck (c): Output c ⊕ G (k )


.Theorem 92.2 Scheme (Gen, Enc, Dec) described in Algorithm 92.1
 is single-message secure.

 Proof. Assume for contradiction that there exists a distinguisher
 D and a polynomial p(n) such that for infinitely many n, there
 exist messages m0n , m1n such that D distinguishes between the
 following two distributions

      • {k ← Gen(1n ) : Enck (m0 )}

      • {k ← Gen(1n ) : Enck (m1 )}

 with probability 1/p(n). Consider the following hybrid distribu-
 tions:

      • Hn1 (Encryption of m0n ): {s ← Gen(1n ) : m0n ⊕ G (s)}.

      • Hn2 (OTP with m1n ): {r ← Un : m0n ⊕ r }.

      • Hn3 (OTP with m1n ): {r ← Un : m1n ⊕ r }.

      • Hn4 (Encryption of m1n ): {s ← Gen(1n ) : m1n ⊕ G (s)}.
 3.7. Multi-message Secure Encryption                                            93


 By construction D distringuishes Hn1 and Hn4 with probability
 1/p(n) for infinitely many n. It follows by the hybrid lemma
 that D also distinguishes two consequetive hybrids with prob-
 ability 1/4p(n) (for infinitely many n). We show that this is a
 contradiction.
     • Consider the n.u. p.p.t. machine Mi ( x ) = mi| x| ⊕ x1 and
       the distribution Xn = {s ← U n2 : G (s)}. By definition,
       Hn1 = M0 ( Xn ), Hn4 = M1 ( Xn ) and Hn2 = M0 (Un ), Hn3 =
       M1 (Un ). But since { Xn }n ≈ {Un }n (by the PRG property
       of G) it follows by closure under efficient operations that
       { Hn1 }n ≈ { Hn2 }n and { Hn3 }n ≈ { Hn4 }n .
     • Additionally, by the perfect secrecy of the OTP, Hn2 and Hn3
       are identically distributed.
 Thus, all consequetive hybrid distributions are indistinguishable,
 which is a contradiction.                                      

 3.7 Multi-message Secure Encryption
 As suggested by the name, single-message secure encryption only
 considers the security of an encryption scheme that is used to
 encrypt a single message. In general, we encrypt many messages
 and still require that the adversary cannot learn anything about
 the messages.
     The following definition extends single-message security to
 multi-message security. The definition is identical, with the only
 exception being that we require that the encryptions of any two
 vectors or messages are indistinguishable.

.Definition 93.1 (Multi-message Secure Encryption). An encryp-
 tion scheme (Gen, Enc, Dec) is said to be multi-message secure if
 for all non uniform p.p.t. D, for all polynomials q(n), there
 exists a negligible function e(·) such that for all n ∈ N and
 m0 , m1 , . . . , mq(n) , m00 , m10 , . . . , m0q(n) ∈ {0, 1}n , D distinguishes be-
 tween the the following distributions with probability at most
 e ( n ):
     1 Note that Mi is non-uniform as for each input lenght n, it has the message

 min hard-coded.
 94            chapter 3. indistinguishability & pseudo-randomness


      • {k ← Gen(1n ) : Enck (m0 ), Enck (m1 ), . . . Enck (mq(n) )}
      • {k ← Gen(1n ) : Enck (m00 ), Enck (m10 ), . . . Enck (m0q(n) )}

    It is easy to see that the single-message secure encryption
 scheme in Scheme 92.1 (i.e., Enck (m) = m ⊕ G (s), where G is a
 PRG) is not multi-message secure. More generally,

.Theorem 94.2 A multi-message secure encryption scheme cannot be
 deterministic and stateless.

 Proof. For any two messages m0 , m1 , consider the encryptions
 (c0 , c1 ), (c00 , c10 ) of the messages (m0 , m0 ) and (m0 , m1 ). If the
 encryption scheme is deterministic and stateless, c0 = c1 , but
 c00 6= c1 .                                                             
      Thus, any multi-message secure encryption scheme (that is
 stateless) must use randomness. One idea for such a scheme
 is to pick a random string r, then output r ||m ⊕ f (r ) for some
 function f . Ideally, we would like the output of f to be a random
 string as well. One way to get such an f might be to have a long
 pseudorandom sequence of length on the order of n2n . Then
 f could use r as an index into this sequence and return the
 n bits at r. But no pseudorandom generator can produce an
 exponential number of bits; the construction in §3.2 only works
 for pseudorandom generators with polynomial expansion.
      If we were to use a pseudorandom generator, then r could be
 at most O(log n) bits long, so even if r is chosen randomly, we
 would end up choosing two identical values of r with reasonable
 probability; this scheme would not be multi-message secure,
 though a stateful scheme that keeps track of the values of r
 used could be. What we need instead is a new type of “pseudo-
 random” function that allows us to index an exponentially long
 pseudo-random string.


 3.8 Pseudorandom Functions
 Before defining pseudorandom function, we first recall the defi-
 nition of a random function.
3.8. Pseudorandom Functions                                        95


3.8.1    Random Functions
The scheme r ||m ⊕ f (r ) would be multi-message secure if f were
a random function. We can describe a random functions in
two different ways: a combinatorial description—as a random
function table—and compuational description—as a machine
that randomly chooses outputs given inputs and keeps track
of its previous answers. In the combinatorial description, the
random function table can be view as a long array that stores the
values of f . So, f ( x ) returns the value at position nx.

        n bits     n bits       n bits                 n bits


     0101 . . .   1101 . . .   0010 . . .             0100 . . .

          1           2            3                     2n

Note that the description length of a random function is n2n ,
                 n
so there are 2n2 random functions from {0, 1}n → {0, 1}n . Let
RFn be the distribution that picks a function mapping {0, 1}n →
{0, 1}n uniformly at random.
     A computational description of a random function is instead
as follows: a random function is a machine that upon receiving
input x proceeds as follows. If it has not seen x before, it chooses
a value y ← {0, 1}n and returns y; it then records that f ( x ) = y.
If it has seen x before, then it looks up x, and outputs the same
value as before.

                     x
                                       f (x) = y
                     y


It can be seen that both of the above descriptions of a random
functions give rise to identical distributions.
    The problem with random functions is that (by definition)
they have a long description length. So, we cannot employ a
random function in our encryption scheme. We will next define
a pseudorandom function, which mimics a random function, but
has a short description.
 96           chapter 3. indistinguishability & pseudo-randomness


 3.8.2    Definition of Pseudorandom Functions
 Intuitively, a pseudorandom function (PRF) “looks” like a ran-
 dom function to any n.u. p.p.t. adversary. In defining this notion,
 we consider an adversary that gets oracle access to either the PRF,
 or a truly random function, and is supposed to decide which
 one it is interacting with. More precisely, an oracle Turing ma-
 chine M is a Turing machine that has been augmented with a
 component called an oracle: the oracle receives requests from M
 on a special tape and writes its responses to a tape in M. We
 now extend the notion of indistinguishability of distributions, to
 indistinguishability of distributions of oracles.

.Definition 96.1 (Oracle Indistinguishability). Let {On }n∈N and
 {On0 }n be ensembles where On , On0 are probability distributions
 over functions f : {0, 1}`1 (n) → {0, 1}`2 (n) for some polynomi-
 als `1 (·), `2 (·). We say that {On }n and {On0 }n are computation-
 ally indistinguishable (denoted by {On0 }n ≈ {On0 }n∈N ) if for all
 non-uniform p.p.t. oracles machines D, there exists a negligible
 function e(·) such that ∀n ∈ N
                    h                         i
                 Pr F ← On : D F(·) (1n ) = 1
                       h                           i < e ( n ).
                   − Pr F ← On0 : D F(·) (1n ) = 1

 It is easy to verify that oracle indistinguishability satisfies “clo-
 sure under efficient operations”, the Hybrid Lemma, and the
 Prediction Lemma.
      We turn to define pseudorandom functions.

.Definition 96.2 (Pseudo-random Function). A family of functions
 { f s : {0, 1}|s| → {0, 1}|s| }s∈{0,1}∗ is pseudo-random if
      • (Easy to compute): f s ( x ) can be computed by a p.p.t. algo-
        rithm that is given input s and x
      • (Pseudorandom): {s ← {0, 1}n : f s }n ≈ { F ← RFn : F }n .

 Note that in the definition of a PRF, it is critical that the seed s
 to the PRF is not revealed; otherwise it is easy to distinguish f s
 from a random function: simply ask the oracle a random query
 x and check whether the oracle’s reply equals f s ( x ).
 3.8. Pseudorandom Functions                                                         97


    Also note that the number of pseudorandom functions is
 much smaller than the number of random function (for the same
 input lenghts); indeed all pseudorandom functions have a short
 description, whereas random functions in general do not.

.Theorem 97.3 If a pseudorandom generator exists, then pseudoran-
 dom functions exist.

 Proof. We have already shown that any pseudorandom generator
 g is sufficient to construct a pseudorandom generator g0 that has
 polynomial expansion. So, without loss of generality, let g be a
 length-doubling pseudorandom generator.

           g:           x                      g0 ( x )         g1 ( x )


                     n bits                    n bits           n bits

 Then we define f s as follows to be a pseudorandom function:

             f s (b1 b2 . . . bn ) = gbn ( gbn−1 (· · · ( gb1 (s)) · · · ))

 f keeps only one side of the pseudorandom generator at each
 of n iterations. Thus, the possible outputs of f for a given input
 form a tree; the first three levels are shown in the following
 diagram. The leaves of the tree are the output of f .

                                           s


              s 0 = g0 ( s )                              s 1 = g1 ( s )


    s00 = g0 (s0 )      s01 = g1 (s0 )         s10 = g0 (s1 )       s11 = g1 (s1 )

     The intuition about why f is a pseudorandom function is
 that a tree of height n contains 2n leaves, so exponentially many
 values can be indexed by a single function with n bits of input.
 Thus, each unique input to f takes a unique path through the
 tree. The output of f is the output of a pseudorandom generator
 on a random string, so it is also pseudo-random.
98         chapter 3. indistinguishability & pseudo-randomness


    One approach to the proof is to look at the leaves of the
tree. Build a sequence of hybrids by successively replacing each
leaf with a random distribution. This approach, however, does
not work because our hybrid lemma does not apply when there
are exponentially many hybrids. Instead, we form hybrids by
replacing successive levels of the tree: hybrid HFin is formed
by picking all levels through the ith uniformly at random, then
applying the tree construction as before.


                                                          random




     Note that HF1n = {s ← {0, 1}n : f s (·)} (picking only the seed
at random), which is the distribution defined originally. Further,
HFnn = RFn (picking the leaves at random).
     Thus, if D can distinguish F ← RFn and f s for a randomly
chosen s, then D distinguishes F1 ← HF1n and Fn ← HFnn with
probability e. By the hybrid lemma, there exists some i such that
D distinguishes HFin and HFin+1 with probability e/n.
     The difference between HFin and HFin+1 is that level i + 1 in
HFn is g(Un ), whereas in HFin+1 , level i + 1 is Un . Afterwards,
   i

both distributions continue to use g to construct the tree.
     To finish the proof, we will construct one more set of hybrid
distributions. Recall that there is some polynomial p(n) such
that the number of queries made by D is bounded by p(n). So,
we can now apply the first hybrid idea suggested above: define
              j
hybrid HHFn that picks F from HFni , and answer the first j new
queries using F, then answer the remaining queries using HFni+1 .
     But now there are only p(n) hybrids, so the hybrid lemma
                                          j           j +1
applies, and D can distinguish HHFn and HHFn for some j
                                            j          j +1
with probability e/(np(n)). But HHFn and HHFn differ only
              j +1
in that HHFn answers its j + 1st query with the output of a
pseudorandom generator on a randomly chosen value, whereas
 3.9. Construction of Multi-message Secure Encryption              99

      j
 HHFn answers its j + 1st query with a randomly chosen value.
                    j
 As queries to HHFn can be emulated in p.p.t. (we here rely on the
 equivalence between the combinatorial and the computational
 view of a random function; we omit the details), it follows by
 closure under efficient operations that D contradicts the pseudo-
 random property of g.                                          


 3.9 Construction of Multi-message Secure
     Encryption
 The idea behind our construction is to use a pseudorandom func-
 tion in order to pick a separate random pad for every message.
 In order to make decryption possible, the ciphertext contains the
 input on which the pseudo-random function is evaluated.

 algorithm 99.1: Many-message Encryption Scheme


  Assume m ∈ {0, 1}n and let { f k } be a PRF family.
  Gen(1n ) : k ← Un
  Enck (m) : Pick r ← Un . Output (r, m ⊕ f k (r ))
  Deck ((r, c)) : Output c ⊕ f k (r )




.Theorem 99.2 (Gen, Enc, Dec) is a many-message secure encryption
 scheme.

 Proof. Assume for contradiction that there exists a n.u. p.p.t.
 distinguisher D, and a polynomial p(·) such that for infinitely
 many n, there exists messages m̄ = {m0 , m1 . . . , mq(n) } and m̄0 =
 {m00 , m10 . . . , m0q(n) } such that D distinguishes between encryp-
 tions of m̄ and m̄0 w.p. p(1n) . (To simplify notation, here—and in
 subsequent proofs—we sometimes omit n from our notation and
 let mi denote min , whenever n is clear from the context). Con-
 sider the following sequence of hybrid distributions: As above, it
 should be clear that Hi denotes Hni .
100           chapter 3. indistinguishability & pseudo-randomness


      • H1 : real encryptions of m0 , m1 . . . , mq(n)

                 s ← {0, 1}n
                 r0 , . . . , rq(n) ← {0, 1}n
                 (r0 , m0 ⊕ f s (r0 )), . . . , (rq(n) , mq(n) ⊕ f s (rq(n) ))

        This is precisely what the adversary sees when receiving
        the encryptions of m0 , . . . , mq(n) .
      • H2 : Replace f with a truly random function R:
                  R ← RFn
                  r0 , . . . , rq(n) ← {0, 1}n
                  (r0 , m0 ⊕ R(r0 )), . . . , (rq(n) , mq(n) ⊕ R(rq(n) ))

      • H3 – using OTP on m0 , m1 , . . . , mq(n)

                           p0 . . . pq(n) ← {0, 1}n
                           r0 , . . . , rq(n) ← {0, 1}n
                           (r0 , m0 ⊕ p0 , . . . , m q ( n ) ⊕ p q ( n ) )

      • H4 – using OTP on m00 , m10 , . . . , m0q(n)

                             p0 . . . pq(n) ← {0, 1}n
                            r0 , . . . , rq(n) ← {0, 1}n
                            (r0 , m00 ⊕ p0 , . . . m0q(n) ⊕ pq(n)

      • H5 – Replace f with a truly random function R:
                  R ← {{0, 1}n → {0, 1}n }
                  r0 , . . . , rq(n) ← {0, 1}n
                  (r0 , m00 ⊕ R(r0 ), . . . (rq(n) , m0q(n) ⊕ R(rq(n) ))}

      • H6 – real encryptions of m00 , m10 , . . . , m0q(n)

                  s ← {0, 1}n
                  r0 , . . . , rq(n) ← {0, 1}n
                  (r0 , m00 ⊕ f s (r0 ), . . . , (rq(n) , m0q(n) ⊕ f s (rq(n) )}
3.10. Public Key Encryption                                       101


By the Hybrid Lemma, D distinguishes between to adjacent
hybrid distributions with inverse polynomial probability (for
infinitely many n). We show that this is a contradiction:

   • First, note that D distinguish between H1 and H2 only with
     negligible probability; otherwise (by closure under efficient
     operations) we contradict the pseudorandomness property
     of { f s }n .
     The same argument applies for H6 and H5 .

   • H2 and H3 are “almost” identical except for the case when
     ∃i, j such that ri = r j , but this happens only with probability

                                  q(n)
                                      
                                         · 2− n ,
                                   2

     which is negligible; thus, D can distinguishes between
     H2 and H3 only with negligible probability. The same
     argument applies for H4 and H5 .

   • Finally, H3 and H4 are identical by the perfect secrecy of
     the OTP.

This contradicts that D distinguishes two adjacent hybrids.        


3.10 Public Key Encryption
So far, our model of communication allows the encryptor and
decryptor to meet in advance and agree on a secret key which
they later can use to send private messages. Ideally, we would
like to drop this requirement of meeting in advance to agree on a
secret key. At first, this seems impossible. Certainly the decryp-
tor of a message needs to use a secret key; otherwise, nothing
prevents the eavesdropper from running the same procedure
as the decryptor to recover the message. It also seems like the
encryptor needs to use a key because otherwise the key cannot
help to decrypt the cyphertext.
    The flaw in this argument is that the encrypter and the de-
cryptor need not share the same key, and in fact this is how
public key cryptography works. We split the key into a secret
 102        chapter 3. indistinguishability & pseudo-randomness


 decryption key sk and a public encryption key pk. The public
 key is published in a secure repository, where anyone can use it
 to encrypt messages. The private key is kept by the recipient so
 that only she can decrypt messages sent to her.
     We define a public key encryption scheme as follows:

.Definition 102.1 (Public Key Encryption Scheme). A triple of
 algorithms (Gen, Enc, Dec) is a public key encryption scheme if

   1. ( pk, sk) ← Gen(1n ) is a p.p.t. algorithm that produces a key
      pair ( pk, sk)
   2. c ← Enc pk (m) is a p.p.t. algorithm that given pk and m ∈
      {0, 1}n produces a ciphertext c.
   3. m ← Decsk (c) is a deterministic algorithm that given a
      ciphertext c and secret key sk produces a message m ∈
      {0, 1}n ∪ ⊥.
   4. There exists a polynomial-time algorithm M that on input
      (1n , i ) outputs the ith n-bit message (if such a message exists)
      according to some order.
   5. For all n ∈ N, m ∈ {0, 1}n

           Pr ( pk, sk) ← Gen(1n ) : Decsk (Enc pk (m)) = m = 1
                                                          


     We allow the decryption algorithm to produce a special sym-
 bol ⊥ when the input ciphertext is “undecipherable.” The secu-
 rity property for public-key encryption can be defined using an
 experiment similar to the ones used in the definition for secure
 private key encryption.

.Definition 102.2 (Secure Public Key Encryption). The public key
 encryption scheme (Gen, Enc, Dec) is said to be secure if for all
 non uniform p.p.t. D, there exists a negligible function e(·) such
 that for all n ∈ N, m0 , m1 ∈ {0, 1}n , D distinguishes between the
 the following distributions with probability at most e(n):

    • {( pk, sk) ← Gen(1n ) : ( pk, Enc pk (m0 ))}n
    • {( pk, sk) ← Gen(1n ) : ( pk, Enc pk (m1 ))}n
3.10. Public Key Encryption                                                 103


   With this definitions, there are some immediate impossibility
results:

Perfect secrecy Perfect secrecy is not possible (even for small
     message spaces) since an unbounded adversary could sim-
     ply encrypt every message in {0, 1}n with every random
     string and compare with the challenge ciphertext to learn
     the underlying message.

Deterministic encryption It is also impossible to have a deter-
     ministic encryption algorithm because otherwise an adver-
     sary could simply encrypt and compare the encryption
     of m0 with the challenge ciphertext to distinguish the two
     experiments.

    As with the case of private-key encryption, we can extend the
definition to multi-message security. Fortunately, for the case of
public-key encryption, multi-message security is equivalent to
single-messages security. This follows by a simple application of
the hybrid lemma, and closure under efficient operations; the key
point here is that we can efficiently generate encryptions of any
message, without knowing the secret key (this was not possible,
in the case of private-key encryption). We leave it as an exercise
to the reader to complete the proof.
    We can consider a weaker notion of “single-bit” secure en-
cryption in which we only require that encryptions of 0 and 1
are indistinguishable. Any single-bit secure encryption can be
turned into a secure encryption scheme by simply encrypting
each bit of the message using the single-bit secure encryption;
the security of the new scheme follows directly from the multi-
message security (which is equivalent to traditional security) of
the single-bit secure encryption scheme.2

3.10.1 Constructing a Public Key Encryption Scheme
Trapdoor permutations seem to fit the requirements for a public
key cryptosystem. We could let the public key be the index i of
    2 As we discuss in a later chapter, this same argument does not apply for

stronger definitions of encryption such as chosen-ciphertext security. In fact, a
more sophisticated argument is needed to show the same simple result.
 104          chapter 3. indistinguishability & pseudo-randomness


 the function to apply, and the private key be the trapdoor t. Then
 we might consider Enci (m) = f i (m), and Deci,t (c) = f i−1 (c). This
 makes it easy to encrypt, and easy to decrypt with the public key,
 and hard to decrypt without. Using the RSA function defined in
 Theorem 53.2, this construction yields the commonly used RSA
 cryptosystem.
        However, according to our definition, this construction does
 not yield a secure encryption scheme. In particular, it is de-
 terministic, so it is subject to comparison attacks. A better
 scheme (for single-bit messages) is to let Enci ( x ) = {r ← {0, 1}n :
 h f i (r ), b(r ) ⊕ mi} where b is a hardcore bit for f . As we show,
 the scheme is secure, as distinguishing encryptions of 0 and
 1 essentially requires predicting the hardcore bit of a one-way
 permutation.
 algorithm 104.3: 1-Bit Secure Public Key Encryption

  Gen(1n ) : ( f i , f i−1 ) ← GenT (1n ). Output ( pk, sk) ← (( f i , bi ), f i−1 )
  Enc pk (m): Pick r ← {0, 1}n . Output ( f i (r ), bi (r ) ⊕ m).
  Decsk (c1 , c2 ): Compute r ← f i−1 (c1 ). Output bi (r ) ⊕ c2 .

 Here, ( f i , f −1 )i∈ I is a family of one-way trapdoor permutations
 and bi is the hard-core bit corresponding to f i . Let GenT be the
 p.p.t. that samples a trapdoor permutation index from I.

.Theorem 104.4 If trapdoor permutations exist, then scheme 104.3 is
 a secure single-bit public-key encryption system.

 Proof: As usual, assume for contradiction that there exists a
 n.u. p.p.t. D and a polynomial p(·), such that D distinguishes
 {( pk, sk) ← Gen(1n ) : ( pk, Enc pk (0))} and {( pk, sk) ← Gen(1n ) :
 ( pk, Enc pk (1))} w.p. p(1n) for infinitely many n. By the prediction
 lemma, there exist a machine A such that
    Pr m ← {0, 1}; ( pk, sk) ← Gen(1n ) : D ( pk, Enc pk (m)) = m
                                                                   

           1   1
       >     +
           2 2p(n)
 We can now use A to construct a machine A0 that predicts the
 hard-core predicate b(·):
 3.11. El-Gamal Public Key Encryption scheme                             105


    • A0 on input ( pk, y) picks c ← {0, 1}, m ← A( pk, (y, c)), and
      outputs c ⊕ m.
 Note that,

 Pr ( pk, sk) ← Gen(1n ); r ← {0, 1}n : A0 ( pk, f pk (r )) = b(r )
                                                                    

             ( pk, sk) ← Gen(1n );
                                                                        

   = Pr  r ← {0, 1}n ;             : A( pk, ( f pk (r ), c)) ⊕ c = b(r )
             c ← {0, 1}
             ( pk, sk) ← Gen(1n );
                                                                          

   = Pr  r ← {0, 1}n ;             : A( pk, ( f pk (r ), m ⊕ b(r ))) = m
             m ← {0, 1}
                                                                
            m ← {0, 1}
   = Pr                            : A( pk, Enc pk (m)) = m
            ( pk, sk) ← Gen(1n )
      1        1
   ≥ +              .
      2 2p(n)
                                                                          

 3.11 El-Gamal Public Key Encryption scheme
 The El-Gamal public key encryption scheme is a popular and
 simple public key encryption scheme that is far more efficient
 than the one just presented. However, this efficiency requires
 us to make a new complexity assumption called the Decisional
 Diffie-Hellman Assumption (DDH).

.Assumption 105.1 (Decisional Diffie-Hellman (DDH)) The fol-
 lowing ensembles are computationally indistinguishable
      n                                                        o
        p ← Π̃n , y ← Genq , a, b ← Zq : p, y, y a , yb , y ab     ≈
                                                                 n
           n                                                         o
             p ← Π̃n , y ← Genq , a, b, z ← Zq : p, y, y a , yb , yz
                                                                     n

 Here the term Π̃n refers to the special subset of safe primes

            Π̃n = { p | p ∈ Πn and p = 2q + 1, q ∈ Πn−1 }

 The corresponding q is called a Sophie Germain prime. We use such
 a multiplicative group G = Z p because it has a special structure
106        chapter 3. indistinguishability & pseudo-randomness


that is convenient to work with. First, G has a subgroup Gq of
order q, and since q is prime, Gq will be a cyclic group. Thus, it is
easy to pick a generator of the group Gq (since every element is
a generator). When p = 2q + 1, then the subgroup Gq consists of
all of the squares modulo p. Thus, choosing a generator involves
simply picking a random element a ∈ G and computing a2 . Note
that all of the math is still done in the “big” group, and therefore
modulo p.
    It is crucial for the DDH assumption that the group within
which we work is a prime-order group. In a prime order group, all
elements except the identity have the same order. On the other
hand, in groups like G, there are elements of order 2, q and 2q,
and it is easy to distinguish between these cases. For example, if
one is given a tuple T = ( p, y, g, h, f ) and one notices that both
g, h are of order q but f is of order 2q, then one can immediately
determine that tuple T is not a DDH-tuple.
    Notice that the DDH assumption implies the discrete-log
assumption (Assumption 52.2) since after solving the discrete
log twice on the first two components, it is easy to distinguish
whether the third component is y ab or not.
    We now construct a Public Key Encryption scheme based on
the DDH assumption.
algorithm 106.2: El-Gamal Secure Public Key Encryption

 Gen(1n ): Pick a safe prime p = 2q + 1 of length n. Choose
     a random element g ∈ Z p and compute h ← g2 mod p.
     Choose a ← Zq . Output pk ← ( p, h, h a mod p) and sk as
     sk ← ( p, h, a).

 Enc pk (m): Choose b ← Zq . Output (hb , h ab · m mod p).

 Decsk (c = (c1 , c2 )): Output c2 /c1a mod p.


    Roughly speaking, this scheme is secure assuming the DDH
assumption since h ab is indistinguishable from a random element
and hence, by closure under efficient operations, h ab · m is indis-
tinguishable from a random element too. We leave the formal
proof as an exercise to the reader.
 3.12. A Note on Complexity Assumptions                        107


.Theorem 107.3 If the DDH Assumption holds, then scheme 106.2 is
 secure.


 3.12 A Note on Complexity Assumptions
 During these first two chapters, we have studied a hierarchy
 of constructions. At the bottom of this hierarchy are computa-
 tionally difficult problems such as one-way functions, one-way
 permutations, and trapdoor permutations. Our efficient con-
 structions of these objects were further based on specific number-
 theoretic assumptions, including factoring, RSA, discrete log, and
 decisional Diffie-Hellman.
     Using these hard problems, we constructed several primi-
 tives: pseudorandom generators, pseudorandom functions, and
 private-key encryption schemes. Although our constructions
 were usually based on one-way permutations, it is possible to
 construct these same primitives using one-way functions. Further,
 one-way functions are a minimal assumption, because the exis-
 tence of any of these primitives implies the existence of one-way
 functions.
     Public-key encryption schemes are noticeably absent from
 the list of primitives above. Although we did construct two
 public key encryption schemes, it is unknown how to base such
 a construction on one-way functions. Moreover, it is known to
 be impossible to create a black-box construction from one-way
 functions.
