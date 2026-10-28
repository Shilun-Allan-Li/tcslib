 Chapter 2

 Computational Hardness

 2.1 Efficient Computation and Efficient
     Adversaries
 We start by formalizing what it means for an algorithm to com-
 pute a function.

.Definition 21.1 (Algorithm) An algorithm is a deterministic Tur-
 ing machine whose input and output are strings over alphabet Σ =
 {0, 1}.

.Definition 21.2 (Running-time) An algorithm A is said to run in
 time T (n) if for all x ∈ {0, 1}∗ , A( x ) halts within T (| x |) steps. A
 runs in polynomial time if there exists a constant c such that A runs
 in time T (n) = nc .

.Definition 21.3 (Deterministic Computation) An algorithm A is
 said to compute a function f : {0, 1}∗ → {0, 1}∗ if for all x ∈ {0, 1}∗ ,
 A, on input x, outputs f ( x ).

     We say that an algorithm is efficient if it runs in polynomial
 time. One may argue about the choice of polynomial-time as a
 cutoff for efficiency, and indeed if the polynomial involved is
 large, computation may not be efficient in practice. There are,
 however, strong arguments to use the polynomial-time definition
 of efficiency:

                                    21
22                            chapter 2. computational hardness


     1. This definition is independent of the representation of the
        algorithm (whether it is given as a Turing machine, a C
        program, etc.) because converting from one representation
        to another only affects the running time by a polynomial
        factor.

     2. This definition is also closed under composition which may
        simplify reasoning in certain proofs.

     3. Our experience suggests that polynomial-time algorithms
        turn out to be efficient; i.e. polynomial almost always
        means “cubic time or better.”

     4. Our experience indicates that “natural” functions that are
        not known to be computable in polynomial-time require
        much more time to compute, so the separation we propose
        seems well-founded.

   Note, our treatment of computation is an asymptotic one. In
practice, concrete running time needs to be considered carefully,
as do other hidden factors such as the size of the description
of A. Thus, when porting theory to practice, one needs to set
parameters carefully.

2.1.1 Some computationally “hard” problems
Many commonly encountered functions are computable by ef-
ficient algorithms. However, there are also functions which are
known or believed to be hard.

Halting: The famous Halting problem is an example of an uncom-
     putable problem: Given a description of a Turing machine
     M, determine whether or not M halts when run on the
     empty input.

Time-hierarchy: The Time Hierarchy Theorem from Complex-
    ity theory states that there exist languages that are de-
    cideable in time O(t(n)) but cannot be decided in time
     o (t(n)/ log t(n)). A corollary of this theorem is that there
    are functions f : {0, 1}∗ → {0, 1} that are computable in
    exponential time but not computable in polynomial time.
 2.1. Efficient Computation and Efficient Adversaries                23


 Satisfiability: The notorious SAT problem is to determine if a
       given Boolean formula has a satisfying assignment. SAT
       is conjectured not to be solvable in polynomial-time—this
       is the famous conjecture that P 6= NP. See Appendix B for
       definitions of P and NP.

 2.1.2   Randomized Computation
 A natural extension of deterministic computation is to allow
 an algorithm to have access to a source of random coin tosses.
 Allowing this extra freedom is certainly plausible (as it is con-
 ceivable to generate such random coins in practice), and it is
 believed to enable more efficient algorithms for computing cer-
 tain tasks. Moreover, it will be necessary for the security of the
 schemes that we present later. For example, as we discussed in
 chapter one, Kerckhoff’s principle states that all algorithms in
 a scheme should be public. Thus, if the private key generation
 algorithm Gen did not use random coins in its computation, then
 Eve would be able to compute the same key that Alice and Bob
 compute. Thus, to allow for this extra resource, we extend the
 above definitions of computation as follows.

.Definition 23.4 (Randomized (PPT) Algorithm) A randomized
 algorithm, also called a probabilistic polynomial-time Turing machine
 and abbreviated as PPT, is a Turing machine equipped with an extra ran-
 dom tape. Each bit of the random tape is uniformly and independently
 chosen.

 Equivalently, a randomized algorithm is a Turing Machine that
 has access to a coin-tossing oracle that outputs a truly random
 bit on demand.
     To define efficiency we must clarify the concept of running
 time for a randomized algorithm. A subtlety arises because
 the run time of a randomized algorithm may depend on the
 particular random tape chosen for an execution. We take a
 conservative approach and define the running time as the upper
 bound over all possible random sequences.

.Definition 23.5 (Running time) A randomized Turing machine A
 runs in time T (n) if for all x ∈ {0, 1}∗ , and for every random tape,
 24                              chapter 2. computational hardness


 A( x ) halts within T (| x |) steps. A runs in polynomial time (or is an
 efficient randomized algorithm) if there exists a constant c such that
 A runs in time T (n) = nc .

 Finally, we must also extend our notion of computation to ran-
 domized algorithms. In particular, once an algorithm has a
 random tape, its output becomes a distribution over some set. In
 the case of deterministic computation, the output is a singleton
 set, and this is what we require here as well.

.Definition 24.6 A randomized algorithm A computes a function
 f : {0, 1}∗ → {0, 1}∗ if for all x ∈ {0, 1}∗ , A on input x, outputs
 f ( x ) with probability 1. The probability is taken over the random tape
 of A.

     Notice that with randomized algorithms, we do not tolerate
 algorithms that on rare occasion make errors. Formally, this
 requirement may be too strong in practice because some of the
 algorithms that we use in practice (e.g., primality testing) do err
 with small negligible probability. In the rest of the book, however,
 we ignore this rare case and assume that a randomized algorithm
 always works correctly.
     On a side note, it is worthwhile to note that a polynomial-time
 randomized algorithm A that computes a function with proba-
 bility 12 + poly1(n) can be used to obtain another polynomial-time
 randomized machine A0 that computes the function with prob-
 ability 1 − 2−n . (A0 simply takes multiple runs of A and finally
 outputs the most frequent output of A. The Chernoff bound (see
 Appendix A) can then be used to analyze the probability with
 which such a “majority” rule works.)
     Polynomial-time randomized algorithms will be the principal
 model of efficient computation considered in this course. We
 will refer to this class of algorithms as probabilistic polynomial-time
 Turing machine (p.p.t.) or efficient randomized algorithm interchange-
 ably.
     Given the above notation we can define the notion of an
 efficient encryption scheme:
 2.1. Efficient Computation and Efficient Adversaries               25


.Definition 24.7 (Efficient Private-key Encryption). A triplet of al-
 gorithms (Gen, Enc, Dec) is called an efficient private-key encryption
 scheme if the following holds:

   1. k ← Gen(1n ) is a p.p.t. such that for every n ∈ N, it samples
      a key k.
   2. c ← Enck (m) is a p.p.t. that given k and m ∈ {0, 1}n pro-
      duces a ciphertext c.
   3. m ← Deck (c) is a p.p.t. that given a ciphertext c and key k
      produces a message m ∈ {0, 1}n ∪ ⊥.
   4. For all n ∈ N, m ∈ {0, 1}n ,

               Pr [k ← Gen(1n ) : Deck (Enck (m)) = m]] = 1

 Notice that the Gen algorithm is given the special input 1n —called
 the security parameter—which represents the string consisting
 of n copies of 1, e.g. 14 = 1111. This security parameter is used
 to instantiate the “security” of the scheme; larger parameters
 correspond to more secure schemes. The security parameter also
 establishes the running time of Gen, and therefore the maximum
 size of k, and thus the running times of Enc and Dec as well.
 Stating that these three algorithms are “polynomial-time” is
 always with respect to the size of their respective inputs.
     In the rest of this book, when discussing encryption schemes
 we always refer to efficient encryption schemes. As a departure
 from our notation in the first chapter, here we no longer refer to
 a message space M or a key space K because we assume that
 both are bit strings. In particular, on security parameter 1n , our
 definition requires a scheme to handle n-bit messages. It is also
 possible, and perhaps simpler, to define an encryption scheme
 that only works on a single-bit message space M = {0, 1} for
 every security parameter.

 2.1.3   Efficient Adversaries
 When modeling adversaries, we use a more relaxed notion of
 efficient computation. In particular, instead of requiring the
 adversary to be a machine with constant-sized description, we
 26                              chapter 2. computational hardness


 allow the size of the adversary’s program to increase (polyno-
 mially) with the input length, i.e., we allow the adversary to
 be non-uniform. As before, we still allow the adversary to use
 random coins and require that the adversary’s running time is
 bounded by a polynomial. The primary motivation for using
 non-uniformity to model the adversary is to simplify definitions
 and proofs.

.Definition 26.8 (Non-Uniform PPT) A non-uniform probabilistic
 polynomial-time machine (abbreviated n.u. p.p.t.) A is a sequence
 of probabilistic machines A = { A1 , A2 , . . .} for which there exists a
 polynomial d such that the description size of | Ai | < d(i ) and the
 running time of Ai is also less than d(i ). We write A( x ) to denote the
 distribution obtained by running A| x| ( x ).

     Alternatively, a non-uniform p.p.t. machine can also be de-
 fined as a uniform p.p.t. machine A that receives an advice string
 for each input length. In the rest of this text, any adversarial
 algorithm A will implicitly be a non-uniform PPT.


 2.2 One-Way Functions
 At a high level, there are two basic desiderata for any encryption
 scheme:

   — it must be feasible to generate c given m and k, but

   — it must be hard to recover m and k given only c.

     This suggests that we require functions that are easy to com-
 pute but hard to invert—one-way functions. Indeed, these func-
 tions turn out to be the most basic building block in cryptography.
 There are several ways that the notion of one-wayness can be
 defined formally. We start with a definition that formalizes our
 intuition in the simplest way.

.Definition 26.1 (Worst-case One-way Function). A function f :
 {0, 1}∗ → {0, 1}∗ is worst-case one-way if:
 2.2. One-Way Functions                                               27


   1. Easy to compute. There is a p.p.t. C that computes f ( x ) on
      all inputs x ∈ {0, 1}∗ , and
   2. Hard to Invert there is no adversary A such that

                     ∀ x Pr[A( f ( x )) ∈ f −1 ( f ( x ))] = 1

     It can be shown that assuming NP ∈ / BPP, one-way functions
 according to the above definition must exist.1 In fact, these two
 assumptions are equivalent (show this!). Note, however, that
 this definition allows for certain pathological functions to be
 considered as one-way—e.g., those where inverting the function
 for most x values is easy, but every machine fails to invert f ( x )
 for infinitely many x’s. It is an open question whether such
 functions can still be used for good encryption schemes. This
 observation motivates us to refine our requirements. We want
 functions where for a randomly chosen x, the probability that
 we are able to invert the function is very small. With this new
 definition in mind, we begin by formalizing the notion of very
 small.

.Definition 27.2 (Negligible function) A function ε(n) is negligi-
 ble if for every c, there exists some n0 such that for all n > n0 ,
 e(n) ≤ n1c .

 Intuitively, a negligible function is asymptotically smaller than
 the inverse of any fixed polynomial. Examples of negligible
 functions include 2−n and n− log log n . We say that a function
 t(n) is non-negligible if there exists some constant c such that
 for infinitely many points {n0 , n1 , . . .}, t(ni ) > nic . This notion
 becomes important in proofs that work by contradiction.
     We can now present a more satisfactory definition of a one-
 way function.

.Definition 27.3 (Strong One-Way Function) A function mapping
 strings to strings f : {0, 1}∗ → {0, 1}∗ is a strong one-way function
 if it satisfies the following two conditions:

    1. Easy to compute. (Same as per worst-case one-way functions)
    1 See Appendix B for definitions of NP and BPP.
 28                               chapter 2. computational hardness


      2. Hard to invert. Any efficient attempt to invert f on random
         input succeeds with only negligible probability. Formally, for any
         adversary A, there exists a negligible function e such that for
         any input length n ∈ N,

            Pr [ x ← {0, 1}n ; y ← f ( x ) : f (A(1n , y)) = y] ≤ e(n).

     Notice the algorithm A receives the additional input of 1n ;
 this is to allow A to run for time polynomial in | x |, even if the
 function f should be substantially length-shrinking. In essence,
 we are ruling out pathological cases where functions might be
 considered one-way because writing down the output of the
 inversion algorithm violates its time bound.
     As before, we must keep in mind that the above definition is
 asymptotic. To define one-way functions with concrete security,
 we would instead use explicit parameters that can be instantiated
 as desired. In such a treatment, we say that a function is (t, s, e)-
 one-way if no A of size s with running time ≤ t will succeed with
 probability better than e in inverting f on a randomly chosen
 input.
     Unfortunately, many natural candidates for one-way func-
 tions will not meet the strong notion of a one-way function. In
 order to capture the property of one-wayness that these examples
 satisfy, we introduce the notion of a weak one-way function which
 relaxes the condition on inverting the function. This relaxed
 version only requires that all efficient attempts at inverting will
 fail with some non-negligible probability.

.Definition 28.4 (Weak One-Way Function) A function mapping
 strings to strings f : {0, 1}∗ → {0, 1}∗ is a weak one-way func-
 tion if it satisfies the following two conditions.

      1. Easy to compute. (Same as that for a strong one-way function.)

      2. Hard to invert. There exists a polynomial function q : N → N
         such that for any adversary A, for sufficiently large n ∈ N,

                                                                      1
          Pr[ x ← {0, 1}n ; y ← f ( x ) : f (A(1n , y)) = y] ≤ 1 −
                                                                     q(n)
2.3. Multiplication, Primes, and Factoring                                 29


    Our eventual goal is to show that weak one-way functions can
be used to construct strong one-way functions. Before showing
this, let us consider some examples.


2.3 Multiplication, Primes, and Factoring
In this section, we consider examples of one-way functions. A
first candidate is the function f mult : N2 → N defined by
                                  
                                          1 if x = 1 ∨ y = 1
               f mult ( x, y) =
                                      x · y otherwise

Is this a one-way function? Clearly, by the multiplication algo-
rithm, f mult is easy to compute. But f mult is not always hard to
invert. If at least one of x and y is even, then their product will
be even as well. This happens with probability 34 if the input
( x, y) is picked uniformly at random from N2 . So the following
attack A will succeed with probability 34 :

                                      (2, 2z ) if z even
                                  
                     A(z) =
                                      (0, 0) otherwise.

Something is not quite right here, since f mult is conjectured to be
hard to invert on some, but not all, inputs2 . The strong definition
of a one-way function is too restrictive to capture this notion, so
we now determine whether the function satisfies the weak notion
of one-wayness. In order to do so, we must first introduce an
assumption and some basic facts from number theory.

2.3.1    The Factoring Assumption
Denote the (finite) set of primes that are smaller than 2n as

                  Πn = {q | q < 2n and q is prime}

Consider the following assumption, which we shall assume for
the remainder of this course:
    2 Notice that by the way we have defined  f mult , (1, xy) will never be a
pre-image of xy. That is why some instances might be hard to invert.
 30                          chapter 2. computational hardness


.Assumption 30.1 (Factoring) For every adversary A, there exists a
 negligible function e such that

      Pr[ p ← Πn ; q ← Πn ; N ← pq : A( N ) ∈ { p, q}] < e(n)

     The factoring assumption is a very important, well-studied
 conjecture. The best provable algorithm for factorization runs
                     1/2
 in time 2O((n log n) ) , and the best heuristic algorithm runs in
            1/3 2/3
 time 2O(n log n) . Factoring composites that are a product of
 two primes is hard in a concrete way as well: In May 2005, the
 research team of F. Bahr, M. Boehm, J. Franke, and T. Klein-
 jung were able to factor a 663-bit challenge number (of the form
 described above). In particular, they started in 2003 and com-
 pleted in May 2005 and estimate to have used the equivalent of
 55 years of computing time of a single 2.2 GHz Opteron CPU.
 See [bbfk05] for details. In January 2010, Kleinjung and 12 col-
 leagues [kaf+ 10] announced the factorization of the RSA-768
 challenge modulus. They describe the amount of work required
 for this task as follows:

      We spent half a year on 80 processors on polynomial
      selection. This was about 3% of the main task, the
      sieving, which was done on many hundreds of ma-
      chines and took almost two years. On a single core
      2.2 GHz AMD Opteron processor with 2 GB RAM per
      core, sieving would have taken about fifteen hundred
      years.

 They go on to mention that factoring a 1024-bit modulus “would
 be about a thousand times harder.”

 2.3.2 There are many primes
 The problem of characterizing the set of prime numbers has been
 considered since antiquity. Euclid, in Book IX, Proposition 20,
 noted that there are an infinite number of primes. However,
 merely having an infinite number of them is not reassuring, since
 perhaps they are distributed in such a haphazard way as to make
 finding them extremely difficult. An empirical way to approach
 2.3. Multiplication, Primes, and Factoring                          31


 the problem is to define the function

                     π ( x ) = number of primes ≤ x

 and graph it for reasonable values of x as we have done in Fig. 2
 below.


  1,000

               2n/ log(n)                                   π(n)
   500

                                                n/ log(n)
     0
          0   1000    2000               4000                      8000
                                          n



     Figure 31.2: Graph of π (n) for the first thousand primes

      By inspecting this curve, at age 15, Gauss conjectured that
 π ( x ) ≈ x/ log x. Since then, many people have answered the
 question with increasing precision; notable are Chebyshev’s theo-
 rem (upon which our argument below is based), and the famous
 Prime Number Theorem which establishes that π ( N ) approaches
  N
 ln N as N grows to infinity. Here, we will prove a much simpler
 theorem which only lower-bounds π ( x ):
                                                  x
.Theorem 31.3 (Chebyshev) For x > 1, π ( x ) > 2 log x

 Proof. Consider the integer

                 (2x )!     x+x    x + ( x − 1)         x+1
                                                     
         2x
   X=         =         =                         ···
          x      ( x!)2      x       ( x − 1)            1

 Observe that X > 2x (since each term is greater than 2) and
 that the largest prime dividing X is at most 2x (since the largest
 numerator in the product is 2x). By these facts and unique
 factorization, we can write

                             X = ∏ p νp ( X ) > 2 x
                                  p<2x



                                            1
 32                                     chapter 2. computational hardness


 where the product is over primes p less than 2x and νp ( X ) de-
 notes the integral power of p in the factorization of X. Taking
 logs on both sides, we have

                             ∑ νp (X ) log p > x
                             p<2x

 We now employ the following claim proven below.

.Claim 32.4 log 2x
             log p > νp ( X )

 Substituting this claim, we have
                                                           !
                        log 2x
             ∑           log p
                                     log p = log 2x   ∑1         >x
             p<2x                                     p<2x

 Notice that the second sum is precisely π (2x ); thus

                                          x     1   2x
                        π (2x ) >              = ·
                                        log 2x  2 log 2x

 which establishes the theorem for even values. For odd values,
 notice that
                                              2x         (2x − 1)
          π (2x ) = π (2x − 1) >                    >
                                           2 log 2x   2 log(2x − 1)

 since x/ log x is an increasing function for x ≥ 3.
 Proof. [Proof Of Claim 32.4] Notice that
                                                  
                 νp ( X ) = ∑ b2x/pi c − 2b x/pi c
                                 i >1
                            < log 2x/ log p

 The first equality follows because the product (2x )! = (2x )(2x −
 1) . . . (1) includes a multiple of pi at most b2x/pi c times in the
 numerator of X; similarly the product x! · x! in the denominator
 of X removes it exactly 2b x/pi c times. The second line follows
 because each term in the summation is at most 1 and after pi >
 2x, all of the terms will be zero.                                
                                                                   
 2.3. Multiplication, Primes, and Factoring                          33


     An important corollary of Chebyshev’s theorem is that at
 least a 1/2n-fraction of n-bit numbers are prime. As we shall see
 in §2.6.5, primality testing can be done in polynomial time—i.e.,
 we can efficiently check whether a number is prime or com-
 posite. With these facts, we can show that, under the factoring
 assumption, f mult is a weak one-way function.

.Theorem 33.5 If the factoring assumption is true, then f mult is a weak
 one-way function.

 Proof. As already mentioned, f mult ( x, y) is clearly computable in
 polynomial time; we just need to show that it is hard to invert.
     Consider a certain input length 2n (i.e, | x | = |y| = n). Intu-
 itively, by Chebyshev’s theorem, with probability 1/4n2 a random
 input pair x, y will consists of two primes; in this case, by the fac-
 toring assumption, the function should be hard to invert (except
 with negligible probability).
     We proceed to a formal proof. Let q(n) = 8n2 ; we show that
 non-uniform p.p.t. cannot invert f mult with probability greater
 than 1 − q(1n) for sufficiently large input lengths. Assume, for
 contradiction, that there exists a non-uniform p.p.t. A that inverts
 f mult with probability at least 1 − q(1n) for infinitely many n ∈ N.
 That is, the probability that A, when given input z = xy for
 randomly chosen n-bit strings, x and y, produces either x or y is:

                                                          1
  Pr x, y ← {0, 1}n , z = xy : A(12n , z) ∈ { x, y} ≥ 1 − 2 (33.2)
                                                  
                                                         8n
 We construct a non-uniform p.p.t machine A0 which uses A to
 break the factoring assumption. The description of A0 follows:
 algorithm 33.6: A0 (z): Breaking the factoring assumption
  1: Sample x, y ← {0, 1}n
  2: if x and y are both prime then
  3:   z0 ← z
  4: else
  5:   z0 ← xy
  6: end if
  7: w ← A (1n , z0 )
  8: Return w if x and y are both prime.
34                           chapter 2. computational hardness



     Note that since primality testing can be done in polynomial
time, and since A is a non-uniform p.p.t., A0 is also a non-uniform
p.p.t. Suppose we now feed A0 the product of a pair of random
n-bit primes, z. In order to give A a uniformly distributed input
(i.e. the product of a pair of random n-bit numbers), A0 samples a
pair ( x, y) uniformly, and replaces the product xy with the input
z if both x and y are prime. By Chebychev’s Theorem (31.3),
A0 fails to pass z to A with probability at most 1 − 4n1 2 . From
Eq. (33.2), A fails to factor its input with probability at most
1/8n2 . Using the union bound, we conclude that A0 fails with

probability at most
                              
                            1       1          1
                      1− 2 + 2 ≤ 1− 2
                          4n       8n        8n

for large n. In other words, A0 factors z with probability at least
  1
8n2
     for infinitely many n. In other words, there does not exist
a negligible function that bounds the success probability of A0 ,
which contradicts the factoring assumption.                      
    Note that in the above proof we relied on the fact that primal-
ity testing can be done in polynomial time. This was done only
for ease of exposition, as it is unnecessary. Consider a machine
A00 that proceeds just as A0 , but always lets z = z0 and always
outputs w. Such a machine succeeds in factoring with at least
the same if not greater probability. But A00 never needs to check
if x and y are prime.


2.4 Hardness Amplification
We have shown that a natural function such as multiplication
satisfies the notion of a weak one-way function if certain assump-
tions hold. In this section, we show an efficient way to transform
any weak one-way function to a strong one. In this sense, the
existence of weak one-way functions is equivalent to the existence
of (strong) one-way functions. The main insight is that running a
weak one-way function f on enough random inputs xi produces
a list of elements yi which contains at least one member that is
hard to invert.
 2.4. Hardness Amplification                                                                35


.Theorem 35.1 For any weak one-way function f : {0, 1}∗ → {0, 1}∗ ,
 there exists a polynomial m(·) such that function

         f 0 ( x1 , x2 , . . . , xm(n) ) = ( f ( x1 ), f ( x2 ), . . . , f ( xm(n) )).

 from f 0 : ({0, 1}n )m(n) → ({0, 1}∗ )m(n) is strongly one-way.

     We prove this theorem by contradiction. We assume that f 0 is
 not strongly one-way and so there is an algorithm A0 that inverts
 it with non-negligible probability. From this, we construct an
 algorithm A that inverts f with high probability. The pattern for
 such an argument is common in cryptographic proofs; we call
 it a security reduction because it essentially reduces the problem
 of “breaking” f (for example, the weak one-way function in the
 theorem above) into the problem of breaking f 0 . Therefore, if
 there is some way to attack f 0 , then that same method can be
 used (via the reduction) to break the original primitive f that we
 assume to be secure.
     The complete proof of Thm. 35.1 appears in §2.4.3 below.
 To introduce that proof, we first present two smaller examples.
 First, to gain familiarity with security reductions, we show a
 simple example of how to argue that if f is a strong one-way
 function, then g( x, y) = ( f ( x ), f (y)) is also a strong one-way
 function. Next, we prove the hardness amplification theorem
 for the function f mult because it is significantly simpler than the
 proof for the general case, and yet offers insight to the proof of
 Theorem 35.1.

 2.4.1   A Simple Security Reduction
.Theorem 35.2 If f is a strong one-way function, then g( x, y) =
 ( f ( x ), f (y)) is a strong one-way function.

 Proof. Suppose for the sake of reaching contradiction that g is
 not a strong one-way function. Thus, there exists a non-uniform
 p.p.t. A0 and a polynomial p such that for infinitely many n,
   h                                                          i                            1
 Pr ( x, y) ← {0, 1}2n ; z ← g( x, y) : A0 (12n , z) ∈ g−1 (z) ≥
                                                                                         p(2n)
 36                                        chapter 2. computational hardness


 We now construct another non-uniform p.p.t. A that uses A0 in
 order to invert f on input u. In order to do this, A will choose a
 random y, compute v ← f (y) and then submit the pair (u, v) to
 A0 . Notice that this pair (u, v) is identically distributed as the pair
                                                                      1
 ( x, y) in the equation above. Therefore, with probability p(2n        )
                                                                          ,
                   0
 the algorithm A returns an inverse ( a, b). Now the algorithm A
 can test whether f ( a) = u, and if so, output a. Formally,
          h                                                                i
                          n                           n            −1
      Pr x ← {0, 1} ; u ← f ( x ) : A(1 , u) ∈ f (u)
             x, y ← {0, 1}2n ;
                                                                      
      = Pr                            : A0 (12n , (u, v)) ∈ g−1 (u, v)
             u ← f ( x ); v ← f ( y )
           h                                                            i
      = Pr ( x, y) ← {0, 1}2n ; z ← g( x, y) : A0 (12n , z) ∈ g−1 (z)
            1
      ≥
          p(2n)

                                                                                               

 2.4.2 Analyzing the function f mult
.Theorem 36.3 Assume the factoring assumption and let mn = 4n3 .
 Then f 0 : ({0, 1}2n )mn → ({0, 1}2n )mn is strongly one-way:

  f 0 (( x1 , y1 ), . . . , ( xmn , ymn )) = ( f mult ( x1 , y1 ), . . . , f mult ( xmn , ymn ))

 Proof. Recall that by Chebyschev’s Theorem, a pair of random
 n-bit numbers are both prime with probability at least 1/4n2 . So,
 if we choose mn = 4n3 pairs, the probability that none of them is
 a prime pair is at most
                                 4n3                     4n2 n
                          1                         1
                       1− 2              =       1− 2                ≤ e−n               (36.2)
                         4n                        4n

 Thus, intuitively, by the factoring assumption f 0 is strongly one-
 way. More formally, suppose that f 0 is not a strong one-way
 function. Let n0 = 2n · m(n) = 8n4 , and let the notation (~x, ~y)
 represent ( x1 , y2 ), . . . , ( xm(n) , ym(n) ). Thus, there exists a non-
 uniform p.p.t. machine A and a polynomial p such that for
2.4. Hardness Amplification                                             37


infinitely many n0 ,
        h                  0      0                    1           i
      Pr (~x, ~y) ← {0, 1}n : A(1n , f 0 (~x, ~y)) ∈ f 0−1 (~x, ~y) ≥
                                                     p(n0 )
                                                        (36.3)
                                   0
We construct a non-uniform p.p.t. A which uses A to break the
factoring assumption.
algorithm 37.4: A0 (z0 ): Breaking the factoring assumption
                                 0
           x, ~y ← {0, 1}n
 1: Sample ~
 2: Compute ~z ← f 0 (~
                      x, ~y)
 3: if some pair ( xi , yi ) are both prime then
 4:   replace zi with z0 (only once even if there are many such
      pairs)
      Compute ( x10 , y10 ), . . . , ( xm
                                        0        0            n0
 5:                                       (n) , ym(n) ) ← A (1 , ~z )
 6:   Output xi0
 7: end if
 8: Else, fail.

Note that since primality testing can be done in polynomial time,
and since A is a non-uniform p.p.t., A0 is also a non-uniform p.p.t.
Also note that A0 (z0 ) feeds A the uniform input distribution by
uniformly sampling (~x, ~y) and replacing some product xi yi with
z0 only if both xi and yi are prime. From (36.3), A0 fails to factor
its inputs with probability at most 1 − 1/p(n0 ); from (36.2), A0
fails to substitute in z0 with probability at most e−n By the union
bound, we conclude that A0 fails to factor z0 with probability at
most
                          1                   1
                    1−      0
                              + e−n ≤ 1 −
                        p(n )               2p(n0 )
for large n. In other words, A0 factors z0 with probability at least
1/2p(n0 ) for infinitely many n0 . This contradicts the factoring
assumption.                                                       
    We note that just as in the proof of Theorem 33.5 the above
proof can be modified to not make use of the fact that primality
testing can be done in polynomial time. We leave this as an
exercise to the reader.

2.4.3      ? Proof of Theorem 35.1
38                                chapter 2. computational hardness


Proof. Since f is weakly one-way, let q : N → N be a polynomial
such that for any non-uniform p.p.t. algorithm A and any input
length n ∈ N,
                                                                     1
     Pr [ x ← {0, 1}n ; y ← f ( x ) : f (A(1n , y)) = y] ≤ 1 −           .
                                                                    q(n)
                                    m
We want to set m such that 1 − q(1n)     tends to 0 for large n.
Since                      nq(n)  n
                        1              1
                   1−             ≈
                       q(n)            e
we pick m = 2nq(n). Let ~x represent ~x = ( x1 , . . . , xm ) where each
xi ∈ {0, 1}n .
Suppose that f 0 as defined in the theorem statement is not a
strongly one-way function. Thus, there exists a non-uniform
p.p.t. algorithm A0 and p0 : N → N be a polynomial such that
for infinitely many input lengths n ∈ N, A0 inverts f 0 with
probability p0 (nm):
                                                                   1
      Pr ~x ← {0, 1}nm ; ~y = f 0 (~x ) : f 0 (A0 (~y)) = ~y >
                                                           
                                                                 p0 (nm)
Since m is polynomial in n, then the function p(n) = p0 (nm) =
p0 (2n2 q(n)) is also a polynomial. Rewriting the above probability,
we have
                                                              1
    Pr ~x ← {0, 1}nm ; ~y = f 0 (~x ) : f 0 (A0 (~y)) = ~y >
                                                         
                                                                  (38.1)
                                                             p(n)
    A first idea for using A to invert f on the input y would be to
feed A the input (y, y, . . . , y). But, it is possible that A always fails
on inputs of such format (these strings form a very small fraction
of all strings of length mn); so this plan will not work. A slightly
better approach would be to feed A the string (y, y2 , . . . , ym )
where y j6=1 = f ( x j ) and x j ← {0, 1}n . Again, this may not work
since A could potentially invert only a small fraction of y1 ’s (but,
say, all y2 , . . . ym ’s). As we show below, letting yi = y, where
i ← [m] is a random “position” will, however, work. More
precisely, define the algorithm A0 which will attempt to use A0
to invert f as per the figure below.
algorithm 38.5: A0 ( f , y) where y ∈ {0, 1}n
2.4. Hardness Amplification                                               39


 1: Pick a random i ← [1, m ].
 2: For all j 6 = i, pick a random x j ← {0, 1}n , and let y j = f ( x j ).
 3: Let yi ← y.
 4: Let (z1 , z2 , . . . , zm ) ← A0 (y1 , y2 , . . . , ym ).
 5: If f (zi ) = y, then output zi ; otherwise, fail and output ⊥.

       To improve our chances of inverting f , we will run A0 several
times using independently chosen random coins. Define the
algorithm A : {0, 1}n → {0, 1}n ∪ ⊥ to run A0 with its input
2nm2 p(n) times and output the first non-⊥ result it receives. If
all runs of A0 result in ⊥, then A also outputs ⊥.
       In order to analyze the success of A, let us define a set of
“good” elements Gn such that x ∈ Gn if A0 can successfully invert
 f ( x ) with non-negligible probability:
                                                            
                          n                              1
         Gn = x ∈ {0, 1} Pr [A0 ( f ( x )) 6= ⊥] ≥
                                                    2m2 p(n)
Otherwise, call x “bad.” Note that the probability that A fails to
invert f ( x ) on a good x is small:
                                                 2m2 np(n)
                                            1
  Pr [A( f ( x )) fails | x ∈ Gn ] ≤ 1 −                     ≈ e−n .
                                         2m2 p(n)
We claim that there are many good elements; there are enough
for A to invert f with sufficient probability to contradict the
weakly one-way
              assumption
                            on f . In particular, we claim there
are at least 2n 1 − 2q1(n)          good elements in {0, 1}n . If this holds,
then
            Pr [A( f ( x )) fails]
                = Pr [A( f ( x )) fails | x ∈ Gn ] · Pr [ x ∈ Gn ]
                  + Pr [A( f ( x )) fails | x 6∈ Gn ] · Pr [ x 6∈ Gn ]
                ≤ Pr [A( f ( x )) fails | x ∈ Gn ] + Pr [ x 6∈ Gn ]
                                    2m2 np(n)
                              1                       1
                ≤ 1−                            +
                         2m2 p(n)                  2q(n)
                             1
                ≈ e−n +
                         2q(n)
                    1
                <      .
                  q(n)
40                                 chapter 2. computational hardness


This contradicts the assumption that f is q(n)-weak.
                                                                  
      It remains to be shown that there are at least 2n 1 − 2q1(n)
good elements in {0, 1}n . Suppose
                                for the sake of reaching a
                                       1
contradiction, that | Gn | < 2n      2q(n)
                                             . We will contradict Eq.(38.1)
which states that A0 succeeds in inverting f 0 ( x ) on a random
input x with probability p(1n) . To do so, we establish an upper
bound on the probability by splitting it into two quantities:

 Pr xi ← {0, 1}n ; yi = f 0 ( xi ) : A0 (~y) succeeds
                                                     

   = Pr xi ← {0, 1}n ; yi = f 0 ( xi ) : A0 (~y) 6= ⊥ ∧ some xi 6∈ Gn
                                                                     

     + Pr xi ← {0, 1}n ; yi = f 0 ( xi ) : A0 (~y) 6= ⊥ ∧ all xi ∈ Gn
                                                                     



For each j ∈ [1, n], we have

     Pr xi ← {0, 1}n ; yi = f 0 ( xi ) : A0 (~y) 6= ⊥ ∧ x j 6∈ Gn
                                                                 

       ≤ Pr xi ← {0, 1}n ; yi = f 0 ( xi ) : A0 (~y) succeeds | x j 6∈ Gn
                                                                         
                                                      
       ≤ m · Pr A0 ( f ( x j )) succeeds | x j is bad
             m               1
       ≤     2
                   =
          2m p(n)      2mp(n)

So taking a union bound, we have

Pr xi ← {0, 1}n ; yi = f 0 ( xi ) : A0 (~y) succeeds ∧ some xi 6∈ Gn
                                                                    

  ≤ ∑ Pr xi ← {0, 1}n ; yi = f 0 ( xi ) : A0 (~y) succeeds ∧ x j 6∈ Gn
                                                                      
          j
            m        1
      ≤          =       .
          2mp(n)   2p(n)

Also,

 Pr xi ← {0, 1}n ; yi = f 0 ( xi ) : A0 (~y) succeeds and all xi ∈ Gn
                                                                     

       ≤ Pr [ xi ← {0, 1}n : all xi ∈ Gn ]
                      m                 2nq(n)
                   1                  1
       < 1−               = 1−                     ≈ e−n
                 2q(n)              2q(n)
 2.5. Collections of One-Way Functions                                 41


 Hence
                                                          1
  Pr xi ← {0, 1}n ; yi = f 0 ( xi ) : A0 (~y) succeeds <      + e−n
                                                     
                                                        2p(n)
                                                         1
                                                      <
                                                        p(n)
 which contradicts (38.1).                                             

 2.5 Collections of One-Way Functions
 In the last two sections, we have come to suitable definitions
 for strong and weak one-way functions. These two definitions
 are concise and elegant, and can nonetheless be used to con-
 struct generic schemes and protocols. However, the definitions
 are more suited for research in complexity-theoretic aspects of
 cryptography.
     Practical considerations motivate us to introduce a more flexi-
 ble definition that combines the practicality of a weak OWF with
 the security of a strong OWF. In particular, instead of requiring
 the function to be one-way on a randomly chosen string, we de-
 fine a domain and a domain sampler for hard-to-invert instances.
 Because the inspiration behind this definition comes from “can-
 didate one-way functions,” we also introduce the concept of a
 collection of functions; one function per input size.

.Definition 41.1 (Collection of OWFs). A collection of one-way func-
 tions is a family F = { f i : Di → Ri }i∈ I satisfying the following
 conditions:
   1. It is easy to sample a function, i.e. there exists a p.p.t. Gen
      such that Gen(1n ) outputs some i ∈ I.
   2. It is easy to sample a given domain, i.e. there exists a p.p.t.
      that on input i returns a uniformly random element of Di
   3. It is easy to evaluate, i.e. there exists a p.p.t. that on input
      i, x ∈ Di computes f i ( x ).
   4. It is hard to invert, i.e. for any p.p.t. A there exists a negligi-
      ble function e such that
       Pr [i ← Gen; x ← Di ; y ← f i ( x ) : f (A(1n , i, y)) = y] ≤ e(n)
 42                            chapter 2. computational hardness


     Despite our various relaxations, the existence of a collection
 of one-way functions is equivalent to the existence of a strong
 one-way function.

.Theorem 42.2 There exists a collection of one-way functions if and
 only if there exists a single strong one-way function.

 Proof idea: If we have a single one-way function f , then we can
 choose our index set ot be the singleton set I = {0}, choose
 D0 = N, and f 0 = f .
        The difficult direction is to construct a single one-way func-
 tion given a collection F . The trick is to define g(r1 , r2 ) to be
 i, f i ( x ) where i is generated using r1 as the random bits and x is
 sampled from Di using r2 as the random bits. The fact that g is a
 strong one-way function is left as an excercise.                    


 2.6 Basic Computational Number Theory
 Before we can study candidate collections of one-way functions,
 it serves us to review some basic algorithms and concepts in
 number theory and group theory.

 2.6.1 Modular Arithmetic
 We state the following basic facts about modular arithmetic:

.Fact 42.1 For N > 0 and a, b ∈ Z,

      1. ( a mod N ) + (b mod N ) mod N ≡ ( a + b) mod N

      2. ( a mod N )(b mod N ) mod N ≡ ab mod N

 We often use = instead of ≡ to denote modular congruency.

 2.6.2 Euclid’s algorithm
 Euclid’s algorithm appears in text around 300B.C. Given two
 numbers a and b such that a ≥ b, Euclid’s algorithm computes the
 greatest common divisor of a and b, denoted gcd( a, b). It is not at
 all obvious how this value can be efficiently computed, without
 say, the factorization of both numbers. Euclid’s insight was to
 2.6. Basic Computational Number Theory                              43


 notice that any divisor of a and b is also a divisor of b and a − b.
 The subtraction is easy to compute and the resulting pair (b, a − b)
 is a smaller instance of original gcd problem. The algorithm has
 since been updated to use a mod b in place of a − b to improve
 efficiency. The version of the algorithm that we present here also
 computes values x, y such that ax + by = gcd( a, b).
 algorithm 43.2: ExtendedEuclid( a, b) such that a > b > 0
  1: if a mod b = 0 then
  2:      Return (0, 1)
  3: else
  4:   ( x, y) ← ExtendedEuclid(b, a mod b)
  5:   Return (y, x − y(b a/bc))
  6: end if

     Note: by polynomial time we always mean polynomial in the
 size of the input, that is poly(log a + log b)
 Proof. On input a > b ≥ 0, we aim to prove that Algorithm 43.2
 returns ( x, y) such that ax + by = gcd( a, b) = d via induction.
 First, let us argue that the procedure terminates in polynomial
 time. (See [knu81] for a better analysis relating to the Fibonacci
 numbers; for us the following suffices since each recursive call
 involves only a constant number of divisions and subtraction
 operations.)

.Claim 43.3 If a > b ≥ 0 and a < 2n , then ExtendedEuclid( a, b)
 makes at most 2n recursive calls.

 Proof. By inspection, if n ≤ 2, the procedure returns after at most
 2 recursive calls. Assume the hypothesis holds for a < 2n . Now
 consider an instance with a < 2n+1 . We identify two cases.

       1. If b < 2n , then the next recursive call on (b, a mod b) meets
          the inductive hypothesis and makes at most 2n recursive
          calls. Thus, the total number of recursive calls is less than
          2n + 1 < 2(n + 1).

       2. If b > 2n , than the first argument of the next recursive
          call on (b, a mod b) is upper-bounded by 2n+1 since a > b.
          Thus, the problem is no “smaller” on face. However, we
 44                              chapter 2. computational hardness


       can show that the second argument will be small enough
       to satisfy the prior case:
                          a mod b = a − b a/bc · b
                                    < 2n +1 − b
                                    < 2n +1 − 2n = 2n
       Thus, after 2 recursive calls, the arguments satisfy the in-
       ductive hypothesis resulting in 2 + 2n = 2(n + 1) recursive
       calls.
                                                                   
     Now for correctness, suppose that b divided a evenly (i.e.,
 a mod b = 0). Then we have gcd( a, b) = b, and the algorithm
 returns (0, 1) which is correct by inspection. By the inductive
 hypothesis, assume that the recursive call returns ( x, y) such that
                 bx + ( a mod b)y = gcd(b, a mod b)
 First, we claim that
.Claim 44.4 gcd( a, b) = gcd(b, a mod b)
 Proof. Divide a by b and write the result as a = qb + r. Rearrange
 to get r = a − qb.
       Observe that if d is a divisor of a and b (i.e. a = a0 d and
 b = b0 d for a0 , b0 ∈ Z) then d is also a divisor of r since r =
 ( a0 d) − q(b0 d) = d( a0 − qb0 ). Similarly, if d is a divisor of b and r,
 then d also divides a. Since this holds for all divisors of a and b
 and all divisors of b and r, it follows that gcd( a, b) = gcd(b, r ).
                                                                         
 Thus, we can write
                          bx + ( a mod b)y = d
 and by adding 0 to the right, and regrouping, we get
           d = bx − b(b a/bc)y + ( a mod b)y + b(b a/bc)y
             = b( x − (b a/bc)y) + ay
 which shows that the return value (y, x − (b a/bc)y) is correct. 
     The assumption that the inputs are such that a > b is without
 loss of generality since otherwise the first recursive call swaps
 the order of the inputs.
 2.6. Basic Computational Number Theory                                  45


 2.6.3   Exponentiation modulo N
 Given a, x, N, we now demonstrate how to efficiently compute
 a x mod N. Recall that by efficient, we require the computation
 to take polynomial time in the size of the representation of
 a, x, N. Since inputs are given in binary notation, this requires
 our procedure to run in time poly(log( a), log( x ), log( N )).
     The key idea is to rewrite x in binary as

                x = 2` x` + 2`−1 x`−1 + · · · + 2x1 + x0

 where xi ∈ {0, 1} so that
                             `      `−1 x             1
             a x mod N = a2 x` +2           `−1 +···+2 x1 + x0   mod N

 This expression can be further simplified as
                                       `
                    a x mod N = ∏ xi a2 mod N
                                                    i


                                     i =0

 using the basic properties of modular arithmetic from Fact 42.1.
 algorithm 45.5: ModularExponentiation( a, x, N )
  1: r ← 1
  2: while x > 0 do
  3:   if x is odd then
  4:      r ← r · a mod N
  5:   end if
  6:   x ← b x/2c
  7:   a ← a2 mod N
  8: end while
  9: return r


.Theorem 45.6 On input ( a, x, N ) where a ∈ [1, N ], Algorithm 45.5
 computes a x mod N in time O(log( x ) log2 ( N )).
                                                i
 Proof. Rewrite a x mod N as ∏i xi a2 mod N. Since multiplying
 and squaring modulo N take time log2 ( N ), each iteration of the
 loop requires O(log2 ( N )) time. Because each iteration divides
 x by two, the loop runs at most log x times which establishes a
 running time of O(log( x ) log2 ( N )).                        
 46                               chapter 2. computational hardness


     Later, after we have introduced Euler’s theorem, we present
 a similar algorithm for modular exponentiation which removes
 the restriction that x < N. In order to discuss this, we must
 introduce the notion of Groups.

 2.6.4 Groups
.Definition 46.7 A group G is a set of elements with a binary operator
 ⊕ : G × G → G that satisfies the following properties:
      1. Closure: For all a, b ∈ G, a ⊕ b ∈ G,
      2. Identity: There is an element i in G such that for all a ∈ G,
         i ⊕ a = a ⊕ i = a. This element i is called the identity element.
      3. Associativity: For all a, b and c in G, ( a ⊕ b) ⊕ c = a ⊕ (b ⊕ c).
      4. Inverse: For all a ∈ G, there is an element b ∈ G such that
         a ⊕ b = b ⊕ a = i where i is the identity.

 Example: The Additive Group Mod N
We have already worked with the additive group modulo N,
which is denoted as (Z N , +) where Z N = {0, 1, . . . , N − 1} and
+ is addition modulo N. It is straightforward to verify the four
properties for this set and operation.

 Example: The Multiplicative Group Mod N
 The multiplicative group modulo N > 0 is denoted (Z∗N , ×),
 where Z∗N = { x ∈ [1, N − 1] | gcd( x, N ) = 1} and × is multipli-
 cation modulo N.
.Theorem 46.8 (Z∗N , ×) is a group
 Proof. Observe that 1 is the identity in this group and that
 ( a ∗ b) ∗ c = a ∗ (b ∗ c) for a, b, c ∈ Z∗N . However, it remains to
 verify that the group is closed and that each element has an
 inverse. In order to do this, we must introduce the notion of a
 prime integer.
.Definition 46.9 A prime is a positive integer p > 1 that is evenly
 divisible by only 1 and p.
 2.6. Basic Computational Number Theory                             47


 Closure Suppose, for the sake of reaching a contradiction, that
 there exist two elements a, b ∈ Z∗N such that ab 6∈ Z∗N . This
 implies that gcd( a, N ) = 1, gcd(b, N ) = 1, but that gcd( ab, N ) =
 d > 1. The latter condition implies that d has a non-trivial prime
 factor that divides both ab and N. Thus, the prime factor must
 also divide either a or b (verify as an exercise), which contradicts
 the assumption that gcd( a, N ) = 1 and gcd(b, N ) = 1.

 Inverse Consider an element a ∈ Z∗N . Since gcd( a, N ) = 1, we
 can use Euclid’s algorithm on ( a, N ) to compute values ( x, y)
 such that ax + Ny = 1. Notice, this directly produces a value x
 such that ax = 1 mod N. Thus, every element a ∈ Z∗N has an
 inverse which can be efficiently computed.                     
     The groups (Z N , +) and (Z∗N , ×) are also abelian or commu-
 tative groups in which a ⊕ b = b ⊕ a.
     The number of unique elements in Z∗N (often referred to
 as the order of the group) is denoted by the the Euler Totient
 function Φ( N ).

     Φ( p) = p − 1            if p is prime
     Φ( N ) = ( p − 1)(q − 1) if N = pq and p, q are primes

 The first case follows because all elements less than p will be
 relatively prime to p. The second case requires some simple
 counting (show this by counting the number of multiples of p
 and q that are less than N).
     The structure of these multiplicative groups offer some special
 properties which we exploit throughout this course. One of the
 first properties is the following identity first proven by Euler in
 1758 and published in 1763 [eul63].

.Theorem 47.10 (Euler) ∀ a ∈ Z∗N , aΦ( N ) = 1 mod N

 Proof. Consider the set A = { ax | x ∈ Z∗N }. Since Z∗N is a
 group, every element ax of A must also be in Z∗N and so it
 follows that A ⊆ Z∗N . Now suppose that | A| < |Z∗N |. By the
 pidgeonhole principle, this implies that there exist two group
 element i, j ∈ Z∗N such that i 6= j but ai = aj. Since a ∈ Z∗N , there
 exists an inverse a−1 such that aa−1 = 1. Multiplying on both
 48                              chapter 2. computational hardness


 sides we have a−1 ai = a−1 aj =⇒ i = j which is a contradiction.
 Thus, | A| = |Z∗N | which implies that A = Z∗N .
    Because the group Z∗N is abelian (i.e., commutative), we can
 take products and substitute the definition of A to get

                      ∏ x = ∏ y = ∏∗ ax
                     x ∈Z∗N       y∈ A      x ∈Z N

 The product further simplifies as

                        ∏∗ x = aΦ( N) ∏∗ x
                       x ∈Z N               x ∈Z N

 Finally, since the closure property guarantees that ∏ x∈Z∗N x ∈ Z∗N
 and since the inverse property guarantees that this element has
 an inverse, we can multiply the inverse on both sides to obtain

                                1 = aΦ( N ) .

                                                                  

.Corollary 48.11 (Fermat’s Little Thm.) ∀ a ∈ Z∗p , a p−1 ≡ 1 mod
 p.

.Corollary 48.12 a x mod N = a x mod Φ( N ) mod N.

 Thus, given Φ( N ), the operation a x mod N can be computed
 efficiently in Z∗N for any x.

                         1241
 Example Compute 26             mod 21 using only paper and pencil.

 2.6.5 Primality Testing
 An important task in generating the parameters of many cryp-
 tographic schemes will be the identification of a suitably large
 prime number. Eratosthenes (276–174BC), a librarian of Alex-
 andria, is credited with devising an elementary sieving method
 to enumerate all primes. However, his method is not practical
 for choosing a large (i.e., 1000 digit) prime.
     Instead, recall that Fermat’s Little Theorem establishes that
 a p−1 = 1 mod p for any a ∈ Z p whenever p is prime. It turns
 2.6. Basic Computational Number Theory                                  49


 out that when p is not prime, then a p−1 is usually not equal to
 1. The first fact and second phenomena form the basic idea
 behind the a primality test: to test p, pick a random a ∈ Z p , and
 check whether a p−1 = 1 mod p. Notice that efficient modular
 exponentiation is critical for this test. Unfortunately, the second
 phenomena is on rare occasion false. Despite there rarity (starting
 with 561, 1105, 1729, . . ., there are only 255 such cases less than
 108 ), there are an infinite number of counter examples collectively
 known as the Carmichael numbers. Thus, for correctness, our
 procedure must handle these rare cases. To do so, we add a
 second check that verifies that none of the intermediate powers of a
 encountered during the modular exponentiation computation of
 an−1 are non-trivial square-roots of 1. This suggest the following
 approach known as the Miller-Rabin primality test presented by
 Miller [mil76] and Rabin [rab80].
 For positive N, write N = u2 j where u is odd. Define the set
            n                                j +1           j
                                                                 o
    L N = α ∈ Z N | α N −1 = 1 and if αu2 = 1 then αu2 = 1


 algorithm 49.13: Miller-Rabin Primality Test
  1: Handle base case N = 2
  2: for t times do
  3:   Pick a random α ∈ Z N
  4:   if α 6∈ L N then
  5:      Output “composite”
  6:   end if
  7: end for
  8: Output “prime”

 Observe that testing whether α ∈ L N can be done by using a
 repeated-squaring algorithm to compute modular exponentiation,
 and adding internal checks to make sure that no non-trivial roots
 of unity are discovered.

.Theorem 49.14 If N is composite, then the Miller-Rabin test outputs
 “composite” with probability 1 − 2−t . If N is prime, then the test outputs
 “prime.”

       The proof of this theorem follows from the following lemma:
 50                           chapter 2. computational hardness


.Lemma 50.15 If N is an odd prime, then | L N | = N − 1. If N > 2 is
 composite, then | L N | < ( N − 1)/2.

     We will not prove this lemma here. See [clrs09] for a full
 proof. The proof idea is as follows. If N is prime, then by
 Fermat’s Little Theorem, the first condition will always hold, and
 since 1 only has two square roots modulo N (namely, 1, −1), the
 second condition holds as well. If N is composite, then either
 there will be some α for which α N −1 is not equal to 1 or the
 process of computing α N −1 reveals a square root of 1 which
 is different from 1 or −1. More formally, the proof works by
 first arguing that all of the α 6∈ L N form a proper subgroup of
 Z∗N . Since the order of a subgroup must divide the order of the
 group, the size of a proper subgroup must therefore be less than
 ( N − 1)/2.
     We mention that a more complicated (and less efficient) de-
 terministic polynomial-time algorithm for primality testing was
 recently presented by Agrawal, Kayal, and Saxena [aks04].

 2.6.6 Selecting a Random Prime
 Our algorithm for finding a random n-bit prime repeatedly sam-
 ples an n-bit number and then checks whether it is prime.
 algorithm 50.16: SamplePrime(n)
  1: repeat
          r
  2:   x ← {0, 1}n
  3: until Miller-Rabin( x ) = “prime”
  4: return x

 Two mathematical facts allow this simple scheme to work. First,
 there are many primes: By Theorem 31.3, the probability that a
 uniformly sampled n-bit integer is prime exceeds (2n /n)/2n = n1 .
 Thus, the expected number of iterations of the loop in Algo-
 rithm 50.16 is polynomial in n.
     Second, it is easy to determine whether a number is prime.
 Since the running time of the Miller-Rabin algorithm is also
 polynomial in n, the expected running time to sample a random
 prime using the simple guess-and-check approach is polynomial
 in n.
 2.7. Factoring-based Collection of OWF                              51


.Lemma 51.17 Algorithm SamplePrime outputs a randomly selected
 n-bit prime number in time poly(n).


 2.7 Factoring-based Collection of OWF
 Under the factoring assumption, we can prove the following
 result, which establishes our first realistic collection of one-way
 functions:
.Theorem 51.1 Let F = { f i : Di → Ri }i∈ I where
               I=N
                                                                i
                 Di = {( p, q) | p, q are prime and | p| = |q| = }
                                                                2
         f i ( p, q) = p · q

 If the Factoring Assumption holds, then F is a collection of one-way
 functions.
 Proof. We can sample a random element of the index set N. It
 is easy to evaluate f i because multiplication is efficiently com-
 putable, and the factoring assumption states that inverting f i
 is hard. Thus, all that remains is to present a method to effi-
 ciently sample two random prime numbers. This follows from
 Lemma 51.17 above. Thus all four conditions in the definition of
 a one-way collection are satisfied.                             

 2.8 Discrete Logarithm-based Collection
 Another often used collection is based on the discrete logarithm
 problem in the group Z∗p for a prime p.

 2.8.1   Discrete logarithm modulo p
 An instance ( p, g, y) of the discrete logarithm problem consists
 of a prime p and two elements g, y ∈ Z∗p . The task is to find an
 x such that g x = y mod p. In some special cases (e.g., g = 1 or
 when p − 1 has many small prime factors), it is easy to either
 declare that no solution exists or solve the problem. However,
 when g is a generator of Z∗p , the problem is believed to be hard.
 52                              chapter 2. computational hardness


.Definition 52.1 (Generator of a Group) A element g of a multi-
 plicative group G is a generator if the set { g, g2 , g3 , . . .} = G. We
 denote the set of all generators of a group G by GenG .

.Assumption 52.2 (Discrete Log) If Gq is a group of prime order q,
 then for every adversary A, there exists a negligible function e such
 that
          h                                             i
       Pr q ← Πn ; g ← GenGq ; x ← Zq : A( g x ) = x < e(n)

 Recall that Πn is the set of n-bit prime numbers. Note that it is
 important that G is a group of prime-order. Thus, for example, the
 normal multiplicative group Z∗p has order ( p − 1) and therefore
 does not satisfy the assumption.
     Instead, one usually picks a prime of the form p = 2q + 1
 (known as a Sophie Germain prime or a “safe prime”) and then
 sets G to be the subgroup of squares in Z∗p . Notice that this
 subgroup has order q which is prime. The practical method for
 sampling safe primes is simple: first pick a prime q as usual,
 and then check whether 2q + 1 is also prime. Unfortunately,
 even though this procedure always terminates in practice, its
 basic theoretical properties are unknown. It is unknown even (a)
 whether there are an infinite number of Sophie Germain primes,
 (b) and even so, whether this simple procedure for finding them
 continues to quickly succeed as the size of q increases. Another
 way to instantiate the assumption is to use the points on an
 elliptic curve for which these issues do not arise.

.Theorem 52.3 Let DL = { f i : Di → Ri }i∈ I where
                      I = {(q, g) | q ∈ Πk , g ∈ GenGq }
                       D i = { x | x ∈ Zq }
                       Ri = G p
                f p,g ( x ) = g x

 If the Discrete Log Assumption holds, then DL is a collection of one-way
 functions.

 Proof. It is easy to sample the domain Di and to evaluate the
 function f p,g ( x ). The discrete log assumption implies that f p,g is
 2.9. RSA Collection                                                    53


 hard to invert. Thus, all that remains is to prove that I can be
 sampled efficiently. Unfortunately, given only a prime p, it is not
 known how to efficiently choose a generator g ∈ Gen p . However,
 it is possible to sample both a prime and a generator g at the same
 time. One approach proposed by Bach and later adapted by Kalai
 is to sample a k-bit integer x in factored form (i.e., sample the
 integer and its factorization at the same time) such that p = x + 1
 is prime. A special case of this approach is to pick safe primes
 of the form p = 2q + 1 as mentioned above. Given such a pair
 p, (q1 , . . . , qk ), one can use a central result from group theory to
 test whether an element is a generator. For example, in the case
 of safe primes, testing whether an element g ∈ Z∗p is a generator
 consists of checking g 6= ±1 mod p and gq 6= 1 mod p.                 
      As we will see later, the collection DL is also a special collec-
 tion of one-way functions in which each function is a permuta-
 tion.


 2.9 RSA Collection
 Another popular assumption is the RSA Assumption. The RSA
 Assumption implies the Factoring assumption; it is not known
 whether the converse is true.

.Assumption 53.1 (RSA Assumption) Given a triple ( N, e, y) such
 that N = pq where p, q ∈ Πn , gcd(e, Φ( N )) = 1 and y ∈ Z∗N ,
 the probability that any adversary A is able to produce x such that
 x e = y mod N is a negligible function e(n).
     "      r                   r
                                                           #
       p, q ← Πn ; N ← pq; e ← Z∗Φ( N ) ;
 Pr                                        : x e = y mod N < e(n)
       y ← Z∗N ; x ← A( N, e, y)

.Theorem 53.2 (RSA Collection) Let RSA = { f i : Di → Ri }i∈ I
 where

           I = {( N, e) | N = p · q s.t. p, q ∈ Πn and e ∈ Z∗Φ( N ) }
           Di = { x | x ∈ Z∗N }
           Ri = Z∗N
    f N,e ( x ) = x e mod N
 54                               chapter 2. computational hardness


 Under the RSA Assumption, RSA is a collection of one-way functions.
 Proof. The set I is easy to sample: generate two primes p, q,
 multiply then to generate N, and use the fact that Φ( N ) =
 ( p − 1)(q − 1) to sample a random element from Z∗Φ( N ) . Likewise,
 the set Di is also easy to sample and the function f N,e requires
 only one modular exponentiation to evaluate. It only remains
 to show that f N,e is difficult to invert. Notice, however, that this
 does not directly follow from the our hardness assumption (as it
 did in previous examples). The RSA assumption states that it
 is difficult to compute the eth root of a random group element y.
 On the other hand, our collection first picks the root and then
 computes y ← x e mod N. One could imagine that picking an
 element that is known to have an eth root makes it easier to find
 such a root. We prove that this is not the case by showing that
 the function f N,e ( x ) = x e mod N is a permutation of the elements
                                              r
 of Z∗N . Thus, the distributions { x, e ← Z∗N : (e, x e mod N )}
             r
 and {y, e ← Z∗N : (e, y)} are identical, and so an algorithm that
 inverts f N,e would also succeed at breaking the RSA-assumption.
                                                                    
.Theorem 54.3 The function f N,e ( x ) = x e mod N is a permutation
 of Z∗N when e ∈ Z∗Φ( N ) .
                                            ∗
 Proof. Since e is an element of the group ZΦ ( N ) , let d be its inverse
 (recall that every element in a group has an inverse), i.e. ed =
 1 mod Φ( N ). Consider the inverse map g N,e ( x ) = x d mod N.
 Now for any x ∈ Z∗N ,
      g N,e ( f N,e ( x )) = g N,e ( x e mod N ) = ( x e mod N )d mod N
                     = x ed mod N
                     = x cΦ( N )+1 mod N
 for some constant c. Recall that Euler’s theorem establishes that
 x Φ( N ) = 1 mod N. Thus, the above can be simplified as
                     x cΦ( N ) · x mod N = x mod N
 Hence, RSA is a permutation.                               
     This phenomena suggests that we formalize a new, stronger
 class of one-way functions.
 2.10. One-way Permutations                                       55


 2.10 One-way Permutations
.Definition 55.1 (One-way permutation). A collection F = { f i :
 Di → Ri }i∈ I is a collection of one-way permutations if F is a
 collection of one-way functions and for all i ∈ I, we have that f i
 is a permutation.

     A natural question is whether this extra property comes at a
 price—that is, how does the RSA-assumption that we must make
 compare to a natural assumption such as factoring. Here, we can
 immediately show that RSA is at least as strong an assumption
 as Factoring.

.Theorem 55.2 The RSA assumption implies the Factoring assump-
 tion.

 Proof. We prove by contrapositive: if factoring is possible in
 polynomial time, then we can break the RSA assumption in
 polynomial time. Formally, assume there an algorithm A and
 polynomial function p(n) so that A can factor N = pq with
 probability 1/p(n), where p and q are random n-bits primes.
 Then there exists an algorithm A0 , which can invert f N,e with
 probability 1/p(n), where N = pq, p, q ← {0, 1}n primes, and
 e ← Z∗Φ( N ) .

 algorithm 55.3: Adversary A0 ( N, e, y)
  1: Run ( p, q ) ← A ( N ) to recover prime factors of N
  2: If N 6 = pq then abort
  3: Compute Φ ( N ) ← ( p − 1)(q − 1)
  4: Compute the inverse d of e in Z∗Φ( N ) using Euclid
  5: Output yd mod N

     The algorithm feeds the factoring algorithm A with exactly
 the same distribution of inputs as with the factoring assumption.
 Hence in the first step A will return the correct prime factors with
 probability 1/p(n). Provided that the factors are correct, then we
 can compute the inverse of y in the same way as we construct the
 inverse map of f N,e . And this always succeeds with probability
 1. Thus overall, A0 succeeds in breaking the RSA-assumption
 with probability 1/p(n). Moreover, the running time of A0 is
 56                             chapter 2. computational hardness


 essentially the running time of A plus O(log3 (n)). Thus, if A
 succeeds in factoring in polynomial time, then A0 succeeds in
 breaking the RSA-assumption in roughly the same time.         
     Unfortunately, as mentioned above, it is not known whether
 the converse it true—i.e., whether the factoring assumption also
 implies the RSA-assumption.


 2.11 Trapdoor Permutations
 The proof that RSA is a permutation actually suggests another
 special property of that collection: if the factorization of N is
 unknown, then inverting f N,e is considered infeasiable; however
 if the factorization of N is known, then it is no longer hard to
 invert. In this sense, the factorization of N is a trapdoor which
 enables f N,e to be inverted.
     This spawns the idea of trapdoor permutations, first con-
 ceived by Diffie and Hellman.

.Definition 56.1 (Trapdoor Permutations). A collection of trapdoor
 permutations is a family F = { f i : Di → Ri }i∈I satisfying the
 following properties:

   1. ∀i ∈ I , f i is a permutation,
   2. It is easy to sample a function: ∃ p.p.t. Gen s.t. (i, t) ←
      Gen(1n ), i ∈ I (t is trapdoor info),
   3. It is easy to sample the domain: there exists a p.p.t. machine
      that given input i ∈ I , samples uniformly in Di .
   4. f i is easy to evaluate: there exists a p.p.t. machine that given
      input i ∈ I , x ∈ Di , computes f i ( x ).
   5. f i is hard to invert: for all p.p.t. A, there exists a negligible
      function e such that
                  (i, t) ← Gen(1n ); x ← Di ;
                                                            
             Pr                                 : f i (z) = y ≤ e(k)
                  y ← f ( x ); z ← A(1n , i, y)

   6. f i is easy to invert with trapdoor information: there exists a
      p.p.t. machine that given input (i, t) from Gen and y ∈ Ri ,
      computes f −1 (y).
 2.12. Rabin collection                                               57


    Now by slightly modifying the definition of the family RSA,
 we can easily show that it is a collection of trapdoor permutations.
.Theorem 57.2 Let RSA be defined as per Theorem 53.2 with the ex-
 ception that

                          [( N, e), d] ← Gen(1n )
                            −1
                          f N,d (y) = yd mod N
 where N = p · q, e ∈ Z∗Φ( N ) and e · d = 1 mod Φ( N ). Assuming
 the RSA-assumption, the collection RSA is a collection of trapdoor
 permutations.
 The proof is an exercise.


 2.12 Rabin collection
 The RSA assumption essentially claims that it is difficult to com-
 pute eth roots modulo a composite N that is a product of two
 primes. A weaker assumption is that it is even hard to com-
 pute square roots modulo N (without knowing the factors of
 N). Note that computing square roots is not a special case of
 RSA since gcd(2, φ( N )) 6= 1. This assumption leads to the Ra-
 bin collection of trapdoor functions; interestingly, we will show
 that this assumption is equivalent to the Factoring assumption
 (whereas it is not known whether Factoring implies the RSA
 assumption). To develop these ideas, we first present a general
 theory of square roots modulo a prime p, and then extend it to
 square roots modulo a composite N.

 Square roots modulo p
 Taking square roots over the integers is a well-studied and effi-
 cient operation. As we now show, taking square roots modulo a
 prime number is also easy.
     Define the set QR p = { x2 mod p| x ∈ Z∗p }. These numbers
 are called the quadratic residues for p and they form a subgroup
 of Z∗p that contains roughly half of its the elements.

.Lemma 57.1 If p > 2 is prime, then QR p is a group of size p−2 1 .
 58                              chapter 2. computational hardness


 Proof. Since 12 = (−1)2 = 1, QR p contains the identity. Since the
 product of squares is also a square, QR p is closed. Associativity
 carries over from Z p . Finally, if a = x2 ∈ QR p , then a−1 = ( x −1 )2
 is also a square, and so QR p contains inverses.
     To analyze the size of QR p , observe that if x2 = a, then
 ( p − x )2 = a and that because p is odd, ( p − x ) 6= x. On the
 other hand, if x2 = y2 , then ( x + y)( x − y) = 0 mod p. Because
 p is a prime, either ( x + y) = 0 mod p or ( x − y) = 0 mod p.
 Thus, for every a ∈ QRP there are exactly two distinct values for
 x ∈ Z p such that x2 = a. It follows that |QR p | = ( p − 1)/2. 
     For every prime p, the square root operation can be per-
 formed efficiently. We show how to compute square roots for the
 special case of primes that are of the form 4k + 3. The remaining
 cases are left as an exercise.

.Theorem 58.2 If p = 3 + 4k and y ∈ QR p , then (±yk+1 )2 = y.

 Proof. Since y ∈ QR p , let y = a2 mod p. Thus,

         (yk+1 )2 = a2(k+1)2 = a4k+4 = a p+1 = a2 = y mod p
                                                                       

 Exercise    Show how to compute square roots if p = 1 mod 4.

    Toward our goal of understanding square roots modulo a
 composite N = p · q, we now introduce a new tool.

 Chinese Remainder Theorem
 Let N = pq and suppose y ∈ Z N . Consider the numbers a1 ≡
 y mod p and a2 ≡ y mod q. The Chinese remainder theorem
 states that y can be uniquely recovered from the pair a1 , a2 and
 vice versa.

.Theorem 58.3 (Chinese Remainder) Let p1 , p2 , . . . , pk be pairwise
 relatively prime integers, i.e. gcd( pi , p j ) = 1 for 1 ≤ i < j ≤ k and
 N = ∏ik pi . The map CN (y) : Zn 7→ Z p1 × · · · × Z pk defined as
            CN (y) 7→ (y mod p1 , y mod p2 , . . . , y mod pk )
 is one-to-one and onto.
 2.12. Rabin collection                                            59


 Proof. For each i, set ni = N/pi ∈ Z. By our hypothesis, for
 each i ∈ [1, k ], it follows that gcd( pi , ni ) = 1 and hence there
 exists bi ∈ Z pi such that ni bi = 1 mod pi . Let ci = bi ni . Notice
 that ci = 1 mod pi = 0 mod p j for j 6= i . Set y = ∑i ci ai mod N.
 Then y = ai mod pi for each i.
     Further, if y0 = ai mod pi for each i then y0 = y mod pi for
 each i and since the pi s are pairwise relatively prime, it follows
 that y ≡ y0 mod N, proving uniqueness.                             

 Example Suppose p = 7 and q = 11. Since 7 and 11 are rela-
 tively prime, we have that

                             11 · 2 ≡ 1 mod 7
                              7 · 8 ≡ 1 mod 11

 and therefore b1 = 2 and b2 = 8. Thus, we have

                          C (y) 7→ (y mod 7, y mod 11)
                C −1 ( a1 , a2 ) 7→ a1 · 22 + a2 · 56 mod 77

       Notice that computing the coefficients b1 and b2 requires two
 calls to Euclid’s algorithm, and computing f −1 requires only two
 modular multplications and an addition. Thus, computing the
 map in either direction can be done efficiently given the factors
 p1 , . . . , p k .

 Square roots modulo N
 We are now ready to study the problem of computing square
 roots in Z N when N = pq. As before, we define the set QR N =
 { x2 mod n : x ∈ Z∗N }. Then we claim:

.Theorem 59.4 Let N = pq and for any x ∈ Z∗N , let (y, z) ← CN ( x ).
 Then x ∈ QR N ⇔ y ∈ QR p and zinQRq .

 Proof. ⇒ Since y ∈ QR p and z ∈ QRq , then there exists a ∈ Z∗p
 such that y ≡ a2 mod p and ∃b ∈ Z∗q such that z ≡ b2 mod q. By
                                                    −1
 the Chinese Remainder Theorem, there exists s ← CN    ( a, b). We
 60                            chapter 2. computational hardness


 show that s is one square root of x in Zn∗ :

                 s2 mod p ≡ a2 mod p ≡ y mod p
                  s2 mod q ≡ b2 mod q ≡ z mod q

 Therefore s2 is congruent to x modulo N and hence s is x’s square
 root, and x ∈ QR N .
    For the other direction of the proof, if x ∈ QR N , then ∃ a ∈ Z∗N
 such that x ≡ a2 mod n. Therefore

      x mod p ≡ a2 mod p ≡ ( a mod p)2 mod p ⇒ y ∈ QR p
      x mod q ≡ a2 mod q ≡ ( a mod q)2 mod q ⇒ z ∈ QRq

                                                                    
 Furthermore, we can characterize the size of the group QR N .

.Theorem 60.5 The mapping x → x2 mod N is 4 to 1.

 Proof. From Thm. 59.4, if x ∈ QR N , then y ≡ x mod p ∈ QR p
 and z ≡ x mod q ∈ QRq .
      Earlier, we proved that | QR p | = |Z∗p |/2 and the mapping
 x → x2 , x ∈ Z∗p is 2 to 1. So we have unique square roots a1 , a2
 for y and b1 , b2 for z. Take any two of them ai , b j , by Chinese
 remainder theorem ∃s ∈ ZN       ∗ , such that s ≡ a mod p and s ≡
                                                      i
 b j mod q. And by the same argument in the proof of Thm. 59.4,
 s is a square root of x in Z∗N . There are in total 4 combinations of
 ai and b j , thus we have 4 such s that are x’s square roots.      

.Corollary 60.6 |QR N | = |Z∗N |/4

       Remark that given p and q, it is easy to compute the square
 roots for elements in ZN ∗ . The proof above shows that the square

 root of x ∈ Z∗N can be combined from square roots of x mod p
 and x mod q in Z ∗p and Zq∗ respectively. And from previous
 sections, we have shown that square root operation is efficient in
 Z ∗p . So given p and q, we can simply calculate the square roots
 of x mod p and x mod q, and combine the result to get square
 roots of x. However, without p and q, it is not known whether
 square roots modulo N can be efficiently computed.
 2.12. Rabin collection                                           61


 Example Continuing our example from above with N = 7 ·
 11 = 77, consider 71 ∈ Z∗N . Thus, we have (1, 5) ← C (42).
 Taking square roots mod 7 and 11, we have (1, 4), and now using
 C −1 , we arrive at 15 ← C −1 (0, 3). Notice, however, that (6, 4),
 (1, 7), and (6, 7) are also roots. These pairs map to 48,29, and 62
 respectively.

 2.12.1 The Rabin Collection
.Theorem 61.7 Let R = { f i : Di → Ri }i∈ I where
                   I = { N : N = p · q, where p, q ∈ Πn }
                 Di = Z∗N
                 Ri = QR N
              f N ( x ) = x2 mod N
 If the Factoring Assumption holds, then R is a collection of one-way
 functions.

 Relationship for Factoring
 The interesting fact is that the Rabin Collection relies only on
 the Factoring assumption, whereas the RSA collection requires
 a stronger assumption to the best of our knowledge. In other
 words, we can show:
.Theorem 61.8 Rabin is a OWF iff factoring assumption holds.
 Proof. ⇒ We first show that if factoring is hard then Rabin is a
 OWF. We prove this by contrapositive: if Rabin can be inverted
 then factoring can be done efficiently. Formally, if there exists
 an adversary A and polynomial function p(n) such that A can
 invert f N with probability 1/p(n) for sufficiently large n, that is
 if
        p, q ← Πn , N ← pq, x ← Z∗N ,
                                                      
                                         2
   Pr                                 : z = y mod N > 1/p(k )
        y ← f N ( x ), z ← A( N, y)
 then there exists A0 that can factor the product of two random
 n-bits primes with probability 1/2p(n):
        Pr p, q ← Πn , N ← pq : A0 ( N ) ∈ { p, q} > 1/2p(k)
                                                 
62                            chapter 2. computational hardness


We construct A0 ( N ) as follows:
algorithm 62.9: Factoring Adversary A0 ( N )
 1: Sample x ← Z∗N
 2: Compute y ← x2 mod N
 3: Run z ← A(y, N )
 4: If z2 6 = y mod N then abort.
 5: Else output gcd( x − z, N ).

    First, because the input to A0 is the product of two random
k-bits primes and A0 randomly samples x from Zn∗ , the inputs
(y, N ) to A in step 3 have exactly the same distribution as those
from the Rabin collection. Thus algorithm A will return a correct
square root of x with probability 1/p(k ). And because A does
not know x and it outputs one of the four square roots with equal
probability, then with probability 1/2p(k ), z 6≡ x and z 6≡ − x.
Since x and z are both square roots of y, we have

        x2 ≡ z2 mod n     ⇒        ( x − z)( x + z) ≡ 0 mod n

When z 6≡ x and z 6≡ − x, it can only be that they are congruent
modulo p and q. Then the gcd( x − z, N ) would be p or q with
probability 1/2p(k ). Thus adversary A0 factors N.
    Only if direction: We want to show if Rabin is hard then
factoring is also hard. Similar to the proof of that RSA is OWP
implies factoring is hard, we show by contrapositive, that is, if
there exists an adversary A that factors N = pq with probability
1/r (k ) for some polynomial r, where p and q are random k-bits
primes, then by using the Chinese Remainder Theorem, it is
straightforward to compute square roots modulo N with 1/p(k ).
    The construction of A0 ( N, y) is also similar to that in RSA
case: first feed A with N, which returns p, q. Check whether
N = pq, if not then abort, else compute square root of y mod p
and y mod q in Z ∗p and Zq∗ respectively. Pick one pair of square
roots a, b and compute s = ac + bd. Output s.
    Since A receives N with the same distribution as in the fac-
toring assumption, A will succeed in factoring with probability
1/r (k ) and from the correct p, q we can compute the square root
of u with probability 1. Overall A0 succeeds with probability
1/r (k ).                                                       
 2.13. A Universal One Way Function                                  63


 Rabin Collection of Trapdoor Permutations
 Technically, Rabin is not a permutation, but by making some
 small adjustments, we can construct a collection of trapoor per-
 mutations as well:

.Theorem 63.10 Let R = { f i : Di → Ri }i∈ I where

           I = { N | N = pq, where p, q ∈ Πn , p = q = 3    mod 4}
        Di = QR N
       Ri = QR N
   Gen(1n ) : Samples a pair ( N, ( p, q)) s.t. N ∈ I
      f N ( x ) = x2 mod N
       −1
     f p,q (y) = x such that x2 = y mod N and x ∈ QR N

 If the Factoring Assumption holds, then R is a collection of trapdoor
 permutations.

    As we’ll show in future homeworks, each square in Q N has
 four square roots, but only one of the roots is also a square. This
 makes Rabin a (trapdoor) permutation.


 2.13 A Universal One Way Function
 As we have mentioned in previous sections, it is not known
 whether one-way functions exist. Although we have presented
 specific assumptions which have lead to specific constructions,
 a much weaker assumption is to assume only that some one-
 way function exists (without knowing exactly which one). The
 following theorem gives a single constructible function that is
 one-way if this weaker assumption is true.

.Theorem 63.1 If there exists a one-way function, then the following
 polynomial-time computable function f universal is also a one-way func-
 tion.

 Proof. We will construct function f universal and show that it is
 weakly one-way. We can then apply the hardness amplification
 construction from §2.3 to get a strong one-way function.
 64                                 chapter 2. computational hardness


      The idea behind the construction is that f universal incorporates
 the computation of all efficient functions in such a way that
 inverting f universal allows us to invert all other functions. This
 ambitious goal can be approached by intrepreting the input y to
 f universal as a machine-input pair y = h M, x i, and then defining
 the output of f universal (y) to be M ( x ). The problem with this
 approach is that f universal will not be computable in polynomial
 time, since M may not even terminate on input x. We can
 overcome this problem by only running M( x ) for a number of
 steps related to |y|.
 algorithm 64.2: A Universal One-way Function f universal (y)
   Interpret y as h M, x i where | M | = log(|y|)
   Run M on input x for |y|3 steps
   if M terminates then
      Output M( x )
   else
      Output ⊥
   end if
     In words, this function interprets the first log |y| bits of the
 input y as a machine M, and the remaining bits are considered
 input x. We assume a standard way to encode Turing machines
 with appropriate padding. We claim that this function is weakly
 one-way. Clearly f universal is computable in time O(|y|3 ), and
 thus it satisfies the “easy” criterion for being one-way. To show
 that it satisfies the “hard” criterion, we must assume that there
 exists some function g that is strongly one-way. By the following
 lemma, we can assume that g runs in O(|y|2 ) time.

.Lemma 64.3 If there exists a strongly one-way function g, then there
 exists a strongly one-way function g0 that is computable in time O(n2 ).

 Proof. Suppose g runs in time at most nc for some c > 2. (If not,
 then the lemma already holds.) Let g0 (h a, bi) = h a, g(b)i, where
 | a| = nc − n and |b| = n. Then if we let m = |h a, bi| = nc , the
 function g0 is computable in time

          | a| +      |b|c       + O(m2 ) < 2m + O(m2 ) = O(m2 )
         |{z}         |{z}         | {z }
       copying a   computing g     parsing
2.13. A Universal One Way Function                              65


Moreover, g0 is still one-way, since any adversary that inverts g0
can easily be used to invert g.                                 
   Now, if f universal is not weakly one-way, then there exists a
machine A such that for every polynomial q and for infinitely
many input lengths n,
         h                                      i
      Pr y ← {0, 1}n ; A( f (y)) ∈ f −1 ( f (y)) > 1 − 1/q(n)

In particular, this holds for q(n) = n3 . Denote the event that A
inverts as Invert.
    Let Mg be the smallest machine which computes function g.
Since Mg is a uniform algorithm it has some constant description
size | Mg |. Thus, on a random n-bit input y = h M, x i, the proba-
bility that machine M = Mg (with appropriate padding of 0) is
2− log n = 1/n. In other words
                   h
                       r
                                               i  1
                Pr y ← {0, 1}n : y = h Mg , x i ≥
                                                  n
Denote this event as event PickG. We can now combine the above
two equations to conclude that A inverts an instance of g with
noticeable probability. By the Union Bound, either A fails to
invert or the instance fails to be g with probability at most

                                                     n3 − 1
      Pr[!Invert ∨ !PickG] ≤ (1/n3 ) + (1 − 1/n) <
                                                       n3
Therefore, A must invert a hard instance of g with probability
                                            1
                   Pr[Invert and PickG] ≥
                                            n3
which contradicts the assumption that g is strongly one-way;
therefore f universal must be weakly one-way.                   
     This theorem gives us a function that we can safely assume
is one-way (because that assumption is equivalent to the as-
sumption that one-way functions exist). However, it is extremely
impractical to compute. First, it is difficult to compute because
it involves interpreting random turing machines. Second, it will
require very large key lengths before the hardness kicks in. A
very open problem is to find a “nicer” universal one way function
(e.g. it would be very nice if f mult is universal).
