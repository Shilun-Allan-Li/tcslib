<!-- generated-by: scoped Poppler extraction of the passages used (DW-8) -->
<!-- source-pdf-sha256: bf2ce542208824ebf39ce132aae2d26a3b90bc04d3496a4ec05361f27e62118c -->
<!-- extractor: pdftotext version 24.02.0; -layout; scoped to the line ranges listed below -->
<!-- scope (physical page: lines of the -layout text): p67: 2510-2545; p88: 3355-3369; p172: 6644-6672; p174: 6727-6757; p176: 6801-6814; p179: 6929-6940; p181: 7013-7037; p182: 7038-7079; p183: 7080-7124; p184: 7125-7139; p212: 8263-8270; p213: 8271-8273 -->
<!-- note: physical page p is printed page p-3 (p182 is printed page 179) -->

<!-- pdf-page: 67 -->
complexity of the constructions.

Deﬁnition 3.21 (pairwise independent hash functions). A
family (i.e., multiset) of functions H = {h : [N ] → [M ]} is pairwise inde-
                                                         R
pendent if the following two conditions hold when H ← H is a function
chosen uniformly at random from H:

     (1) ∀ x ∈ [N ], the random variable H(x) is uniformly distributed
         in [M ].
     (2) ∀ x1 = x2 ∈ [N ], the random variables H(x1 ) and H(x2 ) are
         independent.


   Equivalently, we can combine the two conditions and require that
                                                                       1
∀ x1 = x2 ∈ [N ], ∀ y1 , y2 ∈ [M ], Pr [H(x1 ) = y1 ∧ H(x2 ) = y2 ] = 2 .
                                      R
                                    H ←H                              M
Note that the probability above is over the random choice of a function
from the family H. This is why we talk about a family of functions
rather than a single function. The description in terms of functions
makes it natural to impose a strong eﬃciency requirement:

Deﬁnition 3.22. A family of functions H = {h : [N ] → [M ]} is explicit
if given the description of h and x ∈ [N ], the value h(x) can be com-
puted in time poly(log N, log M ).

    Pairwise independent hash functions are sometimes referred to as
strongly 2-universal hash functions, to contrast with the weaker notion
of 2-universal hash functions, which requires only that Pr[H(x1 ) =
H(x2 )] ≤ 1/M for all x1 = x2 . (Note that this property is all we needed
for the deterministic MaxCut algorithm, and it allows for a small sav-
ings in that we can also include S = ∅ in Construction 3.18.)
    Below we present another construction of a pairwise independent
family.

<!-- pdf-page: 88 -->
probability distributions.

Deﬁnition 4.7. For a probability distribution π, the collision proba-
bility of π is deﬁned to be the probability that two independent sam-
                                           
ples from π are equal, namely CP(π) = x πx2 . The support of π is
Supp(π) = {x : πx > 0}.


Lemma 4.8. For every probability distribution π ∈ [0, 1]N , we have:

   (1) CP(π) = π2 = π − u2 + 1/N , where u is the uniform
       distribution on [N ].
   (2) CP(π) ≥ 1/ |Supp(π)|, with equality iﬀ π is uniform on
       Supp(π).

<!-- pdf-page: 172 -->
                                          6.1 Motivation and Deﬁnition   169


Deﬁnition 6.2.For random variables X and Y taking values in U, their
statistical diﬀerence (also known as variation distance) is ∆(X, Y ) =
maxT ⊂U | Pr[X ∈ T ] − Pr[Y ∈ T ]|. We say that X and Y are ε-close if
∆(X, Y ) ≤ ε.

    Intuitively, any event in X happens in Y with the same proba-
bility ±ε. This is perhaps the most natural measure of distance for
probability distributions (much more so than the 2 distance we used
in the study of random walks). In particular, it satisﬁes the following
natural properties.

Lemma 6.3(properties of statistical diﬀerence). Let X, Y, Z, X1 ,
X2 , Y1 , Y2 be random variables taking values in a universe U. Then,
   (1) ∆(X, Y ) ≥ 0, with equality iﬀ X and Y are identically dis-
       tributed,
   (2) ∆(X, Y ) ≤ 1, with equality iﬀ X and Y have disjoint sup-
       ports,
   (3) ∆(X, Y ) = ∆(Y, X),
   (4) ∆(X, Z) ≤ ∆(X, Y ) + ∆(Y, Z),
   (5) for every function f , we have ∆(f (X), f (Y )) ≤ ∆(X, Y ),
   (6) ∆((X1 , X2 ), (Y1 , Y2 )) ≤ ∆(X1 , Y1 ) + ∆(X2 , Y2 ) if X1 and X2 ,
       as well as Y1 and Y2 , are independent, and
   (7) ∆(X, Y ) = 12 · |X − Y |1 , where | · |1 is the 1 distance. (Thus,
       X is ε-close to Y iﬀ we can transform X into Y by “shifting”
       at most an ε fraction of probability mass.)


<!-- pdf-page: 174 -->

6.1.2   Entropy Measures and General Weak Sources
Intuitively, to extract m almost-uniform bits from a source, the source
must have at least “m bits of randomness” in it. (In particular, its
support cannot be much smaller than 2m .) Ideally, this is all we would
like to assume about a source. Thus, we need some measure of how much
randomness is in a random variable; this can be done using various
notions of entropy described below.

Deﬁnition 6.7 (entropy measures). Let X be a random variable.
Then

     • the Shannon entropy of X is:
                                   !                     "
                                                   1
                   HSh (X) = E log                         .
                                    R
                                  x←X         Pr [X = x]
     • the Rényi entropy of X is:
                                           
                                  1                   1
          H2 (X) = log                        = log       , and
                         Ex←X
                            R  [Pr [X = x]]         CP(X)
     • the min-entropy of X is:
                                        
                                                   1
                      H∞ (X) = min log                   ,
                                   x          Pr [X = x]
where all logs are base 2.


<!-- pdf-page: 176 -->
                                        6.1 Motivation and Deﬁnition   173

  We will consider the task of extracting randomness from sources
where all we know is a lower bound on the min-entropy:

Deﬁnition 6.9. A random variable X is a k-source if H∞ (X) ≥ k, i.e.,
if Pr [X = x] ≤ 2−k .

   A typical setting of parameters is k = δn for some ﬁxed δ, e.g.,
0.01. We call δ the min-entropy rate. Some diﬀerent ranges that are
commonly studied (and are useful for diﬀerent applications): k =
polylog(n), k = nγ for a constant γ ∈ (0, 1), k = δn for a constant
δ ∈ (0, 1), and k = n − O(1). The middle two (k = nγ and k = δn) are
the most natural for simulating randomized algorithms with weak ran-

<!-- pdf-page: 179 -->
random source. We can think of this seed of truly random bits as a
random choice of an extractor from family of extractors. This leads to
the following crucial deﬁnition:

Deﬁnition 6.13 (seeded extractors). A function Ext : {0, 1}n ×
{0, 1}d → {0, 1}m is a (k, ε)-extractor if for every k-source X on {0, 1}n ,
Ext(X, Ud ) is ε-close to Um .

   (Sometimes we will refer to extractors Ext : [N ] × [D] → [M ] whose
domain and range do not consist of bit-strings. These are deﬁned in the
natural way, requiring that Ext(X, U[D] ) is ε-close to U[M ] .)
   The goal is to construct extractors that minimize d and maximize m.

<!-- pdf-page: 181 -->
tions to the other pseudorandom objects we are studying.

6.2     Connections to Other Pseudorandom Objects
As mentioned earlier, extractors have played a unifying role in the
theory of pseudorandomness, through their close connections with a
variety of other pseudorandom objects. In this section, we will see two
of these connections. Speciﬁcally, how by reinterpreting them appropri-
ately, extractors can be viewed as providing families of hash functions,
and as being a certain type of highly expanding graphs.

6.2.1     Extractors as Hash Functions
Proposition 6.12 says that for any subset S ⊂ [N ] of size K, if we choose
a completely random hash function h : [N ] → [M ] for M         K, then h
will map the elements of S almost-uniformly to [M ]. Equivalently, if
we let H be distributed uniformly over all functions h : [N ] → [M ] and
X be uniform on the set S, then (H, H(X)) is statistically close to
(H, U[M ] ), where we use the notation UT to denote the uniform distri-
bution on a set T . Can we use a smaller family of hash functions than
the set of all functions h : [N ] → [M ]? This gives rise to the following
variant of extractors.

Deﬁnition 6.16 (strong extractors). Extractor Ext : {0, 1}n ×
{0, 1}d → {0, 1}m is a strong (k, ε)-extractor if for every k-source
X on {0, 1}n , (Ud , Ext(X, Ud )) is ε-close to (Ud , Um ). Equivalently,
Ext (x, y) = (y, Ext(x, y)) is a standard (k, ε)-extractor.

<!-- pdf-page: 182 -->
                            6.2 Connections to Other Pseudorandom Objects            179

   The nonconstructive existence proof of Theorem 6.14 can be
extended to establish the existence of very good strong extractors:

Theorem 6.17. For every n, k ∈ N and ε > 0 there exists a
strong (k, ε)-extractor Ext : {0, 1}n × {0, 1}d → {0, 1}m with m = k −
2 log(1/ε) − O(1) and d = log(n − k) + 2 log(1/ε) + O(1).

    Note that the output length is m ≈ k instead of m ≈ k + d; intu-
itively a strong extractor needs to extract randomness that is indepen-
dent of the seed and thus can only get the k bits from the source.
    We see that strong extractors can be viewed as very small families of
hash functions having the almost-uniform mapping property mentioned
above. Indeed, our ﬁrst explicit construction of extractors is obtained
by using pairwise independent hash functions.

Theorem 6.18 (Leftover Hash Lemma). If H = {h : {0, 1}n →
{0, 1}m } is a pairwise independent (or even 2-universal) family of hash
                                                                 def
functions where m = k − 2 log(1/ε), then Ext(x, h) = h(x) is a strong
(k, ε)-extractor. Equivalently, Ext(x, h) = (h, h(x)) is a standard (k, ε)-
extractor.

   Note that the seed length equals the number of random bits required
             R
to choose h ← H, which is at least n by Problem 3.5.2 This is far
from optimal; for the purposes of simulating randomized algorithms we
would like d = O(log n). However, the output length of the extractor is
m = k − 2 log(1/ε), which is optimal up to an additive constant.

Proof. Let X be an arbitrary k-source on {0, 1}n , H as above, and
   R
H ← H. Let d be the seed length. We show that (H, H(X)) is ε-close
to Ud × Um in the following three steps:

    (1) We show that the collision probability of (H, H(X)) is close
        to that of Ud × Um .
2 Problem 3.5 refers to pairwise independent families, but a similar argument shows that

 universal families require Ω(n) random bits. (Instead of constructing orthogonal vectors,
 we construct vectors that have nonpositive dot product.)

<!-- pdf-page: 183 -->
180     Randomness Extractors

      (2) We note that this is equivalent to saying that the 2 distance
          between (H, H(X)) and Ud × Um is small.
      (3) Then we deduce that the statistical diﬀerence is small, by
          recalling that the statistical diﬀerence equals half of the 1
          distance, which can be (loosely) bounded by the 2 distance.

Proof of (1): By deﬁnition, CP(H, H(X)) = Pr[(H, H(X)) =
(H  , H  (X  ))], where (H  , X  ) is independent of and identically
distributed to (H, X). Note that (H, H(X)) = (H  , H  (X)) if and only
if H = H  and either X = X  or X = X  but H(X) = H(X  ). Thus

 CP(H, H(X)) = CP(H) · (CP(X) + Pr[H(X) = H(X  ) | X = X  ])
                           
               1     1    1     1 + ε2
             ≤   ·     +      ≤        .
               D     K   M       DM
To see the penultimate inequality, note that CP(H) = 1/D because
there are D hash functions, CP(X) ≤ 1/K because H∞ (X) ≥ k, and
Pr [H(X) = H(X  ) |X = X  ] ≤ 1/M by 2-universality.
Proof of (2):
                                                      1
           (H, H(X)) − Ud × Um 2 = CP(H, H(X)) −
                                                     DM
                                        1+ε 2    1    ε2
                                      ≤       −    =     .
                                         DM     DM   DM
   Proof of (3): Recalling that the statistical diﬀerence between two
random variables X and Y is equal to 12 |X − Y |1 , we have:
                                  1
       ∆((H, H(X)), Ud × Um ) =     · |(H, H(X)) − Ud × Um |1
                                  2
                                  √
                                    DM
                                ≤         · (H, H(X)) − Ud × Um 
                                     2
                                  √         
                                    DM         ε2
                                ≤         ·
                                     2        DM
                                  ε
                                = .
                                  2
Thus, we have in fact obtained a strong (k, ε/2)-extractor.

<!-- pdf-page: 184 -->
                            6.2 Connections to Other Pseudorandom Objects             181

    The proof above actually shows that Ext(x, h) = h(x) extracts with
respect to collision probability, or equivalently, with respect to the
2 -norm. This property may be expressed in terms of Rényi entropy
       def
H2 (Z) = log(1/CP(Z)). Indeed, we can deﬁne Ext : {0, 1}n × {0, 1}d −→
{0, 1}m to be a (k, ε) Rényi-entropy extractor if H2 (X) ≥ k implies
H2 (Ext(X, Ud )) ≥ m − ε (or H2 (Ud , Ext(X, Ud )) ≥ m + d − ε for strong
Rényi-entropy extractors). Then the above proof shows that pairwise-
independent hash functions yield strong Rényi-entropy extractors.
    In general, it turns out that an extractor with respect to
Rényi entropy must have seed length d ≥ min{m/2, n − k} − O(1) (as
opposed to d = O(log n)); this explains why the seed length in the above
extractor is large. (See Problem 6.4.)

<!-- pdf-page: 212 -->
    The notion of seeded extractor we focus on in this section (Deﬁ-
nitions 6.13,6.16) was introduced by Nisan and Zuckerman [303], who
also gave the ﬁrst construction of extractors with polylogarithmic seed
length (building on [426]). A form of the Leftover Hash Lemma (for
ﬂat distributions, and where the quality of the output distribution
is measured with entropy rather than statistical diﬀerence) was
ﬁrst proven by Bennett, Brassard, and Robert [63]. The version in
Theorem 6.18 is due to Impagliazzo, Levin, and Luby [197], and the

<!-- pdf-page: 213 -->
210   Randomness Extractors

proof we give is due to Rackoﬀ [217]. The connection between the
