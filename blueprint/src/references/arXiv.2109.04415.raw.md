<!-- generated-by: proofmatch local extraction -->
<!-- source-pdf-sha256: 9c5df3bb4a04eeeea67f0c590a5340f72bfc2557b6ea9e626202e500afc9f29a -->
<!-- extractor: pymupdf + subset-font decode (+1 shift, ]->a, P->R) -->

<!-- pdf-page: 1 -->
@lgorithms and Certiﬁcates for Boolean CSP Refutation:
’Smoothed is no harder than Random“
Venkatesan Guruswami‡
veniAtg;berielew edu
UC Berkeley
Pravesh K. Kothari”
prAveshi;cs cmu edu
Carnegie Mellon University
Peter Manohar†
pmAnohAr;cs cmu edu
Carnegie Mellon University
September 6* 2023
;bstract
We present an algorithm for strongly refuting smoothed instances of all Boolean CSPs. The
smoothed model is a hybrid between worst and average-case input models* where the input is an
arbitrary instance of the CSP with only the negation patterns of the literals re-randomized with
some small probability. For an 𝑛-variable smoothed instance of a 𝑘-arity CSP* our algorithm
runs in 𝑛𝑂0ℓ) time* and succeeds with high probability in bounding the optimum fraction of
satisﬁable constraints away from 1* provided that the number of constraints is at least ˆ𝑂0𝑛)0 𝑛
ℓ)
𝑘
2
1.
This matches* up to polylogarithmic factors in 𝑛* the trade-oﬀbetween running time and the
number of constraints of the state-of-the-art algorithms for refuting fully rYndom instances of
CSPs [RRS17\.
We also make a surprising connection between the analysis of our refutation algorithm in
the signiﬁcantly ’randomness starved“ setting of semi-random 𝑘-XOR and the existence of
even covers in worst-cYse hypergraphs. We use this connection to positively resolve Feige—s 2008
conjecture – an extremal combinatorics conjecture on the existence of even covers in suﬂciently
dense hypergraphs that generalizes the well-known Moore bound for the girth of graphs. @s a
corollary* we show that polynomial-size refutation witnesses exist for arbitrary smoothed CSP
instances with number of constraints a polynomial factor below the ’spectral threshold“ of 𝑛𝑘02*
extending the celebrated result for random 3-S@T of Feige* Kim and Ofek [FKO06\.
Jeywords: CSP refutation* Smoothed CSPs* Even covers
‡Supported in part by NSF grants CCF-CCF-2228287 and CCF-2211972 and a Simons Investigator award.
”Supported in part by an NSF C@REER @ward #2047933* a Google Research Scholar @ward* and a Sloan Fellowship.
†Supported in part by an @RCS Scholarship* NSF Graduate Research Fellowship $under grant numbers DGE1745016
and DGE2140739)* and NSF CCF-1814603.
@ny opinions* ﬁndings* and conclusions or recommendations expressed in this material are those of the author$s)
and do not necessarily reﬁect the views of the National Science Foundation.
bsYjw;321:/15526w3  \dt/DDa  4 Tfq 3134

<!-- pdf-page: 2 -->
Contents
1
Introduction
1
1.1
Our results . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . .
2
2
Overview of our Techniques
8
2.1
Random 4-XOR via the Kikuchi matrix of [W@M19\ . . . . . . . . . . . . . . . . . . . . . . . .
8
2.2
Semirandom instances of 4-XOR via row bucketing from [@GK21\ . . . . . . . . . . . . . . . .
10
2.3
Proving Feige—s conjecture for 4-uniform hypergraphs . . . . . . . . . . . . . . . . . . . . . . .
11
2.4
Refuting semirandom 3-XOR via row pruning
. . . . . . . . . . . . . . . . . . . . . . . . . . .
14
2.5
Handling 𝑘-XOR for 𝑘= 3: hypergraph regularity . . . . . . . . . . . . . . . . . . . . . . . . .
16
2.6
Organization . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . .
17
3
Preliminaries
18
3.1
Basic notation . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . .
18
3.2
Concentration inequalities . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . .
18
3.3
The sum-of-squares algorithm . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . .
18
4
; Hypergraph Decomposition Lemma
19
5
Refuting Semirandom Sparse Polynomials over the Hypercube
23
5.1
Regular bipartite polynomials . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . .
23
5.2
Reduction to regular bipartite polynomials
. . . . . . . . . . . . . . . . . . . . . . . . . . . . .
25
6
Refuting Regular Bipartite Polynomials
26
6.1
Our Kikuchi matrix and algorithm . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . .
27
6.2
Bounding }𝐴}∞→1: proof plan
. . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . .
30
6.3
Row pruning . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . .
30
6.4
Bounding the ∞→1 norm of the ’good rows“: proof of Lemma 6.11 . . . . . . . . . . . . . .
33
6.5
Bounding the number of bad rows: proof of Lemma 6.9 . . . . . . . . . . . . . . . . . . . . . .
38
7
Strong CSP Refutation: Smoothed via Semirandom
41
7.1
Proof of Theorem 7.4 . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . .
42
8
Proof of Feige{s Conjecture: Even Covers in Hypergraphs
44
8.1
Proof of Lemma 8.4 . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . . .
46
9
Polynomial Size Refutation Witnesses Below the Spectral Threshold
49
; ;nalyzing the YW;M19\ ;pproach for Random 3*XOR
56

<!-- pdf-page: 3 -->
1
Introduction
Worst-case complexity theory paints a grim picture for solving Constraint Satisfaction Prob-
lems $CSPs). For a large class [Cha13* MR10\ of Max CSPs with 𝑘-ary Boolean predicates $𝑘-CSPs)*
the Exponential Time Hypothesis $ETH) [IP01\ implies that for sparse instances* i.e.* with 𝑚> 𝑂0𝑛)
constraints in 𝑛variables* there is no sub-exponential time approximation algorithm that beats sim-
ply returning a random assignment. While fully-dense instances $i.e.* 𝑚⩾𝑂0𝑛𝑘)) admit [@KK95\ a
polynomial time approximation scheme $PT@S)* ETH implies that lowering 𝑚to just ∼𝑛𝑘1 makes
the problem @PX-hard [FLP16\ even for sub-exponential time algorithms. In fact* for instances with
𝑚⩽𝑂0𝑛𝑘1)* we suspect that even eﬂciently veriﬁable certiﬁcYtes of non-vacuous upper bounds on
the value* i.e.* max fraction of constraints satisﬁable* do not exist.
The study of rYndom CSPs* on the other hand* oﬀers a stark contrast. Max 𝑘-CSPs with any strictly
super-linear number of* say* 𝑚⩾𝑛1/1 randomly generated constraints admit [BM16* @OW15*
RRS17\ sub-exponential time tight refutYtion3 algorithms. These are based on spectrYl methods that
exploit problem structure in non-trivial ways. Further* when 𝑚∼ˆ𝑂0𝑛𝑘02) ≪𝑛𝑘1* such algorithms
in fact yield a PT@S for certifying the value of the input instance correctly. In fact* a considerably
more ﬁne-grained* predicate-speciﬁc and likely sharp picture [BCK15* KMOW17\ of the trade-oﬀ
between running time and number of constraints has emerged in the last decade. @dding to this
rich theory is the fascinating work of [FKO06\ that shows that random CSPs admit polynomial-time
veriﬁable certiﬁcates of non-trivial upper bounds on the value even when 𝑚∼𝑛𝑘02 𝛿𝑘– i.e.* when
number of constraints are polynomially smaller than the threshold for eﬂcient refutation.
How does the complexity landscape of CSPs – for both algorithms and certiﬁcates – interpolate
between these two extremes< Is the worst-case understanding too pessimistic< Is the average-case
understanding too idealistic< @nd are the sophisticated algorithmic tools and the structural
properties that govern their success for random CSPs relevant to more general instances<
Refutation algorithms in the smoothed model. To formally study these questions* in 2007*
Feige [Fei07\ introduced a natural ’hybrid“ model in between worst-case and random instances $in
the spirit of the pioneering work of Spielman and Teng [ST03\). In this smoothed model* an instance
is generated by starting from an arbitrary $i.e.* worst-case) instance* and then negating each literal
in each clause independently with some small* constant probability. In contrast to random CSPs
where the clause structure $i.e.* 𝑘-tuples describing the constraints) and the literal patterns $i.e.*
which variables are negated in a constraint) are chosen uniformly at random and independently* the
clause structure in smoothed CSPs is completely arbitrary $i.e.* worst-case) and only a small constant
fraction of the literal patterns are random. In [Fei07\* Feige combined semideﬁnite programming
with a new combinatorial certiﬁcate based on a natural notion of cycles in hypergraphs* and proved
that polynomial algorithms succeed in weakly refuting $i.e.* certifying a 1
𝑜𝑛01) upper bound on
value* Deﬁnition 1.2) smoothed 3-S@T formulas with 𝑚⩾ˆ𝑂0𝑛1/5) constraints.
Feige—s techniques* however* appear fundamentally limited to weak refutation and specialized
to 3-CSPs. @s a result* there is no known strong refutation algorithm $i.e.* certifying a 1
Ω01)
upper bound on value) for smoothed instances of 3-S@T and no known $even weak) refutation
algorithm for smoothed instances of any nontrivial 4-CSP.
In this work* we develop new techniques that yield strong refutation algorithms for all smoothed
i.e.* uniformly random and independently chosen variables and ’literal patterns“ in each constraint.
3Such algorithms correctly certify an upper bound on the value within an arbitrarily small additive 𝜀w.h.p.
1

<!-- pdf-page: 4 -->
Boolean 𝑘-CSPs with $a possibly sharp) trade-oﬀbetween running time and number of constraints
matching that of fully random 𝑘-CSPs [RRS17\* up to polylogarithmic factors. In particular* our
results show that the algorithmic task of strong refutation in the signiﬁcantly ’randomness starved“
setting of smoothed instances is no harder than in a fully random instance.
Refutation witnesses below spectral threshold: Feige{s conjecture. The work [FKO06\ $and
extensions [Wit17\)* prove that there are eﬂciently veriﬁable witnesses of unsatisﬁability for fully
rYndom 𝑘-CSPs with 𝑛
𝑘
2
𝛿𝑘constraints for some constant 𝛿𝑘= 0; when 𝑘> 3* this threshold is 𝑛1/4.
These witnesses are based on certain natural analogs of cycles in hypergraphs called even covers. In
an eﬀort to understand if such witnesses exist in more general instances* Feige [Fei08\ conjectured a
trade-oﬀbetween number of constraints and size of a smallest even cover. This conjecture formally
generalizes the Moore bound [@HL02\ on girth of graphs to hypergraphs.
In this work* we prove Feige—s conjecture by a new spectrYl double counting argument that
relates sub-exponential time smoothed refutation algorithms and the existence of even covers
in hypergraphs. @s a consequence* we derive that there are eﬂciently veriﬁable witnesses of
unsatisﬁability for smoothed instances of all 𝑘-CSPs with 𝑚∼𝑛𝑘02 𝛿𝑘constraints* for some constant
𝛿𝑘* which is polynomially smaller than the threshold at which eﬂcient refutation algorithms exist
even for random 𝑘-CSPs.
Summary. Taken together* our main results can be interpreted as suggesting that the worst-case
picture of complexity of CSPs arises entirely because of islYnds of pYthology: most instances ’around“
the worst-case hard ones are in fact essentially as easy as random* for both refutation algorithms as
well as existence of refutation witnesses. Further* in a precise sense* the diﬂculty of worst-case
instances can be attributed to the worst-case literal patterns* rather than the clause structure.
Our contribution is shown visually in Figure 1. Figure 1 plots the time vs. # constraints
trade-oﬀfor refuting random and smoothed 3-S@T instances $along with the analogous trade-oﬀfor
approximation schemes for worst case instances). Our contribution is the smoothed case $blue line)*
which shows that smoothed 3-S@T instances can be refuted with the same trade-oﬀas random ones
$green line). We also show that there exist eﬂciently veriﬁable refutation witnesses for smoothed
instances at 𝑛1/4 constraints $purple line)* matching the result for random instances due to [FKO06\.
1.1
Our results
We now discuss our results on algorithms and certiﬁcates* as well as the interconnected techniques
and insights that go into them. Let us recall the standard notation to talk about CSPs.
De”nition 1.1 $𝑘-ary Boolean CSPs* random* semirandom* and smoothed instances). @ CSP instance
𝜙on 𝑛variables with a 𝑘-ary predicate 𝑃: |±1|𝑘→|0/ 1| is a set of 𝑚constraints on 𝑛variables
𝑥1/ / / / / 𝑥𝑛taking values in | 1/ 1|𝑛of the form 𝑃0𝜉0𝐶)1𝑥𝐶1/ 𝜉0𝐶)2𝑥𝐶2/ / / / / 𝜉0𝐶)𝑘𝑥𝐶𝑘) > 1. Here*
𝐶> 0𝐶1/ 𝐶2/ / / / / 𝐶𝑘) ranges over a collection ℋof scopes $a.k.a. clause structure) of 𝑘-tuples of
𝑛variables such that 𝐶𝑖≠𝐶𝑗for any 𝑖/ 𝑗and 𝜉: ℋ→|±1|𝑘are ’literal negation patterns“ one
for each 𝐶in ℋ. The vYlue of 𝜙* val0𝜙)* is the maximum fraction of constraints satisﬁed by any
assignment to the 𝑛variables.
In a rYndom $sometimes* fully rYndom in order to disambiguate from related models) instance*
ℋis a collection of 𝑚uniformly random and independently chosen 𝑘-tuples and the 𝜉0𝐶)—s are
chosen uniformly at random and independently from |±1|𝑘for each 𝐶.
2

<!-- pdf-page: 5 -->
Figure 1: Time vs. # constraints trade-oﬀfor refuting random and smoothed 3-S@T instances* and for
approximation schemes for worst-case instances. The smoothed case is our contribution. We also
prove that refutation witnesses exist for smoothed instances at the purple line* i.e.* 𝑛1/4 constraints.
In a semirYndom instance* ℋis arbitrary $i.e.* worst-case) and 𝜉0𝐶) ∈|±1|𝑘are uniformly at
random and independent for each 𝐶.
In a smoothed instance* ℋis arbitrary $i.e.* worst-case) and 𝜉0𝐶) ∈|±1|𝑘are obtained by starting
with arbitrary $i.e.* worst-case) 𝜉′0𝐶) ∈|±1|𝑘for each 𝐶and then for each 𝐶/ 𝑖* setting 𝜉0𝐶)𝑖> 𝜉′0𝐶)𝑖
with probability 0/99 and 𝜉0𝐶)𝑖>
𝜉′0𝐶)𝑖with probability 0/01* independently.
We note that the semirandom model is more general than the random model* and the smoothed
model is more general than the semirandom model.
De”nition 1.2 $Weak* Strong and Tight refutation algorithms). @ refutation algorithm takes as
input a CSP instance 𝜙and outputs a value alg-val0𝜙) ∈*0/ 1\ with alg-val0𝜙) ⩾val0𝜙) for all 𝜙.
For a distribution 𝒟over 𝜙* we say that the refutation algorithm weYkly refutes instances drawn
from 𝒟if with high probability over 𝜙∼𝒟* alg-val0𝜙) = 1. We also deﬁne strong refutYtion
$alg-val0𝜙) = 1
𝛿for some absolute constant 𝛿= 0) and 𝜀-tight refutYtion $alg-val0𝜙) = val0𝜙) ˜ 𝜀*
where 𝜀is a parameter of the algorithm that can be made arbitrarily small) analogously.
1.1.1
;lgorithms for smoothed refutation
Our ﬁrst main result gives a $possibly sharp) trade-oﬀbetween running time and number of
constraints for strongly refuting smoothed CSP instances.
Theorem 1 $Smoothed refutation* informal Theorem 7.4). For every ℓ> ℓ0𝑛)* there is Y 𝑛𝑂0ℓ)-time
strong refutYtion Ylgorithm for smoothed CSPs with 𝑚⩾𝑚0 > ˆ𝑂0𝑛) ·
𝑛
ℓ
0 𝑡
2
1) constrYints. ThYt is* for Yny
CSP instYnce 𝜙with 𝑚⩾𝑚0 constrYints* with probYbility 0/99 over the smoothing 𝜙𝑠of 𝜙* the Ylgorithm
outputs alg-val0𝜙𝑠) ⩽1
𝛿for some Ybsolute constYnt 𝛿= 0.
3

<!-- pdf-page: 6 -->
Here* 𝑡> 𝑡0𝑃) ⩽𝑘is the ’degree of uniformity“ of 𝑃é the smYllest integer 𝑡⩽𝑘such thYt there is
no 𝑡-wise uniform distribution $Deﬁnition 7.3) on |±1|𝑘supported entirely on the sYtisfying Yssignments
𝑃101) ⊆|±1|𝑘.
In order to understand the trade-oﬀdescribed by the theorem* let us apply it to two examples.
Example 1.3. For 𝑘-S@T* 𝑃is the Boolean OR function. We thus have 𝑡0𝑃) > 𝑘* as the uniform
distribution on odd-parity strings is supported on 𝑃101) and is 0𝑘
1)-wise uniform. Our result
gives a polynomial time algorithm to strongly refute smoothed instances of 𝑘-S@T whenever the
number of constraints 𝑚⩾ˆ𝑂0𝑛
𝑘
2 ). More generally* for any 𝛿= 0* in time 2𝑂0𝑛𝛿) the algorithm
strongly refutes smoothed instances with ⩾ˆ𝑂0𝑛01 𝛿) 𝑘
2 ˜𝛿) constraints.
Example 1.4. Consider the ’Hadamard predicate“ 𝑃on 𝑘> 22𝑞1 bits where 𝑃0𝑥) > 1 if and only
if 𝑥is a codeword of the truncated Hadamard code* i.e.* 𝑥is a truth table of a linear function*
excluding the all 0—s function. Hadamard CSPs naturally appear in the design of query eﬂcient
PCPs. Here* 𝑡0𝑃) > 3 ≪𝑘* so our theorem gives a polynomial-time algorithm to strongly refute
smoothed instances of the Hadamard CSP with at least ˆ𝑂0𝑛1/5) constraints* and a 2𝑛𝛿-time algorithm
for instances with at least ˆ𝑂0𝑛1/5 𝛿02) constraints ∀𝛿∈00/ 1\.
Comparison with prior results. Theorem 1 can be directly compared to works on refuting random*
semirandom and smoothed $in the order of increasing generality) CSPs.
Building on [@OW15* BM16\* Raghavendra* Rao and Schramm [RRS17\ proved the same trade-
oﬀ$up to a polylog0𝑛) factor in 𝑚) between running time and number of constraints required as in
Theorem 1 for the signiﬁcantly simpler special case of fully rYndom CSPs – when the clause structure
and the literal patterns are chosen uniformly at random from the respective domains. Our result
shows that the same trade-oﬀholds for smoothed instances – i.e.* with worst-case clause structure and
small random perturbations of worst-case literal patterns. @ll known eﬂcient refutation algorithms*
including ours and that of [RRS17\* can in hindsight be interpreted as an analysis of the canonical
sum-of-squares $SoS) relaxation $Section 3.3) for the max 𝑘-CSP problem. For random CSPs $and
thus also for the more general smoothed instances we study) the trade-oﬀwe obtain is known to
be essentially tight [KMOW17* BCK15\ for such ’SoS-encapsulated“ algorithms: this fact is often
taken as evidence of sharpness of this trade-oﬀ.
Much less is known about refuting CSPs in the more general semirYndom and smoothed models.
Feige [Fei07\ gave a weYk refutation algorithm for refuting smoothed and semirandom instances of
3-S@T. His techniques apply to all 3-CSPs but do not seem to extend to either strong refutation or
4-CSPs. More recently* in a direct precursor to this work* @bascal* Guruswami and Kothari [@GK21\
gave a polynomial time algorithm for refuting semirYndom instances of all CSPs – thus obtaining one
of the extreme points $corresponding to ℓ> 𝑂01)) in the trade-oﬀin Theorem 1 above. Theorem 1
relies on a key idea from their work $row bucketing) along with several new ideas discussed below.
;lgorithms for refuting sejfp nboj 𝑘*XOR. Our main technical result is an algorithm for tight
refutation of semirYndom instances of 𝑘-XOR. Theorem 1 then follows by a simple blackbox reduction
$see Section 7) that relies on a dual polynomial introduced in [@OW15\. For the special case of
𝑘-XOR* an instance 𝜙is completely described by an arbitrary 𝑘-uniform instance hypergraph ℋand
a collection of ’right-hand sides“ 𝑏𝐶∈|±1|* one for each 𝐶∈ℋ; in the notation of Deﬁnition 1.1*
we have 𝑏𝐶> 𝑘
𝑖>1 𝜉0𝐶)𝑖. One can associate to 𝜙a homogeneous degree 𝑘polynomial 𝜙0𝑥) on the
4

<!-- pdf-page: 7 -->
hypercube |±1|𝑛:
𝜙0𝑥) > 1
𝑚

𝐶∈ℋ
𝑏𝐶

𝑖∈𝐶
𝑥𝑖/
This polynomial 𝜙0𝑥) computes the ’advantage over 102“ of an assignment 𝑥. That is* the value
of the associated instance is 1
2 ˜ 1
2 max𝑥∈|±1|𝑛𝜙0𝑥). Tight refutation corresponds to certifying that
𝜙0𝑥) ⩽𝜀for arbitrary 𝜀= 0.
Theorem 1.5 $Tight refutation of semirandom 𝑘-XOR* informal Theorem 5.1). For every 𝑘∈ℕYnd
ℓ> ℓ0𝑛) Ynd every 𝜀= 0* there is Y 𝑛𝑂0ℓ) time 𝜀-tight refutYtion Ylgorithm for homogeneous degree 𝑘
polynomiYls thYt succeeds with probYbility Yt leYst 0/99 over the drYw of the coeﬂcients i.i.d. uniform on
| 1/ 1|* whenever the YssociYted hypergrYph ℋhYs 𝑚⩾𝑛
𝑛
ℓ
𝑘
2
1 · poly0 log 𝑛
𝜀) hyperedges.
In pYrticulYr* for every 𝛿= 0* we obtYin Y 2𝑂0𝑛𝛿)-time 𝜀-tight refutYtion Ylgorithm for semirYndom
𝑘-XOR instYnces with 𝑚≫ˆ𝑂0𝑛) · 𝑛01 𝛿)0 𝑘
2
1) poly0 1
𝜀)-constrYints.
Prior works and brief comparison of techniques. The trade-oﬀabove $up to polylog0𝑛) factors in
𝑚) matches the one obtained for refuting fully random 𝑘-XOR [RRS17\. Our techniques* however*
necessarily need to be signiﬁcantly diﬀerent* as the analysis in [RRS17\ $and related works it built
on [CGL04* BM16* @OW15\) crucially rely on the randomness of the hypergraph ℋ. In particular*
the refutation in [RRS17\ uses the spectral norm of a certain ’symmetric tensor power“ of the
canonical matrix obtained from the instance. They analyze this matrix using a technical tour-de-force
argument using the trace moment method.4 @ couple of follow-up works have attempted to simplify
the analyses in [RRS17\. Wein* @laoui and Moore [W@M19\ succeeded in giving a simpler proof
$introducing the Kikuchi mYtrix* a variant of which is central to this work) for the case of random
𝑘-XOR for even 𝑘* and they also suggest that a natural generalization of their Kikuchi matrix for
random odd 𝑘will work $their suggestion does not pan out* as we prove in @ppendix @). In a recent
work* @hn [@hn20\ simpliﬁed some aspects of the analysis of the ’symmetric tensor power“ matrix
in the analysis of [RRS17\. To summarize* the tools in prior works on random CSPs for analyzing
the spectra of relevant correlated random matrices seem to use the randomness of the hypergraph
both heavily and in a rather opaque manner.
For the more general setting of semirandom 𝑘-XOR refutation* the best known result [@GK21\
obtained an extreme point in the trade-oﬀ$i.e.* the case of ℓ> 𝑂01)). That work analyzes the
∞→1-norm of the canonical matrix associated with the CSP instance. In this special case when
ℓ> 𝑂01)* it turns out that handling 3-XOR instances allows deriving all larger 𝑘as a corollary. For
the case of 3-XOR* their analysis relies on a new row bucketing step according to the butterﬁy degree of
a pair of vertices $a new notion that they deﬁne)* along with a certain pseudo-random vs structure
decomposition for arbitrary 3-uniform hypergraphs associated with the 3-XOR instance.
To prove Theorem 1.5* we build on [@GK21\ and introduce a few new tools. For even 𝑘*
the Kikuchi matrix of [W@M19\ analyzed using the row bucketing idea $with an appropriate
generalization of the butterﬁy degree) of [@GK21\ yields a correct trade-oﬀ$see Sections 2.1 and 2.2).
The case of odd 𝑘turns out to be signiﬁcantly more challenging $as has always been the case in CSP
refutation) and needs new ideas. We introduce a variant of the Kikuchi matrix for this purpose.
Unlike the case of even 𝑘$and the algorithm in [@GK21\)* the spectral norm of this matrix is
provably too large to yield a refutation – even for rYndom instances. Indeed* this is why the strategy
4Just the technical argument in [RRS17\ runs over 20 pages
5

<!-- pdf-page: 8 -->
suggested by [W@M19\ does not pan out* as we show in @ppendix @. Instead* we use the spectral
norm of a matrix obtained by pruning away appropriately chosen rows. We then show that the
number of pruned rows is not too large* and so does not contribute too much to the ∞→1-norm of
the full matrix.
The row pruning step motivates a deﬁnition of regulYrity* a collection of natural pseudorandom
properties that relate to well-spreYdness in the intersection structure of the hyperedges in the instance
hypergraph.5 We then show that the hyperedges in every 𝑘-uniform hypergraph can be decomposed*
via a regulYrity decomposition lemma* into 𝑘′-uniform hypergraphs for 𝑘′ ⩽𝑘* along with some
’error“ hyperedges* such that $i) each of the 𝑘′-uniform hypergraphs satisﬁes regularity* and $ii)
refuting all of these 𝑘′-XOR instances provides a refutation for the original instance. We explain our
row pruning and the regularity decomposition steps in more detail in Section 2.
1.1.2
Short refutations below spectral threshold: proving Feige{s conjecture
In a one-of-a-kind result* Feige* Kim and Ofek [FKO06\ $henceforth* FKO) proved that with high
probability over the draw of a fully random 3-S@T instance 𝜓* there is a polynomial size witness
that weakly refutes 𝜓if 𝜓has 𝑚∼ˆ𝑂0𝑛1/4) constraints. Formally* there is a polynomial time
non-deterministic refutation algorithm that succeeds in ﬁnding a refutation with high probability
over the drawn of a fully random 3-S@T instance with 𝑚∼ˆ𝑂0𝑛1/4) constraints. On the other hand*
all known polynomial time deterministic refutation algorithms require the input random instance
to have Ω0𝑛1/5) constraints – this bound is often called the spectrYl threshold. The fastest known
refutation algorithm [RRS17\ for instances with ∼𝑛1/4 constraints runs in time 2𝑛0/2* matching the
SoS lower bound [KMOW17\. Thus* intriguingly* the FKO result shows the existence of polynomial
time veriﬁable refutation witnesses $i.e.* certiﬁcates of an upper bound of 1
𝑜𝑛01) on the value) at
a constraint density at which there are no known 2𝑛𝑜01)-time refutation algorithms. Does such a
’gap“ between thresholds for existence vs eﬂcient computability of refutation witnesses persist for
semirandom and smoothed instances* i.e.* instances with worst-cYse constraint hypergraphs<
In 2008* Feige [Fei08\ made an elegant conjecture on the existence of even covers in suﬂciently
dense hypergraphs. This conjecture can be interpreted as generalizing to hypergraphs the classical
Moore bound on the girth of graphs with a given number of edges. If true* Feige—s conjecture
implies that the FKO result holds for all semirandom and smoothed CSP instances – in particular*
the FKO result does not rely on the properties of the underlying hypergraph at all. Let us explain
this conjecture below.
De”nition 1.6 $Even Cover and Girth). For a 𝑘-uniform hypergraph ℋon *𝑛\* an even cover of
length 𝑡is a collection of 𝑡distinct hyperedges 𝐶1/ 𝐶2/ / / / / 𝐶𝑡in ℋsuch that every vertex in *𝑛\
appears in an even number of 𝐶𝑖—s. The girth of ℋis the length of the smallest even cover in ℋ.
Conjecture 1.7 $Feige—s conjecture* Conjecture 1.2 in [Fei08\). Every 𝑘-uniform hypergrYph ℋon *𝑛\
with 𝑚⩾𝑚0 > 𝑂0𝑛)
𝑛
ℓ
𝑘
2
1 hyperedges hYs Yn even cover of length 𝑂0ℓlog 𝑛).
; brief history of the conjecture. For 𝑘> 2* an even cover is a 2-regular subgraph $and thus a
union of cycles) in a graph and thus* the conjecture above reduces to the question of determining
the maximum girth $the length of the smallest cycle) in a graph with 𝑛vertices and 𝑛𝑑02 edges for
5This is closely related to the notion of spread encountered in recent work on the sunﬁower conjecture [@LWZ20* Rao19\.
6

<!-- pdf-page: 9 -->
parameter 𝑑. The best known bound is due to @lon* Hoory and Linial [@HL02\ who proved that for
every graph on 𝑛vertices with 𝑛𝑑02 edges for 𝑑= 2* there is a cycle of length at most 𝑐log𝑑1 𝑛for
𝑐⩽2. The best known lower bound on the girth is 𝑐log0𝑑1) 𝑛for 𝑐⩾403 by Margulis [Mar88\ and
Lubotzky* Philips and Sarnak [LPS88\ via explicit constructions of Ramanujan graphs. Obtaining a
tight bound on 𝑐has been an outstanding open problem for the last 3 decades.
Much less is known for hypergraphs. When 𝑘even and ℓ> 𝑂01)* Naor and Verstraete [NV08\
proved the conjecture. They were motivated by a natural coding theory interpretation: viewing
each hyperedge as describing the non-zero coeﬂcients of linear equations over 𝔽2* an even cover is
a spYrse lineYr dependency and thus* the conjecture gives the rate-distance trade-oﬀfor linear codes
with column-sparse parity check matrices. In the more challenging case when 𝑘is odd* the bounds
for ℓ> 𝑂01) case in [NV08\ were improved to essentially optimal ones in [Fei08\. For ℓ≫1* the best
previous bound for 3-uniform hypergraphs is due to a simple argument of @lon and Feige [@F09\
$Lemma 3.3)* who proved that every 3-uniform hypergraph with ˆ𝑂0𝑛20ℓ) hyperedges has an even
cover of size ℓ$this is oﬀby ∼]𝑛factor in 𝑚). For 3-uniform hypergraphs with 𝑚≫𝑛1/5˜𝜀$and the
case when 𝑚≫𝑛𝑘02 in general)* [JHL˜12\ proved that there are even covers of size 𝑂010𝜀). Finally*
Feige and Wagner [FW16\ proved some variants $’generalized girth problems“) in order to build
tools to approach this conjecture.
To summarize* prior to this work* the conjecture was known to be true only for ℓ> 𝑂01). For
larger ℓ* the only approach was the combinatorial strategy introduced in [FW16\. In this work* we
prove Feige—s conjecture $up to poly log 𝑛slack in 𝑚) via a new spectrYl double counting Yrgument.
Theorem 2 $Feige—s conjecture is true* informal Theorem 8.2). For every 𝑘∈ℕYnd ℓ> ℓ0𝑛)* every
𝑘-uniform hypergrYph ℋwith 𝑚⩾𝑚0 > ˆ𝑂0𝑛) · 0 𝑛
ℓ)
𝑘
2
1 hyperedges hYs Yn even cover of size 𝑂0ℓlog 𝑛).
Our spectral double counting argument6 is heavily derived from our analysis for smoothed
refutation using our Kikuchi matrices; indeed* our proof of Theorem 8.2 mirrors our steps in the
analysis of our refutation algorithm. In fact* in a precise sense $as we explain in Section 2.3)* our
approach gives a tight connection between even covers in hypergraphs and simple cycles $and in
turn* the spectral norm of the corresponding adjacency matrix) in the ’Kikuchi graph“ built from
the hypergraph.
Combining with our smoothed refutation algorithms $Theorem 1) we immediately obtain
a generalization of the FKO result that yields a polynomial time non-deterministic refutation
algorithm for smoothed instances of all 𝑘-ary CSPs with number of constraints 𝑚polynomially
below the spectral threshold of 𝑛𝑘02.
Theorem 3 $Informal Theorem 9.2). There is Y non-deterministic polynomiYl time Ylgorithm thYt weYkly
refutes smoothed instYnces of Yny 𝑘-CSP with 𝑚⩾𝑚0 > ˆ𝑂0𝑛
𝑘
2
𝑘2
20𝑘˜8) )-constrYints. For the speciYl cYse of
𝑘> 3* 𝑚0 > ˆ𝑂0𝑛1/4).
6Subsequent to our posting of this paper* Tim Hsieh and Sidhanth Mohanty were able to use our spectral double
counting technique with the non-backtracking walk matrix of a graph to recover the sharpest known result $match-
ing [@HL02\) for the Moore bound for irregular graphs. We believe a similar approach might also help achieve sharper
results for size of smallest even covers in hypergraphs.
7

<!-- pdf-page: 10 -->
2
Overview of our Techniques
In this section* we illustrate our key ideas by giving essentially complete proofs of some special
cases of our main results along with expository comments.
This overview is structured as follows: we will ﬁrst give an essentially complete proof for
refuting semirYndom instances of even-Yrity 𝑘-XOR. @s has been the trend in all the refutation results*
the even-arity case happens to be signiﬁcantly simpler but allows us to showcase two key ideas:
1) The power of the Jikuchi matrix.
In fact* this work can be thought of as a paean to the
beautiful structure and the applications of the Kikuchi matrix and its variant that we introduce
for odd-arity 𝑘-XOR. Combined with the row bucketing idea from [@GK21\* we can easily resolve
the case of even arity 𝑘-XOR. The Kikuchi matrix was introduced by [W@M19\ to give a simpler
proof of the result of [RRS17\ for refuting fully rYndom instances of even-Yrity 𝑘-XOR. They left open
the question of ﬁnding an analogous proof for the odd-arity case $again* for fully random CSPs)
and even suggested an approach. Their approach* however* does not pan out* as we prove in
@ppendix @. Our Kikuchi matrix for the odd-arity case along with our analysis technique $that
does not directly work with spectral norms) allows us to prove sharp trade-oﬀs for refuting random
CSPs and with additional ideas* make them work even for the signiﬁcantly randomness starved
semirandom and smoothed settings.
2) The connection between ’Jikuchi matrix refutations“ and even covers in hypergraphs.
In
this overview* we will use this connection to give a single page proof of Feige—s conjecture for
𝑘-hypergraphs for 𝑘even. We note that this gives an interesting instance of the phenomenon
where the analysis of an algorithm in a reduced-randomness setting can be used to infer a purely
combinatorial property of worst-case structures.
We will then discuss our ideas for the odd-arity case at a high-level by focusing on 3-XOR. @s
is usual in CSP refutation* even for the special case of fully rYndom instances* refuting odd-arity
XOR is signiﬁcantly more challenging [CGL04* BM16* @OW15\. We introduce several new ideas
to tackle the semirandom $and thus also the smoothed) case: $1) a new* suitable variant of the
Kikuchi matrix* $2) the idea of row pruning combined with row bucketing* and $3) a new regulYrity
decomposition for arbitrary hypergraphs.
Our proof of Feige—s conjecture for odd-𝑘-uniform hypergraphs is conceptually similar to the
even case – in that it mimics the refutation argument closely – but needs all the new machinery for
refutation introduced above for handling semirandom odd-arity 𝑘-XOR and must use the trace
moment method $instead of the matrix Bernstein) in the step that upper bounds the spectral norm of
appropriate sequence of matrices produced in our analysis. The combinatorial argument required
in analyzing the trace method turns out to be somewhat more intricate in the odd arity case. We
will not discuss it in this overview.
Our reduction from smoothed CSP refutation to semirandom CSP refutation is short and
elementary* and we present it in full in Section 7. We will not discuss this argument in this overview.
2.1
Random 4*XOR via the Jikuchi matrix of YW;M19\
Let—s start by deﬁning the Kikuchi matrix and showing how it gives a simple refutation algorithm
with the optimal trade-oﬀfor random instances of even-arity 𝑘-XOR. We will focus on 𝑘> 4 here.
8

<!-- pdf-page: 11 -->
De”nition 2.1 $Kikuchi Matrix). Let 𝑁>
𝑛
ℓ
. For a 4-XOR instance described by ℋand 𝑏𝐶—s for
𝐶∈ℋ* we deﬁne the matrices 𝐴𝐶∈ℝ𝑁·𝑁for each 𝐶∈ℋas follows. Let 𝐴𝐶∈ℝ𝑁·𝑁be the
matrix indexed by all possible subsets of *𝑛\ of size exactly ℓ. The entry of 𝐴𝐶at any 0𝑆/ 𝑇) where
𝑆/ 𝑇∈
*𝑛\
ℓ
is deﬁned by:
𝐴𝐶0𝑆/ 𝑇) >

𝑏𝐶
if 𝑆± 𝑇> 𝐶
0
otherwise
Here* 𝑆± 𝑇is the symmetric diﬀerence of the sets 𝑆/ 𝑇. The level ℓKikuchi matrix of the instance is
then simply 𝐴> 
𝐶∈ℋ𝐴𝐶.
Ruadratic forms of the Jikuchi matrix. The quadratic forms of this matrix are closely related to
the polynomial 𝜙0𝑥) associated with the input 4-XOR instance: namely* 𝜙0𝑥) :> 1
𝑚

𝐶∈ℋ𝑏𝐶

𝑖∈𝐶𝑥𝑖.
Notice that the non-zero entries of the matrix 𝐴correspond to pairs of sets 0𝑆/ 𝑇) such that the
symmetric diﬀerence of 𝑆/ 𝑇is one of the clauses in the input 4-XOR instance. Observe that if
𝑆± 𝑇> 𝐶* then ~𝑆∩𝐶~ > 2* ~𝑇∩𝐶~ > 2* and ~𝑆∩𝑇~ > ℓ
2. In particular* each 𝑏𝐶appears in
4
2
·
𝑛4
ℓ2
diﬀerent entries of 𝐴. Now* let 𝑥⊙ℓbe the
𝑛
ℓ
-dimensional vector of degree ℓmonomials
in 𝑥. That is* the entries of 𝑥⊙ℓare indexed by subsets of size ℓof *𝑛\ and the 𝑆-th entry of 𝑥⊙ℓis
given by 
𝑖∈𝑆𝑥𝑖. Then* we must have:
4
2

·
𝑛
4
ℓ
2

𝜙0𝑥) > 1
𝑚

𝑥⊙ℓ⊤
𝐴𝑥⊙ℓ
$2.1)
This immediately provides a certiﬁcate of upper bound on the value of the input instance as it
must hold that
max
𝑥∈| 1/1|𝑛𝜙0𝑥) ⩽
1
6𝑚·
𝑛
4
ℓ
2
1𝑛
ℓ

}𝐴}2 ⩽𝑂
𝑛2
𝑚ℓ2

· }𝐴}2 /
$2.2)
where }𝐴}2 is the spectral norm of the matrix 𝐴. If we can show that }𝐴}2 ⩽ˆ𝑂0ℓ) w.h.p. over the
draw of the hypergraph ℋand the 𝑏𝐶—s* then* whenever 𝑚≫ˆ𝑂0𝑛) · 𝑛
ℓ* the spectral norm of 𝐴
provides a certiﬁcate that 𝜙0𝑥) ⩽0/01 for every 𝑥∈|±1|𝑛.
It is in the ease of establishing such an upper bound on the spectral norm that the choice of
Kikuchi matrix really shines Observe that 𝐴𝐶—s are a sequence of independent* rYndom matrices
and thus* one can try to apply oﬀ-the-shelf matrix concentration inequalities to bound the spectral
norm of 𝐴. Instead of using the matrix Chernoﬀinequality as in [W@M19\* we will use the matrix
Bernstein inequality below as it turns out to generalize better. We also give a completely elementary
trace moment based proof of the same fact $see Section 6.4.2).
Fact 2.2 $Matrix Bernstein Inequality). Let 𝑀1/ 𝑀2/ / / / / be independent rYndom 𝑁· 𝑁mYtrices with
meYn 0 such thYt }𝑀𝑖}2 ⩽𝑅Ylmost surely. Let 𝜎2 > max|
𝔼*
𝑖𝑀𝑖𝑀⊤
𝑖\

2 /
𝔼*
𝑖𝑀⊤
𝑖𝑀𝑖\

2| be the
variance term. Then* with probYbility Yt leYst 1
10𝑛100*


𝑖
𝑀𝑖

2
⩽𝑂0𝑅log 𝑁˜ 𝜎

log 𝑁) /
Spectral norm of the Jikuchi matrix. Let—s analyze }𝐴}2 using this inequality. First* observe that
any row of 𝐴𝐶has at most 1 non-zero entry of magnitude 1. Since the spectral norm of a symmetric
9

<!-- pdf-page: 12 -->
matrix is upper bounded by the maximum ℓ1-norm of any of its rows* this immediately yields
that }𝐴𝐶}2 ⩽1. Let—s now compute the ’variance“ term. Here—s the key observation about the
Kikuchi matrix that makes this analysis so simple: the matrix 𝐴2
𝐶is diYgonYl for every 𝐶. To see this*
observe that the entry at any 0𝑆/ 𝑇) of this matrix is given by 
𝑈𝐴𝐶0𝑆/ 𝑈)𝐴𝐶0𝑈/ 𝑇). @ term in the
summation is non-zero only if 𝑆± 𝑈> 𝑈± 𝑇> 𝐶which can happen if and only if 𝑇> 𝑆.
Let—s now compute the diagonals of 𝔼
𝐶𝐴2
𝐶. Notice that 𝐴2
𝐶0𝑆/ 𝑆) equals either 1 or 0 for every
𝐶. Thus* 
𝐶𝐴2
𝐶0𝑆/ 𝑆) > deg0𝑆) where
deg0𝑆) :> ~|𝐶~ ~𝑆∩𝐶~ > 2|~ /
and so the variance term 𝜎2 is max𝑆deg0𝑆).
How large can this be< Since each constraint contributes
4
2
·
𝑛4
ℓ2
non-zero entries to 𝐴*

𝑆∈0𝑛
ℓ) deg0𝑆) >
4
2
·
𝑛4
ℓ2
𝑚. Thus* on average deg0𝑆) is ≈𝑚ℓ20𝑛2. When 𝑚∼𝑛20ℓ* this is ∼ℓ.
When ℋis a rYndom hypergrYph with ∼𝑛20ℓhyperedges* we expect deg0𝑆) to not deviate too
much from its expectation. In fact* using the Chernoﬀbound yields deg0𝑆) ⩽𝑂0ℓlog 𝑛) for all 𝑆
whp. Since 𝑁>
𝑛
ℓ
* this yields that }𝐴}2 ⩽𝑂0log 𝑁) ˜ 𝑂0

ℓlog 𝑛· log 𝑁) > ˆ𝑂0ℓ)* as desired.
2.2
Semirandom instances of 4*XOR via row bucketing from Y;GJ21\
Let us now conduct a post-mortem of the above proof to see where we used the randomness of
the hypergraph ℋ. Even after ﬁxing ℋ* the 𝐴𝐶—s are independent random matrices* with all the
randomness coming from the 𝑏𝐶—s. Thus* we can still apply the matrix Bernstein inequality. The
only point in the proof where we used the randomness of the hypergraph ℋwas to establish that
deg0𝑆) > 𝑂0ℓlog 𝑛) for every 𝑆. So* our proof immediately extends to semirandom instances where
the instance hypergraph ℋis such that deg0𝑆) > 𝑂0ℓlog 𝑛) for every 𝑆.
This bound is delicate: when deg0𝑆) > Ω0ℓ2)* we obtain no non-trivial refutation guarantee and
even deg0𝑆) ∼ℓ1/1 results in a suboptimal trade-oﬀ. On the other hand* in arbitrary ℋ* deg0𝑆) can
be as large as 𝑚$but no larger). Further* this is a ’real“ issue $and not an artefact of the use of
Matrix Bernstein inequality): when deg0𝑆) is large* so is the spectral norm of 𝐴.
Jey observation: only sparse vectors cause large quadratic forms. Our way forward builds on
that of [@GK21\ who recently gave a polynomial time algorithm for $strongly) refuting semirandom
instances of 𝑘-XOR with ⩾ˆ𝑂0𝑛𝑘02) constraints. The key observation is when deg0𝑆) is large* the
spectral norm of 𝐴is high but intuitively* the ’oﬀending“ large quadratic forms are induced only by
’sparse“ vectors* i.e.* vectors where the ℓ2 norm is contributed by a small fraction of the coordinates.
On the other hand* we only care about upper bounding quadratic forms of 𝐴on vectors where all
coordinates are ±1 and are thus are maximally ’non-sparse“ or ’ﬁat“.
Row bucketing. We can formalize this observation via row bucketing. Let 𝑑0 ∼𝑚· ℓ20𝑛2 be the
average value of deg0𝑆). Let—s partition the row indices in
𝑛
ℓ
into multiplicatively close buckets
ℱ0/ ℱ1/ · · · / ℱ𝑡so that for each 𝑖⩾1*
ℱ𝑖> 
𝑆~ 2𝑖1𝑑0 = deg0𝑆) ⩽2𝑖𝑑0

/
and ℱ0 > 
𝑆~ deg0𝑆) ⩽𝑑0

. Then* since deg0𝑆) ⩽𝑚and 𝑑0 ⩾1 $as 𝑚∼𝑛20ℓ)* we can take
𝑡⩽log2 𝑚. Further* by Markov—s inequality* ~ℱ𝑖~ ⩽2 𝑖𝑛
ℓ
> 2 𝑖𝑁. For each 𝑖/ 𝑗⩽𝑡* let 𝐴𝑖/𝑗be the
10

<!-- pdf-page: 13 -->
matrix obtained by zeroing out all rows not in ℱ𝑖and all columns not in ℱ𝑗from the Kikuchi matrix
𝐴. Then* 𝐴> 
𝑖/𝑗⩽𝑡𝐴𝑖/𝑗.
The key observation is the following: while 𝐴𝑖/𝑗has non-zero rows and columns where deg0𝑆)
is larger by a 2𝑖$2𝑗* respectively) factor than the average* we are compensated for this by a reduction
in the number of non-zero rows and columns.
Let 𝑦∈ℝ𝑁be any vector with entries in |±1|𝑁* and let 𝑦ℱ𝑖be the vector obtained by zeroing
out all coordinates of 𝑦that are not indexed by elements of ℱ𝑖. Then* by Cauchy-Schwarz* we must
have:
max
𝑦∈|±1|𝑁𝑦⊤𝐴𝑖/𝑗𝑦>
max
𝑦∈|±1|𝑁0𝑦ℱ𝑖)⊤𝐴𝑖/𝑗0𝑦ℱ𝑗) ⩽

~ℱ𝑖~~ℱ𝑗~ ·
𝐴𝑖/𝑗

2 /
$2.3)
We apply the Matrix Bernstein inequality in a similar manner to the previous analysis. The
’variance“ term grows by a factor of max|2𝑖/ 2𝑗| over the bound obtained for the random case.
@s a result* the spectral norm of 𝐴𝑖/𝑗is higher by a factor of max|2𝑖02/ 2𝑗02|. On the other hand*
the eﬀective ℓ2 norm of the vector drops by 2 0𝑖˜𝑗)02. The trade-oﬀ’breaks in our favor“ and the
dominating term in the bound is 𝐴0/0 – the spectral norm of which is at most of the same order as that
of the 𝐴in the case of the previous random 4-XOR analysis We thus obtain that max𝑦∈|±1|𝑁𝑦𝑇𝐴𝑦
is ˆ𝑂0 𝑛2
𝑚ℓ2 · ℓ)* and so we certify that 𝜙0𝑥) ⩽0/01 for every 𝑥∈|±1|𝑛.
2.3
Proving Feige{s conjecture for 4*uniform hypergraphs
We now discuss how the analyses of the Kikuchi matrix from the previous section relates to Feige—s
conjecture on even covers in 4-uniform $and in general* any even-uniform) hypergraphs. @ priori*
such a connection may appear rather surprising that the analysis of a super-polynomial size matrix
introduced for refuting 𝑘-XOR can shed light on a purely combinatorial fact. But we will soon see
that this is yet another instance of the Kikuchi matrix doing its magic.
Recall that Feige—s conjecture suggests a trade-oﬀbetween the number of hyperedges and an
appropriate notion of girth $i.e.* length of the smallest cycle* or even cover) in hypergraphs that
generalizes the classical Moore bound [@HL02\* which asserts that every graph on 𝑛vertices with
𝑛𝑑02 edges has a cycle of length ⩽2 log𝑑10𝑛). To explain our spectrYl double counting argument
to prove this conjecture* it is helpful to ﬁrst use it to prove a $signiﬁcantly weaker) version of the
Moore bound and then generalize to hypergraphs 𝐻via the ’Kikuchi graph“ derived from 𝐻.
Proposition 2.3 $Weak Moore bound in irregular graphs). Every grYph 𝐺on 𝑛vertices Ynd 𝑛𝑑02 edges
for 𝑑⩾𝑂0log3
20𝑛)) hYs Y cycle of length ⩽2⌈log2 𝑛⌉.
Our spectrYl double counting argument counts the number of edges of 𝐺in two diﬀerent ways: let
𝐴be the 0-1 adjacency matrix of 𝐺. Then* we have 1⊤𝐴1 > 𝑛𝑑. We will show that if 𝐺does not
have a cycle of size ⩽2⌈log2 𝑛⌉* then* all ±1-coordinate quadratic forms of 𝐴are at most 𝑛· ˆ𝑂0
]
𝑑).
Together* these two bounds yields the desired contradiction.
ClYim 2.4 $Trace Method in the absence of even covers). Let 𝐴be the 0-1 adjacency matrix of a
graph 𝐺on 𝑛vertices with 𝑛𝑑02 edges with no cycle of length ⩽2𝑟for 𝑟> ⌈log2 𝑛⌉. Then* for every
𝑦∈|±1|𝑛*
𝑦⊤𝐴𝑦⩽𝑛
]
𝑑· 𝑂0log1/5
2 0𝑛)) /
Notice that this claim immediately yields a contradiction if 𝑛𝑑= 𝑛
]
𝑑· 𝑂0log1/5
2 0𝑛))* which holds
if 𝑑⩾𝑂0log3
2 𝑛)* thus proving Proposition 2.3. Let—s now see how to prove this claim.
11

<!-- pdf-page: 14 -->
Proof. The average degree of vertices in 𝐺is 𝑑. Let ℱ𝑖> |𝑣~ 2𝑖𝑑⩽deg0𝑣) ⩽2𝑖˜1𝑑| for each
1 ⩽𝑖⩽log2 𝑛. Let 𝐴𝑖/𝑗be obtained by zeroing out all rows not in ℱ𝑖and all columns not in ℱ𝑗from
𝐴. Then* 𝐴> 
𝑖/𝑗𝐴𝑖/𝑗.
By a similar observation as in the previous subsection* we have:
𝑦⊤𝐴𝑦⩽

𝑖/𝑗

~ℱ𝑖~~ℱ𝑗~
𝐴𝑖/𝑗

2 /
$2.4)
Let—s now bound
𝐴𝑖/𝑗

2. The idea is to use the trace moment method on the matrix 𝐴𝑖/𝑗: for
every 𝑟* tr00𝐴𝑖/𝑗𝐴⊤
𝑖/𝑗)𝑟) ⩾
𝐴𝑖/𝑗
2𝑟
2 . This method is typically employed in analyzing the spectral norm
of rYndom matrices. But notice that 𝐴𝑖/𝑗is a ﬁxed matrix – nothing random in it. Nevertheless* our
key observation is if 𝐺has no cycle of length ⩽2𝑟* then one can derive the same exYct upper bound
on tr0𝐴2𝑟
𝑖/𝑗) Ys if it wYs Y rYndom ’signing“ of the adjacency matrix of 𝐺.
We have:
tr00𝐴𝑖/𝑗𝐴⊤
𝑖/𝑗)𝑟) >

𝑣1/𝑣2/////𝑣2𝑟∈*𝑛\
𝐴𝑖/𝑗0𝑣1/ 𝑣2)𝐴𝑖/𝑗0𝑣3/ 𝑣2) · · · 𝐴𝑖/𝑗0𝑣2𝑟1/ 𝑣2𝑟)𝐴𝑖/𝑗0𝑣1/ 𝑣2𝑟) /
The term corresponding to 0𝑣1/ 𝑣2/ / / / / 𝑣2𝑟) contributes a non-zero value $of at most 1) to the right
hand side above only if the sequence |𝑣𝑖/ 𝑣𝑖˜1| is an edge* say 𝑒𝑖in 𝐺for each 𝑖⩽2𝑟. Consider
now the multiset of edges 𝐸′ > |𝑒1/ 𝑒2/ / / / / 𝑒𝑟|. Since these are edges on a walk* viewing the 𝑒𝑖—s as
subsets of *𝑛\ of size exactly 2* we must have that ±2𝑟
𝑖>1𝑒𝑖> 0. Let—s now prune 𝐸′ by removing any
𝑒𝑖/ 𝑒𝑗that are equal. We must be able to remove all edges in this procedure* as otherwise we are left
with a 2-regular induced subgraph inside 𝐺* and so 𝐺must have a cycle of length ⩽2𝑟. Thus* each
edge of 𝐺occurs an even number of times in the multiset 𝐸′.
Let—s now use this observation to count the number of returning walks beginning with a ﬁxed
vertex 𝑣1. For each edge* we ’match“ its ﬁrst occurrence along the walk with the last occurrence.
There are 02𝑟)
𝑟2𝑟diﬀerent ways to select this matching. Given a matching* there are at most 𝑟distinct
choices of edges to be made. We make these choices inductively along the path from 𝑣1 to 𝑣2𝑟. @t
each step we can make a new choice $i.e.* we are not traversing an edge that is already matched to a
previously chosen edge) given our previous choices* there are at most Δ > max|2𝑖/ 2𝑗|𝑑choices for
the edge. Summing up over all choices for 𝑣1* we obtain that the number of non-zero contributing
2𝑟length walks is at most 𝑛· Δ𝑟2𝑟𝑟. Thus*
𝐴𝑖/𝑗

2 ⩽max|2𝑖02/ 2𝑗02| · 𝑛102𝑟𝑑1022102]
𝑟⩽2𝑑102 max|2𝑖02/ 2𝑗02|

2 log2 𝑛/
for 𝑟> 2⌈log2 𝑛⌉and large enough 𝑛.
Plugging back in $2.4) yields that
𝑦⊤𝐴𝑦⩽2

𝑖⩽𝑗
2 0𝑖˜𝑗)02𝑛2𝑗02 ·

2𝑑log2 𝑛⩽𝑛𝑑102𝑂0log1/5
2
𝑛) /
Let—s summarize the idea of the proof: analyzing the quadratic forms on the hypercube of
adjacency matrix with row bucketing yields a $signiﬁcantly weaker but still non-trivial) bound
on the girth of a graph with a given number of edges. This argument can possibly be sharpened
12

<!-- pdf-page: 15 -->
$to only an absolute constant factor loss) by switching to the non-backtracking walk matrix of 𝐺
$instead of the adjacency matrix) and dropping the row bucketing step. The above loose argument*
however* generalizes to hypergraphs as we show below.
Lemma 2.5 $Feige—s Conjecture for 4-Uniform Hypergraphs). Every 4-uniform hypergrYph ℋon *𝑛\
with 𝑚⩾𝑂0 𝑛2
ℓlog3
2 𝑛) hyperedges hYs Yn even cover of length 𝑂0ℓlog2 𝑛).
For every 𝐶∈ℋ* let 𝑏𝐶> 1 and consider the Kikuchi matrix 𝐴of the 4-XOR instance speciﬁed
by ℋand 𝑏𝐶—s. Equivalently* 𝐴is simply the adjacency matrix of the ’Kikuchi graph“ on vertex set
*𝑛\
ℓ
where edges correspond to pairs 0𝑆/ 𝑇) such that 𝑆± 𝑇> 𝐶for some 𝐶∈ℋ. The idea is to
repeat the argument for the adjacency matrix above but this time on the Kikuchi graph. The ’win“
in this scheme is a reduction of the problem on hypergraphs to a related problem on the associated
Kikuchi graph that is signiﬁcantly easier to reason about.
@s in the previous section* each 𝐶∈ℋcorresponds to
4
2
·
𝑛4
ℓ2
diﬀerent non-zero entries in 𝐴
and in particular* we have for 𝑥> 1𝑛*
0𝑥⊙ℓ)⊤𝐴𝑥⊙ℓ> 6
𝑛
4
ℓ
2

~ℋ~ /
Our proof exactly mirrors the proof of the above weak Moore bound for graphs. We will
show that if ℋhas no even cover of length 2𝑟for 𝑟> 0/5 log2 𝑁* then* 𝑦⊤𝐴𝑦⩽
𝑛
ℓ
ˆ𝑂0ℓ) for any
𝑦∈| 1/ 1|𝑁.
Let deg0𝑆) > ~|𝐶~ ~𝑆∩𝐶~ > 2|~. For every 𝑖⩽⌈log2 𝑚⌉* let ℱ𝑖> |𝑆~ 2𝑖1𝑑0 = deg0𝑆) ⩽2𝑖𝑑0|
$ℱ0 > |𝑆~ deg0𝑆) ⩽𝑑0|) denote the 𝑖-th row bucket* where 𝑑0 ∼𝑚ℓ20𝑛2. Note that deg0𝑆) ⩽𝑚and
𝑑0 ⩾1 so the number of buckets is indeed at most ⌈log2 𝑚⌉. Write 𝐴> 
𝑖/𝑗𝐴𝑖/𝑗where 𝐴𝑖/𝑗has all
rows not in ℱ𝑖and all columns not in ℱ𝑗zeroed out. We can now argue:
0𝑦⊤𝐴𝑦) ⩽

𝑖/𝑗
𝐴𝑖/𝑗

2 ·

~ℱ𝑖~~ℱ𝑗~ /
In the previous section* when 𝑏𝐶—s were independent* random bits* we used the matrix Bernstein
inequality to bound
𝐴𝑖/𝑗

2. Here* 𝑏𝐶—s are ﬁxed $and equal to 1) so* of course* that strategy cannot
work. Instead* our proof uses the trace moment method as in the proof of the weak Moore bound.
Proposition 2.6. Suppose ℋhYs no even cover of length 2𝑟for 𝑟⩽log2 𝑁. Then*
𝐴𝑖/𝑗

2 ⩽𝑂0ℓlog2 𝑛).
Proof of Proposition. @s before* we use
𝐴𝑖/𝑗
2𝑟
2 ⩽tr00𝐴𝑖/𝑗𝐴⊤
𝑖/𝑗)𝑟)) for any 𝑟∈ℕ. We then have:
tr00𝐴𝑖/𝑗𝐴⊤
𝑖/𝑗)𝑟)) >

𝑆1/𝑆2/////𝑆2𝑟∈0*𝑛\
ℓ)
𝐴𝑖/𝑗0𝑆1/ 𝑆2) · 𝐴𝑖/𝑗0𝑆3/ 𝑆2) · · · 𝐴𝑖/𝑗0𝑆2𝑟1/ 𝑆2𝑟)𝐴𝑖/𝑗0𝑆2𝑟˜1/ 𝑆2𝑟) /
where we adopt the convention that 𝑆2𝑟˜1 > 𝑆1. Let us now analyze the right hand side of this
equality. Each term in the RHS corresponds to a 2𝑟-tuple 0𝑆1/ 𝑆2/ / / / / 𝑆2𝑟) of sets from
*𝑛\
ℓ
and
contributes either 0 or 1.
If a term corresponding to 0𝑆1/ 𝑆2/ / / / / 𝑆2𝑟) contributes a ˜1* then* for each 𝑡⩽2𝑟* there
must be a 𝐶𝑡∈ℋsuch that 𝑆𝑡± 𝑆𝑡˜1 > 𝐶𝑡.
Thus* each non-zero term is in büection with
0𝑆1/ 𝐶1/ 𝐶2/ / / / / 𝐶2𝑟). On the other hand* we must have that ∅> ±2𝑟
𝑡>1𝑆𝑡± 𝑆𝑡˜1 > ±2𝑟
𝑡>1𝐶𝑡* as each 𝑆𝑡
13

<!-- pdf-page: 16 -->
appears twice in ±2𝑟
𝑡>1𝑆𝑡± 𝑆𝑡˜1* and thus the total symmetric diﬀerence is ∅. Hence* a non-zero term
0𝑆1/ 𝐶1/ 𝐶2/ / / / / 𝐶2𝑟) must satisfy ±2𝑟
𝑡>1𝐶𝑡> ∅.
Let us analyze such a 2𝑟-tuple of hyperedges. By removing equal pairs repeatedly as in the
previous proof* we can conclude that since ℋhas no even cover of length ⩽2𝑟* each hyperedge in
ℋoccurs an even number of times in the $multi)set |𝐶1/ 𝐶2/ / / / / 𝐶2𝑟|.
We now count the number of 0𝑆1/ 𝐶1/ / / / / 𝐶2𝑟) such that each 𝐶𝑡occurs an even number of times.
Since 𝐶𝑡—s occur in pairs* we can match the ﬁrst occurrence of the hyperedge in the ordered set
0𝐶1/ 𝐶2/ / / / / 𝐶2𝑟) to the last. There are ⩽2𝑟𝑟diﬀerent ways of selecting this matching. Given 𝑆1
and the matching* there are at most 𝑟unique 𝐶𝑡—s to choose. When making a choice of 𝐶𝑡$say)* 𝑆𝑡is
already determined by the previous choices. Thus* we have at most deg0𝑆𝑡) ⩽Δ :> max|2𝑖/ 2𝑗|𝑑0
unique choices for the hyperedge 𝐶. In total* there are ⩽𝑁· 2𝑟𝑟Δ𝑟non-zero terms* and so
𝐴𝑖/𝑗

2 ⩽𝑁102𝑟2102]
𝑟max|2𝑖02/ 2𝑗02|

𝑑0 ⩽max|2𝑖02/ 2𝑗02|2

log2 𝑁

𝑑0 /
for 𝑟> 0/5 log2 𝑁and large enough 𝑛.
The remaining calculation now mimics the one for
Proposition 2.3 $recalling that 𝑑0 ∼𝑚ℓ20𝑛2)* and ﬁnishes the proof of Lemma 2.5
2.4
Refuting semirandom 3*XOR via row pruning
The case of odd arity XOR refutation is lot more challenging. Even in the well-studied special case
of random CSP refutation and the special case of ℓ> 𝑂01) $i.e.* polynomial time refutation)* the
case of odd arity CSPs turns out to be signiﬁcantly more challenging than the even case. So let us
start by focusing on the case of random 3-XOR ﬁrst.
@s in the case of 4-XOR* we would like to begin by ﬁnding a simpler argument $compared to
[RRS17\) for the special case of rYndom 3-XOR using some appropriate variant of the Kikuchi matrix.
In fact* [W@M19\ attempted this by introducing a variant of the Kikuchi matrix* and suggested an
explicit approach $see Section F.1 of [W@M19\) to prove that the spectral norm of that matrix yields
a refutation* but this does not work $see @ppendix @). Indeed* we do not know of any reasonable
variant of the Kikuchi matrix whose spectral norm yields a refutation for even fully rYndom 3-XOR
instances with the expected trade-oﬀ.
Instead* we will introduce a variant of the Kikuchi matrix and use it to give a refutation algorithm
for rYndom 3-XOR instances by relying not on the spectral norm $which is too large) but* instead* the
spectral norm of a ’pruned“ version of the matrix. We will then discuss the remaining key ideas of
regulYrity decomposition combined with row bucketing to refute semirandom odd-arity XOR.
Bipartite 3*XOR. The Kikuchi matrix we introduce relates directly to a polynomial obtained by
applying the standard ’Cauchy-Schwarz trick“ to the input polynomial. Consider the polynomial
𝜓0𝑥) > 1
𝑚

𝐶∈ℋ𝑏𝐶𝑥𝐶associated with a 3-XOR instance described by a 3-uniform hypergraph ℋ
with 𝑚hyperedges and ’right-hand sides“ 𝑏𝐶—s. Here* for a set 𝑅we deﬁne 𝑥𝑅:> 
𝑖∈𝑅𝑥𝑖* and in
particular* 𝑥𝐶> 
𝑖∈𝐶𝑥𝑖. For each 𝐶∈ℋ* let 𝐶min be the minimum indexed element in 𝐶$using
the natural ordering on *𝑛\). Then*
max
𝑥∈|±1|𝑛𝜓0𝑥) ⩽
max
𝑥/𝑦∈|±1|𝑛
1
𝑚

𝐶∈ℋ
𝑏𝐶𝑦𝐶min𝑥𝐶]𝐶min /
where each 𝑦𝑢is formally a new variable* but we think of 𝑦𝑢as equal to 𝑥𝑢. Let us reformulate this
14

<!-- pdf-page: 17 -->
expression a bit: let ℋ𝑢> |𝐶~ 𝐶′ > 0𝐶/ 𝑢) ∈ℋ/ 𝐶′
min > 𝑢|. Then*
max
𝑥∈|±1|𝑛𝜓0𝑥) ⩽
max
𝑥/𝑦∈|±1|𝑛
1
𝑚

𝑢∈*𝑛\
𝑦𝑢

𝐶∈ℋ𝑢
𝑏𝑢/𝐶𝑥𝐶/
One can think of the RHS as the polynomial associated with a bipYrtite instance of the 3-XOR
problem on 2𝑛variables* since every constraint uses one 𝑦variable and two 𝑥variables. Our
refutation algorithm works for such bipartite instances more generally.
For such a bipartite instance* using the Cauchy-Schwarz inequality* we can derive:


1
𝑚

𝑢∈*𝑛\
𝑦𝑢

𝐶∈ℋ𝑢
𝑏𝑢/𝐶𝑥𝐶

2
⩽𝑛
𝑚2

𝑢

𝐶/𝐶′∈ℋ𝑢
𝑏𝑢/𝐶𝑏𝑢/𝐶′𝑥𝐶𝑥𝐶′
> 𝑛𝑚
𝑚2 ˜ 𝑛
𝑚2

𝑢

𝐶≠𝐶′∈ℋ𝑢
𝑏𝑢/𝐶𝑏𝑢/𝐶′𝑥𝐶𝑥𝐶′ :> 𝑛
𝑚˜ 𝑓0𝑥)
$2.5)
The ﬁrst term on the RHS is ⩽𝜀202 if 𝑚⩾2𝑛0𝜀2. The second term produces a ⩽4-XOR instance.
We thus end up with a 4-XOR instance – an even arity instance – albeit with signiﬁcantly less
randomness than required in the argument from previous section. So* we need some diﬀerent
tools to refute such instances. The ﬁrst of this is the following variant of the Kikuchi matrix that is
designed speciﬁcally for ’playing well“ with the symmetries produced by the squaring step above.
Our Jikuchi matrix. Our Kikuchi matrix is indexed by subsets of size ℓon a universe of size 2𝑛–
corresponding to two labeled copies of each of the original 𝑛𝑥variables. For each 𝐶∈ℋ* let 𝐶01)
be the subset of *𝑛\ · *2\ where every variable is labeled with ’1“* and similarly for 𝐶02). This trick
is done to ensure that the clauses 𝑥𝐶01)𝑥𝐶′02) form a 4-XOR instance* as now 𝐶01) and 𝐶′02) by deﬁnition
cannot intersect.
For even 𝑘* the ’independent“ pieces in the Kikuchi matrix were the matrices 𝐴𝐶* one for each
𝐶∈ℋ. For odd 𝑘* the independence pieces will be 𝐴𝑢– one for each 𝑦𝑢because of the loss of
independence due to the Cauchy-Schwarz step above.
De”nition 2.7 $Kikuchi Matrix* 3-XOR). Let 𝑁>
*2𝑛\
ℓ
. For every 𝑢∈*𝑛\* let 𝐴𝑢∈ℝ𝑁·𝑁be
deﬁned as follows: for each 𝑆/ 𝑇⊆*𝑛\ · *2\ of size ℓ* we will set 𝐴𝑢0𝑆/ 𝑇) to be non-zero if there are
𝐶/ 𝐶′ ∈ℋ𝑢such that 𝑆± 𝑇> 𝐶01) ± 𝐶′02) and 1 > ~𝑆∩𝐶01)~ > ~𝑆∩𝐶′02)~ > ~𝑇∩𝐶01)~ > ~𝑇∩𝐶′02)~.
That is* 𝐴𝑢0𝑆/ 𝑇) is non-zero if each of 𝑆/ 𝑇contain one variable from each of 𝐶01) and 𝐶′02). In that
case* we will set 𝐴𝑢0𝑆/ 𝑇) > 𝑏𝑢/𝐶· 𝑏𝑢/𝐶′. Finally* set 𝐴> 
𝑢𝐴𝑢.
Equivalently* 𝐴𝑢0𝑆/ 𝑇) is non-zero if there are 𝐶/ 𝐶′ ∈ℋ𝑢such that the 1-labeled $respectively*
2-labeled) elements in 𝑆/ 𝑇have symmetric diﬀerence 𝐶$𝐶′* respectively). This construction is
important for the success of our row pruning step $which we will soon discuss) and at the same
time ensures that every pair 0𝐶/ 𝐶′) of constraints in ℋ𝑢contributes an equal number of non-zero
entries in the Kikuchi matrix 𝐴. We note that if we do not introduce the 2 copies of each variable*
the number of times a pair 0𝐶/ 𝐶′) appears in the matrix would depend on ~𝐶∩𝐶′~.
The quadratic forms of 𝐴relate to the value of the underlying 4-XOR instance: for 𝐷> 4 2𝑛4
ℓ2
*
val0𝜙)2 ⩽𝑛
𝑚˜ val0 𝑓) ⩽𝑛
𝑚˜
𝑛
𝑚2𝐷0 max
 ∈|±1|𝑁 ⊤𝐴 ) /
15

<!-- pdf-page: 18 -->
Bounding  ⊤𝐴 . In the even arity case* we were able to obtain a refutation at this point by simply
using the spectral norm of 𝐴to bound the right hand side above. However* this turns out to
provably fail here. To see why* let us deﬁne the relevant notion of degree – the count of the number
of non-zero entries in each row of 𝐴𝑢:
deg0𝑆) > ~|𝐶/ 𝐶′ ∈ℋ𝑢~ ~𝑆∩𝐶01)~ > ~𝑆∩𝐶′02)~ > 1|~
If we were to apply the matrix Bernstein inequality* the ’almost sure“ upper bound on 𝐴𝑢for all 𝑢
is at least as large as ∼max𝑆

deg0𝑆) and it—s not too hard to show that there are 𝑆for which this
bound is at least ℓ. @s a result* the best possible spectral norm upper bound that we can hope to
obtain on 𝐴is Ω0ℓlog2 𝑁) > ˆΩ0ℓ2) – a bound that gives us no non-trivial refutation algorithm.
Row pruning. The key observation that ’rescues“ this bad bound is that deg0𝑆) cannot be large
for too many rows. To see why* consider the random variable that selects a uniformly random
𝑆∈
*2𝑛\
ℓ
and outputs deg0𝑆). This can be well approximated $for our purposes) by a random set
where every element is included independently with probability ∼ℓ02𝑛. The expectation of deg0𝑆)
on this distribution is 𝑂01). By relying on the fact that ~𝐶∩𝐶′~ > ∅in ℋ𝑢for almost all pairs with
high probability* Uar*deg0𝑆)\ > 𝑂01). @ Chernoﬀbound yields that the fraction of 𝑆for which
~|𝐶∈ℋ𝑢~ ~𝑆∩𝐶~ = 𝑂0log 𝑛)|~ is inverse polynomially small in 𝑛. @ union bound on all 𝑢then
shows the fraction of rows that are ’bad“ for any 𝑢is at most an inverse polynomial.
It turns out we can ignore such ’bad“ rows with impunity. This is because we are interested in
certifying upper bounds on quadratic forms of 𝐴over ’ﬁat“ vectors again and we can argue that
removing ’bad“ rows cannot appreciably aﬀect them. For the ’residual matrix“* we can now apply
the matrix Bernstein inequality and ﬁnish oﬀthe proof The execution here requires row bucketing
with respect to a combinatorial parameter called the butterﬁy degree $generalizing a similar notion
in [@GK21\) that controls the variance term in the analysis.
Extending to semirandom instances. Looking back* the previous analysis uses that the graphs
ℋ𝑢—s obtained from the random 3-uniform hypergraph ℋsatisfy a ’spread“ condition: there are
few to none distinct pairs 𝐶/ 𝐶′ ∈ℋ𝑢such that 𝐶∩𝐶′ ≠∅. This notion of regulYrity is the precise
pseudo-random property of ℋthat is enough for our argument $i.e. the row pruning step) above to
go through.
For the case of 3-XOR* such a regularity property is relatively easy to ensure by a certain ad hoc
argument: if too many pairs 𝐶/ 𝐶′ ∈ℋ𝑢happen to share a variable* then* ’resolving“ them yields a
system of 2-XOR constraints. Refutation in the special case of 2-XOR is easy using the Grothendieck
inequality; this has been observed in several works* including [Fei07* @GK21\. Indeed* this was
roughly the strategy employed in the recent work [@GK21\ for the case of ℓ> 𝑂01) for semirandom
𝑘-XOR. In fact* in the ℓ> 𝑂01) regime* it turns out that one can reduce 𝑘-XOR for all 𝑘to the case of
3-XOR and get the right trade-oﬀ; thus* such a decomposition for 3-XOR is enough for the argument
of [@GK21\ to go through for all 𝑘.
2.5
Handling 𝑘*XOR for 𝑘= 3: hypergraph regularity
When ℓ≫𝑂01)* the case of higher arity 𝑘does not reduce to 𝑘> 3. Once again* working through
the case of random 𝑘-XOR inspires our more general argument. We work with a generalization
of the Kikuchi matrix introduced in the previous section for the case of 𝑘> 3. When analyzing
the row pruning step* we need to rely on certain tail inequalities for low-degree polynomials that
16

<!-- pdf-page: 19 -->
depends on the ’spread“ of the hypergraph deﬁned by the indices of the non-zero coeﬂcients in
the polynomial. We use the result of Schudy and Sviridenko [SS12\ that builds on an inﬁuential
line of work on concentration inequalities for polynomials with combinatorial structure in the
monomials begun by [KV00\. Our application of this inequality is rather delicate and as a result* we
need a signiﬁcantly stricter notion of regulYrity – we call this 0𝜀/ ℓ)-regularity – for our row pruning
argument to go through.
Hypergraph regularity decomposition. Roughly speaking the notion of 0𝜀/ ℓ)-regularity $indexed
by the parameter ℓand an accuracy bound 𝜀) we need demands that for each subset 𝑄⊆*𝑛\* the
number of hyperedges 𝐶∈ℋ𝑢such that 𝑄⊆𝐶is bounded above by an appropriate function of
𝑚/ 𝑛and ℓ. Random hypergraphs ℋsatisfy such a regularity property naturally.
In order to handle arbitrary hypergraphs* we introduce a new regulYrity decomposition for
hypergraphs. Our regularity decomposition is based on a certain bipYrtite contrYction operation that
takes a bipartite hyperedge 0𝑢/ 𝐶) ∈ℋand a subset 𝑄⊆𝐶and replaces it with 00𝑢/ 𝑄)/ 𝐶] 𝑄). This
operation should be thought of as ’merging“ all the elements in 𝑄and 𝑢into a new single element
0𝑢/ 𝑄) and obtaining a smaller arity hyperedge in a variable extended space.
We give a greedy $and eﬂcient) algorithm that starts from a 𝑘-uniform hypergraph and
repeatedly applies bipartite contraction operations to obtain a sequence of 𝑘′-uniform hypergraphs
for 𝑘′ ⩽𝑘along with some ’error“ hyperedges* with the property that each of the 𝑘′-uniform
hypergraphs produced are 0𝜀/ ℓ)-regular. Each of the 𝑘′-uniform hypergraphs produced is naturally
associated with a 𝑘′-XOR instance related to the input 𝑘-XOR instance. We show that refuting each
of these output instances yields a refutation for the original 𝑘-XOR instance.
Cauchy*Schwarz even in the even*arity setting. Unlike in the case of 3-XOR where the resulting
bipartite 3-XOR instance had an equal number of 𝑦and 𝑥variables above* the bipartite 𝑘′-XOR
instances produced via our regularity decomposition are lopsided – the number of 𝑦variables can
be polynomially larger in 𝑛than the number 𝑛of the 𝑥variables. @ naive bound on the number of
constraints required to refute such instances is too large to yield the required trade-oﬀ* even in the
case for even 𝑘.
Instead $and in contrast to all previous works on CSP refutation)* we show that an appropriate
application of the ’Cauchy-Schwarz“ trick above to even-arity 𝑘-XOR instances allows us to ’kill“
the 𝑦𝑢—s appearing in the polynomial* leaving us with only a polynomial in the 𝑥𝑖—s. This is a rather
diﬀerent usage of the technique – in prior works $and as in the case of 3-XOR highlighted above)*
it was instead used to build the right ’square“ matrices for obtaining spectral refutations of the
associated CSP instances when 𝑘is odd.
2.6
Organization
The rest of the paper is organized as follows. In Section 3* we introduce some notation* and recall
the various concentration inequalities and facts that we will use in our proofs. In Section 4* we state
and prove our hypergraph decomposition lemma. In Section 5* we begin the proof of Theorem 1.5*
reducing to the case of 𝑘-XOR to handling ’lopsided“ polynomials. In Section 6* we handle the
’lopsided“ polynomials* ﬁnishing the proof of Theorem 1.5. In Section 7* we use Theorem 1.5 to
prove Theorem 1. In Section 8* we prove Feige—s conjecture $Theorem 2)* and ﬁnally in Section 9 we
use Theorems 1 and 2 to prove Theorem 3.
17

<!-- pdf-page: 20 -->
3
Preliminaries
3.1
Basic notation
We let *𝑛\ denote the set |1/ / / / / 𝑛|. For two subsets 𝑆/ 𝑇⊆*𝑛\* we let 𝑆± 𝑇denote the symmetric
diﬀerence of 𝑆and 𝑇* i.e.* 𝑆± 𝑇:> |𝑖: 0𝑖∈𝑆∧𝑖∉𝑇) ∨0𝑖∉𝑆∧𝑖∈𝑇)|.
For a rectangular matrix 𝐴∈ℝ𝑚·𝑛* we let }𝐴}2 :> max𝑥∈ℝ𝑚/𝑦∈ℝ𝑛:}𝑥}2>}𝑦}2>1 𝑥⊤𝐴𝑦denote the
spectral norm of 𝐴* and }𝐴}∞→1 :> max𝑥∈|±1|𝑚/𝑦∈|±1|𝑛𝑥⊤𝐴𝑦denote the ∞→1 norm of 𝐴. We note
that }𝐴}∞→1 ⩽]𝑛𝑚}𝐴}2.
Given a multiset ℋ* we will use the notation 𝐶∈ℋto refer to a distinct element of 𝐶* and
𝐶≠𝐶′ for 𝐶/ 𝐶′ ∈ℋto denote that 𝐶and 𝐶′ are distinct elements in ℋ$even if they are two
diﬀerent copies of the same element).
Given a set 𝑅and variables 𝑥1/ / / / / 𝑥𝑛* we will let 𝑥𝑅:> 
𝑖∈𝑅𝑥𝑖. In particular* 𝑥𝐶:> 
𝑖∈𝐶𝑥𝑖.
3.2
Concentration inequalities
We will rely on the following concentration inequalities. The ﬁrst is the standard rectangular matrix
Bernstein inequality.
Fact 3.1 $Rectangular matrix Bernstein* Theorem 1.6 of [Tro12\). Let 𝑋1/ / / / / 𝑋𝑘be indepen-
dent rYndom 𝑑1 · 𝑑2 mYtrices with 𝔼*𝑋𝑖\ > 0 Ynd }𝑋𝑖} ⩽𝑅for Yll 𝑖.
Let 𝜎2 be such thYt
𝜎2 ⩾max0} 𝔼*𝑘
𝑖>1 𝑋𝑖𝑋⊤
𝑖\}/ } 𝔼*𝑘
𝑖>1 𝑋⊤
𝑖𝑋𝑖\}).
Then for Yll 𝑡⩾0* ℙ*} 𝑘
𝑖>1 𝑋𝑖} ⩾𝑡\ ⩽0𝑑1 ˜
𝑑2) exp0
𝑡202
𝜎2˜𝑅𝑡03).
The second concentration inequality is a result for combinatorial polynomials due to Schudy
and Sviridenko [SS12\ that is the culmination of an inﬁuential line of work begun by Kim and
Vu [KV00\.
Fact 3.2 $Concentration of polynomials* Theorem 1.2 in [SS12\* specialized). Let ℋ⊆
*𝑛\
𝑡
be Y
collection of multilineYr monomiYls of degree 𝑡in 𝑛|0/ 1|-vYlued vYriYbles* Ynd let 𝑓0𝑥) :> 
𝐶∈ℋ

𝑖∈𝐶𝑥𝑖.
Let 𝑌1/ 𝑌2/ / / / / 𝑌𝑛be independent Ynd identicYlly distributed Bernoulli rYndom vYriYbles with ℙ*𝑌𝑖> 1\ > 𝜏.
Then* for some Ybsolute constYnt 𝑅⩾1*
ℙ*~ 𝑓0𝑌)
𝔼𝑓0𝑌)~ ⩾𝜆\ ⩽𝑒2 max

max
𝑟>1/2/////𝑡𝑒𝜆20𝜈0𝜈𝑟𝑅𝑡/
max
𝑟>1/2/////𝑡𝑒
0
𝜆
𝜈𝑟𝑅𝑡)10𝑟
/
where* for every 𝑟⩽𝑡* 𝜈𝑟> 𝜏𝑡𝑟maxℎ0⊆*𝑛\/~ℎ0~>𝑟~|ℎ∈ℋ: ℎ⊇ℎ0|~.
3.3
The sum*of*squares algorithm
We brieﬁy deﬁne the key sum-of-squares facts that we use. These facts are all taken from [BS16*
FKP19\.
De”nition 3.3 $Pseudo-expectations over the hypercube). @ degree 𝑑pseudo-expectation 𝔼over
|±1|𝑛is a linear operator that maps degree ⩽𝑑polynomials on |±1|𝑛into real numbers with the
following three properties:
1. $Normalization) 𝔼*1\ > 1.
18

<!-- pdf-page: 21 -->
2. $Booleanity) For any 𝑥𝑖and any polynomial 𝑓of degree ⩽𝑑
2* 𝔼* 𝑓𝑥2
𝑖\ > 𝔼* 𝑓\.
3. $Positivity) For any polynomial 𝑓of degree at most 𝑑02* 𝔼* 𝑓2\ ⩾0.
We note that if 𝔼is the expectation operator of a distribution over |±1|𝑛* then 𝔼is a degree 𝑑
pseudo-expectation $for any 𝑑)* and thus max𝑥∈|±1|𝑛𝑓0𝑥) ⩽max𝔼𝔼* 𝑓\* where the second max is
taken over all degree 𝑑pseudo-expectations 𝔼.
The SoS algorithm shows that we can eﬂciently maximize 𝔼* 𝑓\ over degree 𝑑pseudo-
expectations 𝔼for a polynomial 𝑓.
Fact 3.4 $Sum-of-squares algorithm* Corollary 3.40 in [FKP19\). Let 𝑓0𝑥1/ / / / / 𝑥𝑛) be Y polynomiYl of
degree 𝑘* where the coeﬂcients of 𝑓Yre rYtionYl numbers with poly0𝑛) bit complexity. Let 𝑑⩾𝑘. There is Yn
Ylgorithm thYt* on input 𝑓/ 𝑑* runs in time 𝑛𝑂0𝑑) Ynd outputs Y vYlue
such thYt 𝛽˜ 2 𝑛⩾
⩾𝛽* where 𝛽
is the mYximum* over Yll degree 𝑑pseudo-expectYtions 𝔼over |±1|𝑛* of 𝔼* 𝑓\.
We now list the other key properties of pseudo-expectations that we will use. First* we note that
pseudo-expectations satisfy the Cauchy-Schwarz inequality.
Fact 3.5 $SoS Cauchy-Schwarz inequality). Let 𝑓/ 𝑔be polynomiYls with deg0 𝑓)/ deg0𝑔) ⩽𝑑02* Ynd let
𝔼be Y degree 𝑑pseudo-expectYtion. Then 𝔼* 𝑓𝑔\ ⩽

𝔼* 𝑓2\𝔼*𝑔2\.
Next* we observe that SoS captures Grothendieck—s inequality* which we recall below.
Fact 3.6 $Grothendieck—s inequality). Let 𝐴be Yn 𝑛·𝑛mYtrix Ynd let 𝑠> max𝑍∈ℝ𝑛·𝑛/𝑍⪰0/𝑍𝑖/𝑖>1∀𝑖tr0𝐴·𝑍).
Then* 𝑠⩽𝐾𝐺}𝐴}∞→1* where 𝐾𝐺⩽1/8 is Y universYl constYnt independent of 𝐴.
Fact 3.7 $SoS ’knows of" Grothendieck). Let 𝐴∈ℝ𝑛·𝑛. Let 𝔼be Y pseudo-expectYtion over |±1|𝑛of
degree ⩾2. Then
𝔼*𝑥⊤𝐴𝑥\ ⩽𝐾𝐺}𝐴}∞→1 ⩽1/8}𝐴}∞→1 /
Proof. Since 𝔼is a pseudo-expectation of degree ⩾2* the pseudo-moment matrix 𝔼*𝑥𝑥⊤\ ⪰0.
Further* since 𝔼is over |±1|𝑛* 𝔼*𝑥2
𝑖\ > 1 for every 𝑖∈*𝑛\. Thus* the matrix 𝑍> 𝔼*𝑥𝑥⊤\ ⪰0* and
has 𝑍𝑖/𝑖> 1. @pplying Fact 3.6 completes the proof.
Finally* we observe that 𝔼* 𝑓\ ⩾0 holds for all nonnegative 𝑓on 𝑘variables* provided that the
degree 𝑑is at least 2𝑘.
Fact 3.8. Let 𝑓0𝑥1/ / / / / 𝑥𝑘) be Y non-negative degree ⩽𝑘multilineYr polynomiYl in 𝑥1/ / / / / 𝑥𝑘* i.e.*
𝑓0𝑥1/ / / / / 𝑥𝑘) ⩾0 for Yll 𝑥1/ / / / / 𝑥𝑘∈|±1|𝑘. Let 𝔼be Y pseudo-expectYtion of degree 𝑑over |±1|𝑛* where
𝑑⩾2𝑘. Then* 𝔼* 𝑓\ ⩾0.
4
; Hypergraph Decomposition Lemma
@ key ingredient in our proof of Theorem 1 is a regulYr hypergrYph decomposition algorithm that takes
an arbitrary 𝑘-uniform hypergraph and decomposes it into a 𝑘
1 diﬀerent regulYr sub-hypergraphs
$after removing a small fraction of the hyperedges). In this section* we present this decomposition
step. We ﬁrst introduce some notation* and then explain the decomposition.
19

<!-- pdf-page: 22 -->
De”nition 4.1 $Uniform hypergraphs). @ 𝑘-uniform hypergraph ℋon 𝑛vertices is a collection ℋ
of subsets of *𝑛\ of size exactly 𝑘. For a set 𝑄⊆*𝑛\* we deﬁne deg0𝑄) :> ~|𝐶∈ℋ: 𝑄⊆𝐶|~.
RemYrk 4.2. We will not assume that ℋis simple* i.e.* ℋcan be a multiset. For simplicity* we will
abuse notation and let 𝐶∈ℋrefer to an element of the multiset ℋ. We will say that 𝐶≠𝐶′ if 𝐶and
𝐶′ are diﬀerent elements of the multiset ℋ* even if 𝐶and 𝐶′ are equal as sets* i.e.* they are distinct
copies of the same element in the underlying set of ℋ. @s an example* we use the above deﬁnition
of deg0𝑄) to refer to the number of 𝐶∈ℋwith 𝑄⊆𝐶* counted with multiplicity. We encourage the
reader to assume that ℋis simple* and then observe that nothing changes if ℋis a multiset* and
deﬁnitions are changed appropriately to count multiplicities.
Our decomposition lemma will decompose a uniform hypergraph into bipYrtite hypergraphs*
which we introduce.
De”nition 4.3 $Bipartite hypergraphs). @ 𝑝-bipartite 𝑡-uniform hypergraph on 𝑛vertices is a
collection |ℋ𝑢|𝑢∈*𝑝\* where each ℋ𝑢is a collection of subsets of *𝑛\ of size exactly 𝑡
1. We call each
ℋ𝑢* or just 𝑢* a pYrtition of the bipartite hypergraph. @ set 𝐶∈ℋ𝑢corresponds to the hyperedge
0𝑢/ 𝐶). For a set 𝑄⊆*𝑛\ and 𝑢∈*𝑝\* we deﬁne deg𝑢0𝑄) :> ~|𝐶∈ℋ𝑢: 𝑄⊆𝐶|~. When 𝑝is clear
from context or not relevant* we just use the terminology ’bipartite 𝑡-uniform hypergraph“.
One should think of a bipartite hypergraph |ℋ𝑢|𝑢∈*𝑝\ as a hypergraph ℋon two sets of vertices*
*𝑝\ and *𝑛\* where each hyperedge 0𝑢/ 𝐶) ∈ℋcontains one vertex 𝑢∈*𝑝\ and 𝑘
1 vertices in *𝑛\;
for 𝑢∈*𝑝\* the 0𝑘
1)-uniform hypergraph ℋ𝑢contains all hyperedges 𝐶such that the hyperedge
0𝑢/ 𝐶) is in the hypergraph ℋ.
De”nition 4.4 $Hypergraph regularity). We say that a 𝑝-bipartite 𝑘-uniform hypergraph |ℋ𝑢|𝑢∈*𝑝\
is 0𝜀/ ℓ)-regular if deg𝑢0𝑄) ⩽
1
𝜀2 max0 𝑛
ℓ
𝑘
2
1 ~𝑄~ / 1) for all 𝑄⊆*𝑛\ of size at most 𝑘
1 and all
𝑢∈*𝑝\. For convenience* we will say |ℋ𝑢|𝑢∈*𝑝\ is regular when 𝜀/ ℓare clear from context.
RemYrk 4.5 $Regularity is a pseudorandom property). Informally speaking* a collection of 𝑘-tuples
is regular if the number of 𝑘-tuples in ℋ𝑢that all contain a ﬁxed set of size 𝑗is appropriately upper
bounded. It is not hard to show that if ℋ> ∪𝑢∈*𝑝\ℋ𝑢is a uniformly rYndom bipartite hypergraph with
𝑝> 𝑛partitions and 𝑚> ℓ0 𝑛
ℓ)
𝑘
2 random 𝑘-tuples* then with high probability* for every 𝑢∈*𝑝\/ 𝑄*
deg𝑢0𝑄) ⩽max0
𝑚
𝑝𝑛~𝑄~ / 1) · 𝑂0log 𝑛) ⩽max0 𝑛
ℓ
𝑘
2
1 ~𝑄~ / 1) · 𝑂0log 𝑛)* which is the same condition of
regularity* up to the 𝑂0log 𝑛) extra factor. Thus* regularity can be seen as a $weak) pseudorandom
property of a bipartite hypergraph.
Next* we deﬁne a notion of hypergraph decomposition that we call a bipartite contraction.
De”nition 4.6 $Bipartite contractions). Let ℋbe a 𝑘-uniform hypergraph on 𝑛vertices. We say that
a pair of subsets 0𝑄/ 𝐶′) $of *𝑛\) is a contrYction of the hyperedge 𝐶∈ℋif 𝐶> 𝑄∪𝐶′ and 𝑄/ 𝐶′ are
disjoint. It is sometimes useful to think of this pair as denoting a set of size 1 ˜ 𝑘
~𝑄~* where the
ﬁrst ’element“ of the set is the entire set 𝑄* and the remaining 𝑘
~𝑄~ elements come from the set
𝐶] 𝑄.
@ bipYrtite contrYction of ℋis a collection of 𝑘
1 bipartite hypergraphs |ℋ0𝑡)
𝑢|𝑢∈*𝑝0𝑡)\ for
𝑡> 2/ / / / / 𝑘* along with a set ℋ01) of ’discarded edges“ where:
$1) each |ℋ0𝑡)
𝑢|𝑢∈*𝑝0𝑡)\ is a bipartite 𝑡-uniform hypergraph*
20

<!-- pdf-page: 23 -->
$2) each 𝑢∈*𝑝0𝑡)\ corresponds to a subset 𝑄𝑢⊆*𝑛\ of size 𝑘˜ 1
𝑡$it is possible that 𝑄𝑢> 𝑄𝑢′ for
distinct 𝑢/ 𝑢′)*
$3) every hyperedge in any ℋ0𝑡)
𝑢
is a bipartite contraction of some hyperedge in ℋ* i.e.* for every
𝑡and any 𝑢∈*𝑝0𝑡)\ and 𝑅∈ℋ0𝑡)
𝑢* the set 𝑄𝑢∪𝑅> 𝐶for some 𝐶∈ℋ* so that the hyperedge
0𝑄𝑢/ 𝑅) is a contraction of 𝐶*
$4) every hyperedge 𝐶is contracted exactly once* i.e.* for each 𝐶∈ℋ* either 𝐶∈ℋ01) or there
exists unique 𝑡* 𝑢∈*𝑝0𝑡)\/ 𝑅∈ℋ0𝑡)
𝑢
such that 𝑄𝑢∪𝑅> 𝐶.
Our hypergraph contraction lemma shows that for any 𝑘-uniform hypergraph ℋ* we can
eﬂciently ﬁnd a bipartite contraction of ℋsuch that each of the resulting bipartite hypergraphs is
regular.
Lemma 4.7 $Hypergraph contraction lemma). Let ℋbe Y 𝑘-uniform hypergrYph on 𝑛vertices with
𝑘⩾2 Ynd ~ℋ~ > 𝑚. Then* there is Y bipYrtite contrYction of ℋsuch thYt
$1) 𝑚01) :>
ℋ01)⩽
𝑛
𝑘𝜀2
𝑛
ℓ
𝑘
2
1.
$2) For 𝑡⩾2* eYch bipYrtite 𝑡-uniform hypergrYph |ℋ0𝑡)|𝑢∈*𝑝0𝑡)\ is
$Y) 0𝜀/ ℓ)-regulYr*
$b)
ℋ0𝑡)
𝑢
> 𝑚0𝑡)0𝑝0𝑡) >

1
𝜀2 max0 𝑛
ℓ
𝑡
𝑘
2
1 / 1)

for Yll 𝑢∈*𝑝0𝑡)\* where 𝑚0𝑡) :> 
𝑢∈*𝑝0𝑡)\
ℋ0𝑡)
𝑢
.
Further* given ℋ* the decomposition itself cYn be computed by Yn Ylgorithm running in time 𝑂0𝑛𝑘~ℋ~2).
Observe that the lemma does not assume any lower bound on 𝑚. Indeed if 𝑚is too small then
we will have 𝑚0𝑡) > 0 for all 𝑡⩾2.
Proof of LemmY 4.7. We prove Lemma 4.7 by analyzing the following greedy algorithm to construct
the bipartite contraction. Before stating the formal algorithm* we ﬁrst explain the high level idea of
the algorithm* as it is very simple.
If ℋdoes not have enough hyperedges* then we set ℋ01) > ℋand are done. Otherwise* there
must be some ’violating“ set 𝑄: namely* a set 𝑄where deg0𝑄) is above a threshold 𝜏$related to
the deﬁnition of regularity). We choose a ’maximal“ such violating 𝑄* i.e.* no set containing 𝑄
is a violation* and then $1) remove an arbitrary 𝜏hyperedges of the form 𝑄∪𝐶from ℋ* $2) take
bipartite contractions 0𝑄/ 𝐶] 𝑄) of all such hyperedges* and $3) add them all to ℋ0𝑘˜1 ~𝑄~)
𝑢
where 𝑢
is ’new“ partition where 𝑄𝑢:> 𝑄. Notice that we may pick the same 𝑄more than once since we
only decrease deg0𝑄) by 𝜏in one such step. We repeatedly ﬁx such violations greedily until we
cannot and stop. Notice that this procedure is ’one-shot“ – we do not recursively operate on the
ℋ0𝑡)
𝑢—s produced* as $we will show) that they are guaranteed to 0𝜀/ ℓ)-regular by the design of our
decomposition procedure.
We now state and analyze the greedy algorithm.
;lgorithm 4.8.
Given: @ 𝑘-uniform hypergraph ℋover 𝑛vertices* where 𝑚> ~ℋ~.
21

<!-- pdf-page: 24 -->
Output: @ bipartite contraction ||ℋ0𝑡)
𝑢|𝑢∈*𝑝0𝑡)\|𝑡>2/////𝑘of ℋ.
Operation:
1. Initialize: 𝑝0𝑡) > 0 for 𝑡> 2/ / / / / 𝑘.
2. Fix violations greedily:
$a) Find a maximal nonempty violating 𝑄. That is* ﬁnd 𝑄⊆*𝑛\ of size 1 ⩽
~𝑄~ ⩽𝑘
1 such that deg0𝑄) > ~|𝐶∈ℋ: 𝑄⊆𝐶|~ =
1
𝜀2 max0 𝑛
ℓ
𝑘
2
~𝑄~ / 1)* and
deg0𝑄′) ⩽
1
𝜀2 max0 𝑛
ℓ
𝑘
2
~𝑄′~ / 1) for all 𝑄′ ⊋𝑄.
$b) Let 𝑞> ~𝑄~. Let 𝑢> 1 ˜ 𝑝0𝑘˜1 𝑞) be a new ’label“* and deﬁne ℋ′ to be an
arbitrary subset of |𝐶∈ℋ: 𝑄⊆𝐶| of size exactly

1
𝜀2 max0 𝑛
ℓ
𝑘
2
𝑞/ 1)

. Let 𝑄
be the set 𝑄𝑢associated with 𝑢* and deﬁne ℋ0𝑘˜1 𝑞)
𝑢
:> |𝐶] 𝑄: 𝐶∈ℋ′|.
$c) Set 𝑝0𝑘˜1 𝑞) ←1 ˜ 𝑝0𝑘˜1 𝑞)* and ℋ←ℋ] ℋ′.
3. If no such 𝑄exists* then put the remaining hyperedges in ℋ01).
First* we argue that 𝑚01) is small. By construction* ℋ01) is the set of remaining hyperedges
when the inner loop terminates* and so we must have deg0|𝑖|) ⩽
1
𝜀2 max0 𝑛
ℓ
𝑘
2
1 / 1) >
1
𝜀2
𝑛
ℓ
𝑘
2
1
for every 𝑖∈*𝑛\; we abuse notation and let deg only count hyperedges remaining in ℋ. We then
have 
𝑖∈*𝑛\ deg0|𝑖|) > 𝑘
ℋ01)* as every 𝐶∈ℋ01) is counted exactly 𝑘times in the sum. Hence*
𝑚01) ⩽
𝑛
𝑘𝜀2
𝑛
ℓ
𝑘
2
1.
We now argue that for each 𝑡* the bipartite hypergraphs |ℋ0𝑡)
𝑢|𝑢∈*𝑝0𝑡)\ have the desired properties.
Fix 𝑡∈|2/ / / / / 𝑘|. By construction* each ℋ0𝑡)
𝑢
has the same size* namely

1
𝜀2 max0 𝑛
ℓ
𝑡
𝑘
2
1 / 1)

.
It then follows that 𝑚0𝑡) :> 
𝑢∈*𝑝0𝑡)\
ℋ0𝑡)
𝑢
> 𝑝0𝑡) ·

1
𝜀2 max

𝑛
ℓ
𝑡
𝑘
2
1 / 1

* and so 𝑝0𝑡) ⩽𝜀2𝑚0𝑡) and
ℋ0𝑡)
𝑢
> 𝑚0𝑡)
𝑝0𝑡) . This proves property $b) in Item $2).
It remains to show property $a)* that |ℋ0𝑡)
𝑢|𝑢∈*𝑝0𝑡)\ is 0𝜀/ ℓ)-regular. To see this* let 𝑢∈*𝑝0𝑡)\* and
let 𝑄𝑢be the set associated with the label 𝑢. Note that we must have ~𝑄𝑢~ > 𝑘˜ 1
𝑡. Let ℋ′ denote
the set of constraints in ℋat the time when 𝑢and ℋ0𝑡)
𝑢
are added to the bipartite hypergraph.
Namely* we have that for every 𝐶∈ℋ0𝑡)
𝑢* 𝑄𝑢∪𝐶∈ℋ′. Now* let 𝑅⊆*𝑛\ be a nonempty set of size
at most 𝑡
1. First* observe that if 𝑅∩𝑄𝑢is nonempty* then we must have deg𝑢0𝑅) > 0 $this degree
is in the hypergraph ℋ0𝑡)
𝑢). Indeed* this is because 𝐶∩𝑄𝑢> ∅for all 𝐶∈ℋ0𝑡)
𝑢. So* we can assume
that 𝑅∩𝑄𝑢> ∅. Next* we see that deg𝑢0𝑅) ⩽degℋ′0𝑄𝑢∪𝑅) $where degℋ′ is the degree in ℋ′)*
as 𝑄𝑢∪𝐶∈ℋ′ for every 𝐶∈ℋ0𝑡)
𝑢. Because 𝑄𝑢was maximal whenever it was processed in our
decomposition algorithm and 𝑄𝑢
𝑄𝑢∪𝑅as 𝑅is nonempty and 𝑅∩𝑄𝑢> ∅* it follows that
degℋ′0𝑄𝑢∪𝑅) ⩽1
𝜀2 max0
𝑛
ℓ
𝑘
2
~𝑄𝑢∪𝑅~
/ 1) > 1
𝜀2 max0
𝑛
ℓ
𝑘
2
~𝑄𝑢~ ~𝑅~
/ 1)
> 1
𝜀2 max0
𝑛
ℓ
𝑡
𝑘
2
1 ~𝑅~
/ 1) ⩽1
𝜀2 max0
𝑛
ℓ
𝑡
2
1 ~𝑅~
/ 1) /
where the last inequality follows because 𝑡
𝑘
2
1
~𝑅~ ⩽𝑡
2
1
~𝑅~ always holds* as 𝑡⩽𝑘. This
22

<!-- pdf-page: 25 -->
ﬁnishes the proof.
Finally* when 𝑅> ∅* we trivially have deg𝑢0∅) >
ℋ0𝑡)
𝑢
>

1
𝜀2 max0 𝑛
ℓ
𝑡
𝑘
2
1 / 1)

⩽
1
𝜀2 max0 𝑛
ℓ
𝑡
𝑘
2
1 / 1) ⩽
1
𝜀2 max0 𝑛
ℓ
𝑡
2
1 / 1)* where we use again that 𝑡
𝑘
2 ⩽𝑡
2 as 𝑡⩽𝑘.
To argue the runtime bound* we simply observe that each iteration takes 𝑂0~ℋ~ 𝑛𝑘) time via
brute-force* and there are clearly at most ~ℋ~ iterations.
5
Refuting Semirandom Sparse Polynomials over the Hypercube
In this section* we describe an algorithm to tightly refute semirandom instances of homogenous*
multilinear degree-𝑘polynomials.
Concretely* our algorithm takes as input a homogenous*
multilinear degree-𝑘polynomial 𝜙in 𝑛variables 𝑥1/ / / / / 𝑥𝑛and outputs a correct upper bound
on val0𝜙) :> max𝑥∈| 1/1|𝑛𝜙0𝑥). Whenever the coeﬂcients of the polynomial are generated from
independent random probability distributions on * 1/ 1\ and the $multi-)hypergraph of coeﬂcients
has suﬂciently many hyperedges* with high probability* the algorithm outputs a value that is
smaller than a target 𝜀. The guarantees of our algorithm are captured by the theorem below.
Theorem 5.1 $Refuting semirandom sparse polynomials). Let 𝑘∈ℕYnd ℓ: ℕ→ℕbe Y function such
thYt 20𝑘
1) ⩽ℓ0𝑛) ⩽𝑛. There is Yn Ylgorithm thYt tYkes Ys input Y homogeneous* multilineYr polynomiYl 𝜙
in 𝑛vYriYbles 𝑥1/ 𝑥2/ / / / / 𝑥𝑛of totYl degree 𝑘speciﬁed by Y 𝑘-uniform multi-hypergrYph ℋYnd Y collection
of rYtionYl numbers |𝑏𝐶|𝐶∈ℋ:
𝜙0𝑥) > 1
𝑚

𝐶∈ℋ
𝑏𝐶·

𝑖⩽𝑘
𝑥𝐶𝑖/
$5.1)
Ynd the Ylgorithm outputs Y vYlue alg-val0𝜙) ∈* 1/ 1\ in time 𝑛𝑂0ℓ) sYtisfying the following:
$1) 1 ⩾alg-val0𝜙) ⩾val0𝜙).
$2) There is Yn Ybsolute constYnt
= 0 such thYt if 𝑛log2 𝑛⩾~ℋ~ > 𝑚⩾𝑚0 >  𝑘·
𝑛
ℓ
𝑘
2 ℓ· 0log2 𝑛)4𝑘˜1
𝜀5
Ynd the 𝑏𝐶–s Yre independent* meYn 0 rYndom vYriYbles supported in * 1/ 1\* then with probYbility
1
10poly0𝑛) over the drYw of 𝑏𝐶–s* it holds thYt alg-val0𝜙) ⩽𝜀˜ 2 𝑛.
Moreover* our Ylgorithm is ’cYptured“ by the cYnonicYl degree 2ℓsum-of-squYres relYxYtion of polynomiYl
mYximizYtion problem over the hypercube. SpeciﬁcYlly* under the sYme hypothesis on 𝜙Ys Ybove* for every
pseudo-expectYtion 𝔼of degree ⩾2ℓover |±1|𝑛* it holds thYt 𝔼*𝜙\ ⩽𝜀.
@s is the case in Section 4* we will not assume that ℋis simple* and we will adopt the same
notational conventions as in Remark 4.2.
5.1
Regular bipartite polynomials
Our proof of Theorem 5.1 goes via a reduction to refuting sparse polynomials with additional
structure that we call bipYrtite polynomials. Bipartite polynomials can be seen as a generalization
of partitioned 2-XOR instances introduced in [@GK21\. We next present this class of polynomials
and identify a regulYrity property of such polynomials that will be a key technical ingredient in our
algorithm.
23

<!-- pdf-page: 26 -->
De”nition 5.2 $𝑝-bipartite polynomials). Let 𝑘∈ℕ. @ 𝑝-bipartite polynomial 𝜓is a homogeneous
degree 𝑘polynomial in 𝑝˜ 𝑛variables 𝑦> |𝑦𝑢|𝑢∈*𝑝\ and 𝑥> |𝑥𝑗|𝑗∈*𝑛\ deﬁned by
𝜓0𝑦/ 𝑥) > 1
𝑚
𝑝

𝑢>1
𝑦𝑢

𝐶∈ℋ𝑢
𝑏𝑢/𝐶𝑥𝐶/
where |ℋ𝑢|𝑢∈*𝑝\ is a 𝑝-bipartite 𝑘-uniform hypergraph $Deﬁnition 4.3)* 𝑏𝑢/𝐶∈* 1/ 1\ for ev-
ery 𝐶∈ℋ* 𝑥𝐶:> 
𝑖∈𝐶𝑥𝑖* and 𝑚:> 
𝑢∈*𝑝\ ~ℋ𝑢~.
The vYlue of 𝜓* denoted by val0𝜓)* is
max𝑦∈|±1|𝑝/𝑥∈|±1|𝑛𝜓0𝑦/ 𝑥). Note that val0𝜓) ∈* 1/ 1\ always. We also note that 𝜓is a homo-
geneous degree 1 polynomial in 𝑦.
De”nition 5.3 $Regular 𝑝-bipartite polynomials). We say that a 𝑝-bipartite polynomial 𝜓is 0𝜀/ ℓ)-
regular if the underlying 𝑝-bipartite 𝑘-uniform hypergraph |ℋ𝑢|𝑢∈*𝑝\ is 0𝜀/ ℓ)-regular $Deﬁnition 4.4).
When 𝜀/ ℓare clear from context* we will simply say that 𝜓is regular.
The bulk of the technical work in proving Theorem 5.1 is in analyzing a refutation algorithm for
regular instances of 𝑝-bipartite polynomials encapsulated in the following theorem.
Theorem 5.4 $Refuting regular bipartite polynomials). Let 𝑘∈ℕ.
For Yny ℓ: ℕ→ℕwith
20𝑘
1) ⩽ℓ0𝑛) ⩽𝑛for Yll 𝑛∈ℕ* there is Yn Ylgorithm with the following properties: the Ylgorithm tYkes Ys
input Y 𝑝-bipYrtite* homogeneous* polynomiYl 𝜓> 𝜓0𝑦/ 𝑥) in vYriYbles 𝑦> |𝑦𝑢|𝑢∈*𝑝\ Ynd 𝑥> |𝑥𝑖|𝑖∈*𝑛\ of
totYl degree 𝑘:
𝜓0𝑦/ 𝑥) > 1
𝑚
𝑝

𝑢>1
𝑦𝑢

𝐶∈ℋ𝑢
𝑏𝑢/𝐶𝑥𝐶/
speciﬁed by Y collection of 0𝑘
1)-uniform hypergrYphs |ℋ𝑢|𝑢∈*𝑝\ Ynd rYtionYl numbers in * 1/ 1\
|𝑏𝑢/𝐶|𝑢∈*𝑝\/𝐶∈ℋ𝑢. The Ylgorithm runs in time 0𝑝˜ 𝑛)𝑂0ℓ) time Ynd outputs alg-val0𝜓) ∈* 1/ 1\ sYtisfying
the following:
1. For every 𝜓* alg-val0𝜓) ⩾val0𝜓).
2. Whenever 𝜓Ynd 𝑏𝑢/𝐶–s sYtisfy:
$Y) 𝜓is 0𝜀/ ℓ)-regulYr*
$b) ~ℋ𝑢~ ⩽2𝑚
𝑝for Yll 𝑢∈*𝑝\*
$c) 𝑛log2 𝑛⩾𝑚⩾max

 𝑘·
𝑛
ℓ
𝑘1
2 
𝑝ℓ· 0log2 𝑛)2𝑘˜0/5
𝜀3
/ 𝑝0𝜀2
* where
is Yn Ybsolute constYnt* Ynd
$d) EYch 𝑏𝑢/𝐶–s is chosen from $possibly di”erent) independent meYn zero distributions on * 1/ 1\.
Then with probYbility 1
10poly0𝑛) over the drYw of 𝑏𝑢/𝐶–s* alg-val0𝜓) ⩽
]
2/8 · 𝜀˜ 2 𝑛.
Further* our Ylgorithm is ’cYptured“ by the sum-of-squYres Ylgorithm of degree 2ℓ: for every pseudo-expectYtion
𝔼in vYriYbles 𝑥/ 𝑦of degree 2ℓover |±1|𝑝˜𝑛* 𝔼*𝜓0𝑥/ 𝑦)\ ⩽
]
2/8 · 𝜀.
We defer the proof of Theorem 5.4 to Section 6.
24

<!-- pdf-page: 27 -->
5.2
Reduction to regular bipartite polynomials
We now use Lemma 4.7 along with Theorem 5.4 to complete the proof of Theorem 5.1 by analyzing
the following algorithm:
Main Refutation ;lgorithm
;lgorithm 5.5.
Given: @ polynomial 𝜙speciﬁed by a 𝑘-uniform multi-hypergraph ℋover 𝑛vertices and
rational numbers |𝑏𝐶|𝐶∈ℋ.
Output: @ value alg-val ∈* 1/ 1\.
Operation:
1. @pply the decomposition algorithm from Lemma 4.7 to construct bipartite hyper-
graphs |ℋ0𝑡)
𝑢|𝑢∈*𝑝0𝑡)\ for 2 ⩽𝑡⩽𝑘* and a set of discarded edges ℋ01).
2. For every 𝑡* 𝑢∈*𝑝0𝑡)\ and for every hyperedge 𝐶∈ℋ0𝑡)
𝑢* set 𝑏𝑢/𝐶> 𝑏𝑄𝑢∪𝐶.
3. For 2 ⩽𝑡⩽𝑘* apply the refutation algorithm for regular bipartite polynomials
from Theorem 5.4 to the degree 𝑡𝑝0𝑡)-bipartite polynomial speciﬁed by the bipartite
hypergraph |ℋ0𝑡)
𝑢|𝑢∈*𝑝0𝑡)\ and 𝑏𝑢/𝐶—s to obtain alg-val𝑡. Set alg-val1 > 1.
4. Output alg-val > 1
𝑚

𝑡>1𝑘𝑚0𝑡) · alg-val𝑡* where 𝑚0𝑡) > 
𝑢∈*𝑝0𝑡)\
ℋ0𝑡)
𝑢
.
Proof of Theorem 5.1 from LemmY 4.7 Ynd Theorem 5.4. First* without loss of generality we will assume
that 𝜀⩽
1
]
2* so that
1
𝜀2 ⩾2. This is without loss of generality* as it only changes the universal
constant in Theorem 5.1.
For each 𝑡and 𝑢∈*𝑝0𝑡)\* let 𝑄𝑢⊆*𝑛\ denote the subset of size 𝑘˜ 1
𝑡associated to 𝑢* and let
𝜓𝑡be the polynomial associated with the 𝑡-uniform 0𝜀/ ℓ)-regular bipartite hypergraph |ℋ0𝑡)
𝑢|𝑢∈*𝑝0𝑡)\
obtained from the hypergraph ℋspecifying the input polynomial 𝜙by applying the decomposition
algorithm from Lemma 4.7. Thus* 𝜓𝑡is a polynomial in the 𝑝0𝑡) ˜ 𝑛variables |𝑦0𝑡)
𝑢|𝑢∈*𝑝0𝑡)\ ∪|𝑥𝑖|𝑖∈*𝑛\*
and 𝜓𝑡0|𝑦0𝑡)
𝑢|𝑢∈*𝑝0𝑡)\/ 𝑥) :>
1
𝑚0𝑡)

𝑢∈*𝑝0𝑡)\ 𝑦0𝑡)
𝑢

𝐶∈ℋ0𝑡)
𝑢𝑏𝑄𝑢∪𝐶𝑥𝐶. We then have that
𝜙0𝑥) > 1
𝑚
𝑘

𝑡>2
𝑚0𝑡)𝜓𝑡0|𝑥𝑄𝑢|𝑢∈*𝑝0𝑡)\/ 𝑥) ˜ 1
𝑚

𝐶∈ℋ01)
𝑏𝐶𝑥𝐶/
$5.2)
Indeed* this follows immediately from the deﬁnition of a bipartite contraction* because when we
substitute 𝑥𝑄𝑢for 𝑦𝑢for some 𝑢∈*𝑝0𝑡)\* then 𝑦𝑢𝑥𝐶> 𝑥𝑄𝑢∪𝐶> 𝑥𝐶′ for 𝐶′ ∈ℋ.
Let alg-val𝑡> alg-val0𝜓𝑡) be the output of the refutation algorithm from Theorem 5.4 applied to
𝜓𝑡. Then* val0𝜓𝑡) ⩽alg-val𝑡. Thus* using $5.2)* val0𝜙) ⩽1
𝑚
𝑘
𝑡>1 𝑚0𝑡)alg-val𝑡> alg-val.
Next* if for some 𝑡* 𝑚0𝑡) ⩽𝜀𝑚* then using the trivial bound of alg-val0𝜓𝑡) ⩽1 yields
𝑚0𝑡)alg-val0𝜓𝑡) ⩽𝜀𝑚.
Note that in particular* 𝑚01) ⩽𝜀𝑚always holds* as 𝑚⩾
1
𝜀3
𝑛
ℓ
𝑘
2 · ℓ
and 𝑚01) ⩽
𝑛
𝑘𝜀2
𝑛
ℓ
𝑘
2
1.
25

<!-- pdf-page: 28 -->
Now* suppose that for some 𝑡* 𝑚0𝑡) ⩾𝜀𝑚. Notice that 𝑚0𝑡) ⩽𝑚⩽𝑛𝑘⩽𝑛log2 𝑛. We now prove that
in this setting* 𝑚0𝑡) ⩾ 𝑡·
𝑛
ℓ
𝑡1
2 
𝑝0𝑡)ℓ· 0log2 𝑛)2𝑡˜0/5
𝜀3
. We know that 𝑚0𝑡) > 𝑝0𝑡) ·

1
𝜀2 max0 𝑛
ℓ
𝑡
𝑘
2
1 / 1)

.
Hence* it suﬂces to show
𝜀𝑚⩾
2𝑡·
𝑛
ℓ
𝑡1
ℓ· 0log2 𝑛)4𝑡˜1
𝜀6
·
1
1
2𝜀2 max0 𝑛
ℓ
𝑡
𝑘
2
1 / 1)
/
where we use that

1
𝜀2 max0 𝑛
ℓ
𝑡
𝑘
2
1 / 1)

⩾1
𝜀2
⩾
1
2𝜀2 as 1
𝜀2 ⩾2.
Hence* for 𝑡⩾𝑘
2 ˜ 1* it suﬂces to have
𝜀𝑚⩾2 2𝑡·
𝑛
ℓ
𝑘
2 ℓ· 0log2 𝑛)4𝑡˜1
𝜀4
/
and for 𝑡= 𝑘
2 ˜ 1* it suﬂces to have
𝜀𝑚⩾2 2𝑡·
𝑛
ℓ
𝑡1
ℓ· 0log2 𝑛)4𝑡˜1
𝜀4
/
@s 𝑚⩾
′𝑘·
𝑛
ℓ
𝑘
2 ℓ· 0log2 𝑛)4𝑘˜1
𝜀5
* for the absolute constant  ′ > 2 2* both conditions are satisﬁed.
We have thus shown that if 𝑚0𝑡) ⩾𝜀𝑚* then 𝜓𝑡satisﬁes the conditions of Theorem 5.4* and so
we have 𝑚0𝑡)alg-val𝑡⩽𝜀𝑚0𝑡) ⩽𝜀𝑚with probability 1
10poly0𝑛) over the draw of 𝑏𝐶—s. By union
bound over all 𝑡* we thus get that alg-val0𝜙) ⩽𝑂0𝑘𝜀) with probability 1
𝑘0poly0𝑛) ⩾1
10poly0𝑛)
over the draw of 𝑏𝐶—s. This completes the analysis of the second guarantee.
The running time of the algorithm is dominated by the time required to apply the refutation
algorithm from Theorem 5.4 to each of the bipartite polyomials produced by the decomposition
algorithm. This cost is bounded above by 𝑛𝑂0ℓ).
Finally* the fact that this algorithm is ’captured“ by SoS follows because Theorem 5.4 is ’captured“
by SoS and the linearity of the pseudo-expectations.
6
Refuting Regular Bipartite Polynomials
In this section* we prove Theorem 5.4. Our algorithm is based on the semideﬁnite programming
relaxation of the ’∞→1“-norm of an appropriate matrix associated with the polynomial 𝜓. The
analysis of the algorithm will naturally establish the ’Further*...“ part of the statement.
@s in several prior works starting with [CGL04\* our proof of Theorem 5.4 applies the ’Cauchy-
Schwarz“ trick in order to work with an even-degree polynomial associated with 𝜓.
Lemma 6.1 $Cauchy-Schwarz trick). Let 𝜓be Y 𝑝-bipYrtite* homogeneous* polynomiYl 𝜓> 𝜓0𝑦/ 𝑥) in
vYriYbles 𝑦> |𝑦𝑢|𝑢∈*𝑝\ Ynd 𝑥> |𝑥𝑖|𝑖∈*𝑛\ of totYl degree 𝑘:
𝜓0𝑦/ 𝑥) > 1
𝑚
𝑝

𝑢>1
𝑦𝑢

𝐶∈ℋ𝑢
𝑏𝑢/𝐶𝑥𝐶/
26

<!-- pdf-page: 29 -->
Let 𝑓be the following polynomiYl obtYined from 𝜓:
𝑓0𝑥) > 𝑝
𝑚2
𝑝

𝑢>1

0𝐶/𝐶′)∈ℋ𝑢·ℋ𝑢/𝐶≠𝐶′
𝑏𝑢/𝐶𝑏𝑢/𝐶′𝑥𝐶𝑥𝐶′ /
Then val0𝜓)2 ⩽
𝑝
𝑚˜ val0 𝑓). Further* for every pseudo-expectYtion 𝔼of degree ⩾2𝑘over |±1|𝑝˜𝑛*
𝔼*𝜓\2 ⩽𝑝
𝑚˜ 𝔼* 𝑓\.
Proof. Fix an assignment in |±1| to the 𝑦𝑢—s and 𝑥𝑖—s. We then have
𝜓20𝑦/ 𝑥) >

1
𝑚
𝑝

𝑢>1
𝑦𝑢

𝐶∈ℋ𝑢
𝑏𝑢/𝐶𝑥𝐶
2
⩽
1
𝑚2
𝑝

𝑢>1
𝑦2
𝑢



𝑝

𝑢>1

𝐶∈ℋ𝑢
𝑏𝑢/𝐶𝑥𝐶
2


⩽𝑝
𝑚2 ·
𝑝

𝑢>1

𝐶∈ℋ𝑢
𝑏2
𝑢/𝐶𝑥2
𝐶˜ 𝑝
𝑚2

𝑢⩽𝑝

0𝐶/𝐶′)∈ℋ𝑢·ℋ𝑢/𝐶≠𝐶′
𝑏𝑢/𝐶𝑏𝑢/𝐶′𝑥𝐶𝑥𝐶′
⩽𝑝
𝑚˜ 𝑝
𝑚2
𝑝

𝑢>1

0𝐶/𝐶′)∈ℋ𝑢·ℋ𝑢/𝐶≠𝐶′
𝑏𝑢/𝐶𝑏𝑢/𝐶′𝑥𝐶𝑥𝐶′ /
where the ﬁrst inequality above uses the Cauchy-Schwarz inequality* the second uses that 𝑦2
𝑢> 1
for every 𝑢* and the third uses that 𝑏2
𝑢/𝐶⩽1 and 𝑥2
𝐶> 1. Further* observe that by using the SoS
version of the Cauchy-Schwarz inequality $Fact 3.5) and the fact that 𝔼is over |±1|𝑝˜𝑛* we see that
the above also holds for all degree 𝑑⩾20𝑘
1) pseudo-expectations 𝔼.
Taking the maximum over 𝑥and 𝑦on both sides then yields that val0𝜓)2 ⩽
𝑝
𝑚˜ val0 𝑓).
Taking the maximum over all pseudo-expectations 𝔼on |±1|𝑝˜𝑛and using Fact 3.5 yields that
𝔼*𝜓\2 ⩽𝔼*𝜓2\ ⩽𝑝
𝑚˜ 𝔼* 𝑓\.
6.1
Our Jikuchi matrix and algorithm
@s Lemma 6.1 shows* it suﬂces to upper bound val0 𝑓). Our certiﬁcate of an upper bound on val0 𝑓)
is based on an appropriate variant of the Kikuchi matrix of [W@M19\. To deﬁne our matrix* it is
convenient to think of having two clones of each of the 𝑛possible ’𝑥“ variables. For every 𝑖* we will
use 0𝑖/ 1) and 0𝑖/ 2) to denote the two clones of the 𝑖-th variable below. For any set 𝐶⊆*𝑛\* we will
use 𝐶01) to denote the set |0𝑖/ 1) ~ 𝑖∈𝐶|* i.e.* the clause 𝐶using the ﬁrst type of clones* and 𝐶02)
to be the clause 𝐶using the second type of clones. Recall that for any sets 𝑆/ 𝑇* let 𝑆± 𝑇denote
the symmetric diﬀerence of the two sets. More generally* let 𝑆1 ± 𝑆2 ± · · · ± 𝑆𝑡denote the set of all
elements that occur in an odd number of diﬀerent 𝑆𝑖—s.
De”nition 6.2 $Our Kikuchi Matrix). Let ℓ∈ℕand let 𝑁:>
2𝑛
ℓ
.
Fix a 𝑝-bipartite 𝑘-uniform hypergraph |ℋ𝑢|𝑢∈*𝑝\. For each 𝑢∈*𝑝\* deﬁne the 𝑁· 𝑁matrix
𝐴𝑢* indexed by sets 𝑆⊆*𝑛\ · *2\ of size ℓ* as follows. For any two sets 𝑆/ 𝑇⊆*𝑛\ · *2\ of size ℓand
sets 𝐶≠𝐶′ ∈ℋ𝑢of size 𝑘
1* we say that 𝑆
𝐶/𝐶′
↔𝑇if
1. 𝑆± 𝑇> 𝐶01) ± 𝐶′02)*
2. 𝑘is odd* and
𝑆∩𝐶01)>
𝑆∩𝐶′02)>
𝑇∩𝐶01)>
𝑇∩𝐶′02)> 𝑘1
2 * or*
27

<!-- pdf-page: 30 -->
3. 𝑘is even* and
𝑆∩𝐶01)>
𝑇∩𝐶′02)> 𝑘
2 and
𝑆∩𝐶′02)>
𝑇∩𝐶01)> 𝑘2
2 * or*
4. 𝑘is even* and
𝑆∩𝐶01)>
𝑇∩𝐶′02)> 𝑘2
2
and
𝑆∩𝐶′02)>
𝑇∩𝐶01)> 𝑘
2.
Note that 𝐶01) ± 𝐶′02) > 𝐶01) ∪𝐶′02)* as 𝐶01) and 𝐶′02) are disjoint by construction.
We deﬁne
𝐴𝑢0𝑆/ 𝑇) >

𝑏𝑢/𝐶· 𝑏𝑢/𝐶′ if ∃𝐶/ 𝐶′ ∈ℋ𝑢/ s.t. 𝑆
𝐶/𝐶′
↔𝑇/
0 otherwise.
$6.1)
If ℋis not simple* then the nonzero entry above is replaced with 
𝐶≠𝐶′∈ℋ𝑢:𝑆
𝐶/𝐶′
↔𝑇𝑏𝑢/𝐶· 𝑏𝑢/𝐶′. Note
that the the sum is over pairs of diﬀerent elements 𝐶/ 𝐶′ of the multiset ℋ$which may nonetheless
be equal as sets).
Our $overall) Kikuchi matrix 𝐴for the polynomial 𝑓is deﬁned as
𝐴:>
𝑝

𝑢>1
𝐴𝑢/
$6.2)
The matrix 𝐴allows us to write 𝑓as a quadratic form* as the following lemma shows.
Lemma 6.3. Let 𝑁:>
2𝑛
ℓ
Ynd let 𝐴be the Kikuchi mYtrix in Deﬁnition 6.2 YssociYted with Yn YrbitrYry
𝑝-bipYrtite 𝜓speciﬁed by Y bipYrtite hypergrYph ℋYnd coeﬂcients |𝑏𝑢/𝐶|𝑢∈*𝑝\/𝐶∈ℋ. For Yny 𝑥∈| 1/ 1|𝑛*
let 𝑥⊙ℓ∈| 1/ 1|𝑁be the vector where the 𝑆-th entry of 𝑥⊙ℓis 𝑥𝑆:> 
𝑏∈*2\

0𝑖/𝑏)∈𝑆𝑥𝑖. Then*
0𝑥⊙ℓ)⊤𝐴𝑥⊙ℓ> 𝑚2𝐷
𝑝
· 𝑓0𝑥)
$6.3)
for 𝐷Ys deﬁned in Eq. $6.6). ;s Y consequence* since 𝑥⊙ℓhYs ±1-vYlued entries* val0 𝑓) ⩽
𝑝
𝑚2𝐷}𝐴}∞→1.
Furthermore* for every pseudo-expectYtion 𝔼of degree ⩾2ℓover |±1|𝑛*
𝔼* 𝑓\ >
𝑝
𝑚2𝐷
𝔼*0𝑥⊙ℓ)⊤𝐴𝑥⊙ℓ\ ⩽𝐾𝐺·
𝑝
𝑚2𝐷}𝐴}∞→1 /
where 𝐾𝐺⩽1/8 is the universYl constYnt in FYct 3.6.
Proof. To see $6.3)* observe that by deﬁnition of 𝐴* if 𝑘is odd then every pair 0𝐶/ 𝐶′) in ℋ𝑢with
𝐶≠𝐶′ appears exactly
𝑘1
𝑘1
2
2 2𝑛20𝑘1)
ℓ0𝑘1)
> 𝐷times when we expand the LHS. This is because we
can choose 𝑆by ﬁrst picking its size 𝑘1
2
intersection with 𝐶01) and its intersection with 𝐶′02) $ 𝑘1
𝑘1
2
2
choices) and then picking the rest of the set $ 2𝑛20𝑘1)
ℓ0𝑘1)
choices)* and this also completely determines
𝑇. @ similar calculation yields the value of 𝐷when 𝑘is even* and so Eq. $6.3) then follows. This
is the place where we crucially use the ’clones“ of the variables to ensure that each pair 0𝐶/ 𝐶′)
appears the same number of times on the LHS. Without this trick* the number of times a pair 0𝐶/ 𝐶′)
appears would instead depend on ~𝐶∩𝐶′~.
The ’@s a consequence*...“ part now follows by the deﬁnition of the ∞→1 norm. The
’furthermore“ follows by Fact 3.6 and Fact 3.7.
Below* we summarize the deﬁnitions that we have made so far.
28

<!-- pdf-page: 31 -->
Jey Notation
1. The input polynomial 𝜓
𝜓0𝑦/ 𝑥) > 1
𝑚
𝑝

𝑢>1
𝑦𝑢

𝐶∈ℋ𝑢
𝑏𝑢/𝐶𝑥𝐶/
$6.4)
is 0𝜀/ ℓ)-regular* and 𝑝-bipartite* homogeneous of total degree 𝑘and is described by a
collection of 0𝑘
1)-uniform hypergraphs |ℋ𝑢|𝑢∈*𝑝\ one for every 𝑢∈*𝑝\ and a collection
of rationals |𝑏𝑢/𝐶|𝑢∈*𝑝\/𝐶∈ℋ𝑢.
2. The polynomial 𝑓obtained after the Cauchy-Schwarz trick applied to 𝜓:
𝑓0𝑥) > 𝑝
𝑚2
𝑝

𝑢>1

0𝐶/𝐶′)∈ℋ𝑢·ℋ𝑢/𝐶≠𝐶′
𝑏𝑢/𝐶𝑏𝑢/𝐶′𝑥𝐶𝑥𝐶′ /
$6.5)
is homogeneous of total degree 20𝑘
1). Furthermore* val0𝜓)2 ⩽val0 𝑓) ˜ 𝑝
𝑚⩽val0 𝑓) ˜ 𝜀2.
3. The Kikuchi matrix 𝐴> 
𝑢𝐴𝑢of 𝑓is an 𝑁· 𝑁matrix for 𝑁>
2𝑛
ℓ
. The entries of 𝐴are
indexed by sets 𝑆/ 𝑇⊆*𝑛\ · *2\ of size ℓand the entry 𝐴𝑢0𝑆/ 𝑇) is non-zero $and equal to
𝑏𝑢/𝐶𝑏𝑢/𝐶′) if and only if 𝑆
𝐶/𝐶′
↔𝑇for some distinct pair 𝐶/ 𝐶′ ∈ℋ𝑢. Each pair 0𝐶/ 𝐶′) from
ℋ𝑢contributes 𝐷non-zero entries in 𝐴where
𝐷>


𝑘1
𝑘1
2
2 2𝑛20𝑘1)
ℓ0𝑘1)

if 𝑘is odd
2 𝑘1
𝑘
2
𝑘1
𝑘2
2
2𝑛20𝑘1)
ℓ0𝑘1)

if 𝑘is even.
$6.6)
Furthermore* val0 𝑓) ⩽
𝑝
𝑚2𝐷}𝐴}∞→1.
We now describe our algorithm in the box below.
Refutation ;lgorithm for Regular Polynomials
;lgorithm 6.4.
Given: @n 0𝜀/ ℓ)-regular* 𝑝-bipartite polynomial 𝜓> 
𝑢

𝐶∈ℋ𝑢𝑏𝑢/𝐶𝑦𝑢𝑥𝐶in variables 𝑥/ 𝑦
speciﬁed by a collection of 0𝑘
1)-uniform hypergraphs |ℋ𝑢|𝑢∈*𝑝\ on *𝑛\ and rational
numbers |𝑏𝑢/𝐶|𝑢∈*𝑝\/𝐶∈ℋ𝑢in * 1/ 1\.
Output: @ value   ∈* 1/ 1\ such that
⩾val0𝜓).
Operation:
1. Construct 𝐴* the 𝑁· 𝑁Kikuchi matrix from Deﬁnition 6.2.
2. Compute the value of the following SDP: 𝑠> max𝑍∈𝑅𝑁·𝑁/𝑍⪰0/𝑍𝑆/𝑆>1 ∀𝑆tr0𝐴· 𝑍).
3. Output
>

𝑝
𝑚2𝐷· 𝑠˜ 𝑝
𝑚.
29

<!-- pdf-page: 32 -->
The crux of the analysis of the algorithm is captured in the following lemma that we establish in the
remaining part of this section.
Lemma 6.5 $Bounding }𝐴}∞→1). Let 𝐴be the Kikuchi mYtrix deﬁned in Deﬁnition 6.2. Then with
probYbility 1
10poly0𝑛) over the drYw of the 𝑏𝑢/𝐶–s*
}𝐴}∞→1 ⩽𝑚2𝐷𝜀2
𝑝
/
Observe that this lemma immediately ﬁnishes the proof of Theorem 5.4. Indeed* we clearly have
𝑠⩾val0 𝑓) 𝐷𝑚2
𝑝
because 𝑍> 𝑥⊙ℓ0𝑥⊙ℓ)⊤is a valid SDP solution with this value* and so by Lemma 6.1*
⩾val0𝜓) always holds. By Fact 3.6* we have 𝑠⩽1/8}𝐴}∞→1. We already argued that 𝑝
𝑚⩽𝜀2* and
so the output of our algorithm is at most
]
2/8𝜀. We note that we additionally require an additive
2 𝑛error in the ﬁnal algorithm because we can only eﬂciently solve SDPs up to an exponentially
small error.
6.2
Bounding }𝐴}∞→1: proof plan
Using Lemma 6.3* our task reduces to proving that }𝐴}∞→1 ⩽𝑚2𝐷𝜀2
𝑝
whenever 𝑏𝑢/𝐶—s are chosen
independently at random from distributions supported on * 1/ 1\. Our proof proceeds in three
conceptual steps:
1. Row pruning.
First* we remove all rows in 𝐴that have too large ℓ1 norm in any 𝐴𝑢and
show that this only incurs a small additive loss in our bound on }𝐴}∞→1. This is somewhat
delicate and crucially relies on regularity of the ℋ𝑢—s and a careful application of the celebrated
Schudy-Sviridenko polynomial concentration inequality for combinatorial polynomials [SS12\.
2. Row bucketing.
The row pruning ensures that no row has a large ℓ1-norm in any single
𝐴𝑢. Taking inspiration from spectral analyses of combinatorial random matrices* one might
expect that the spectral norm of 𝐴after row pruning is upper bounded. However* this turns
out not to be true when the ℋ𝑢—s are arbitrary regular hypergraphs. Instead* we show that
one can partition the row and columns of 𝐴so that in each bucket of the partition* all the
rows/columns have roughly equal contribution to the ’variance term“.
3. Spectral norm bound.
Our ﬁnal step involves proving a spectral norm upper bound on each
piece of the partition in order to upper bound its ∞→1 norm. This is the only step where
we use randomness of the right-hand sides 𝑏𝐶—s. While diﬀerent parts of the partition can
have larger spectral norm* this is compensated for by the fact that these partitions will have a
proportionally smaller number of rows/columns* thus yielding a good bound on the ∞→1
norm of 𝐴.
Let us now proceed with the details of each of the three steps above.
6.3
Row pruning
In order to implement our row pruning step* we will deﬁne bYd rows/columns of 𝐴𝑢for each 𝑢.
The following key deﬁnition abstracts out the property $of the hypergraphs deﬁning the input
polynomial) that decides which rows are bad:
30

<!-- pdf-page: 33 -->
De”nition 6.6 $Butterﬁy Degree). Let ℋ𝑢be a 0𝑘
1)-uniform hypergraph on *𝑛\. For any 𝐶/ 𝐶′ ∈ℋ𝑢*
let
ℛ0𝐶/𝐶′) >

𝑅⊆*𝑛\ · *2\
~𝑅~ > 𝑘
1/
𝑅∩𝐶01)/
𝑅∩𝐶′02)

>
𝑘
1
2

/
𝑘
1
2

/
For any 𝑆⊆*𝑛\ · *2\* and 0𝑘
1)-uniform hypergraph ℋ𝑢on *𝑛\* the butterﬁy degree of 𝑆in ℋ𝑢is
deﬁned by:
𝛾𝑢0𝑆) >

0𝐶/𝐶′)∈ℋ𝑢·ℋ𝑢/𝐶≠𝐶′

𝑅∈ℛ0𝐶/𝐶′)
10𝑆∩0𝐶01) ∪𝐶′02)) > 𝑅) /
For a collection of 0𝑘
1)-uniform hypergraphs ℋ𝑢on *𝑛\ for 𝑢∈*𝑝\* the totYl butterﬁy degree of 𝑆is
deﬁned by 𝛾0𝑆) > 
𝑢∈*𝑝\ 𝛾𝑢0𝑆).
We note that the notion of total butterﬁy degree above generalizes the notion of butterﬁy degree
studied in [@GK21\; the original notion of ’butterﬁy degree“ is so named because it counts numbers
of butterﬁy-shaped graphs.
The following lemma shows that the butterﬁy degree characterizes the ℓ1-norm of the rows of
the Kikuchi matrix 𝐴𝑢.
Lemma 6.7 $Butterﬁy Degree and the ℓ1 norm of rows of the Kikuchi Matrix). Let ℋ𝑢be Y 0𝑘
1)-
uniform hypergrYph on *𝑛\ Ynd 𝐴𝑢be the YssociYted mYtrix in Deﬁnition 6.2. Then* for Yny 𝑆⊆*𝑛\ · *2\*
we hYve:
𝛾𝑢0𝑆) ⩾

𝑇
~𝐴𝑢0𝑆/ 𝑇)~ /
Proof. If 𝑘is odd* we observe that 𝛾𝑢0𝑆) is the number pairs 0𝐶/ 𝐶′) ∈ℋ𝑢·ℋ𝑢with 𝐶≠𝐶′ such that
𝑆∩𝐶01)>
𝑆∩𝐶′02)> 𝑘1
2 * and if 𝑘is even* 𝛾𝑢0𝑆) is the number of pairs such that
𝑆∩𝐶01)> 𝑘
2
and
𝑆∩𝐶′02)> 𝑘2
2
or
𝑆∩𝐶01)> 𝑘2
2
and
𝑆∩𝐶′02)> 𝑘
2. The lemma now follows.
We now identify ’bad rows“ in 𝐴as those that have too large total butterﬁy degrees.
De”nition 6.8 $Δ-Bad rows in 𝐴). We deﬁne the set of Δ-bad rows in 𝐴to be:
ℬ:> |𝑆: ∃𝑢∈*𝑝\* 𝛾𝑢0𝑆) = Δ| /
Note that the set ℬdoes not depend on the values of the 𝑏𝑢/𝐶—s.
Observe that by Lemma 6.7* every row that is not bad has an ℓ1-norm that is not too large. The
following lemma bounds the number of bad rows in the Kikuchi matrix 𝐴. We defer the proof of
Lemma 6.9 to Section 6.5.
Lemma 6.9 $Bound on bad rows). Let 𝐴be the Kikuchi mYtrix YssociYted with the polynomiYl 𝑓obtYined
from Yn 0𝜀/ ℓ)-regulYr 𝑝-bipYrtite polynomiYl 𝜓of totYl degree 𝑘deﬁned by 0𝑘
1) uniform hypergrYphs
|ℋ𝑢|𝑢∈*𝑝\. Let ℬbe the set of Δ-bYd rows in 𝐴for
Δ > 𝑐𝑘1 1
𝜀4

ln
32𝑝𝑁
𝜀2𝐷
20𝑘1)
/
$6.7)
where 𝑐is Yn Ybsolute constYnt. Then ~ℬ~ ⩽𝜀2𝐷016.
31

<!-- pdf-page: 34 -->
This immediately implies the following corollary.
Corollary 6.1/ $Row pruning error). Let 𝐴𝒢/𝒢be the mYtrix obtYined by ’zeroing out“ 𝐴on Yll
rows/columns in ℬ. Then }𝐴
𝐴𝒢/𝒢}∞→1 ⩽𝑚2𝐷𝜀2
2𝑝
.
Proof of CorollYry 6.10 from LemmY 6.9. Let 𝐵> 𝐴
𝐴𝒢/𝒢. Let 𝑆⊆*𝑛\ · *2\ be an arbitrary row $or
column). We observe that the ℓ1 norm of the 𝑆-th row $or column) in 𝐵$or even in 𝐴) is naively
at most 𝑝
𝑢>1 ~ℋ𝑢~2. This is because each $ordered) pair 0𝐶/ 𝐶′) ∈ℋ𝑢· ℋ𝑢can contribute at most
one nonzero entry to the 𝑆-th row* namely to the 𝑇-th entry where 𝑇> 𝑆± 𝐶01) ± 𝐶′02) $and this
is only a valid entry if ~𝑇~ > ℓ). @s ~ℋ𝑢~ ⩽2𝑚0𝑝for all 𝑢* the ℓ1 norm of the 𝑆-th row is at most
𝑝· 4𝑚2
𝑝2 > 4𝑚20𝑝.
We next observe that if 𝐵0𝑆/ 𝑇) ≠0* then at least one of 𝑆/ 𝑇is in ℬ. Hence*
}𝐵}∞→1 ⩽

𝑆/𝑇
~𝐵0𝑆/ 𝑇)~ ⩽

𝑆∈ℬ

𝑇
~𝐵0𝑆/ 𝑇)~ ˜

𝑇∈ℬ

𝑆
~𝐵0𝑆/ 𝑇)~ ⩽2 ~ℬ~ · 4𝑚2
𝑝
/
@s ~ℬ~ ⩽𝜀2𝐷016* this is at most 𝑚2𝐷𝜀202𝑝* as required.
We will now ﬁnish the proof* using the following bound on }𝐴𝒢/𝒢}∞→1 that we will prove.
Lemma 6.11. Let 𝐴be the Kikuchi mYtrix YssociYted with the polynomiYl 𝑓obtYined from Yn 0𝜀/ ℓ)-regulYr
𝑝-bipYrtite polynomiYl 𝜓of totYl degree 𝑘deﬁned by 0𝑘
1) uniform hypergrYphs |ℋ𝑢|𝑢∈*𝑝\ Ynd coeﬂcients
|𝑏𝑢/𝐶|𝑢∈*𝑝\/𝐶∈ℋ𝑢. Then* with probYbility 1
10poly0𝑛) over the drYw of 𝑏𝑢/𝐶–s* it holds thYt
}𝐴𝒢/𝒢}∞→1 ⩽𝑂0log2 𝑚)𝑁Δ · 0log 𝑁˜ log log 𝑚) ˜ 𝑂0log 𝑚)

𝑁𝐷𝑚20log 𝑁˜ log log 𝑚)
𝑝
/
Finishing the proof of LemmY 6.5. By Corollary 6.10 and Lemma 6.11* we have with probability
1
10poly0𝑛)*
}𝐴}∞→1 ⩽}𝐴
𝐴𝒢/𝒢}∞→1 ˜ }𝐴𝒢/𝒢}∞→1
⩽𝑚2𝐷𝜀2
2𝑝
˜ 𝑂

log2 𝑚· 𝑁Δ · 0log 𝑁˜ log log 𝑚)

˜ 𝑂

log 𝑚

𝑁𝐷𝑚20log 𝑁˜ log log 𝑚)
𝑝


/
We now bound 𝑁
𝐷.
ClYim 6.12.
𝑁
𝐷⩽16𝑘1 · 0 𝑛
ℓ)𝑘1* where 𝐷is deﬁned as in Eq. $6.6).
Proof. We have
𝑁
𝐷⩽
2𝑛
ℓ

2𝑛20𝑘1)
ℓ0𝑘1)
> 0ℓ
0𝑘
1))
ℓ
·
02𝑛)
02𝑛
20𝑘
1)) · 02𝑛
ℓ
0𝑘
1))
02𝑛
ℓ)
⩽
𝑛
ℓ
𝑘1
·

ℓ
ℓ
0𝑘
1) · 4 ·
𝑛
2𝑛
ℓ
0𝑘
1)
𝑘1
⩽
𝑛
ℓ
𝑘1
· 16𝑘1 /
for 𝑛suﬂciently large* as ℓ⩾20𝑘
1).
32

<!-- pdf-page: 35 -->
By Claim 6.12* we thus have that 𝑂0log2 𝑚· 𝑁Δ0log 𝑁˜ log log 𝑚)) is at most 𝑚2𝐷𝜀2
4𝑝
. Indeed*
using that 𝑚⩽𝑛log2 𝑛* we have
𝑂01) 𝑝
𝜀2𝐷· 0log2 𝑚)2 · 𝑁Δ0log 𝑁˜ log log 𝑚)
⩽𝑂01)𝑘1 𝑝
𝜀2𝐷· 0log2 𝑛)5 · 𝑁ℓ· 1
𝜀4

ln032𝑝𝑁
𝜀2𝐷)
20𝑘1)
⩽𝑂01)𝑘1ℓ𝑝𝑁
𝜀6𝐷· 0log2 𝑛)5 · 0ln2 𝑛)20𝑘1) $as 𝑝⩽𝜀2𝑚and 𝑚⩽𝑛log2 𝑛)
⩽𝑂01)𝑘1ℓ𝑝
𝜀6
𝑛
ℓ
𝑘1
· 0log2 𝑛)4𝑘˜1 ⩽𝑚2 /
for 𝑛suﬂciently large* using the lower bound on 𝑚in Theorem 5.4.
Similarly* we also have 𝑂

log 𝑚

𝑁𝐷𝑚20log 𝑁˜log log 𝑚)
𝑝

is at most 𝑚2𝐷𝜀2
4𝑝
* as
𝑂01) ·
𝑝
𝜀2𝐷· log2 𝑚

𝑁𝐷𝑚20log 𝑁˜ log log 𝑚)
𝑝
⩽𝑂01) · 0log2 𝑛)2/5 · 𝑚
𝜀2 ·

𝑝𝑁ℓ
𝐷
⩽𝑂01)𝑘1 · 0log2 𝑛)2/5 · 𝑚
𝜀2 ·

𝑝ℓ·
𝑛
ℓ
𝑘1
2 ⩽𝑚2 /
again using the lower bound on 𝑚in Theorem 5.4. Hence* }𝐴}∞→1 ⩽𝑚2𝐷𝜀2
𝑝
* which ﬁnishes the
proof.
We now prove Lemma 6.11 $bounding }𝐴𝒢/𝒢}∞→1) and Lemma 6.9 $bound on bad rows).
6.4
Bounding the ∞→1 norm of the ’good rows“: proof of Lemma 6.11
Let us denote 𝐴𝒢/𝒢–the matrix obtained by zeroing out all rows in ℬfrom the Kikuchi matrix
𝐴–by 𝐺in this subsection for ease of notation. Similarly* we let 𝐺𝑢:> 0𝐴𝑢)𝒢/𝒢be the matrix
obtained by zeroing out all rows and columns in ℬfrom the Kikuchi matrix 𝐴𝑢. Since 𝐴> 𝑝
𝑢>1 𝐴𝑢*
we must have 𝐺> 𝑝
𝑢>1 𝐺𝑢.
@t a high level* the idea of the proof is to split 𝐺> 
𝑖/𝑗𝐺0𝑖/𝑗) into 𝑂0log2 𝑚) submatrices 𝐺0𝑖/𝑗)
such that $1) each entry 0𝑆/ 𝑇) is non-zero in exactly one of 𝐺0𝑖/𝑗) and in that case* equals 𝐺0𝑆/ 𝑇)
and $2) all non-zero rows $or columns) in any given 𝐺0𝑖/𝑗) have roughly the same butterﬁy degree.
This splitting accomplishes our ’row bucketing“ step. The second property above allows us to
infer a reasonably good upper bound on the ∞→1 norm of 𝐺0𝑖/𝑗) in terms of an appropriately
scaled spectral norm bound on 𝐺0𝑖/𝑗) – we will provide two diﬀerent proofs of this fact* one using
the Matrix Bernstein inequality and the other based on the trace moment method. The ﬁrst proof is
simple but somewhat opaque in that it uses a powerful concentration inequality. The second proof
is a little more elaborate but will be directly useful in Section 8. We will then use the bounds on
𝐺0𝑖/𝑗)
2 to upper bound the ∞→1 norm of 𝐺> 𝐴𝒢/𝒢.
Let us start by deﬁning the row bucketing formally by deﬁning the 𝐺0𝑖/𝑗)—s.
33

<!-- pdf-page: 36 -->
De”nition 6.13 $Row bucketing). Let 𝑑> 4𝑚2𝐷
𝑝𝑁
⩾1. Deﬁne a partition of the rows of the matrix 𝐺
into ℱ0 ∪ℱ1 ∪/ / / ℱ𝑡as follows: Set ℱ0 :> |𝑆∈𝒢: 𝛾0𝑆) ⩽𝑑|. For each 𝑡⩾𝑖⩾1* let
ℱ𝑖:> |𝑆∈𝒢: 2𝑖1𝑑= 𝛾0𝑆) ⩽2𝑖𝑑| /
Observe that since 𝛾0𝑆) ⩽𝑝
𝑢>1 ~ℋ𝑢~2 ⩽𝑚2 and 𝑑⩾1* every good row index 𝑆∈𝒢is in some ℱ𝑖
for 𝑖⩽𝑡> 2 log2 𝑚. Thus* the ℱ𝑖—s for 𝑖⩽2 log2 𝑚form a partition of all the rows of 𝐺.
For each 𝑖/ 𝑗∈|0/ 1/ / / / / 𝑡|* let 𝐺0𝑖/𝑗) be the submatrix of 𝐺such that for any entry 0𝑆/ 𝑇)* if
𝑆∈ℱ𝑖/ 𝑇∈ℱ𝑗* 𝐺0𝑖/𝑗)0𝑆/ 𝑇) > 𝐺0𝑆/ 𝑇) and 𝐺0𝑖/𝑗)0𝑆/ 𝑇) > 0 otherwise.
Lemma 6.14 $Size of ℱ𝑖—s). Let ℱ0 ∪ℱ1 ∪/ / / ℱ𝑡for 𝑡⩽2 log2 𝑚be the pYrtition of the rows of the mYtrix
𝐺constructed in Deﬁnition 6.13. Then* ~ℱ0~ ⩽𝑁Ynd ~ℱ𝑖~ ⩽21 𝑖𝑁for eYch 𝑖∈*𝑡\.
Proof. The bound on ~ℱ0~ is trivial. For 𝑖⩾1* we observe that 2𝑖1𝑑~ℱ𝑖~ = 
𝑆∈ℱ𝑖𝛾0𝑆) ⩽
𝑆𝛾0𝑆) ⩽
𝐷𝑝
𝑢>1 ~ℋ𝑢~2 > 𝐷· 4𝑚2
𝑝
> 𝑑𝑁* as every $ordered) pair 0𝐶/ 𝐶′) ∈ℋ𝑢· ℋ𝑢with 𝐶≠𝐶′ appears in
exactly 𝐷entries in the original matrix 𝐴.
We now come to the key part of the proof that establishes an upper bound on the spectral norm
of each 𝐺0𝑖/𝑗).
Lemma 6.15 $Spectral norm of 𝐺0𝑖/𝑗)—s). Let the 𝐺0𝑖/𝑗)–s be the mYtrices deﬁned in Deﬁnition 6.13. Then*
for eYch 𝑖/ 𝑗∈|0/ / / / / 𝑡|* with probYbility 1
1
log2
2 𝑚·poly0𝑛) over the drYw of the 𝑏𝑢/𝐶–s*
𝐺0𝑖/𝑗)
2 ⩽𝑂01) · Δ0log 𝑁˜ log log 𝑚) ˜ 𝑂01) · 20/5 max0𝑖/𝑗)
𝑑0log 𝑁˜ log log 𝑚) /
This is enough to immediately complete the proof of Lemma 6.11.
Proof of LemmY 6.11. The total number of pairs of 0𝑖/ 𝑗) such that 𝑖/ 𝑗⩽𝑡> 2 log2 𝑚is at most 4 log2
2 𝑚.
Thus* applying Lemma 6.15 and doing a union bound over all 0𝑖/ 𝑗) yields that with probability
at least 1
10poly0𝑛) over the draw of the 𝑏𝑢/𝐶—s*
𝐺0𝑖/𝑗)
2 ⩽𝑂01) · Δ0log 𝑁˜ log log 𝑚) ˜ 𝑂01) ·
20/5 max0𝑖/𝑗)
𝑑0log 𝑁˜ log log 𝑚) for every 𝑖/ 𝑗simultaneously. Let us condition on this event in the
following.
The ﬁnal idea in the proof is to observe the following key fact: for any 𝑦/   ∈|±1|𝑁* we must
have:
𝑦⊤𝐺0𝑖/𝑗)  > 𝑦⊤
ℱ𝑖𝐺0𝑖/𝑗) ℱ𝑗⩽
𝑦ℱ𝑖

2
 ℱ𝑗

2
𝐺0𝑖/𝑗)
2 >

~ℱ𝑖~~ℱ𝑗~
𝐺0𝑖/𝑗)
2 /
In the ﬁrst equality we used the fact that only the rows in ℱ𝑖$and columns in ℱ𝑗* respectively) are
non-zero in 𝐺0𝑖/𝑗) and in the inequality* we used the deﬁnition of the spectral norm.
Thus* we must have:
}𝐺0𝑖/𝑗)}∞→1 >
max
𝑦/ ∈|±1|𝑁𝑦⊤𝐺0𝑖/𝑗)  ⩽

~ℱ𝑖~~ℱ𝑗~
𝐺0𝑖/𝑗)
2 /
Thus* by triangle inequality for }·}∞→1* we have:
}𝐺}∞→1 ⩽
𝑡
𝑖>0
𝑡
𝑗>0
}𝐺0𝑖/𝑗)}∞→1 ⩽
𝑡
𝑖>0
𝑡
𝑗>0

~ℱ𝑖~
ℱ𝑗

𝐺0𝑖/𝑗)
2
34

<!-- pdf-page: 37 -->
⩽𝑂0𝑁𝑡2Δ0log 𝑁˜ log log 𝑚)) ˜ 2
𝑡
𝑖>0
𝑡
𝑗>𝑖
𝑁

22 𝑖𝑗· 𝑂01) · 20/5𝑗
𝑑0log 𝑁˜ log log 𝑚)
> 𝑂0𝑁𝑡2Δ0log 𝑁˜ log log 𝑚)) ˜ 𝑂0𝑁

𝑑0log 𝑁˜ log log 𝑚))
𝑡
𝑖>0
𝑡
𝑗>𝑖
2 0/5𝑖
> 𝑂0𝑁𝑡2Δ0log 𝑁˜ log log 𝑚)) ˜ 𝑂0𝑁𝑡

𝑑0log 𝑁˜ log log 𝑚)) /
@s 𝑡> 𝑂0log 𝑚) and 𝑑> 4𝑚2𝐷
𝑝𝑁* Lemma 6.11 follows.
We now complete the proof of Lemma 6.15. We present two diﬀerent proofs of Lemma 6.15.
The ﬁrst is a simple proof using the Matrix Bernstein inequality. The second proof is based on the
trace moment method* and will be important to us in Section 8.
6.4.1
Proof of Lemma 6.15 using Matrix Bernstein inequality
Proof. Fix a pair 0𝑖/ 𝑗). We can write 𝐺0𝑖/𝑗) as 𝑝
𝑢>1 𝐺0𝑖/𝑗)
𝑢
. Then the 𝐺0𝑖/𝑗)
𝑢
—s are independent random
matrices* as 𝑏𝑢/𝐶and 𝑏𝑢′/𝐶′ are independent for 𝑢≠𝑢′. We will apply Matrix Bernstein $Fact 3.1) to
the 𝐺0𝑖/𝑗)
𝑢
—s.
Because all nonzero rows $columns) 𝑆in the 𝐺0𝑖/𝑗)
𝑢
—s must have 𝑆∈𝒢* it follows that 𝛾𝑢0𝑆) ⩽Δ
for every 𝑢. In particular* the ℓ1 norm of any row $column) in 𝐺0𝑖/𝑗)
𝑢
is at most Δ* and so
𝐺0𝑖/𝑗)
𝑢

2 ⩽Δ
always holds.
We now compute the ’variance term“ 𝜎2 in Fact 3.1. Let 𝑀> 𝔼*𝑝
𝑢>1 𝐺0𝑖/𝑗)
𝑢
𝐺0𝑖/𝑗)
𝑢
⊤
\* where the
expectation is taken over the 𝑏𝑢/𝐶—s. The ℓ1 norm of the 𝑆-th row in 𝑀is
𝑝

𝑢>1

𝑇∈ℱ𝑖

𝑅∈ℱ𝑗
𝔼*𝐺0𝑖/𝑗)
𝑢
0𝑆/ 𝑅)𝐺0𝑖/𝑗)
𝑢
0𝑇/ 𝑅)\ /
Because the 𝑏𝑢/𝐶—s are mean zero* 𝔼*𝐺0𝑖/𝑗)0𝑆/ 𝑅)𝐺0𝑖/𝑗)0𝑇/ 𝑅)\ is nonzero iﬀthere exist 𝐶/ 𝐶′ ∈ℋ𝑢with
𝐶≠𝐶′ such that 𝑆± 𝑅> 𝐶01) ± 𝐶′02) and either 𝑇± 𝑅> 𝐶01) ± 𝐶′02) or 𝑇± 𝑅> 𝐶02) ± 𝐶′01)* and when
this occurs the expectation of the corresponding term is at most 1. $If ℋis non-simple* then the
expectation will simply be the sum over valid choices for 𝐶/ 𝐶′.) For each 𝑢* there are at most 𝛾𝑢0𝑆)
such 𝑅—s* and each contributes at most 2 $for the two diﬀerent choices of 𝑇) to the sum. Hence* the
ℓ1-norm of the 𝑆-th row in 𝑀is at most 2 𝑝
𝑢>1 𝛾𝑢0𝑆) > 2𝛾0𝑆). @s 𝑆∈ℱ𝑖* we must have 𝛾0𝑆) ⩽2𝑖𝑑*
and so we have }𝑀}2 ⩽2𝑖˜1𝑑.
Swapping the roles of 𝑖and 𝑗* we see that we can take 𝜎2 > 2 · 2max0𝑖/𝑗)𝑑. @pplying Fact 3.1
then yields that with probability 1
1
log2
2 𝑚·poly0𝑁) ⩾1
1
log2
2 𝑚·poly0𝑛)* we have
𝐺0𝑖/𝑗)
2 ⩽𝑂0Δ0log 𝑁˜
log log 𝑚) ˜

2max0𝑖/𝑗)𝑑0log 𝑁˜ log log 𝑚))* which ﬁnishes the proof.
6.4.2
Proof of Lemma 6.15 using trace moment method
Proof. Let 𝑍> 𝐺0𝑖/𝑗) and 𝑍𝑢> 𝐺0𝑖/𝑗)
𝑢
* and let 𝑟∈ℕ. We observe that }𝑍}2𝑟
2 ⩽tr00𝑍𝑍⊤)𝑟). We will
proceed with the proof in two steps. First* we upper bound 𝔼*tr00𝑍𝑍⊤)𝑟)\ by a combinatorial
35

<!-- pdf-page: 38 -->
quantity: the number of ’even walk sequences“* which we deﬁne below. Then* we bound the
number of such sequences.
De”nition 6.16. Let 𝑆∈ℱ𝑖. We say that a sequence 0𝑢1/ 𝐶1/ 𝐶′
1)/ / / / / 0𝑢2𝑟/ 𝐶2𝑟/ 𝐶′
2𝑟) with 𝑢ℎ∈*𝑝\
and 𝐶ℎ≠𝐶′
ℎ∈ℋ𝑢ℎis a ’walk sequence“ for 𝑆if the sets 𝑇ℎ:> 𝑆± 
𝑗=ℎ0𝐶01)
𝑗
± 𝐶′
𝑗
02)) each have
size exYctly ℓand the entries 𝑍𝑢2ℎ10𝑇2ℎ1/ 𝑇2ℎ) and 𝑍𝑢2ℎ0𝑇2ℎ˜1/ 𝑇2ℎ) are nonzero for each ℎ> 1/ / / / / 𝑟.
Moreover* the sequence is even if each 0𝑢/ 𝑄) appears an even number of times in the multiset
|0𝑢ℎ/ 𝐶ℎ)/ 0𝑢ℎ/ 𝐶′
ℎ)|ℎ∈*2𝑟\.
Proposition 6.17. 𝔼*tr00𝑍𝑍⊤)𝑟)\ ⩽
𝑆∈ℱ𝑖  {even wYlk sequences 0𝑢1/ 𝐶1/ 𝐶′
1)/ / / / / 0𝑢2𝑟/ 𝐶2𝑟/ 𝐶′
2𝑟) for 𝑆|.
Lemma 6.18 $Sequence counting). For eYch 𝑆
∈
ℱ𝑖* the number of even wYlk sequences
0𝑢1/ 𝐶1/ 𝐶′
1)/ / / / / 0𝑢2𝑟/ 𝐶2𝑟/ 𝐶′
2𝑟) for 𝑆is Yt most 04𝑟)𝑟02max0𝑖/𝑗)𝑑˜ 𝑟Δ2)𝑟.
We observe that Proposition 6.17 and Lemma 6.18 immediately imply Lemma 6.15. Indeed* we
have that
𝔼*tr00𝑍𝑍⊤)𝑟)\ ⩽~ℱ𝑖~ 04𝑟)𝑟02max0𝑖/𝑗)𝑑˜ 𝑟Δ2)𝑟⩽𝑁04𝑟)𝑟02max0𝑖/𝑗)𝑑˜ 𝑟Δ2)𝑟/
and hence by Markov—s inequality*
ℙ*}𝑍}2 ⩾𝜆\ ⩽𝔼*}𝑍}2𝑟
2 \
𝜆2𝑟
⩽𝑁04𝑟)𝑟02max0𝑖/𝑗)𝑑˜ 𝑟Δ2)𝑟
𝜆2𝑟
/
Taking 𝑟> 
log2 𝑁˜ log2 log2 𝑚
and 𝜆> 𝑐]𝑟0
]
2max0𝑖/𝑗)𝑑˜ 𝑟Δ2) for a large enough absolute
constant 𝑐thus implies
ℙ*}𝑍}2 ⩾𝑐

2max0𝑖/𝑗)𝑑𝑟˜ Δ2𝑟2\ ⩽𝑁4𝑟
𝑐2𝑟⩽
1
poly0𝑁) · polylog0𝑚) /
Finally* we observe that
]
2max0𝑖/𝑗)𝑑𝑟˜ Δ2𝑟2 ⩽
]
2max0𝑖/𝑗)𝑑𝑟˜ Δ𝑟* which ﬁnishes the proof
of Lemma 6.15* as 𝑟⩽𝑂0log 𝑁˜ log log 𝑚).
We now prove Proposition 6.17 and Lemma 6.18.
Proof of Proposition 6.17. We compute:
𝔼*tr00𝑍𝑍⊤)𝑟)\ >

0𝑢1/𝑆1)/////0𝑢2𝑟/𝑆2𝑟)
𝔼*
𝑟

ℎ>1
𝑍𝑢2ℎ10𝑆2ℎ1/ 𝑆2ℎ)𝑍𝑢2ℎ0𝑆2ℎ˜1/ 𝑆2ℎ)\ /
where we use the convention that 𝑢2𝑟˜1 :> 𝑢1 and 𝑆2𝑟˜1 :> 𝑆1. Next* we observe that this is equal to
>

𝑆∈ℱ𝑖

0𝑢1/𝐶1/𝐶′
1)/////0𝑢2𝑟/𝐶2𝑟/𝐶′
2𝑟) walk sequence for 𝑆
𝔼*
𝑟

ℎ>1
𝑍𝑢2ℎ10𝑇2ℎ1/ 𝑇2ℎ)𝑍𝑢2ℎ0𝑇2ℎ˜1/ 𝑇2ℎ)\
>

𝑆∈ℱ𝑖

0𝑢1/𝐶1/𝐶′
1)/////0𝑢2𝑟/𝐶2𝑟/𝐶′
2𝑟) walk sequence for 𝑆
𝔼*
𝑟

ℎ>1
𝑏𝑢2ℎ1/𝐶2ℎ1𝑏𝑢2ℎ1/𝐶′
2ℎ1𝑏𝑢2ℎ/𝐶2ℎ𝑏𝑢2ℎ/𝐶′
2ℎ\
36

<!-- pdf-page: 39 -->
⩽

𝑆∈ℱ𝑖
# even walk sequences 0𝑢1/ 𝐶1/ 𝐶′
1)/ / / / / 0𝑢2𝑟/ 𝐶2𝑟/ 𝐶′
2𝑟) for 𝑆/
as the term in the sum is 0 unless the walk sequence is even.
Proof of LemmY 6.18. We shall upper bound the number of such sequences for each 𝑆via an
encoding argument.
For a set 𝑆∈ℱ𝑖and 𝑢∈*𝑝\* we will say that 𝐶/ 𝐶′ ∈ℋ𝑢extends 𝑆if
𝑍𝑢0𝑆/ 𝑆± 𝐶01) ± 𝐶′02)) is well-deﬁned and non-zero. For 𝑆∈ℱ𝑗* we make a similar deﬁnition*
requiring that 𝑍𝑢0𝑆± 𝐶01) ± 𝐶′02)/ 𝑆) is well-deﬁned and non-zero. The encoding is as follows:
$1) Choose   ∈*𝑟\* the number of distinct 𝑢—s that appear in the sequence. Note that   must be at
most 𝑟because the sequence is even; 𝑢ℎcannot appear once in |𝑢1/ / / / / 𝑢2𝑟|* as then we must
pair 0𝑢ℎ/ 𝐶ℎ) with 0𝑢ℎ/ 𝐶′
ℎ)* but we must have 𝐶ℎ≠𝐶′
ℎ.
$2) Choose 2  locations 𝐿in *2𝑟\. These will denote the ﬁrst and last occurrence of each distinct 𝑢ℎ
for ℎ∈* \.
$3) Choose a perfect matching 𝜋for the 2  chosen locations. We will think of 𝜋as a function
𝜋: 𝐿→* \* satisfying 𝑡1 = 𝑡2 = · · · = 𝑡 * where 𝑡ℎis the ﬁrst preimage of ℎin 𝐿$using the
natural ordering on 𝐿inherited from *2𝑟\). We let 𝑡′
ℎdenote the second preimage of ℎin 𝐿.
$4) Proceed in order of steps 𝑡> 1/ / / / / 2𝑟. We thus know the set 𝑆𝑡that we are currently ’at“.
There are three cases.
$a) Suppose 𝑡> 𝑡ℎfor some ℎ. Then* $1) choose 𝑢∈*𝑝\ $that has not yet been chosen); $2) choose
𝐶/ 𝐶′ ∈ℋ𝑢extending 𝑆𝑡; $3) set the 𝑡-th element of the sequence to be 0𝑢/ 𝐶/ 𝐶′).
$b) Suppose that 𝑡≠𝑡ℎ/ 𝑡′
ℎfor all ℎ∈* \. Then* pick a previously chosen 𝑢$that has not yet
reached its last occurrence according to the matching 𝜋)* and pick 𝐶/ 𝐶′ ∈ℋ𝑢that extends
𝑆𝑡. Set the 𝑡-th element of the sequence to be 0𝑢/ 𝐶/ 𝐶′).
$c) Suppose that 𝑡> 𝑡′
ℎfor some ℎ. Then* choose 𝑢> 𝑢ℎand let 𝐶/ 𝐶′ ∈ℋ𝑢be the unique pair
that extends 𝑆𝑡and keeps the sequence even. Set the 𝑡-th element of the sequence to be
either 0𝑢/ 𝐶/ 𝐶′) or 0𝑢/ 𝐶′/ 𝐶).
We now count the number of choices. Let us ﬁrst think of the ﬁrst 3 steps as ﬁxed. There are 3 cases.
If we are choosing a new 𝑢* then there are 
𝑢𝛾𝑢0𝑆𝑡) ⩽2max0𝑖/𝑗)𝑑ways to pick 0𝑢/ 𝐶/ 𝐶′). If we are
choosing an old 𝑢* then there are  Δ ways to pick 0𝑢/ 𝐶/ 𝐶′)* as we have   choices for 𝑢and then
𝛾𝑢0𝑆𝑡) ⩽Δ choices for the pair 𝐶/ 𝐶′. Finally* if we are at 𝑡> 𝑡′
ℎfor some ℎ* then we have 2 choices.
Hence* across all steps* we have 02max0𝑖/𝑗)𝑑)  · 2  · 0 Δ)2𝑟2  choices.
Next* we think of   as ﬁxed* and count the choices for Steps $2) and $3). These have
2𝑟
2 choices
and 02 )
2   choices* respectively. Combining* we thus have the bound
# 0𝑢1/ 𝐶1/ 𝐶′
1)/ / / / / 0𝑢2𝑟/ 𝐶2𝑟/ 𝐶′
2𝑟) even* well-formed for 𝑆⩽
𝑟
 >1
2𝑟
2 02 )
2   02max0𝑖/𝑗)𝑑)  · 2  · 0 Δ)2𝑟2  /
We now observe that
2𝑟
2 02 )
  2𝑟2  >
02𝑟)
02𝑟
2 )   ·  2𝑟2 37

<!-- pdf-page: 40 -->
> 02𝑟)
𝑟𝑟
· 0𝑟
 ) 0𝑟
 )
02𝑟
2 )
·
𝑟
0𝑟
 ) ·
𝑟
  0𝑟
 ) ·  2𝑟2 ⩽22𝑟· 1 · 𝑟  ·
𝑟
 
· 𝑟2𝑟2 ⩽04𝑟)𝑟
𝑟
 
𝑟𝑟  /
Thus*
𝑟
 >1
2𝑟
2 02 )
2   02max0𝑖/𝑗)𝑑)  · 2  · 0 Δ)2𝑟2  ⩽04𝑟)𝑟
𝑟
 >1
𝑟
 
02max0𝑖/𝑗)𝑑)  · 0𝑟Δ2)𝑟 ⩽04𝑟)𝑟02max0𝑖/𝑗)𝑑˜ 𝑟Δ2)𝑟/
which ﬁnishes the proof.
6.5
Bounding the number of bad rows: proof of Lemma 6.9
Let 𝒰ℓbe the uniform distribution on subsets of *𝑛\ · *2\ of size exactly ℓ. In order to bound the
fraction of bad rows $i.e. the size of ~ℬ~)* we will analyze the probability that a draw from 𝒰ℓ
produces a set 𝑆that indexes a bad row in the Kikuchi matrix 𝐴.
We will do this by viewing 𝛾𝑢0𝑆) as a polynomial of degree 𝑘
1 in the indicator vector of the
set 𝑆:
Lemma 6.19 $Polynomial View of 𝛾𝑢0𝑆)). Let 𝑃𝑢be the following polynomiYl in vYriYbles | 0𝑖/𝑏)|𝑖⩽𝑛/𝑏∈|1/2|:
𝑃𝑢0 ) >

0𝐶/𝐶′)∈ℋ𝑢·ℋ𝑢/𝐶≠𝐶′

𝑅∈ℛ0𝐶/𝐶′)
 𝑅/
where  𝑅:> 
0𝑖/𝑏)∈𝑅 𝑖/𝑏. Then* for every 𝑆⊆*𝑛\ · *2\* we hYve: 𝛾𝑢0𝑆) ⩽𝑃𝑢01𝑆)* where 1𝑆is the 0-1
indicYtor of the set 𝑆$i.e.* 1𝑆hYs Y 1 in the 0𝑖/ 𝑏)-th coordinYte if Ynd only if 0𝑖/ 𝑏) ∈𝑆).
Proof. By Deﬁnition 6.6* we have:
𝛾𝑢0𝑆) >

0𝐶/𝐶′)∈ℋ𝑢·ℋ𝑢/𝐶≠𝐶′

𝑅∈ℛ0𝐶/𝐶′)
10𝑆∩0𝐶01)∪𝐶′02)) > 𝑅) ⩽

0𝐶/𝐶′)∈ℋ𝑢·ℋ𝑢/𝐶≠𝐶′

𝑅∈ℛ0𝐶/𝐶′)
10𝑅⊆𝑆) > 𝑃𝑢01𝑆) /
Thus* it is enough to upper bound the probability of the event 𝑃𝑢0 ) ⩾Δ under 𝒰ℓ. Next* we
will switch 𝒰ℓwith a more convenient-to-analyze product distribution 𝒰′
ℓon  . The following
lemma argues why this suﬂces for our purpose:
Lemma 6.2/ $Switching to a Product Distribution). Let 𝒰′
ℓbe the distribution where eYch element 0𝑖/ 𝑏)
in *𝑛\ · *2\ is included in 𝑆independently with probYbility 𝑞>
ℓ
2𝑛01 ˜ 𝛽) $equivYlently* eYch  𝑖/𝑏is Yn
independent Bernoulli0𝑞) rYndom vYriYble) where 𝛽> max

4
ℓln0 32𝑝𝑁
𝜀2𝐷)/

4
ℓln0 32𝑝𝑁
𝜀2𝐷)

. Then* for Yny 𝜆*
ℙ
 ←𝒰ℓ
*𝑃𝑢0 ) = 𝜆\ ⩽
ℙ
 ←𝒰′
ℓ
*𝑃𝑢0 ) = 𝜆\ ˜ 𝜀2𝐷
32𝑝𝑁/
38

<!-- pdf-page: 41 -->
Note that under 𝒰′
ℓ* the set sampled does not always have size exactly ℓ.
Proof. To relate the two probabilities* we will couple 𝒰′
ℓwith 𝒰ℓas follows. First* sample 𝑇←𝒰′
ℓ*
and then choose 𝑆to be a uniformly random subset of 𝑇of size exactly ℓ$if ~𝑇~ = ℓ* then abort).
Let 𝒥be the joint distribution induced by this coupling. By Chernoﬀbound* we have for every
𝛿∈*0/ 1\*
ℙ
𝑇∼𝒰′
ℓ
*~𝑇~ = 01
𝛿)01 ˜ 𝛽)ℓ\ ⩽exp
𝛿2ℓ01 ˜ 𝛽)
2

/
Setting 𝛿> 1
1
1˜𝛽* we see that ℙ𝑇∼𝒰′
ℓ*~𝑇~ = ℓ\ ⩽
𝜀2𝐷
32𝑝𝑁* as
𝛽2
1˜𝛽⩾2
ℓln0 32𝑝𝑁
𝜀2𝐷)* by choice of 𝛽.
We also observe that 𝑃𝑢0𝑇) ⩾𝑃𝑢0𝑆) for Yny 𝑆⊆𝑇. In particular* if we ﬁrst sample 𝑇←𝒟′ and
𝑃𝑢0𝑇) ⩽𝜆* then it also holds that 𝑃𝑢0𝑆) ⩽𝜆* regardless of the choice of 𝑆. We thus have
ℙ
𝑆←𝒰ℓ
*𝑃𝑢0𝑆) = 𝜆\ ⩽
ℙ
0𝑆/𝑇)∼𝒥*𝑃𝑢0𝑇) = 𝜆~ ~𝑇~ ⩾ℓ\ ⩽
ℙ
𝑇←𝒰′
ℓ
*𝑃𝑢0𝑇) = 𝜆\ ˜ 𝜀2𝐷
32𝑝𝑁/
We now ﬁnish the proof of Lemma 6.9 by analyzing ℙ𝒰′
ℓ*𝑃𝑢0 ) ⩾Δ\:
Proof of LemmY 6.9. In order to bound the probability that 𝑃𝑢0 ) ⩾Δ under 𝒰′
ℓ* let—s apply the
polynomial concentration inequality $Fact 3.2). Let—s ﬁrst bound 𝔼𝒰′
ℓ*𝑃𝑢0 )\. Let 𝑞>
ℓ
2𝑛01 ˜ 𝛽) as in
Lemma 6.20. We have
𝔼
 ←𝒰′
ℓ
*𝑃𝑢0 )\ >

0𝐶/𝐶′)∈ℋ𝑢·ℋ𝑢/𝐶≠𝐶′
𝑞𝑘1 ·
ℛ0𝐶/𝐶′)
> 𝑤𝑘𝑞𝑘1 ~ℋ𝑢~ 0~ℋ𝑢~
1) /
where 𝑤𝑘:>
𝑘1
𝑘1
2
2 if 𝑘is odd and 𝑤𝑘:> 2 𝑘1
𝑘
2
𝑘1
𝑘2
2
if 𝑘is even.
Let 𝜂> 4 ln

32𝑝𝑁
𝜀2𝐷

. Notice that 𝜂⩾4 ln 32 ⩾1* as 𝑁0𝐷⩾1* 𝑝⩾1* and 𝜀= 1 all hold. We also
observe that 1˜𝛽
2
⩽𝜂.
Recall that by regularity of the polynomial 𝜓$described by |ℋ𝑢|𝑢∈*𝑝\)* we have that deg𝑢0𝑄) ⩽
1
𝜀2
𝑛
ℓ
𝑘
2
1 ~𝑄~ for all 𝑄⊆*𝑛\* ~𝑄~ ⩽𝑘2
2 . In particular* this means that ~ℋ𝑢~ > deg𝑢0∅) ⩽
1
𝜀2
𝑛
ℓ
𝑘
2
1*
and thus
𝔼
 ←𝒰′
ℓ
*𝑃𝑢0 )\ ⩽𝑤𝑘
1 ˜ 𝛽
2
𝑘1 1
𝜀4
ℓ
𝑛⩽𝑤𝑘𝜂𝑘1 1
𝜀4
ℓ
𝑛/
We now compute the parameters 𝜈𝑟for 𝑟> 0/ / / / / 𝑘
1 that appear in the statement of Fact 3.2.
We have
𝜈𝑟>
max
𝑅⊆*𝑛\·*2\/~𝑅~>𝑟

0𝐶/𝐶′)∈ℋ𝑢·ℋ𝑢/𝐶≠𝐶′

𝑅′∈ℛ0𝐶/𝐶′)
10𝑅⊆𝑅′) · 𝑞𝑘1 ~𝑅~ /
Letting 𝑅1 and 𝑅2 denote 𝑅∩*𝑛\ · |1| and 𝑅∩*𝑛\ · |2|* we see that if 𝑅⊆𝑅′ and 𝑅′ ∈ℛ0𝐶/𝐶′)* then
this implies that 𝑅⊆𝐶01) ∪𝐶′02)* and that $if 𝑘is odd) ~𝑅1~ / ~𝑅2~ ⩽𝑘1
2 or $if 𝑘is even) ~𝑅1~ / ~𝑅2~ ⩽𝑘
2.
For each 𝑅* the number of 𝐶01) ∪𝐶′02) such that 𝑅⊆𝐶01) ∪𝐶′02) is at most deg𝑢0𝑅1) deg𝑢0𝑅2)* and
39

<!-- pdf-page: 42 -->
the number of 𝑅′ with 𝑅⊆𝑅′ ⊆𝐶01) ∪𝐶′02) is at most
ℛ0𝐶/𝐶′)
> 𝑤𝑘. We thus have
𝜈𝑟⩽𝑤𝑘𝑞𝑘1 𝑟
max
𝑅1/𝑅2⊆*𝑛\/~𝑅1~˜~𝑅2~>𝑟/~𝑅1~/~𝑅2~⩽𝑘1
2
deg𝑢0𝑅1) deg𝑢0𝑅2) $if 𝑘is odd)
𝜈𝑟⩽𝑤𝑘𝑞𝑘1 𝑟
max
𝑅1/𝑅2⊆*𝑛\/~𝑅1~˜~𝑅2~>𝑟/~𝑅1~/~𝑅2~⩽𝑘
2
deg𝑢0𝑅1) deg𝑢0𝑅2) $if 𝑘is even) /
Fix 𝑅1/ 𝑅2 that maximize the above expression. Because the ℋ𝑢—s are 0𝜀/ ℓ)-regular* we have that
deg𝑢0𝑅𝑏) ⩽
1
𝜀2
𝑛
ℓ
𝑘
2
1 ~𝑅𝑏~ if ~𝑅𝑏~ ⩽𝑘2
2 * and deg𝑢0𝑅𝑏) ⩽
1
𝜀2 if ~𝑅𝑏~ > 𝑘1
2
$if 𝑘odd) or 𝑘
2 $if 𝑘even).
So* if ~𝑅𝑏~ ⩽𝑘2
2 * then it holds that
deg𝑢0𝑅𝑏)𝑞
𝑘1
2
~𝑅𝑏~ ⩽1
𝜀2
1 ˜ 𝛽
2
𝑘1
2
~𝑅𝑏~
·
𝑛
ℓ
𝑘
2
1 ~𝑅𝑏~
𝑘1
2 ˜~𝑅𝑏~
> 1
𝜀2
1 ˜ 𝛽
2
𝑘1
2
~𝑅𝑏~
·

ℓ
𝑛/
If ~𝑅𝑏~ > 𝑘1
2
$and thus 𝑘is odd)* we also have
deg𝑢0𝑅𝑏)𝑞
𝑘1
2
~𝑅𝑏~ > deg𝑢0𝑅𝑏) ⩽1
𝜀2 /
which implies that for 𝑘odd*
𝜈𝑟⩽𝑤𝑘
1
𝜀4𝜂𝑘1 /
Let us now upper bound 𝜈𝑟when 𝑘is even. We either have ~𝑅1~ / ~𝑅2~ ⩽
𝑘2
2 * in which case
𝑞𝑘1 𝑟deg𝑢0𝑅1) deg𝑢0𝑅2) ⩽
1
𝜀4𝜂𝑘1 trivially holds. Otherwise* suppose that one of 𝑅1 or 𝑅2 has size
exactly 𝑘
2. Note that exactly one of 𝑅1/ 𝑅2 can have size 𝑘
2* as 𝑟⩽𝑘
1. Without loss of generality*
let us suppose that ~𝑅1~ > 𝑘
2* so that ~𝑅2~ > 𝑟
𝑘
2 ⩽𝑘2
2 . We then have
𝑞𝑘1 𝑟deg𝑢0𝑅1) deg𝑢0𝑅2) ⩽1
𝜀4
1 ˜ 𝛽
2
𝑘1 𝑟𝑛
ℓ
𝑘
2
1 0𝑟
𝑘
2 ) 0𝑘1 𝑟)
> 1
𝜀4
1 ˜ 𝛽
2
𝑘1 𝑟
⩽1
𝜀4𝜂𝑘1 /
Now* taking 𝜆> 𝑤𝑘1
𝜀4𝜂𝑘1𝑐𝑘1 ln𝑘1 
32𝑝𝑁
𝜀2𝐷

for some absolute constant 𝑐and applying Fact 3.2*
we get that
ℙ
 ←𝒰′
ℓ

𝑃𝑢0 ) = 2𝑤𝑘
1
𝜀4𝜂𝑘1𝑐𝑘1 ln𝑘1
32𝑝𝑁
𝜀2𝐷

⩽𝜀2𝐷
32𝑝𝑁/
Lemma 6.9 now follows by a union bound on the 𝑝diﬀerent 𝑢—s and Lemma 6.20* and observing
that
2𝑤𝑘
1
𝜀4𝜂𝑘1𝑐𝑘1 ln𝑘1
32𝑝𝑁
𝜀2𝐷

⩽𝑐′𝑘1 1
𝜀4 ln20𝑘1)
32𝑝𝑁
𝜀2𝐷

> Δ /
where 𝑐′ is an absolute constant* as 𝜂> 4 ln

32𝑝𝑁
𝜀2𝐷

.
40

<!-- pdf-page: 43 -->
7
Strong CSP Refutation: Smoothed via Semirandom
In this section* we show how the tight refutation of semirandom sparse polynomials in Section 5
can be used in a black-box way to derive nearly optimal algorithms for strongly refuting smoothed
CSPs and* as a special case* semirandom CSPs.
Smoothed model.
Let us ﬁrst formally describe the model of smoothed Boolean CSPs.
De”nition 7.1 $Smoothed CSP Instances [Fei07\). Let 𝑘∈ℕ. Let 𝜓be an instance of a CSP with
predicate 𝑃: |±1|𝑘→|0/ 1| speciﬁed by a collection of 𝑘-tuples ℋand literal patterns 𝜉. Let
a𝑝> |𝑝𝐶/𝑖|𝐶∈ℋ/𝑖∈*𝑘\ with each 𝑝𝐶/𝑖∈*0/ 1\ be smoothing parameters* one for every 𝐶∈ℋand 𝑖∈*𝑘\.
@ a𝑝-smoothing of 𝜓is obtained as follows:
1. For every 𝐶∈ℋ* let 𝑆𝐶⊆*𝑘\ be obtained by adding 𝑖to 𝑆𝐶with probability 𝑝𝐶/𝑖independently
for every 𝑖∈𝐶.
2. For every 𝑖∈𝑆𝐶* reset 𝜉0𝐶/ 𝑖) to be a uniform and independent random bit in ±1.
RemYrk 7.2.
1. The notion of smoothing allows using a diﬀerent probability of ’rerandomizing“
each of 𝑚𝑘literals in a 𝑘-CSP instance 𝜓with 𝑚constraints.
2. The two-step random process above is equivalent to ﬁipping the negation pattern 𝜉0𝐶/ 𝑖) of
the 𝑖-th literal in clause 𝐶∈ℋindependently of others with probability 𝑝𝐶/𝑖02.
3. Setting 𝑝𝐶/𝑖> 1 for every 𝑖/ 𝐶yields the model where the literal patterns are uniformly random
and independent in |±1|. This is the semirandom model of CSPs.
We now proceed to state and prove our main results concerning refutation of smoothed instances*
along the way noting also a better bound for the special semirandom case. We recall the notion of
𝑡-wise uniform distributions before presenting the main result.
De”nition 7.3 $𝑡-wise uniform distribution). @ probability distribution 𝜇on |±1|𝑘is said to be
𝑡-wise uniform if 𝔼 ∼𝜇

𝑖∈𝑆 𝑖> 0 for every 𝑆⊆*𝑘\ of size ~𝑆~ ⩽𝑡.
Theorem 7.4 $Smoothed Boolean CSP Refutation). Let 𝑃: |±1|𝑘→|0/ 1| be Y 𝑘-Yry BooleYn
predicYte such thYt there is no 𝑡-wise uniform distribution supported on 𝑃101). Let ℓbe Yn integer with
20𝑘
1) ⩽ℓ⩽𝑛. There is Yn Ylgorithm thYt tYkes Ys input Yn instYnce Θ of CSP$𝑃) Ynd outputs Y vYlue
alg-val0Θ) ∈*0/ 1\ in time 𝑛𝑂0ℓ) sYtisfying the following:
$1) val0Θ) ⩽alg-val0Θ) ⩽1.
$2) Suppose the input instYnce Θ is Y smoothing 𝜓𝑠of Yn YrbitrYry CSP instYnce 𝜓> 0ℋ/ 𝜉) with 𝑛
vYriYbles Ynd 𝑚constrYints w.r.t. Y vector of smoothing pYrYmeters a𝑝> |𝑝𝐶/𝑖| in *0/ 1\. Suppose thYt
𝑚⩾2𝑚0
𝑞0a𝑝)* where
𝑚0 > 2𝑂0𝑘)0log2 𝑛)4𝑡˜1
𝜀5
· ℓ
𝑛
ℓ
𝑡
2
Ynd
𝑞0a𝑝) > 1
𝑚

𝐶∈ℋ

𝑖∈𝐶
𝑝𝐶/𝑖/
$7.1)
41

<!-- pdf-page: 44 -->
Then with probYbility Yt leYst 1
10poly0𝑛) over the rYndomness of the smoothening process* it holds
thYt alg-val0Θ) ⩽1
𝑞0a𝑝)
2
· 0𝛿𝑡
𝜀) ˜ 2 𝑛. Here* 𝛿𝑡⩾2
ˆ𝑂0𝑘𝑡) depends only on the predicYte 𝑃.
Furthermore* in the semirYndom cYse $where Yll 𝑝𝐶/𝑖> 1)* we hYve alg-val0Θ) ⩽1
𝛿𝑡˜ 𝜀˜ 2 𝑛with
probYbility 1
10poly0𝑛).
Moreover* the Ylgorithm is cYptured by the cYnonicYl degree 2ℓsum-of-squYres relYxYtion of the CSP
mYximizYtion problem over the hypercube.
The following result* proved in [@OW15\ using LP duality* plays a crucial role in our proof
of the above theorem* by allowing us to bound the value of CSP with predicate 𝑃that does not
support a 𝑡-wise uniform distribution by a degree-𝑡polynomial as proxy.
Fact 7.5 $Separating Polynomials* Lemma 3.16 and Theorem 4.10 in [@OW15\). Let 𝑃: |±1|𝑘→|0/ 1|
be Y predicYte such thYt there is no 𝑡-wise uniform distribution supported on 𝑃101). Then* there is Y
𝛿𝑡⩾2
ˆ𝑂0𝑘𝑡) such thYt for every 𝑡-wise uniform distribution 𝜁* 𝔼𝜁*𝑃\ ⩽1
𝛿𝑡. Furthermore* there is Y
degree-𝑡polynomiYl 𝑄: |±1|𝑘→ℝsuch thYt 𝑄0 ) > 
𝑇⊆*𝑘\ ˆ𝑄0𝑇) 𝑇Ynd:
1. 𝑃0 ) ⩽1
𝛿𝑡˜ 𝑄0 ) for every   ∈|±1|𝑘
2.
ˆ𝑄0∅) > 0* i.e. 𝑄hYs no constYnt coeﬂcient* Ynd*
3. 
𝑇⊆*𝑘\ ~ ˆ𝑄0𝑇)~ ⩽22𝑘.
We now turn to the task of proving Theorem 7.4.
7.1
Proof of Theorem 7.4
By Fact 3.4* there is an algorithm that in 𝑛𝑂0ℓ)-time outputs a value alg-val0Θ) ∈*0/ 1\ such that
𝛽⩽alg-val0Θ) ⩽𝛽˜ 2 𝑛* where 𝛽> max 𝔼*Θ\* Θ0𝑥) :> 
𝐶∈ℋ𝑃0𝜉0𝐶/ 1)𝑥𝐶1/ / / / / 𝜉0𝐶/ 𝑘)𝑥𝐶𝑘) is a
degree ⩽2𝑘polynomial* and the maximum is taken over degree-2ℓpseudo-expectations 𝔼over
|±1|𝑛. Note that Θ is indeed a degree ⩽2𝑘polynomial* as 𝑃can always be expressed as a degree
⩽2𝑘polynomial.
First* we observe that Item $1)* i.e.* completeness* is completely trivial: simply take 𝔼to be the
expectation 𝔼𝜇of a distribution 𝜇supported only on optimal solutions to Θ. Indeed* this implies
that val0Θ) ⩽𝛽⩽alg-val0Θ). We thus focus on proving Item $2).
We will analyze the smoothing random process using the two steps that deﬁne it. Let us ﬁrst
consider the event that the ﬁrst step chooses to re-randomize Yll the literals in a given clause 𝐶∈ℋ;
the probability of this event is 𝑘
𝑖>1 𝑝𝐶/𝑖. Let 𝒢be the set of clauses for which this occurs. Observe
that the 0-1 indicator of ’all literals are chosen to be re-randomized in 𝐶“ is independent across
clauses 𝐶∈ℋ. The expected number of clauses in 𝒢equals 𝑚𝑞0a𝑝) > 
𝐶∈ℋ
𝑘
𝑖>1 𝑝𝐶/𝑖. Thus* by
Chernoﬀbound* ~𝒢~ ⩾0/5𝑚𝑞0a𝑝) with probability at least 1
𝑒𝑚𝑞0a𝑝)08 ⩾1
𝑒𝑚004 ⩾1
10poly0𝑛)*
as 𝑚𝑞0a𝑝) ⩾2𝑚0. Let us proceed assuming that ~𝒢~ ⩾0/5𝑚𝑞0a𝑝).
Let 𝜉denote the literal patterns after re-randomizing. We see that for every 𝐶∈𝒢and 𝑖∈*𝑘\*
𝜉0𝐶/ 𝑖) is drawn uniformly and independently from |±1|. We shall view 𝜉0𝐶/ 𝑖) as ﬁxed for all
𝐶∉𝒢/ 𝑖∈*𝑘\* and think of the 𝜉0𝐶/ 𝑖)—s for 𝐶∈𝒢/ 𝑖∈*𝑘\ as being random. For 𝐶∈𝒢* let 𝑟𝐶/𝑖
denote the random variable 𝜉0𝐶/ 𝑖)* which is uniformly random in |±1|.
42

<!-- pdf-page: 45 -->
Let
𝜓𝑔>
1
~𝒢~

𝐶∈𝒢
𝑃0𝑟𝐶1𝑥𝐶1/ / / / / 𝑟𝐶𝑘𝑥𝐶𝑘) /
𝜓𝑏>
1
~ℋ~
~𝒢~

𝐶∉𝒢
𝑃0𝜉0𝐶/ 1)𝑥𝐶1/ / / / / 𝜉0𝐶/ 𝑘)𝑥𝐶𝑘) /
so that ~ℋ~ 𝜓𝑠> ~𝒢~ 𝜓𝑔˜ 0~ℋ~
~𝒢~)𝜓𝑏. Thus* by linearity of pseudo-expectations* we must have
that for any pseudo-expectation 𝔼*
𝔼*𝜓𝑠\ ⩽~𝒢~
~ℋ~ ~𝔼*𝜓𝑔\~ ˜ 01
~𝒢~
~ℋ~ )~𝔼*𝜓𝑏\~ /
$7.2)
Note that 𝜓𝑔and 𝜓𝑏are not known to our algorithm; these quantities appear only in our analysis.
Now* we know that for every 𝑥* 𝑃0𝜉0𝐶/ 1)𝑥𝐶1/ / / / / 𝜉0𝐶/ 𝑘)𝑥𝐶𝑘) ⩽1.
@s 𝑃is a degree 𝑘
polynomial on 𝑘variables* by Fact 3.8* for every pseudo-expectation 𝔼of degree 2ℓ⩾2𝑘*
𝔼*𝑃0𝜉0𝐶/ 1)𝑥𝐶1/ / / / / 𝜉0𝐶/ 𝑘)𝑥𝐶𝑘)\ ⩽1. Using linearity of 𝔼and adding up the inequalities above for
𝐶∉𝒢yields that:
𝔼*𝜓𝑏\ ⩽1 /
$7.3)
Let us now analyze 𝔼*𝜓𝑔\. First* we invoke Fact 7.5 to conclude that for every 𝑥* it holds that:
𝑃0𝑟𝐶/1𝑥𝐶1/ / / / / 𝑟𝐶/𝑘𝑥𝐶𝑘) ⩽1
𝛿𝑡˜ 𝑄0𝑟𝐶/1𝑥𝐶1/ / / / / 𝑟𝐶/𝑘𝑥𝐶𝑘) /
@s deg0𝑄) > 𝑡⩽𝑘* by Fact 3.8 and summing up over 𝐶∈𝒢* for every pseudo-expectation of
degree 2ℓ⩾2𝑘* we must have that:
𝔼*𝜓𝑔\ ⩽1
𝛿𝑡˜ 1
~𝒢~

𝐶∈𝒢
𝔼*𝑄0𝑟𝐶/1𝑥𝐶1/ / / / / 𝑟𝐶/𝑘𝑥𝐶𝑘)\ /
Next* let 𝑇⊆*𝑘\ of size ⩽𝑡. For each 𝐶* let 𝑥𝐶~𝑇> 
𝑖∈𝑇𝑥𝐶𝑖and 𝑏𝐶~𝑇> Π𝑖∈𝑇𝑟𝐶/𝑖. Observe that
𝑄0 ) > 
0=~𝑇~⩽𝑡ˆ𝑄0𝑇) 𝑇from Fact 7.5 and that further* 
0=~𝑇~⩽𝑡~ ˆ𝑄0𝑇)~ ⩽22𝑘. Thus* we have:
𝔼*𝜓𝑔\ ⩽1
𝛿𝑡˜ 1
~𝒢~

𝐶∈𝒢

𝑇⊆*𝑘\/0=~𝑇~⩽𝑡
~ ˆ𝑄0𝑇)~𝑏𝐶~𝑇𝔼
𝑥𝐶~𝑇

/
Deﬁne 𝜙𝑇to be the homogenous degree ~𝑇~ polynomial described by:
𝜙𝑇0𝑥) >
1
~𝒢~

𝐶∈𝒢
𝑏𝐶~𝑇𝑥𝐶~𝑇
Then* notice that:
𝔼*𝜓𝑔\ ⩽1
𝛿𝑡˜

𝑇⊆*𝑘\/0=~𝑇~⩽𝑡
~ ˆ𝑄0𝑇)~𝔼*𝜙𝑇\ /
$7.4)
We now observe that each 𝜙𝑇is a polynomial with independent random coeﬂcients in | 1/ 1|.
Further* since ~𝒢~ ⩾0/5𝑞0a𝑝)𝑚⩾𝑚0* by Theorem 5.1* with probability at least 1
10poly0𝑛)* we
43

<!-- pdf-page: 46 -->
must have that for every pseudo-expectation 𝔼of degree at least 2ℓ*
𝔼*𝜙𝑇\ ⩽
𝜀
22𝑘/
By a union bound over ⩽2𝑘possible 𝑇* this bound holds for every 𝑇with probability at least
1
10poly0𝑛). Conditioning on this event* combining with $7.4)* and using that 
𝑇~ ˆ𝑄0𝑇)~ ⩽22𝑘
gives:
𝔼*𝜓𝑔\ ⩽1
𝛿𝑡˜ 𝜀/
$7.5)
Thus* plugging this bound into $7.2) and using $7.3) yields:
𝔼*𝜓𝑠\ ⩽

1
~𝒢~
~ℋ~

· 1 ˜ ~𝒢~
~ℋ~ · 01
𝛿𝑡˜ 𝜀) ⩽1
~𝒢~
~ℋ~ 0𝛿𝑡
𝜀) ⩽1
0𝛿𝑡
𝜀) · 𝑞0a𝑝)
2
/
$7.6)
where we use that ~𝒢~
~ℋ~ ⩾𝑞0a𝑝)02. Note that here we require 𝛿𝑡⩾𝜀* although the conclusion is trivial
if this does not hold. @s alg-val0𝜓𝑠) ⩽𝛽˜ 2 𝑛⩽1
0𝛿𝑡
𝜀) · 𝑞0a𝑝)
2 ˜ 2 𝑛* this completes the proof for
the smoothed case.
@s the semirandom model is the special case of the smoothed model $where 𝑝𝐶/𝑖> 1 for every
𝑖)* the above argument directly yields an upper bound of 𝔼*𝜓\ ⩽1
0/50𝛿𝑡
𝜀) ˜ 2 𝑛for the case
of semirandom instances. However* we incurred the 0/5 factor entirely due to the probabilistic
bound on ~𝒢~* and in the semirandom setting* ~𝒢~ > ~ℋ~ with probability 1. Hence* for semirandom
refutation* we do not lose this extra 0/5 factor.
8
Proof of Feige{s Conjecture: Even Covers in Hypergraphs
In this section* we prove Feige—s conjecture* that every 𝑘-uniform hypergraph with a certain number
of hyperedges has a short even cover. In the next section* we will use it to establish $using Feige*
Kim and Ofek—s ideas) that there exist polynomial size refutations for arbitrary semirYndom instances
of 3-S@T at a density 𝑚> ˆΩ0𝑛1/4) which is ˆ𝑂0𝑛0/1) factor smaller than the spectral threshold of 𝑛1/5
for refuting random instances. @n appropriate generalization of this result holds for 𝑘-S@T and
more generally any CSP.
We begin by deﬁning even covers.
De”nition 8.1 $Even $multi)covers). Let ℋbe a 𝑘-uniform hypergraph on *𝑛\. @ set of distinct
hyperedges 𝐶1/ 𝐶2/ / / / / 𝐶𝑟∈ℋis said to be an even cover of length 𝑟in ℋif every element 𝑗∈*𝑛\
belongs to an even number of 𝐶𝑖—s; equivalently* ±𝑟
𝑖>1𝐶𝑖> ∅. @n even multicover in ℋis exactly the
same except 𝐶1/ 𝐶2/ / / / / 𝐶𝑟∈ℋneed not be distinct. Even $multi)covers are deﬁned similarly for
bipartite hypergraphs* using the hyperedges 0𝑢/ 𝐶).
We note that if ℋis not simple* i.e.* ℋis a multi-set* then ℋtrivially has an even cover of
length 2. Indeed* ℋmust contain distinct elements 𝐶1 and 𝐶2 that are equal as sets* and so
𝐶1 ± 𝐶2 > ∅.
The main result of this section is a proof of Feige—s conjecture $Conjecture 1.7) up to poly log 𝑛
factor loss in the number of hyperedges 𝑚in the hypergraph.
44

<!-- pdf-page: 47 -->
Theorem 8.2 $Resolution of Feige—s Conjecture). Let 𝑘∈ℕYnd ℓ> ℓ0𝑛) with 20𝑘
1) ⩽ℓ⩽𝑛. Let
ℋbe Y 𝑘-uniform hypergrYph on *𝑛\ with 𝑚⩾ 𝑘· 𝑛
𝑛
ℓ
𝑘
2
1 log4𝑘˜1 𝑛hyperedges* where   is Yn Ybsolute
constYnt. Then* ℋcontYins Yn even cover of size 𝑂0ℓlog 𝑛).
Our proof closely mimics the steps taken in Sections 4 to 6 on the way to obtaining an eﬂcient
refutation algorithm for semirandom sparse multilinear polynomials. In the ﬁrst step* we observe
that without loss of generality* we can assume that ℋis a simple* 𝑝-bipartite* 0𝜀/ ℓ)-regular
hypergraph for 𝜀> 104.
Lemma 8.3 $Reduction to Simple* 𝑝-bipartite* 0104/ ℓ)-regular hypergraphs). Fix 𝑘/ ℓ> ℓ0𝑛) ∈ℕ
with 20𝑘
1) ⩽ℓ⩽𝑛. Suppose thYt for every 𝑝-bipYrtite* 0104/ ℓ)-regulYr* simple 𝑘-uniform hypergrYph
ℋ> |ℋ𝑢|𝑢∈*𝑝\ with 𝑚⩾max|𝑐𝑘
𝑛
ℓ
𝑘1
2 
𝑝ℓlog2𝑘˜0/5 𝑛/ 16𝑝| hyperedges for some Ybsolute constYnt
𝑐Ynd ~ℋ𝑢~ > 𝑚
𝑝for Yll 𝑢* there exists Yn even cover in ℋof length Yt most 𝑟. Then* every 𝑘-uniform
hypergrYph ℋwith 𝑚⩾
𝑘· 𝑛
𝑛
ℓ
𝑘
2
1 log4𝑘˜1 𝑛hyperedges hYs Yn even cover of length Yt most 𝑟.
Proof. Let ℋbe an arbitrary 𝑘-uniform hypergraph. First* note that if ℋis not simple* we are
immediately done since any pair of parallel hyperedges yields an even cover of size 2.
We
thus assume that ℋis simple. @pply the decomposition algorithm from Lemma 4.7 to ℋto
get bipartite hypergraphs ℋ01)/ / / / / ℋ0𝑘); these hypergraphs must be simple* as ℋwas.
@s
𝑘
𝑡>1 𝑚0𝑡) > 𝑚* there must exist some 𝑡with 1 ⩽𝑡⩽𝑘such that 𝑚0𝑡) ⩾𝑚0𝑘. @s 𝑚01) ⩽𝜀𝑚0𝑘
always holds* we must have 𝑡≠1. The bound on 𝑚0𝑡)0𝑝0𝑡) in Lemma 4.7 implies that 𝑚0𝑡) ⩾𝑚0𝑘⩾
max|𝑐𝑘
𝑛
ℓ
𝑘1
2 
𝑝0𝑡)ℓlog2𝑘˜0/5 𝑛/ 16𝑝0𝑡)|. Thus* the 𝑝0𝑡)-bipartite 0104/ ℓ)-regular hypergraph ℋ0𝑡)
must contain an even cover* say 0𝑢1/ 𝐶1)/ / / / 0𝑢𝑟′/ 𝐶𝑟′) for some 𝑟′ ⩽𝑟. From Lemma 4.7* for each
𝑢𝑖* there is a 𝑄𝑖such that each hyperedge 0𝑢𝑖/ 𝐶𝑖) in ℋ0𝑡) is a bipartite contraction of the unique
hyperedge 0𝑄𝑖∪𝐶𝑖) in ℋ. We then observe that 0𝑄1 ∪𝐶1)/ / / / / 0𝑄𝑟′ ∪𝐶𝑟′) is trivially an even cover
of length 𝑟′ ⩽𝑟in ℋ* which ﬁnishes the proof.
This brings us to the crux of the argument presented in the following lemma.
Lemma 8.4 $No even covers implies refutation for semirandom polynomials on regular bipartite
hypergraphs). Fix Yn odd 𝑘∈ℕYnd ℓ> ℓ0𝑛) with 20𝑘
1) ⩽ℓ⩽𝑛. Let ℋ> |ℋ𝑢|𝑢∈*𝑝\ be Y 𝑝-bipYrtite
0104/ ℓ)-regulYr simple 𝑘-uniform hypergrYph with 𝑚⩾𝑚0 > max0𝑐𝑘
𝑛
ℓ
𝑘1
2 
𝑝ℓ· log2𝑘˜0/5 𝑛/ 16𝑝)
hyperedges* where 𝑐is Yn Ybsolute constYnt* Ynd ~ℋ𝑢~ >
𝑚
𝑝for Yll 𝑢.
Let 𝜓be the polynomiYl
1
𝑚

𝑢∈*𝑝\

𝐶∈ℋ𝑢𝑏𝑢/𝐶𝑦𝑢𝑥𝐶for YrbitrYry 𝑏𝑢/𝐶∈| 1/ 1|. Suppose thYt ℋhYs no even covers of length
⩽𝑂0ℓlog 𝑛). Then* val0𝜓) ⩽0/5.
Observe that this lemma has an absurd conclusion. Clearly* if one sets 𝑏𝑢/𝐶> 1 for all 𝑢/ 𝐶*
then val0𝜓) is trivially 1: simply set 𝑥> 1𝑛and 𝑦> 1𝑝. Thus* this lemma immediately gives a
contradiction* in that ℋmust admit an even cover of length 𝑂0ℓlog 𝑛).
The reason we state the $somewhat absurd) lemma is because as we will see* our proof mimics
our refutation argument from Section 6 and shows that we can essentially carry out all the steps for
YrbitrYry 𝑏𝑢/𝐶—s as long as we can assume that ℋhas no even covers of length 𝑂0ℓlog 𝑛). Lemma 8.4
eﬀectively captures this argument and* in our opinion* is the most enjoyable way to present it.
It is easy to ﬁnish the proof of Theorem 8.2 assuming the Lemma 8.4.
45

<!-- pdf-page: 48 -->
Proof of Theorem 8.2. By Lemma 8.3* we can assume that ℋ:> ∪𝑢∈*𝑝\ℋ𝑢is a 0104/ ℓ)-regular* simple*
𝑘-uniform bipartite hypergraph with 𝑝⩽𝑛𝑘partitions and 𝑚⩾𝑚0 hyperedges.
Suppose for the sake of contradiction that the hypergraph ℋhas no even cover of
length 𝑂0ℓlog 𝑛).
We set 𝑏𝑢/𝐶
> 1 for every 𝑢/ 𝐶* and consider the polynomial 𝜓>
1
~ℋ′~

𝑢∈*𝑝\

𝐶∈ℋ𝑢𝑏𝑢/𝐶𝑦𝑢𝑥𝐶in 𝑥/ 𝑦. Observe that by setting 𝑥> 1𝑛/ 𝑦> 1𝑝* we obtain that val0𝜓) > 1.
On the other hand* applying Lemma 8.4 to 𝜓yields that val0𝜓) ⩽0/5. This is a contradiction* and
so ℋmust have an even cover of length ⩽𝑂0ℓlog 𝑛).
We now focus on the proof of Lemma 8.4.
8.1
Proof of Lemma 8.4
Our proof follows the exact same outline as in Section 6 for ﬁnding an eﬂcient refutation algorithm
for the polynomial 𝜓. One important diﬀerence is that in this section* we will use the argument to
argue an upper bound on val0𝜓); we do not care about ﬁnding an eﬂcient certiﬁcate for a bound on
val0𝜓) here.
The key observation that we use in this proof is that there is exactly one step of the proof
in Section 6 that uses the randomness of the coeﬂcients 𝑏𝑢/𝐶—s – namely* Lemma 6.15. Our proof in
this section is exactly the same with the key innovation being an analog of Lemma 6.15 that works
for YrbitrYry 𝑏𝑢/𝐶—s as long as ℋhas no 𝑂0ℓlog 𝑛)-length even cover. Indeed* as the hypergraph ℋ
satisﬁes the assumptions of Theorem 5.4* with this observation we immediately see that in order to
ﬁnish the proof* it suﬂces to show that the spectral norm bounds in Lemma 6.15 still hold. In what
follows* we use the exact same notation and conventions as in Section 6.
Let 𝑓be the polynomial obtained in Lemma 6.1 to the polynomial 𝜓. Let 𝐴be the Kikuchi
matrix $Deﬁnition 6.2) corresponding to the polynomial 𝑓. Using Lemma 6.3* we obtain that:
val0𝜓)2 ⩽1
12 ˜ val0 𝑓) ⩽1
12 ˜
𝑝
𝑚2𝐷}𝐴}∞→1 /
where we use that 12𝑝⩽
𝑚.7
Recall also that 𝐷:>
𝑘1
𝑘1
2
2 2𝑛20𝑘1)
ℓ0𝑘1)
if 𝑘is odd and
2 𝑘1
𝑘
2
𝑘1
𝑘2
2
2𝑛20𝑘1)
ℓ0𝑘1)
if 𝑘is even.
Next* let ℬbe the bad rows in 𝐴. Using Lemma 6.9* we know that for Δ > 𝑐′𝑘1 1
𝜀4 ln20𝑘1)0 32𝑝𝑁
𝜀2𝐷)
$where 𝑐′ is an absolute constant and 𝜀> 104)* ~ℬ~
𝑁⩽𝜀2𝐷016𝑁. Let 𝐺be the matrix deﬁned
by zeroing out rows/columns in ℬfrom 𝐴* as in the proof of Lemma 6.11 in Section 6.4. Let
ℱ0 ∪ℱ1 ∪/ / / ℱ𝑡for 𝑡⩽2 log2 𝑚be the partition of non-bad rows of 𝐴and let 𝐺0𝑖/𝑗) be the matrices
obtained by zeroing out rows and columns not in ℱ𝑖and ℱ𝑗from 𝐺respectively as in Deﬁnition 6.13.
Let 𝐺0𝑖/𝑗)
𝑢
be deﬁned similarly by zeroing out rows and columns not in ℱ𝑖and ℱ𝑗respectively from 𝐺𝑢.
Then* following the steps in the proof of Section 6.4* all that remains to be shown is the conclusion
of Lemma 6.15 holds. In Section 6.4* we proved Lemma 6.15 by crucially exploiting the randomness
of 𝑏𝑢/𝐶—s. Here* the 𝑏𝑢/𝐶—s are allowed to be YrbitrYry. We nonetheless show that the same conclusion
holds if we additionally assume that ℋhas no small even cover. Formally* we prove the following
lemma.
7We note that this is the only other part where we deviate at all from the proof in Section 6; here* we now have 12𝑝⩽𝑚
instead of 16𝑝⩽𝑚because we removed 4𝑝edges; this is not important.
46

<!-- pdf-page: 49 -->
Lemma 8.5 $Spectral Norm of 𝐺0𝑖/𝑗)—s when ℋhas no small even cover). Suppose thYt the 0104/ ℓ)-
regulYr 𝑝-bipYrtite simple 𝑘-uniform hypergrYph ℋYssociYted to the polynomiYl 𝜓hYs no even cover of
length ⩽𝑐0ℓlog2 𝑛for some lYrge enough constYnt 𝑐0. Then* for eYch 𝑖/ 𝑗∈|0/ / / / / 𝑡|* we hYve:
𝐺0𝑖/𝑗)
2 ⩽𝑂01) · 20/5 max0𝑖/𝑗)
𝑑log 𝑁˜ 𝑂01)Δ log 𝑁/
Lemma 8.5 ﬁnishes the proof of Lemma 8.4. Indeed* via the identical calculation in Section 6* it
implies that
𝑝
𝑚2𝐷}𝐴}∞→1 ⩽𝜀2 > 1
16* and thus val0𝜙) ⩽
1
12 ˜ 1
16 ⩽1
3* so we are done.
It thus remains to prove Lemma 8.5.
Proof of LemmY 8.5. We will follow the proof of Lemma 6.15 that uses the trace method $Section 6.4.2).
Fix a pair 0𝑖/ 𝑗). For ease of notation* let us write 𝑍> 𝐺0𝑖/𝑗) and 𝑍𝑢for 𝐺0𝑖/𝑗)
𝑢
in the following. We know
that }𝑍}2 ⩽tr00𝑍𝑍⊤)𝑟)102𝑟for every 𝑟∈ℕ. We prove Lemma 8.5 by upper bounding tr00𝑍𝑍⊤)𝑟) for
some 𝑟> 𝑂0ℓlog2 𝑛).
We remind the reader that the trace moment method is classically used in analyzing the spectral
norms of rYndom matrices. In that setting* one bounds the expectYtion of tr00𝑍𝑍⊤)𝑟) which is analyzed
by understanding the terms on the expansion on the right hand side above that contribute a
non-zero expectation often by utilizing inherent independence in the random variables appearing
as entries of the matrix 𝑍. In contrast* there is no rYndomness in the matrix 𝑍* and so we are not
bounding the expectation. Instead* we will analyze the ’contributing“ terms on the right hand
side by appealing to a crucial $and hitherto unobserved) property of the contributing walks in the
Kikuchi matrix. We stress that the analysis appearing below does $as in fact any such analysis
must ) strongly rely on the combinatorial structure of the support of the non-zero entries in our
Kikuchi matrix 𝐴and cannot work for arbitrary matrices.
In fact* our key observation is to show that if ℋhas no short even covers* then our upper
bound on the expectYtion of tr00𝑍𝑍⊤)𝑟) in the semirandom setting $Proposition 6.17) still holds for
tr00𝑍𝑍⊤)𝑟)* i.e.* when the 𝑏𝑢/𝐶—s are YrbitrYry. Formally* we show the following.
Proposition 8.6. Suppose thYt the 0104/ ℓ)-regulYr 𝑝-bipYrtite simple 𝑘-uniform hypergrYph ℋYssociYted to
the polynomiYl 𝜓hYs no even cover of length ⩽4𝑐0ℓlog2 𝑛for some lYrge enough constYnt 𝑐0. Then* for 𝑟⩽
𝑐0ℓlog2 𝑛* it holds thYt tr00𝑍𝑍⊤)𝑟) ⩽
𝑆∈ℱ𝑖  even wYlk sequences 0𝑢1/ 𝐶1/ 𝐶′
1)/ / / / / 0𝑢2𝑟/ 𝐶2𝑟/ 𝐶′
2𝑟) for 𝑆.
We note $at the cost of repetition) that Proposition 8.6 holds regYrdless of the 𝑏𝑢/𝐶—s and is a
consequence of the combinatorial structure of the support of Kikuchi matrices.
We now ﬁnish the proof of Lemma 8.5 assuming Proposition 8.6. This is immediate given the
calculations in Section 6.4.2. By Lemma 6.18* we know that for each 𝑆∈ℱ𝑖* the number of such
sequences is at most 04𝑟)𝑟02max0𝑖/𝑗)𝑑˜ 𝑟Δ2)𝑟. Hence*
}𝑍}2𝑟
2 ⩽tr00𝑍𝑍⊤)𝑟) ⩽𝑁04𝑟)𝑟02max0𝑖/𝑗)𝑑˜ 𝑟Δ2)𝑟/
Setting 𝑟> 𝑐0ℓlog2 𝑛for 𝑐0 a suﬂciently large constant* the above implies that
}𝑍}2 ⩽𝑂01)20/5 max0𝑖/𝑗)
𝑑log2 𝑁˜ 𝑂01)Δ log2 𝑁/
assuming that ℋhas no even cover of length ⩽4𝑟> 4𝑐0ℓlog2 𝑛. This ﬁnishes the proof* up to
Proposition 8.6.
47

<!-- pdf-page: 50 -->
Proof of Proposition 8.6. We compute:
tr00𝑍𝑍⊤)𝑟) >

𝑢1/𝑆1/𝑢2/𝑆2/////𝑢2𝑟/𝑆2𝑟
𝑟

ℎ>1
𝑍𝑢2ℎ10𝑆2ℎ1/ 𝑆2ℎ)𝑍𝑢2ℎ0𝑆2ℎ˜1/ 𝑆2ℎ) /
$8.1)
where we let 𝑢2𝑟˜1 :> 𝑢1 and 𝑆2𝑟˜1 :> 𝑆1.
Observe that each term in $8.1) can contribute a value at most 1 since all 𝑏𝑢/𝐶—s are |±1| and ℋ
is simple. Thus* the RHS of $8.1) is upper-bounded by the number of non-zero ’walk“ terms* i.e.*
the number of terms in the sum in $8.1).
The central observation is the following lemma that observes a combinatorial property of
non-zero terms on the RHS in $8.1).
ClYim 8.7 $Non-zero terms are even multicovers). If the walk term corresponding to
0𝑢1/ 𝑆1/ 𝑢2/ 𝑆2/ / / / / 𝑢2𝑟/ 𝑆2𝑟) is non-zero* then for every ℎ∈*2𝑟\* there exist 𝐶ℎ≠𝐶′
ℎ∈ℋ𝑢ℎsuch that
𝑆ℎ˜1 > 𝑆ℎ± 𝐶01)
ℎ
± 𝐶′
ℎ
02). Moreover* 
ℎ⩽2𝑟0𝑢ℎ/ 𝐶ℎ) ± 0𝑢ℎ/ 𝐶′
ℎ) > ∅* i.e.* |0𝑢ℎ/ 𝐶ℎ)/ 0𝑢ℎ/ 𝐶′
ℎ)|ℎ⩽2𝑟is an
even multicover in ℋ.
Proof. By deﬁnition of the Kikuchi matrix* the walk term equals

ℎ⩽𝑟
𝑍𝑢2ℎ10𝑆2ℎ1/ 𝑆2ℎ)𝑍𝑢2ℎ0𝑆2ℎ˜1/ 𝑆2ℎ)
>

ℎ⩽𝑟
𝑏𝑢2ℎ1/𝐶2ℎ1𝑏𝑢2ℎ1/𝐶′
2ℎ1𝑏𝑢2ℎ/𝐶2ℎ𝑏𝑢2ℎ/𝐶′
2ℎ10𝑆2ℎ1
𝐶01)
2ℎ1/𝐶′
2ℎ1
02)
←→
𝑆2ℎ)10𝑆2ℎ
𝐶01)
2ℎ/𝐶′
2ℎ
02)
←→
𝑆2ℎ˜1) /
$8.2)
where for each ℎ* 𝐶2ℎ1/ 𝐶′
2ℎ1 ∈ℋ𝑢2ℎ1 and 𝐶2ℎ/ 𝐶′
2ℎ∈ℋ𝑢2ℎ.
Clearly*
if
the
term
corresponding
to
0𝑢1/ 𝑆1/ 𝑢2/ 𝑆2/ / / / / 𝑢2𝑟/ 𝑆2𝑟)
is
non-zero
then
10𝑆2ℎ1
𝐶01)
2ℎ1/𝐶′
2ℎ1
02)
↔
𝑆2ℎ) > 1 for every ℎ⩽𝑟.
Expanding the deﬁnition* this implies that
𝑆2ℎ> 𝑆2ℎ1 ± 𝐶01)
2ℎ1 ± 𝐶′
2ℎ1
02). Similarly* we also have that 𝑆2ℎ˜1 > 𝑆2ℎ± 𝐶01)
2ℎ± 𝐶′
2ℎ
02).
To show the ’moreover“* we observe that by adding up all the aforementioned two equations*
we obtain:
2𝑟˜1

ℎ>2
𝑆ℎ>
2𝑟

ℎ>1
𝑆ℎ±
2𝑟

ℎ>1
𝐶01)
ℎ
± 𝐶′
ℎ
02) /
@s 𝑆2𝑟˜1 :> 𝑆1* canceling the 𝑆ℎ—s on both sides yields 
ℎ⩽2𝑟𝐶01)
ℎ
± 𝐶′
ℎ
02) > ∅. This then trivially
implies that 
ℎ⩽2𝑟𝐶ℎ> 
ℎ⩽2𝑟𝐶′
ℎ> ∅* and hence 
ℎ⩽2𝑟0𝑢ℎ/ 𝐶ℎ) ± 0𝑢ℎ/ 𝐶′
ℎ) > ∅* as 0𝑢ℎ/ 𝐶ℎ) ±
0𝑢ℎ/ 𝐶′
ℎ) > 𝐶ℎ± 𝐶′
ℎ.
Observe that the even multicover |0𝑢ℎ/ 𝐶ℎ)/ 0𝑢ℎ/ 𝐶′
ℎ)|ℎ⩽2𝑟in Claim 8.7 need not be an even cover
as the 0𝑢ℎ/ 𝐶ℎ)—s need not be distinct. Indeed* the main punch of what follows is that when there
are no small even covers in ℋ* then the 0𝑢ℎ/ 𝐶ℎ)—s must occur in pairs* i.e.* each 0𝑢ℎ/ 𝐶ℎ) appears an
even number of times in the two multicovers obtained in Claim 8.7.
ClYim 8.8 $No short even cover implies short multicovers are unions of pairs). Suppose ℋ>
|ℋ𝑢|𝑢∈*𝑝\ has no even cover of length ⩽4𝑟. Then* if the walk term in $8.1) corresponding to
|𝑢ℎ/ 𝑆ℎ/ 𝐶ℎ/ 𝐶′
ℎ|ℎ⩽2𝑟is non-zero* then each 0𝑢/ 𝐶) ∈∪𝑢∈*𝑝\ℋ𝑢occurs an even number of times in the
48

<!-- pdf-page: 51 -->
multiset |0𝑢ℎ/ 𝐶ℎ)/ 0𝑢ℎ/ 𝐶′
ℎ)|ℎ⩽2𝑟. In particular* |0𝑢ℎ/ 𝐶ℎ/ 𝐶′
ℎ)|ℎ⩽2𝑟is an even wYlk sequence for 𝑆1* as
deﬁned in Deﬁnition 6.16.
Proof. From Claim 8.7* 2𝑟
ℎ>10𝑢ℎ/ 𝐶ℎ) ± 0𝑢ℎ/ 𝐶′
ℎ) > ∅. Start from the multiset |0𝑢ℎ/ 𝐶ℎ)/ 0𝑢ℎ/ 𝐶′
ℎ)|ℎ⩽2𝑟*
and remove pairs greedily until this is no longer possible. Observe that the symmetric diﬀerence
of the resulting set must also be empty since we removed sets in equal pairs. If at the end of this
process* we are left with a non-zero number of hyperedges* i.e.* we assume that the conclusion does
not hold* then we have at most 4𝑟distinct hyperedges whose symmetric diﬀerence is empty. Thus*
the remaining set must be an even cover of length ⩽4𝑟in ℋ* which is a contradiction.
Combining Claims 8.7 and 8.8* we thus see that the RHS of $8.1) is upper bounded by

𝑆∈ℱ𝑖# even walk sequences 0𝑢1/ 𝐶1/ 𝐶′
1)/ / / / / 0𝑢2𝑟/ 𝐶2𝑟/ 𝐶′
2𝑟) for 𝑆* which ﬁnishes the proof of Propo-
sition 8.6.
9
Polynomial Size Refutation Witnesses Below the Spectral Threshold
In this section* we use our smoothed refutation algorithm along with our proof of Feige—s conjecture
to show the existence of polynomial size refutation witnesses below the spectral threshold for
smoothed instances of Boolean CSPs. Modulo the use of our key new ingredients – Theorems 5.1
and 8.2 – the rest of the proof plan largely follows the inﬁuential work of Feige* Kim and
Ofek [FKO06\ who proved that fully rYndom instances of 3-S@T admit polynomial size refutation
witnesses whenever they have at least ˆ𝑂0𝑛1/4) constraints. Our new ingredients allow us to $1) show
a similar result for not just fully random instances* but also semirandom and smoothed ones* and
$2) provide an arguably simpler refutation witness even for the fully random instances of 3-S@T
studied by [FKO06\.
Let us ﬁrst formalize the idea of a refutYtion witness* or equivalently* a nondeterministic refutation
algorithm.
De”nition 9.1 $Nondeterministic refutation). Fix 𝑘∈ℕ* and let 𝑃: |±1|𝑘→|0/ 1| be a predicate.
We say that a nondeterministic algorithm 𝑉is an nondeterministic eﬂcient weYk refutYtion Ylgorithm if
𝑉takes as input a CSP instance 𝜓with predicate 𝑃in 𝑛variables and 𝑚clauses and in poly0𝑛/ 𝑚)-
nondeterministic time outputs either ’unsatisﬁable“ or ’don—t know“* such that for every 𝜓* if 𝑉0𝜓)
outputs ’unsatisﬁable“ then 𝜓is unsatisﬁable. If 𝑉0𝜓) outputs ’unsatisﬁable“* then we say that 𝑉
weakly refutes 𝜓. The string 𝜋∈|0/ 1|poly0𝑛/𝑚) of nondeterministic guesses of 𝑉is called the weak
refutation witness.
We will sketch a proof of the following theorem. We only provide a proof sketch* as the proof
merely combines the ideas of [FKO06\ with our theorems* Theorems 5.1 and 8.2.
Theorem 9.2. Let 𝑘⩾3* Ynd let 𝑃: |±1|𝑘→|0/ 1| be Y non-triviYl predicYte.
Then there is Y
nondeterministic eﬂcient weYk refutYtion Ylgorithm 𝑉with the following properties. Let 𝜓be Yn instYnce of
Y CSP with predicYte 𝑃with 𝑛vYriYbles Ynd 𝑚clYuses* speciﬁed by Y collection of 𝑚𝑘-tuples ℋYnd literYl
pYtterns 𝜉. Then:
$1) If 𝜓is Y uniformly rYndom instYnce with 𝑚⩾ˆ𝑂01) · 𝑛
𝑘
2
𝑘2
20𝑘˜2) clYuses* then 𝑉weYkly refutes 𝜓with
probYbility Yt leYst 1
10poly0𝑛).
49

<!-- pdf-page: 52 -->
$2) If 𝜓is Y semirYndom instYnce with 𝑚⩾ˆ𝑂01)· 𝑛
𝑘
2
𝑘2
20𝑘˜8) clYuses* then 𝑉weYkly refutes 𝜓with probYbility
Yt leYst 1
10poly0𝑛).
$3) If 𝜓is Y smoothed instYnce obtYined using smoothing pYrYmeters a𝑝> |𝑝𝐶/𝑖|𝐶∈ℋ/𝑖∈*𝑘\ with 𝑚⩾
ˆ𝑂01) · 𝑛
𝑘
2
𝑘2
20𝑘˜8) 0𝑞0a𝑝) clYuses* where 𝑞0a𝑝) :>
1
𝑚

𝐶∈ℋ

𝑖∈𝐶𝑝𝐶/𝑖* then 𝑉weYkly refutes 𝜓with
probYbility Yt leYst 1
10poly0𝑛).
FinYlly* if 𝑘> 3* the threshold of 𝑚for the semirYndom/smoothed cYse cYn be improved to ˆ𝑂0𝑛1/4) Ynd
ˆ𝑂0𝑛1/4)0𝑞0a𝑝)* respectively* mYtching the rYndom cYse.
We will ﬁrst begin by focusing on the case of 𝑘-XOR. @s in the case of Section 7* refuting arbitrary
predicates 𝑃will reduce to refuting XOR.
In [FKO06\* FKO observed that the following type of refutation witnesses* which we shall call
ideYl FKO witnesses* allow for a non-trivial8 weak refutation of instances of 𝑘-XOR whenever the
𝑏𝐶—s are chosen uniformly and independently at random. Informally speaking* ideal FKO witnesses
are simply a disjoint collection of even covers in ℋ.
De”nition 9.3 $Ideal FKO witnesses). Let ℋbe 𝑘-uniform hypergraph on *𝑛\. We say that a
collection of even covers 𝐸1/ 𝐸2/ / / / / 𝐸𝑟⊆ℋis an ideYl FKO witness of length ℎif each 𝐸𝑖∩𝐸𝑗> ∅for
every 𝑖≠𝑗and ~𝐸𝑖~ ⩽ℎfor every 𝑖* where ~𝐸𝑖~ denotes the length of the even cover 𝐸𝑖. The size of
the witness is 𝑠> 𝑟
𝑖>1 ~𝐸𝑖~ ⩽ℎ𝑟.
Ideal FKO witnesses yield non-trivial weak refutation witnesses for semi-random instances of
𝑘-XOR.
Lemma 9.4 $Ideal FKO witnesses yield refutation witnesses for XOR). Let 𝜓> 0ℋ/ 𝑏) be Yn instYnce
of 𝑘-XOR on 𝑛vYriYbles. Suppose 𝐸1/ 𝐸2/ / / / / 𝐸𝑟⊆ℋis Yn ideYl FKO witness in ℋ. Suppose further thYt
eYch 𝑏𝐶is Y uniformly rYndom Ynd independent bit in ±1. Then* with probYbility Yt leYst 1
exp0Ω0𝑟)) over
the drYw of 𝑏> |𝑏𝐶|𝐶∈ℋ* val0𝜓) ⩽1
𝑟
3𝑚.
Proof. For each 𝑖* consider 𝑍𝑖> 
𝐶∈𝐸𝑖𝑏𝐶. Then* notice that 𝑍1/ 𝑍2/ / / / / 𝑍𝑟are independent random
variables* each uniformly drawn from |±1|. Thus* by a Chernoﬀbound* with probability at least
1
exp0Ω0𝑟)) there must exist at least 𝑟03 𝐸𝑖—s such that 𝑍𝑖>
1. Consider any such 𝐸𝑖where this
holds.
Suppose some 𝑥∈|±1|𝑛satisﬁes all the constraints in 𝜓corresponding to 𝑘-tuples 𝐶∈𝐸𝑖.
Then* 
𝐶∈𝐸𝑖𝑏𝐶> 
𝐶∈𝐸𝑖

𝑗⩽𝑘𝑥𝐶𝑗. Since 𝐸𝑖is an even cover* every variable occurs an even number
of times in the 𝐶—s in 𝐸𝑖. Since even powers of any 𝑥𝑗evaluate to 1* the RHS above must evaluate to
1. Since we know that 
𝐶∈𝐸𝑖𝑏𝐶>
1* this implies that such an 𝑥cannot exist: every 𝑥must violate
at least one constraint in each 𝐸𝑖if 
𝐶∈𝐸𝑖𝑏𝐶>
1. Since 𝐸𝑖—s are disjoint* this implies that every 𝑥
violates at least 𝑟03 constraints in 𝜓. The bound on val0𝜓) now follows.
The key question is whether Ideal FKO witnesses exist in the 𝑘-uniform hypergraph specifying
the 𝑘-XOR instance. In [FKO06\* the authors study the question of ﬁnding such refutation witnesses
in rYndom suﬂciently dense hypergraphs. They comment that* while they expect Ideal FKO
witnesses to exist in the regime they are working in* proving that they exist appears hard. They
8Note that by running Gaussian elimination* one can decide if a 𝑘-XOR instance is unsatisﬁable in polynomial time.
This is a triviYl weak refutation.
50

<!-- pdf-page: 53 -->
instead show that a related form of witnesses $these are ’almost disjoint“ even covers instead of
perfectly disjoint) exist by means of a sophisticated second moment method argument.
Here* we show that Ideal FKO witnesses do indeed exist – not only in random dense hypergraphs
but in YrbitrYry hypergraphs with the same density. Indeed* this follows almost immediately
from Theorem 8.2.
Lemma 9.5. Fix 𝑘∈ℕYnd ℓ> ℓ0𝑛). Let ℋbe Yny 𝑘-uniform hypergrYph with 𝑚⩾2𝑚0 hyperedges*
where 𝑚0 >  𝑘· 𝑛
𝑛
ℓ
𝑘
2
1 log4𝑘˜1 𝑛is the threshold YppeYring in Theorem 8.2. Then* ℋcontYins Y collection
of 𝑚00ℎ0𝑛) hyperedge-disjoint even covers eYch of length Yt most ℎ0𝑛) > 𝑂0ℓlog 𝑛).
Proof. The idea is simple. Let 𝑚0 be the number of constraints required in Theorem 8.2. Choose
𝑚> 2𝑚0. Then* by an application of Theorem 8.2* there is an even cover in ℋ* say* 𝐸1 of size
~𝐸1~ ⩽ℎ0𝑛) > 𝑂0ℓlog 𝑛). Let ℋ0 > ℋ. We now repeat the following process for 𝑖> 1/ 2/ / / / / 𝑟:
apply Theorem 8.2 to ℋ𝑖:> ℋ𝑖1 ] 𝐸𝑖to ﬁnd an even cover 𝐸𝑖˜1 ⊆ℋ𝑖of size ⩽ℎ0𝑛) > 𝑂0ℓlog 𝑛).
Notice that the conditions of Theorem 8.2 are met so long as ~ℋ𝑖~ ⩾𝑚
ℎ0𝑛)𝑟⩾𝑚02* i.e.* if
𝑟⩽0/5𝑚0ℎ0𝑛). Further* each of the even covers 𝐸1/ 𝐸2/ / / / / 𝐸𝑟are pairwise disjoint by construction.
This completes the proof.
By combining the above observation with semirandom refutation algorithms* one can show
that Ideal FKO witnesses yield weak refutation witnesses for all 𝑘-CSPs at densities polynomially
below 𝑛𝑘02. This is one of the key insights of FKO [FKO06\ – to use the non-trivial weak refutation
oﬀered by $their variant of) ideal FKO witnesses in order to show the existence of polynomial size
weak-refutation witnesses for random 3-S@T with 𝑚> ˆΩ0𝑛1/4) constraints: namely* in a regime
of 𝑚where known spectral algorithms* and more generally those based on the polynomial-time
canonical sum-of-squares relaxation* provably fail. Theorem 8.2 $and its consequence Lemma 9.5)
implies that the same result holds for YrbitrYry constraint hypergraphs* up to additional polylog0𝑛)
factors in the number of constraints.
Lemma 9.6 $Ideal FKO witnesses yield weak refutation witnesses for 3-S@T). Let 𝜓> 0ℋ/ 𝜉) be Yn
instYnce of 3-S;T described by Y 3-uniform hypergrYph ℋon *𝑛\ with 𝑚⩾ˆ𝑂0𝑛1/4) YrbitrYry constrYints Ynd
uniformly rYndomly generYted literYl pYtterns. Then* with probYbility Yt leYst 1
10poly0𝑛) over the drYw of
the literYl pYtterns in the instYnce* there is Y polynomiYl-size refutYtion witness thYt certiﬁes val0𝜓) = 1.
Proof Sketch. Let 𝑃: |±1|3 →|0/ 1| be the 3-S@T predicate. Then* 𝑃0 ) > 7
8 ˜ 1
80 1 ˜  2 ˜  3)
1
8 0 1 2 ˜  2 3 ˜  1 3
 1 2 3). We write
𝜓0𝑥) >
1
~ℋ~

𝐶∈ℋ
𝑃0𝑥𝐶1𝜉𝐶/1/ 𝑥𝐶2𝜉𝐶/2/ 𝑥𝐶3𝜉𝐶/3)
> 7
8 ˜
1
8~ℋ~

𝐶∈ℋ
0𝜉𝐶/1𝑥𝐶1 ˜ 𝜉𝐶/2𝑥𝐶2 ˜ 𝜉𝐶/3𝑥𝐶3
𝜉𝐶/1𝑥𝐶1𝜉𝐶/2𝑥𝐶2
𝜉𝐶/2𝑥𝐶2𝜉𝐶/3𝑥𝐶3
𝜉𝐶/1𝑥𝐶1𝜉𝐶/3𝑥𝐶3 ˜ 𝜉𝐶/1𝜉𝐶/2𝜉𝐶/3𝑥𝐶1𝑥𝐶2𝑥𝐶3) /
where the 𝜉𝐶/𝑖—s are the literal negation patterns in |±1|. Note that 𝜓0𝑥) computes the fraction
of constraints satisﬁed by the assignment 𝑥∈|±1|𝑛. We refute each of the 7 diﬀerent XOR
instances produced by taking each of the 7 non-constant terms in the expansion of 𝑃as a multilinear
polynomial above separately.
51

<!-- pdf-page: 54 -->
Our refutation witness helps us eﬂciently refute each of the instances corresponding to the 7
terms in the expansion above. Speciﬁcally* by collecting coeﬂcients together* each the ﬁrst three
terms each produce a linear polynomial of the form 
𝑖𝐵𝑖𝑥𝑖. The next three terms each produce a
homogenous quadratic polynomial of the form
1
~ℋ~

𝐶∈ℋ𝑥𝐶𝑖𝑥𝐶𝑗* and ﬁnally the last term is a cubic
polynomial of the form
1
~ℋ~

𝐶∈ℋ𝑥𝐶1𝑥𝐶2𝑥𝐶3. Our refutation witness for each linear polynomial is
simply }𝐵}1* where 𝐵> 0𝐵1/ / / / / 𝐵𝑛)* noting that this is exactly the maximum of the ﬁrst kind of
terms as 𝑥varies over the hypercube. For the quadratic case* our refutation witness is the value of
SDP relaxation for the ∞→1 norm that gives a = 2 factor approximation to maximum of bilinear
forms over the hypercube. For the homogeneous degree 3 term* our witness is an ideal FKO witness
guaranteed by Lemma 9.5.
By Chernoﬀand union bound argument $applied to every assignment in |±1|𝑛)* }𝐵}1 for any
linear term above is at most 𝑂0

𝑛0𝑚).
By Chernoﬀand union bound argument* the ∞→1-norm of the matrix deﬁning the 2-XOR
constraints is at most 𝑂0

𝑛0𝑚). By Grothendieck—s inequality $Fact 3.6)* we can certify this value
eﬂciently $with an additional loss of at most a factor of = 2) using an SDP.
Thus* we can certify an upper bound of 𝑂0

𝑛0𝑚) on all but homogeneous degree 3 polynomial
produced in the Fourier expansion above. When 𝑚⩾ˆΩ0𝑛)𝑛0/501 𝛿)* i.e.* ℓ> 𝑛𝛿* by Lemma 9.5*
ℋhas a collection of
𝑚
ˆ𝑂0𝑛𝛿) pairwise disjoint even covers of length at most ˆ𝑂0𝑛𝛿). By Chernoﬀ
bounds* at least 1
3 of these even covers must violated and thus* we have obtained a certiﬁcate for an
upper-bound of 1
1
ˆ𝑂0𝑛𝛿) on the value of the ﬁnal term.
Putting these upper bounds together gives an upper bound of 7
8 ˜ 1
8𝑂0𝑛
𝑚) ˜ 1
801
1
ˆ𝑂0𝑛𝛿)) on
the value of the 3-S@T instance. For 𝛿> 0/2* we observe that 𝑛
𝑚> ˆ𝑂0 𝑛0/25˜𝛿04) ≪
1
ˆ𝑂0𝑛𝛿). Thus*
for 𝑚⩾ˆ𝑂0𝑛1/4)* with probability at least 1
10poly0𝑛)* we obtain a refutation for the input 3-S@T
instance.
Lemma 9.6 generalizes to all 𝑘-CSPs with predicate 𝑃* provided that 𝑃is non-trivial* i.e.* 𝑃is
not identically 1. We only need the following basic fact $and the rest of the proof remains the same
as above)* as well as known results for spectral refutation of rYndom 𝑘
1 and smaller-arity XOR
instances.
Lemma 9.7 $Highest Fourier Coeﬂcient of Boolean Functions). Let 𝑃: |±1|𝑘→|0/ 1|.
Let

𝑆⊆*𝑘\ ˆ𝑃0𝑆)𝑥𝑆be the Fourier polynomiYl representYtion of 𝑃. Then* ˆ𝑃0∅) ˜ ~ ˆ𝑃0*𝑘\)~ ⩽1.
Proof. For each 𝑏∈|±1|* consider the distribution that is uniform on all 𝑥such that 
𝑖𝑥𝑖> 𝑏.
Then* the expectation of 𝑃on this distribution is exactly ˆ𝑃0∅) ˜ 𝑏ˆ𝑃0*𝑘\). On the other hand* since 𝑃
takes values in |0/ 1|* this expectation cannot exceed 1. Thus* 1 ⩾ˆ𝑃0∅) ˜ 𝑏ˆ𝑃0*𝑘\) for both values of
𝑏and in particular* 1 ⩾ˆ𝑃0∅) ˜ ~ ˆ𝑃0*𝑘\)~ as desired.
We now sketch a proof of the generalization of Lemma 9.6 to all fully rYndom CSPs. This is
captured by Item $1) in Theorem 9.2. We will assume that the Fourier coeﬂcient ˆ𝑃0*𝑘\) is nonzero*
as otherwise by Theorem 7.4* we have enough constraints to give a polynomial time deterministic
refutation.9
9This is because there cannot be a 0𝑘
1)-uniform distribution 𝜇supported on 𝑃101)* as otherwise we would have
1 > 𝔼𝑥∼𝜇*𝑃0𝑥)\ > ˆ𝑃0∅) = 1* where we have ˆ𝑃0∅) = 1 as 𝑃is nontrivial. @nd then we observe that the CSP instance has at
52

<!-- pdf-page: 55 -->
Lemma 9.8 $Polynomial Size Refutation Witnesses for all rYndom 𝑘-CSPs). Let 𝑃: |±1|𝑘→|0/ 1| be
Yn YrbitrYry 𝑘-Yry BooleYn predicYte for 𝑘⩾3. Let 𝜓be Y CSP instYnce with predicYte 𝑃speciﬁed by ℋé
Y collection of uniformly Yt rYndom Ynd independently generYted 𝑚⩾𝑚0 > ˆ𝑂01) · 𝑛
𝑘
2
𝑘2
20𝑘˜2) 𝑘-tuples Ynd
uniformly rYndom Ynd independently generYted literYl pYtterns |𝜉0𝐶/ 𝑖)|𝐶∈ℋ/𝑖∈*𝑘\. Then* with probYbility Yt
leYst 1
10poly0𝑛) over the drYw of ℋYnd 𝜉0𝐶/ 𝑖)–s* there exists Y polynomiYl size refutYtion witness for 𝜓.
Proof. Observe that the instance 𝜓has 𝑚> ˆ𝑂01) ·
𝑛
ℓ
𝑘02 ℓconstraints for ℓ⩽ˆ𝑂0𝑛
1
𝑘˜2 ). We now use
Fourier analysis to decompose 𝜓0𝑥) :>
1
~ℋ~

𝐶∈ℋ𝑃0𝑥𝐶1𝜉𝐶/1/ / / / / 𝑥𝐶𝑘𝜉𝐶/𝑘) into 2𝑘polynomials* each
of degree 𝑡⩽𝑘. We use the same certiﬁcate as in Lemma 9.6 for the linear polynomials appearing in
this decomposition. For quadratic and higher degree 0⩽𝑘
1) terms* we now use spectral refutation
from prior results on refuting fully random CSPs* such as Theorem 1 in [@OW15\. Each degree 𝑡
polynomial $with 𝑡⩽𝑘
1) that appears requires at least ˆ𝑂0𝑛𝑡020𝜀2) constraints to certify an upper
bound of 𝜀on its value; we can thus certify an upper bound of 𝜀>

𝑛0𝑘1)02
𝑚
on each polynomial.
Note that by choice of 𝑚* we have 𝜀⩽1.
Finally* to refute the ﬁnal and highest degree polynomial obtained by taking the *𝑘\-indexed
Fourier coeﬂcient of 𝑃* we use the the Ideal FKO witness from Lemma 9.4. Then* as in the argument
for 3-S@T above* we arrive at a certiﬁcate that $with probability at least 1
10poly0𝑛)) certiﬁes an
upper-bound of ˆ𝑃0∅) ˜ ˆ𝑂0

𝑛0𝑘1)02
𝑚
) ˜ ~ ˆ𝑃0*𝑘\)~ · 01
ˆ𝑂01)
ℓlog 𝑛) on the value of 𝜓* using Lemma 9.5. The
size of the witness is 𝑠0𝑛) ⩽𝑚0 > poly0𝑛)* as the degree = 𝑘terms used deterministic refutations.
Using Lemma 9.7* we thus certify an upper bound of 1 ˜ ˆ𝑂0

𝑛0𝑘1)02
𝑚
)
ˆ𝑂01)
ℓlog 𝑛> 1
𝑜01) on 𝜓0𝑥)*
which ﬁnishes the proof. Note that this is indeed 1
𝑜01) as ˆ𝑂01)

𝑛0𝑘1)02
𝑚
> ˆ𝑂01)·ℓ
𝑘
4
1
2 0𝑛
1
4 ≪ˆ𝑂010ℓ)*
since ℓ⩽ˆ𝑂01)𝑛
1
𝑘˜2 .
By switching the CSP refutation algorithms in [@OW15\ with the semirandom refutation
algorithm from Theorem 5.1 in this work* we arrive at Item $2) of Theorem 9.2* a version of the above
result that shows the existence of polynomial size refutation witnesses below the 𝑛𝑘02-threshold
for semirYndom instances. @s the proof is very similar* we omit the details of the proof; the ﬁnal
bound is stated in Item $2). Note that the precise value of 𝑚at which this refutation succeeds is
strictly larger $though still polynomially smaller than 𝑛𝑘02) than the one in Lemma 9.8* i.e.* Item $1).
The diﬀerence comes from the fact that the dependence on 𝜀$the strength of the refutation) in our
semirandom refutation algorithms grows as 10𝜀5 instead of the 10𝜀2 dependence of algorithms for
fully random instances; we thus have to take 𝜀>

𝑛0𝑘1)020𝑚
105
instead of

𝑛0𝑘1)020𝑚
102
* which
in turn makes ℓ> 𝑛100𝑘˜8) and then 𝑚⩾ˆ𝑂01)𝑛
𝑘
2
𝑘2
20𝑘˜8) . Our belief is that the 10𝜀5 dependence is
sub-optimal in the semirandom setting but inherent to our current proof techniques.
We note that for large 𝑘* the density required for the polynomial size refutation witnesses to
exist in both Item $1) and Item $2) is ∼𝑛
𝑘
2
0/5˜𝑜𝑘01)* eﬀectively giving a ]𝑛factor ’win“ over the
threshold at which spectral $and sum-of-squares based methods more generally) succeed.
In the speciﬁc case of 𝑘> 3* we can improve the bound in the semirandom case to match the
ˆ𝑂0𝑛1/4) achieved in the random case. This is because the instances appearing in the decomposition
are all semirandom 2-XOR instances* and we can refute these instances with the correct 10𝜀2
least ˆ𝑂0𝑛
𝑘
2
𝑘2
20𝑘˜2) ) constraints* which is at least ˆ𝑂0𝑛
𝑘1
2 ).
53

<!-- pdf-page: 56 -->
dependence: see Proposition 5.2.2 and Theorem 5.2.3 in [Wit17\* combined with the fact that the
value of a semirandom 2-XOR instance is at most 1
2 ˜ 𝜀when 𝑚≫𝑛0𝜀2.
Finally* to handle Item $3)* we observe that by Chernoﬀbound* if 𝑚⩾𝑂01)𝑚00𝑞0a𝑝)* where
𝑚0 > ˆ𝑂01) · 𝑛
𝑘
2
𝑘2
20𝑘˜8) * then with high probability there are at least 𝑚0 clauses in 𝜓where all literals
in the clause are re-randomized by the smoothing process. Call this subinstance 𝜓′. @s 𝜓′ is
semirandom* by Item $2) there is a weak refutation for 𝜓′. @s we can nondeterministically guess 𝜓′*
it follows that the smoothed instance 𝜓also has a weak refutation.
We note that technically speaking* the smoothed nondeterministic refutation algorithm 𝑉is
diﬀerent than the 𝑉for the random/semirandom settings* as it has the additional step of guessing
𝜓′. However* we can use the 𝑉for the smoothed case also in the random/semirandom settings* by
simply guessing 𝜓′ > 𝜓.
References
[@F09\
Noga @lon and Uriel Feige. On the power of two* three and four probes. In Proceedings
of the Twentieth ;nnuYl ;CM-SI;M Symposium on Discrete ;lgorithms* pages 346–354.
SI@M* Philadelphia* P@* 2009.
[@GK21\
Jackson @bascal* Venkatesan Guruswami* and Pravesh K. Kothari. Strongly refuting
all semi-random boolean csps. In Proceedings of the 2021 ;CM-SI;M Symposium on
Discrete ;lgorithms* SOD; 2021* VirtuYl Conference* JYnuYry 10 - 13* 2021* pages 454–472.
SI@M* 2021.
[@HL02\
Noga @lon* Shlomo Hoory* and Nathan Linial. The Moore bound for irregular graphs.
GrYphs Combin.* 18$1):53–57* 2002.
[@hn20\
Kwangjun @hn. @ simpler strong refutation of random k-xor. In ;pproximYtion* RYndom-
izYtion* Ynd CombinYtoriYl OptimizYtion. ;lgorithms Ynd Techniques* ;PPROX/R;NDOM
2020* ;ugust 17-19* 2020* VirtuYl Conference* volume 176 of LIPIcs* pages 2:1–2:15.
Schloss Dagstuhl - Leibniz-Zentrum för Informatik* 2020.
[@KK95\
Sanjeev @rora* David R. Karger* and Marek Karpinski. Polynomial time approximation
schemes for dense instances of NP-hard problems. In Proceedings of the Twenty-Seventh
;nnuYl ;CM Symposium on Theory of Computing* 29 MYy-1 June 1995* LYs VegYs* NevYdY*
US;* pages 284–293. @CM* 1995.
[@LWZ20\
Ryan @lweiss* Shachar Lovett* Kewen Wu* and Jiapeng Zhang. Improved bounds for
the sunﬁower lemma. In Proccedings of the 52nd ;nnuYl ;CM SIG;CT Symposium on
Theory of Computing* STOC 2020* ChicYgo* IL* US;* June 22-26* 2020* pages 624–630.
@CM* 2020.
[@OW15\
Sarah R. @llen* Ryan O—Donnell* and David Witmer. How to refute a random CSP. In
Proceedings of the 56th ;nnuYl IEEE Symposium on FoundYtions of Computer Science* pages
689–708* 2015.
[BCK15\
Boaz Barak* Siu On Chan* and Pravesh Kothari. Sum of squares lower bounds from
pairwise independence. In Proceedings of the 47th ;nnuYl ;CM Symposium on Theory of
Computing* pages 97–106* 2015.
54

<!-- pdf-page: 57 -->
[BM16\
Boaz Barak and @nkur Moitra. Noisy Tensor Completion via the Sum-of-Squares
Hierarchy. In Proceedings of the 29th ;nnuYl Conference on LeYrning Theory* pages 417–445*
2016.
[BS16\
Boaz Barak and David Steurer. Proofs* beliefs* and algorithms through the lens of sum-
of-squares* 2016. Lecture notes in preparation* available on http0//sumofsquAres org.
[CGL04\
@min Coja-Oghlan* @ndreas Goerdt* and @ndr{ Lanka. Strong refutation heuristics
for random k-sat. In ;pproximYtion* RYndomizYtion* Ynd CombinYtoriYl OptimizYtion*
;lgorithms Ynd Techniques* volume 3122 of Lecture Notes in Computer Science* pages
310–321. Springer* 2004.
[Cha13\
Siu On Chan. @pproximation resistance from pairwise independent subgroups. In
Proceedings of the 45th ;nnuYl ;CM Symposium on Theory of Computing* pages 447–456*
2013.
[Fei07\
Uriel Feige. Refuting smoothed 3CNF formulas. In Proceedings of the 48th ;nnuYl IEEE
Symposium on FoundYtions of Computer Science* pages 407–417* 2007.
[Fei08\
Uriel Feige. Small linear dependencies for binary vectors of low weight. In Building
bridges* volume 19 of BolyYi Soc. MYth. Stud.* pages 283–307. Springer* Berlin* 2008.
[FKO06\
Uriel Feige* Jeong Han Kim* and Eran Ofek. Witnesses for non-satisﬁability of dense
random 3CNF formulas. In Proceedings of the 47th ;nnuYl IEEE Symposium on FoundYtions
of Computer Science* pages 497–508* 2006.
[FKP19\
Noah Fleming* Pravesh Kothari* and Toniann Pitassi. Semialgebraic proofs and eﬂcient
algorithm design. FoundYtions Ynd Trends in TheoreticYl Computer Science* 14$1-2):1–221*
2019.
[FLP16\
Dimitris Fotakis* Michael Lampis* and Vangelis Th. Paschos. Sub-exponential approxi-
mation schemes for csps: From dense to almost sparse. In 33rd Symposium on TheoreticYl
;spects of Computer Science* ST;CS 2016* FebruYry 17-20* 2016* Orl~Yns* FrYnce* volume 47
of LIPIcs* pages 37:1–37:14. Schloss Dagstuhl - Leibniz-Zentrum för Informatik* 2016.
[FW16\
Uriel Feige and Tal Wagner. Generalized girth problems in graphs and hypergraphs*
2016.
[IP01\
Russell Impagliazzo and Ramamohan Paturi. On the complexity of k-sat. J. Comput.
Syst. Sci.* 62$2):367–375* 2001.
[JHL˜12\
Domingos Dellamonica Jr.* Penny E. Haxell* Tomasz Luczak* Dhruv Mubayi* Brendan
Nagle* Yury Person* Vojtech Rëdl* Mathias Schacht* and Jacques Verstraéte. On
even-degree subgraphs of linear hypergraphs. Comb. ProbYb. Comput.* 21$1-2):113–127*
2012.
[KMOW17\ Pravesh K. Kothari* Ryuhei Mori* Ryan O—Donnell* and David Witmer. Sum of squares
lower bounds for refuting any CSP. In STOC* pages 132–145. @CM* 2017.
[KV00\
Jeong Han Kim and Van H Vu. Concentration of multivariate polynomials and its
applications. CombinYtoricY* 20$3):417–434* 2000.
55

<!-- pdf-page: 58 -->
[LPS88\
@. Lubotzky* R. Phillips* and P. Sarnak. Ramanujan graphs. CombinYtoricY* 8$3):261–277*
1988.
[Mar88\
G. @. Margulis. Explicit group-theoretic constructions of combinatorial schemes
and their applications in the construction of expanders and concentrators. Problemy
PeredYchi InformYtsii* 24$1):51–60* 1988.
[MR10\
Dana Moshkovitz and Ran Raz. Two-query PCP with subconstant error. J. ;CM*
57$5):@rt. 29* 29* 2010.
[NV08\
@ssaf Naor and Jacques Verstraéte. Parity check matrices and product representations
of squares. CombinYtoricY* 28$2):163–185* 2008.
[Rao19\
@nup Rao. Coding for sunﬁowers. CoRR* abs/1909.04774* 2019.
[RRS17\
Prasad Raghavendra* Satish Rao* and Tselil Schramm. Strongly refuting random csps
below the spectral threshold. In STOC* pages 121–131. @CM* 2017.
[SS12\
Warren Schudy and Maxim Sviridenko. Concentration and moment inequalities for
polynomials of independent random variables. In Proceedings of the Twenty-Third ;nnuYl
;CM-SI;M Symposium on Discrete ;lgorithms* SOD@ —12* page 437–446* US@* 2012.
Society for Industrial and @pplied Mathematics.
[ST03\
Daniel @. Spielman and Shang-Hua Teng. Smoothed analysis: motivation and discrete
models. In ;lgorithms Ynd dYtY structures* volume 2748 of Lecture Notes in Comput. Sci.*
pages 256–270. Springer* Berlin* 2003.
[Tro12\
Joel @. Tropp. User-friendly tail bounds for sums of random matrices. FoundYtions of
ComputYtionYl MYthemYtics* 12$4):389–434* @ug 2012.
[W@M19\
@lexander S. Wein* @hmed El @laoui* and Cristopher Moore. The kikuchi hierarchy
and tensor PC@. In 60th IEEE ;nnuYl Symposium on FoundYtions of Computer Science*
FOCS 2019* BYltimore* MYrylYnd* US;* November 9-12* 2019* pages 1446–1468. IEEE
Computer Society* 2019.
[Wit17\
David Witmer. RefutYtion of rYndom constrYint sYtisfYction problems using the sum of squYres
proof system. PhD thesis* Carnegie Mellon University* 2017.
;
;nalyzing the YW;M19\ ;pproach for Random 3*XOR
In this section* we will prove that the approach suggested by [W@M19\ $in their @ppendix F.1* F.2)
for strongly refuting random 𝑘-XOR with 𝑘odd does not yield the right trade-oﬀfor 𝑚as a function
of 𝑛/ ℓ. Our proof reduces to showing that a certain matrix deﬁned in [W@M19\ does not have small
spectral norm. For simplicity* we present the argument for 𝑘> 3.
First* we give a brief overview of their approach. Let 𝜙be a random 3-XOR instance in 𝑛
variables and 𝑚clauses* with hypergraph ℋand coeﬂcients |𝑏𝐶|𝐶∈ℋ. We will assume that each
pair 𝐶1 ≠𝐶2 ∈ℋhas ~𝐶1 ∩𝐶2~ ⩽1; this ’morally“ holds with high probability provided that
𝑚≪𝑛2 $and recall that we are working in the regime of 𝑚∼𝑛1/5 or smaller* as for 𝑚≫𝑛1/5 there is
a polynomial-time refutation [@GK21\). More formally* when 𝑚≪𝑛2* then with high probability
56

<!-- pdf-page: 59 -->
over ℋ* one can remove 𝑜0𝑚) constraints from ℋso that the remaining hypergraph satisﬁes this
condition.
The construction of [W@M19\ is as follows. First* partition the hyperedges ℋarbitrarily into
ℋ1/ / / / / ℋ𝑛* such that if 𝐶∈ℋ𝑢then 𝑢∈𝐶. From now on* we shall think of ℋas ∪𝑛
𝑢>1ℋ𝑢. We note
that our lower bound will hold regardless of the choice of the partition here.
Next* let 𝜙be the polynomial 𝜙0𝑥) :>
1
𝑚

𝐶∈ℋ𝑏𝐶𝑥𝐶* where 𝑥𝐶:> 
𝑖∈𝐶𝑥𝑖. @pplying the
Cauchy-Schwarz inequality* we have that
𝜙0𝑥)2 ⩽1
𝑚
𝑛

𝑢>1
𝑥2
𝑢˜ 𝑛
𝑚2
𝑛

𝑢>1

𝐶≠𝐶′∈ℋ𝑢
𝑏𝐶𝑏𝐶′𝑥𝐶]|𝑢|𝑥𝐶′]|𝑢| > 𝑛
𝑚˜ 𝑓0𝑥) /
where 𝑓0𝑥) :>
𝑛
𝑚2
𝑛
𝑢>1

𝐶≠𝐶′∈ℋ𝑢𝑏𝐶𝑏𝐶′𝑥𝐶]|𝑢|𝑥𝐶′]|𝑢|.
We now recall the following deﬁnition from [W@M19\.
De”nition ;.1. Let ℓ∈ℕ* and let ℋ> ∪𝑛
𝑢>1ℋ𝑢be a 3-uniform hypergraph. For a𝑆/ a𝑇∈*𝑛\ℓand
𝐶1 > |𝑢/ 𝑣1/ 𝑤1|/ 𝐶2 > |𝑢/ 𝑣2/ 𝑤2| ∈ℋ𝑢with |𝑣1/ 𝑤1| ∩|𝑣2/ 𝑤2| > ∅* we write a𝑆
𝐶1/𝐶2
↔
a𝑇if there exist
𝑖≠𝑗∈*ℓ\ such that $1) a𝑆𝑡> a𝑇𝑡for all 𝑡≠𝑖/ 𝑗* and $2) | a𝑆𝑖/ a𝑆𝑗| contains exactly one element from each
of |𝑣1/ 𝑤1| and |𝑣2/ 𝑤2|* and | a𝑇𝑖/ a𝑇𝑗| contains the other two remaining elements. Here* a𝑆𝑖denotes
the 𝑖-th element in the tuple a𝑆∈*𝑛\ℓ. We note that if a𝑆
𝐶1/𝐶2
↔
a𝑇for some 𝐶1/ 𝐶2* then we cannot have
a𝑆
𝐶′
1/𝐶′
2
↔
a𝑇for any other pair 𝐶′
1/ 𝐶′
2.
Let 𝐴𝑢∈ℝ𝑛ℓ·𝑛ℓbe the matrix where 𝐴𝑢0a𝑆/ a𝑇) > 𝑏𝐶1𝑏𝐶2 if a𝑆
𝐶1/𝐶2
↔
a𝑇for some 𝐶1 ≠𝐶2 ∈ℋ𝑢* and
0 otherwise* and let 𝐴:> 𝑛
𝑢>1 𝐴𝑢.
It is simple to observe that max𝑥∈|±1|𝑛𝑓0𝑥) ⩽
𝑛
𝑚2 · 𝑂0 𝑛2
ℓ2 ) }𝐴}2* as 𝑚2
𝑛𝑓0𝑥) >
1
40ℓ
2)0𝑛4)ℓ2 0𝑥⊗ℓ)⊤𝐴𝑥⊗ℓ
for all 𝑥∈|±1|𝑛because each pair 𝐶1 ≠𝐶2 ∈ℋ𝑢’appears“ exactly 4 ℓ
2
0𝑛
4)ℓ2 times in the
matrix 𝐴. Thus* in order to get the correct 𝑚> 𝑛1/50
]
ℓtrade-oﬀ* we need to show that }𝐴}2 ⩽𝑂0ℓ)*
with high probability over ℋand the 𝑏𝐶—s.
We prove that }𝐴}2 is in fact lYrge with high probability* and so the above approach of [W@M19\
fails. Formally* we prove that with high probability* the matrix 𝐴has a spectral norm Ω0min0ℓ2/ 𝑚2
𝑛2 ))*
which has the following implications. If the minimum is 𝑚2
𝑛2 * then the upper bound certiﬁed on
𝑓is Ω0𝑛0ℓ2)* and thus the upper bound certiﬁed on 𝜙is Ω0]𝑛0ℓ). This is not very useful* as it is
greater than 1 when ℓ≪]𝑛. If the minimum is ℓ2* then we certify a good upper bound on 𝑓$and
therefore also 𝜙) only if 𝑚⩾𝑛1/5* which is higher than the desired threshold of 𝑛1/50
]
ℓ.
Proposition ;.2. Let 𝜙be Y 3-XOR instYnce with 𝑛vYriYbles Ynd 𝑚constrYints* with constrYint hypergrYph
ℋ> ∪𝑛
𝑢>1ℋ𝑢Ynd coeﬂcients |𝑏𝐶|𝐶∈ℋ. Suppose thYt 2𝑛⩽𝑚* Ynd thYt for every pYir of constrYints
𝐶1 ≠𝐶2 ∈ℋ* it holds thYt ~𝐶1 ∩𝐶2~ ⩽1. Let ℓ⩽𝑛. Then* }𝐴}2 ⩾
ℓ′
2
* where ℓ′ :> min0𝑚
2𝑛

/ ℓ).
We note that the Proposition @.2 holds regardless of the choice of the partitioning of ℋinto
the ℋ𝑢—s* and also for any choice of the 𝑏𝐶—s $and so* in particular* for random 𝑏𝐶—s). We also note
that Proposition @.2 essentially holds for a random ℋ* provided that 𝑚≪𝑛2* for the same reason
mentioned earlier: when 𝑚≪𝑛2* with high probability over ℋ* after removing 𝑜0𝑚) constraints
from ℋ* the resulting hypergraph ℋ′ satisﬁes ~𝐶1 ∩𝐶2~ ⩽1 for all 𝐶1 ≠𝐶2 ∈ℋ′.
57

<!-- pdf-page: 60 -->
Proof. @s 𝑚⩾2𝑛* there must exist some variable 𝑢∈*𝑛\ that appears in at least 𝑚
𝑛constraints.
Hence* there must exist at least 𝑚
2𝑛

constraints that include 𝑢and all have the same sign 𝑏∈|±1|.
Let ℓ′ :> min0𝑚
2𝑛

/ ℓ). By the above* we have ℓ′ constraints |𝐶𝑖|𝑖∈*ℓ′\ > ||𝑢/ 𝑣𝑖/ 𝑤𝑖||𝑖∈*ℓ′\ such
that 𝑏𝐶𝑖> 𝑏for all 𝑖. Furthermore* by assumption on ℋ* we have
𝐶𝑖∩𝐶𝑗
⩽1 for all 𝑖≠𝑗∈*ℓ′\.
@s 𝑢∈𝐶𝑖∩𝐶𝑗* it thus follows that |𝑣𝑖/ 𝑤𝑖| ∩|𝑣𝑗/ 𝑤𝑗| > ∅. Let   ∈*𝑛\ be arbitrary. Let ℛdenote
the set of tuples 0𝑟1/ / / / / 𝑟ℓ′/  / / / / /  ) ∈*𝑛\ℓsuch that 𝑟𝑖∈|𝑣𝑖/ 𝑤𝑖| for all 𝑖∈*ℓ′\. We note that the
element   merely pads each tuple in ℛto have length exactly ℓwhen ℓ′ = ℓ.
Let 𝑀be the submatrix of 𝐴indexed by the tuples in ℛ. Note that 𝑀is a 2ℓ′ · 2ℓ′ matrix* as
~𝑅~ > 2ℓ′. Let a𝑆> 0𝑟1/ / / / / 𝑟ℓ′/  / / / / /  ) be a row in 𝑀. We will show that each row of 𝑀has exactly
ℓ′
2
nonzero entries* each of which is 1.
First* let us consider the contribution to 𝑀from 𝐴𝑢. Fix a row a𝑆∈ℛ. For each pair of indices
𝑖≠𝑗∈*ℓ′\* we can replace the 𝑖-th and 𝑗-th elements of a𝑆with the elements of |𝑣𝑖/ 𝑤𝑖| and |𝑣𝑗/ 𝑤𝑗|
not used in a𝑆* and this will yield some a𝑇∈ℛwith a𝑆
|𝑢/𝑣𝑖/𝑤𝑖|/|𝑢/𝑣𝑗/𝑤𝑗|
↔
a𝑇. Hence* 𝐴𝑢0a𝑆/ a𝑇) > 𝑏2 > 1.
@ny other a𝑇∈ℛwill diﬀer from a𝑆by at least 2 elements* and thus we must have 𝐴𝑢0a𝑆/ a𝑇) > 0 for
such a𝑇.
Next* let us consider the contribution to 𝑀from 𝐴𝑢′ for 𝑢′ ≠𝑢. Fix a row a𝑆∈ℛ. It suﬂces to
only consider a𝑇obtained by swapping the 𝑖-th and 𝑗-th entries of a𝑆* for some 𝑖≠𝑗∈*ℓ′\* as above. If
𝐴𝑢′0a𝑆/ a𝑇) is nonzero* then we must have a𝑆
|𝑢′/𝑣𝑖/𝑤𝑖|/|𝑢′/𝑣𝑗/𝑤𝑗|
↔
a𝑇* and thus that |𝑢′/ 𝑣𝑖/ 𝑤𝑖|/ |𝑢′/ 𝑣𝑗/ 𝑤𝑗| ∈
ℋ𝑢′. However* this implies that ~|𝑢/ 𝑣𝑖/ 𝑤𝑖|/ |𝑢′/ 𝑣𝑖/ 𝑤𝑖|~ > 2 = 1* which contradicts our assumption
on ℋ.
We have thus shown that the matrix 𝑀is 2ℓ′ · 2ℓ′* with each row having exactly
ℓ′
2
nonzero
entries* all of which are 1. It thus follows that }𝐴}2 ⩾}𝑀}2 ⩾012ℓ′
)⊤𝑀12ℓ′
02ℓ′ >
ℓ′
2
* which ﬁnishes
the proof.
58
