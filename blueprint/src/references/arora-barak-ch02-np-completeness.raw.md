<!-- generated-by: scoped pypdf extraction (maintainer ingest for EF-H12, 2026-11-19; ruling EF-H12-R4 A / Q-H12-2 A) -->
<!-- source-pdf-sha256: da0881782a35bde6a0779a2eb1a8d480f39fbddf70bbb92824d1dc5550a033b2 -->
<!-- source: S. Arora, B. Barak, "Computational Complexity: A Modern Approach", authors' public web draft (Princeton), https://theory.cs.princeton.edu/complexity/book.pdf, 489 pages, page footers "Web draft 2007-01-08 21:59"; NOT the Cambridge University Press 2009 edition: its chapter, section, theorem and page numbers are the draft's and may differ from CUP 2009 -->
<!-- extractor: pypdf 6.17.0 under python3 -I, extract_text(extraction_mode="layout"); per page the common left indentation is removed, trailing spaces are stripped and runs of blank lines are collapsed; nothing else is edited (the "DRAFT" watermark, running heads, footers and figure debris are kept as extracted) -->
<!-- scope: PDF pages 55-80, the whole of Chapter 2 'NP and NP completeness' (chapter title to the end of Exercise 23; Chapter 3 begins on PDF page 81) -->
<!-- note: physical PDF page p is printed draft page p - 16; the draft prints a chapter label as well, "p2.k (N)" with k = p - 54 and N = p - 16 -->
<!-- validation-status: awaiting Codex source review -->

<!-- pdf-page: 55 -->
              Chapter 2

              NP and NP completeness

                       “(ifφ(n)≈Kn2)a         then this would have consequences of the greatest magnitude.  That
                       is  to  say,  it  would  clearly  indicate  that,  despite  the  unsolvability  of  the  (Hilbert)
                       Entscheidungsproblem,  the  mental  eﬀort  of  the  mathematician  in  the  case  of  the
                       yes-or-no questions would be completely replaced by machines....  (this) seems to me,
                       however, within the realm of possibility.”
                       Kurt G¨odel in a letter to John von Neumann, 1956

                          aIn modern terminology, if SAT has a quadratic time algorithm

                       “I  conjecture  that  there  is  no  good  algorithm  for  the  traveling  salesman  problem.
                       My reasons are the same as for any mathematical conjecture:  (1) It is a legitimate
                       mathematical possibility, and (2) I do not know.”
                       Jack Edmonds, 1966

                       “In this paper we give theorems that suggest, but do not imply, that these problems,
                       as well as many others, will remain intractable perpetually.”
                       Richard Karp, 1972

                   If you have ever attempted a crossword puzzle, you know that there is often a big diﬀerence
              between solving a problem from scratch and verifying a given solution.  In the previous chapter we
              encountered P, the class of decision problems that can be eﬃciently solved.  In this chapter, we
              deﬁne the complexity class NP that aims to capture the set of problems whose solutions can be
              eﬃciently veriﬁed.  The famous P versus NP question asks whether or not the two are the same.
              The resolution of this conjecture will be of great practical, scientiﬁc and philosophical interest; see
              Section   2.7.
                   This chapter also introduces NP-completeness, an important class of computational problems
              that are in P if and only if P = NP.  Notions such as reductions and completeness encountered in
              this study motivate many other deﬁnitions encountered later in the book.

              Web  draft  2007-01-08  21:59                          p2.1 (39)
              Complexity Theory:  A Modern Approach. © 2006 Sanjeev Arora and Boaz Barak.  References and attributions are
DRAFTstill incomplete.

<!-- pdf-page: 56 -->
p2.2 (40)                                                                                                        2.1.   THE CLASS NP
2.1   The class NP

As  mentioned  above,  the  complexity  class NP  will  serve  as  our  formal  model  for  the  class  of
problems having eﬃciently veriﬁable solutions:  a decision problem / language is in NP if given an
input x, we can easily verify that x is a YES instance of the problem (or equivalently, x is in the
language) if  we are given the polynomial-size solution  for x, that certiﬁes  this fact.  We will give
several equivalent deﬁnitions for NP.  The ﬁrst one is as follows:

 Definition 2.1 (The class NP)
 A  language L⊆{0, 1}∗  is  in NP  if  there  exists  a  polynomial p  : N→ N  and  a
 polynomial-time TM M  such that for every x∈{0, 1}∗,

                           x∈L⇔∃u∈{0, 1}p(|x|)  s.t. M(x,u) = 1

 If x∈ L and u∈{0, 1}p(|x|)  satisfy M(x,u) = 1 then we call u a certiﬁcate1for x
 (with respect to the language L and machine M).

Example 2.2
Here are a few examples for decision problems in NP:

Independent set:         (See Example      1.1 in the previous chapter.)  Given a graphG and a numberk,
       decide if there is a k-size independent subset of G’s vertices.  The certiﬁcate for membership
       is the list of k vertices forming an independent set.
Traveling salesperson:          Given a set ofn nodes,(n) numbersdi,j denoting the distances between
                                                               2
       all  pairs  of  nodes,  and  a  number k,  decide  if  there  is  a  closed  circuit  (i.e.,  a  “salesperson
       tour”) that visits every node exactly once and has total length at most k.  The certiﬁcate is
       the sequence of nodes in the tour.

Subset sum:        Given a list ofn numbersA1,...,An and a numberT, decide if there is a subset of
       the numbers that sums up to T.  The certiﬁcate is the list of members in this subset.

Linear programming:            Given a list ofm linear inequalities with rational coeﬃcients overn vari-
       ables u1,...,un  (a  linear  inequality  has  the  form a1u1 +a2u2 +... +anun ≤ b  for  some
       coeﬃcientsa1,...,an,b), decide if there is an assignment of rational numbers to the variables
       u1,...,un that satisﬁes all the inequalities.  The certiﬁcate is the assignment.

Integer programming:             Given  a  list  of m  linear  inequalities  with  rational  coeﬃcients  over n
       variables u1,...,um,  ﬁnd  out  if  there  is  an  assignment  of  integer  numbers  to u1,...,un
       satisfying the inequalities.  The certiﬁcate is the assignment.

   1Some texts use the term witness instead of certiﬁcate.

                                                                                   Web  draft  2007-01-08  21:59
DRAFT

<!-- pdf-page: 57 -->
2.1.   THE CLASS NP                                                                                                                            p2.3 (41)
Graph isomorphism:            Given two n×n adjacency matrices M1,M2, decide if M1 and M2 deﬁne
       the same graph, up to renaming of vertices.  The certiﬁcate is the permutation π : [n]→ [n]
       such that M2 is equal to M1 after reordering M1’s indices according to π.

Composite numbers:            Given a number N  decide if N  is a composite (i.e., non-prime) number.
       The certiﬁcate is the factorization of N.

Factoring:      Given three numbers N,L,U  decide if N  has a factor M  in the interval [L,U].  The
       certiﬁcate is the factor M.

Connectivity:       Given a graphG and two verticess,t inG, decide ifs is connected tot inG.  The
       certiﬁcate is the path from s to t.

2.1.1   Relation between NP and P
We  have  the  following  trivial  relationships  between NP  and  the  classes P  and DTIME(T(n))
deﬁned in the previous chapter:
Claim 2.3
P⊆ NP⊆⋃c>1 DTIME(2nc).

Proof: (P⊆ NP):  Suppose L∈ P is decided in polynomial-time by a TM N.  Then L∈ NP
since we can take N  as the machine M  in Deﬁnition               2.1 and make p(x) the zero polynomial (in
other words, u is an empty string).
     (NP⊆⋃c>1 DTIME(2nc)):  IfL∈ NP andM,p() are as in Deﬁnition                           2.1 then we can decide
L in time 2O(p(n)) by enumerating all possibleu and usingM to check whetheru is a valid certiﬁcate
for the inputx.  The machine accepts iﬀ such au is ever found.  Sincep(n) =O(nc) for somec> 1
then this machine runs in 2O(nc) time.  Thus the theorem is proven. ■
     At the moment, we do not know of any stronger relation between NP and deterministic time
classes than the trivial ones stated in Claim       2.3. The question whether or not P = NP is considered
the central open question of complexity theory, and is also an important question in mathematics
and science at large (see Section       2.7).  Most researchers believe that P⁄= NP since years of eﬀort
has failed to yield eﬃcient algorithms for certain NP languages.

Example 2.4
Here is the current knowledge regarding the NP decision problems mentioned in Example                         2.2:
The Connectivity, Composite Numbers and Linear programming problems are known to be
in P.  For connectivity this follows from the simple and well known breadth-ﬁrst search algorithm
(see  [KT06,    CLRS01]).   The  composite  numbers  problem  was  only  recently  shown  to  be  in P
by  Agrawal,  Kayal  and  Saxena  [?],  who  gave  a  beautiful  algorithm  to  solve  it.   For  the  linear
programming problem this is again highly non-trivial, and follows from the Ellipsoid algorithm of
Khachiyan [?] (there are also faster algorithms, following Karmarkar’s interior point paradigm [?]).

Web  draft  2007-01-08  21:59
DRAFT

<!-- pdf-page: 58 -->
p2.4 (42)                                                                                                        2.1.   THE CLASS NP
     All the rest of the problems are not known to have a polynomial-time algorithm, although we
have no proof that they are not in P.  The Independent Set, Traveling Salesperson, Subset
Sum, and Integer Programming problems are known to be NP-complete, which, as we will see
in this chapter, implies that they are not in P unless P = NP.  The Graph Isomorphism and
Factoring problems are not known to be either in P nor NP-complete.

2.1.2   Non-deterministic Turing machines.
The  class NP  can  also  be  deﬁned  using  a  variant  of  Turing  machines  called  non-deterministic
Turing machines (abbreviated NDTM). In fact, this was the original deﬁnition and the reason for
the name NP, which stands for non-deterministic polynomial-time. The only diﬀerence between an
NDTM and a standard TM is that an NDTM has two transition functions δ0 and δ1.  In addition
the NDTM has a special state we denote by qaccept.   When an NDTM M  computes a function,
we envision that at each computational step M  makes an arbitrary choice as to which of its two
transition functions to apply. We say thatM outputs 1 on a given inputx if there is some sequence
of these choices (which we call the non-deterministic choices ofM) that would makeM reachqaccept
on inputx.  Otherwise— if every sequence of choices makesM halt without reachingqaccept— then
we say that M(x) = 0.  We say that M  runs in T(n) time if for every input x∈{0, 1}∗ and every
sequence of non-deterministic choices, M  reaches either the halting state or qaccept  within T(|x|)
steps.
Definition 2.5
For  every  function T  : N→ N  and L⊆{0, 1}∗,  we  say  that L∈ NTIME(T(n))  if  there  is  a
constant c> 0 and a cT(n)-time NDTM M  such that for every x∈{0, 1}∗, x∈L⇔M(x) = 1

     The next theorem gives an alternative deﬁnition of NP, the one that appears in most texts.
Theorem 2.6
NP =∪c∈NNTIME(nc)

Proof:  The  main  idea  is  that  the  sequence  of  nondeterministic  choices  made  by  an  accepting
computation of an NDTM can be viewed as a certiﬁcate that the input is in the language, and vice
versa.
     Supposep :N→N is a polynomial andL is decided by a NDTMN that runs in timep(n).  For
everyx∈L, there is a sequence of nondeterministic choices that makesN reachqaccept on inputx.
We can use this sequence as a certiﬁcate forx.  Notice, this certiﬁcate has lengthp(|x|) and can be
veriﬁed in polynomial time by a deterministic machine, which checks that N  would have entered
qaccept after using these nondeterministic choices.  Thus L∈ NP according to Deﬁnition                    2.1.
     Conversely, if L∈ NP according to Deﬁnition            2.1, then we describe a polynomial-time NDTM
N  that decides L.  On input x, it uses the ability to make non-deterministic choices to write down
a string u of length p(|x|).  (Concretely,  this can be done by having transition δ0  correspond to
writing a 0 on the tape and transitionδ1 correspond to writing a 1.)  Then it runs the deterministic

                                                                                Web  draft  2007-01-08  21:59
DRAFT

<!-- pdf-page: 59 -->
2.2.   REDUCIBILITY AND NP-COMPLETENESS                                                                      p2.5 (43)
veriﬁer M  of  Deﬁnition      2.1  to  verify  that u  is  a  valid  certiﬁcate  for x,  and  if  so,  enters qaccept.
Clearly, N  enters qaccept on x if and only if a valid certiﬁcate exists for x.  Since p(n) =O(nc) for
some c> 1, we conclude that L∈ NTIME(nc). ■
    As is the case with deterministic TM’s, NDTM’s can be easily represented as strings and there
exists a universal non-deterministic Turing machine, see Exercise             1. (In fact, using non-determinism
we can even make the simulation by a universal TM slightly more eﬃcient.)

2.2   Reducibility and NP-completeness

It turns out that the independent set problem is at least as hard as any other language in NP:  if
it has a polynomial-time algorithm then so do all the problems in NP.  This fascinating property
is called NP-hardness.  Since most scientists conjecture that NP⁄= P, the fact that a language is
NP-hard can be viewed as evidence that it cannot be decided in polynomial time.
    How can we prove that a languageB is at least as hard as some other languageA?  The crucial
tool we use is the notion of a reduction (see Figure           2.1):

 Definition 2.7 (Reductions, NP-hardness and NP-completeness)
 We say that a languageA⊆{0, 1}∗ is polynomial-time Karp reducible to a language
 B⊆{0, 1}∗ (sometimes shortened to just “polynomial-time reducible”2) denoted by
 A≤pB if there is a polynomial-time computable functionf :{0, 1}∗→{0, 1}∗ such
 that for every x∈{0, 1}∗, x∈A if and only if f(x)∈B.
 We  say  that B  is NP-hard  if A ≤p B  for  every A ∈  NP.   We  say  that B  is
 NP-complete if B is NP-hard and B∈ NP.

Figure 2.1:  A Karp reduction fromL toL′ is a polynomial-time functionf  that maps strings inL to strings inL′
and strings in L = {0, 1}∗ \L to strings in  L′.  It can be used to transform a polynomial-time TM M′ that decides
L′ into a polynomial-time TM M  for L by setting M(x) =M′(f(x)).
    Now we observe some properties of polynomial-time reductions. Part 1 of the following Theorem
shows that this relation is transitive.  (Later we will deﬁne other notions of reduction, and all will

   2Some texts call this notion “many-to-one reducibility” or “polynomial-time mapping reducibility”.

Web  draft  2007-01-08  21:59
DRAFT

<!-- pdf-page: 60 -->
p2.6 (44)                                2.3.   THE COOK-LEVIN THEOREM: COMPUTATION IS LOCAL
satisfy  transitivity.)   Part  2  suggests  the  reason  for  the  term NP-hard  —namely,  an NP-hard
languages  is  at  least  as  hard  as  any  other NP  language.   Part  3  similarly  suggests  the  reason
for the term NP-complete:  to study the P versus NP question it suﬃces to study whether any
NP-complete problem can be decided in polynomial time.

Theorem 2.8
   1.  (Transitivity) If A≤pB and B≤pC, then A≤pC.

   2.  If language A is NP-hard and A∈ P then P = NP.

   3.  If language A is NP-complete then A∈ P if and only if P = NP.

Proof: The main observation is that if p,q are two functions that have polynomial growth then
their composition p(q(n)) also has polynomial growth.  We prove part 1 and leave the others as
simple exercises.
    If f1  is  a  polynomial-time  reduction  from A  to B  and f2  is  a  reduction  from B  to C  then
the  mapping x↦→ f2(f1(x))  is  a  polynomial-time  reduction  from A  to C  since f2(f1(x))  takes
polynomial time to compute given x and f2(f1(x))∈C iﬀ x∈A. ■

    Do NP-complete languages exist?  It may not be clear that NP should possess a language that
is as hard as any other language in the class.  However, this does turn out to be the case:

Theorem 2.9
The following language is NP-complete:

      TMSAT ={⟨α,x, 1n, 1t⟩ :∃u∈{0, 1}n  s.t. Mα outputs 1 on input⟨x,u⟩ within t steps}

where Mα denotes the TM represented by the string α.3

    Once you internalize the deﬁnition of NP, the proof of Theorem                2.9  is straightforward and so
is left to the reader as Exercise      2.  But TMSAT is not a very useful NP-complete problem since
its deﬁnition is intimately tied to the notion of the Turing machine, and hence the fact that it is
NP-complete does not provide much new insight.

2.3   The Cook-Levin Theorem:  Computation is Local

Around 1971, Cook and Levin independently discovered the notion of NP-completeness and gave
examples of combinatorial NP-complete problems whose deﬁnition seems to have nothing to do
with Turing machines.  Soon after, Karp showed that NP-completeness occurs widely and many
problems of practical interest are NP-complete.  To date, thousands of computational problems in
a variety of disciplines have been found to be NP-complete.

   3Recall that 1k denotes the string consisting of k 1’s.  it is a common convention in complexity theory to provide
a polynomial TM with such an input to allow it to run in time polynomial in k.

                                                                               Web  draft  2007-01-08  21:59
DRAFT

<!-- pdf-page: 61 -->
2.3.   THE COOK-LEVIN THEOREM: COMPUTATION IS LOCAL                                      p2.7 (45)
2.3.1   Boolean formulae and the CNF form.
Some of the simplest examples of NP-complete problems come from propositional logic.  A Boolean
formula  over the variables u1,...,un consists of the variables and the logical operators AND (∧),
NOT (¬) and OR (∨); see Appendix            A  for their deﬁnitions.  For example, (a∧b)∨ (a∧c)∨ (b∧c)
is a Boolean formula that is True if and only if the majority of the variables a,b,c are True.  If
ϕ is a Boolean formula over variables u1,...,un, and z∈{0, 1}n, then ϕ(z) denotes the value of
ϕ when the variables of ϕ are assigned the values z  (where we identify 1 with True and 0 with
False).  A formula ϕ is satisﬁable if there there exists some assignment z such that ϕ(z) is True.
Otherwise, we say that ϕ is unsatisﬁable.
    A Boolean formula over variablesu1,...,un is in CNF form (shorthand for Conjunctive Normal
Form) if it is an AND of OR’s of variables or their negations.  For example, the following is a 3CNF
formula:
                              (u1∨ ¯u2∨u3)∧ (u2∨ ¯u3∨u4)∧ (¯u1∨u3∨ ¯u4).
where ¯u denotes the negation of the variable u.
    More generally, a CNF formula has the form
                                                             
                                                  ⋀⋁      vij,

                                                   i    j

where each vij  is either a variable uk  or to its negation¬uk.  The terms vij  are called the literals
of the formula and the terms (∨jvij) are called its clauses.  AkCNF is a CNF formula in which all
clauses contain at most k literals.

2.3.2   The Cook-Levin Theorem
The following theorem provides us with our ﬁrst natural NP-complete problems:

  Theorem 2.10 (Cook-Levin Theorem [Coo71,                     Lev73])
  Let SAT be the language of all satisﬁable CNF formulae and 3SAT be the language
  of all satisﬁable 3CNF formulae.  Then,

     1. SAT is NP-complete.

     2. 3SAT is NP-complete.

Remark 2.11
An alternative proof of the Cook-Levin theorem, using the notion of Boolean circuits, is described
in Section   6.7.

    Both SAT and 3SAT are clearly in NP, since a satisfying assignment can serve as the certiﬁcate
that a formula is satisﬁable.  Thus we only need to prove that they are NP-hard.  We do so by ﬁrst

Web  draft  2007-01-08  21:59
DRAFT

<!-- pdf-page: 62 -->
p2.8 (46)                                2.3.   THE COOK-LEVIN THEOREM: COMPUTATION IS LOCAL
proving that SAT is NP-hard and then showing that SAT is polynomial-time Karp reducible to
3SAT.  This implies that 3SAT is NP-hard by the transitivity of polynomial-time reductions.  Thus
the following lemma is the key to the proof.
Lemma 2.12
SAT is NP-hard.
    Notice, to prove this we have to show how to reduce every NP language L to SAT, in other
words give a polynomial-time transformation that turns any x∈{0, 1}∗  into a CNF formula ϕx
such that x∈L iﬀ ϕx is satisﬁable.  Since we know nothing about the language L except that it is
in NP, this reduction has to rely just upon the deﬁnition of computation, and express it in some
way using a Boolean formula.

2.3.3   Warmup:  Expressiveness of boolean formulae
As a warmup for the proof of Lemma           2.12  we show how to express various conditions using CNF
formulae.

Example 2.13
The formula (a∨      b)∧ (a∨b) is in CNF form.  It is satisﬁed by only those values of a,b that are
equal.  Thus, the formula
                             (x1∨   y1)∧ (x1∨y1)∧···∧ (xn∨           yn)∧ (xn∨yn)
is True if and only if the strings x,y∈{0, 1}n are equal to one another.
    Thus, though = is not a standard boolean operator like∨ or∧, we will use it as a convenient
shorthand  since  the  formula φ1  = φ2  is  equivalent  to  (in  other  words,  has  the  same  satisfying
assignments as) (φ1∨      φ2)∧ (φ1∨φ2).

    In fact, CNF formulae of suﬃcient size can express every  Boolean condition, as shown by the
following simple claim:  (this fact is sometimes known as universality  of the operations AND, OR
and NOT)
Claim 2.14
For every Boolean function f  :{0, 1}𝓁→{0, 1} there is an 𝓁-variable CNF formula ϕ of size 𝓁2𝓁
such that ϕ(u) =f(u) for every u∈{0, 1}𝓁, where the size of a CNF formula is deﬁned to be the
number of∧/∨ symbols it contains.
Proof Sketch:   For everyv∈{0, 1}𝓁, it is not hard to see that there exists a clauseCv such that
Cv(v) = 0 and Cv(u) = 1 for every u⁄=v.  For example, if v =⟨1, 1, 0, 1⟩, the corresponding clause
is u1∨  u2∨u3∨      u4.
    We let ϕ be the AND of all the clauses Cv  for v such that f(v) = 0 (note that ϕ is indeed of
size at most 𝓁2𝓁).  Then for every u such that f(u) = 0 it holds that Cu(u) = 0 and hence ϕ(u) is
also equal to 0.  On the other hand, if f(u) = 1 then Cv(u) = 1 for every v such that f(v) = 0 and
hence ϕ(u) = 1.  We get that for every u, ϕ(u) =f(u). ■
    In this chapter we will use Claim      2.14 only when the number of variables is some ﬁxed constant.

                                                                               Web  draft  2007-01-08  21:59
DRAFT

<!-- pdf-page: 63 -->
2.3.   THE COOK-LEVIN THEOREM: COMPUTATION IS LOCAL                                      p2.9 (47)
2.3.4   Proof of Lemma              2.12

LetL be an NP language and letM be the polynomial time TM such that that for everyx∈{0, 1}∗,
x∈L⇔M(x,u) = 1 for some u∈{0, 1}p(|x|), where p :N→N is some polynomial.  We show L is
polynomial-time Karp reducible to SAT by describing a way to transform in polynomial-time every
string x∈{0, 1}∗ into a CNF formula ϕx such that x∈L iﬀ ϕx is satisﬁable.
    How can we construct such a formulaϕx? By Claim                2.14, the function that mapsu∈{0, 1}p(|x|)
toM(x,u) can be expressed as a CNF formulaψx (i.e.,ψx(u) =M(x,u) for everyu∈{0, 1}p(|x|)).
Thus a string u such that M(x,u) = 1 exists if and only if ψx is satisﬁable.  But this is not useful
for us, since the size of the formulaψx obtained from Claim             2.14  can be as large asp(|x|)2p(|x|).  To
get a smaller formula we use the fact that M  runs in polynomial time, and that each basic step of
a Turing machine is highly local  (in the sense that it examines and changes only a few bits of the
machine’s tapes).

    In the course of the proof we will make the following simplifying assumptions about the TM
M: (1) M  only has two tapes:  an input tape and a work/output tape and (2) M  is an oblivious
TM in the sense that its head movement does not depend on the contents of its input tape.  In
particular, this means that M’s computation takes the same time for all inputs of size n and for
each time stepi the location ofM’s heads at theith step depends only oni andM’s input length.
    We  can  make  these  assumptions  without  loss  of  generality  because  for  every T(n)-time  TM
M  there exists a two-tape oblivious TM   ˜M  computing the same function in O(T(n)2) time (see
Remark    1.10   and  Exercise    8 of  Chapter    1).4   Thus  in  particular,  if L  is  in NP  then  there  ex-
ists a two-tape oblivious polynomial-time TM M  and a polynomial p such that x∈ L⇔∃u∈
{0, 1}p(|x|)  s.t. M(x,u) = 1.
    The advantage of assuming thatM is oblivious is that for any given input length, we can deﬁne
functions inputpos(i), prev(i) where inputpos(i) denotes the location of the input tape head at
theith step and prev(i) denotes the last step beforei thatM visited the same location on its work
tape, see Figure    2.3.5  These values can be computed in polynomial time by simulating M  on, say,
the all-zeroes input.
    Denote byQ the set ofM’s possible states and by Γ its alphabet. The snapshot ofM’s execution
on some inputy at a particular stepi is the triple⟨a,b,q⟩∈ Γ×Γ×Q such thata,b are the symbols
read by M’s heads from the two tapes and q is the state M  is in at the ith step (see Figure                     2.2).
For everym∈N andy∈{0, 1}m, the snapshot ofM’s execution on inputy at theith step depends
on (1) its state in the i− 1st step and (2) the contents of the current cells of its input and work
tapes.  We write this relation as

                                       zi =F(zi−1,zprev(i),yinputpos(i)),

where inputpos(i) and prev(i) are as deﬁned earlier, zi  is the encoding of the ith  snapshot as a
binary string of some lengthc, andF  is some function (derived fromM’s transition function) that

   4In fact, with some more eﬀort we even simulate a non-oblivious T(n)-time TM by an oblivious TM running in
O(T(n) logT(n))-time, see Exercise   9 of Chapter  1.  This oblivious machine may have more than two tapes, but the
proof below easily generalizes to this case.
   5If i is the ﬁrst step that M  visits a certain location, then we deﬁne prev(i) = 1.

Web  draft  2007-01-08  21:59
DRAFT

<!-- pdf-page: 64 -->
p2.10 (48)                               2.3.   THE COOK-LEVIN THEOREM: COMPUTATION IS LOCAL

Figure 2.2:  A snapshot of a TM contains the current state and symbols read by the TM at a particular step.  If at
the ith step M  reads the symbols 0, 1 from its tapes and is in the state q7 then the snapshot of M  at the ith step is
⟨0, 1,q7⟩.

maps{0, 1}2c+1 to{0, 1}c.  (Note that c is a constant depending only on M’s state and alphabet
size, and independent of the input size.)

Figure 2.3:   The snapshot of M  at the ith  step depends on its previous state (contained in the snapshot at the
i − 1st step), and the symbols read from the input tape, which is in position inputpos(i), and from the work tape,
which was last written to in step prev(i).

    Let n∈ N  and x∈{0, 1}n.   We  need  to  construct  a  CNF  formula ϕx  such  that x∈ L⇔
ϕx∈ SAT.  Recall that x∈ L if and only if there exists some u∈{0, 1}p(n)  such that M(y) = 1
wherey =x◦u (with◦ denoting concatenation).  Since the sequence of snapshots inM’s execution
completely determines its outcome, this happens if and only if there exists a stringy∈{0, 1}n+p(n)
and a sequence of strings z1,...,zT∈{0, 1}c (where T  =T(n) is the number of steps M  takes on
inputs of length n +p(n)) satisfying the following four conditions:

   1.  The ﬁrst n bits of y are equal to x.

   2.  The string z1 encodes the initial snapshot of M  (i.e., the triple⟨⊿,□,qstart⟩ where ⊿ is the
       start symbol of the input tape, □ is the blank symbol, andqstart is the initial state of the TM

                                                                                   Web  draft  2007-01-08  21:59
DRAFT

<!-- pdf-page: 65 -->
2.3.   THE COOK-LEVIN THEOREM: COMPUTATION IS LOCAL                                     p2.11 (49)
       M).

   3.  For every i∈{2,..,T}, zi =F(zi−1,zinputpos(i),zprev(i)).

   4.  The last string zT  encodes a snapshot in which the machine halts and outputs 1.

    The formula ϕx  will take variables y∈{0, 1}n+p(n)  and z∈{0, 1}cT  and will verify that y,z
satisfy the AND of these four conditions.  Clearly x∈L⇔ϕx∈ SAT and so all that remains is to
show that we can express ϕx as a polynomial-sized CNF formula.
    Condition 1 can be expressed as a CNF formula of size 4n (see Example                   2.13).  Conditions 2
and 4 each depend on c variables and hence by Claim              2.14 can be expressed by CNF formulae of
sizec2c.  Condition 3, which is an AND ofT  conditions each depending on at most 3c+1 variables,
can be expressed as a CNF formula of size at most T(3c + 1)23c+1.  Hence the AND of all these
conditions can be expressed as a CNF formula of sized(n +T) whered is some constant depending
only onM.  Moreover, this CNF formula can be computed in time polynomial in the running time
of M. ■

2.3.5   Reducing SAT to 3SAT.
Since both SAT and 3SAT are clearly in NP, Lemma                 2.12  completes the proof that SAT is NP-
complete.  Thus all that is left to prove Theorem         2.10  is the following lemma:

Lemma 2.15
SAT≤p 3SAT.

Proof: We will map a CNF formulaϕ into a 3CNF formulaψ such thatψ is satisﬁable if and only if
ϕ is. We demonstrate ﬁrst the case thatϕ is a 4CNF. LetC be a clause ofϕ, sayC =u1∨u2∨u3∨u4.
We add a new variable z  to the ϕ and replace C  with the pair of clauses C1  = u1∨                   u2∨z  and
C2 =   u3∨u4∨     z.  Clearly, ifu1∨   u2∨  u3∨u4 is true then there is an assignment toz that satisﬁes
both u1∨    u2∨z and     u3∨u4∨      z and vice versa:  if C is false then no matter what value we assign
to z either C1 or C2 will be false.  The same idea can be applied to a general clause of size 4, and
in fact can be used to change every clauseC of sizek (fork> 3) into an equivalent pair of clauses
C1 of size k− 1 and C2 of size 3 that depend on the k variables of C  and an additional auxiliary
variable z.  Applying this transformation repeatedly yields a polynomial-time transformation of a
CNF formula ϕ into an equivalent 3CNF formula ψ. ■

2.3.6   More thoughts on the Cook-Levin theorem
The Cook-Levin theorem is a good example of the power of abstraction.  Even though the theorem
holds regardless of whether our computational model is the C programming language or the Turing
machine, it may have been considerably more diﬃcult to discover in the former context.
    Also, it is worth pointing out that the proof actually yields a result that is a bit stronger than
the theorem’s statement:

Web  draft  2007-01-08  21:59
DRAFT

<!-- pdf-page: 66 -->
p2.12 (50)                                                                                 2.4.   THE WEB OF REDUCTIONS
   1.  If  we  use  the  eﬃcient  simulation  of  a  standard  TM  by  an  oblivious  TM  (see  Exercise              9,
       Chapter    1) then for every x∈{0, 1}∗, the size of the formula ϕx (and the time to compute
       it)  is O(T logT),  where T  is  the  number  of  steps  the  machine M  takes  on  input x  (see
       Exercise   10).

   2.  The reductionf  from an NP-languageL to SAT presented in Lemma                        2.12  not only satisﬁed
       that x∈ L⇔ f(x)∈  SAT  but  actually  the  proof  yields  an  eﬃcient  way  to  transform  a
       certiﬁcate for x to a satisfying assignment for f(x) and vice versa.  We call a reduction with
       this property a Levin reduction.  One can also verify that the proof supplied a one-to-one and
       onto map between the set of certiﬁcates for x and the set of satisfying assignments for f(x),
       implying that they are of the same size. A reduction with this property is called parsimonious.
       Most of the known NP-complete problems (including all the ones mentioned in this chapter)
       have parsimonious Levin reductions from all the NP languages (see Exercise                    11).  As we will
       see in this book, this fact is sometimes useful for certain applications.

Why  3SAT?    The reader may wonder why is the fact that 3SAT is NP-complete so much more
interesting  than  the  fact  that,  say,  the  language  TMSAT  of  Theorem            2.9 is NP-complete.   One
answer  is  that  3SAT  is  useful  for  proving  the NP-completeness  of  other  problems:  it  has  very
minimal combinatorial structure and thus easy to use in reductions.   Another answer has to do
with  history:   propositional  logic  has  had  a  central  role  in  mathematical  logic  —in  fact  it  was
exclusively the language of classical logic (e.g.  in ancient Greece).  This historical resonance is one
reason why Cook and Levin were interested in 3SAT in the ﬁrst place.  A third answer has to do
with practical importance:  it is a simple example of  constraint  satisfaction  problems,  which are
ubiquitous in many ﬁelds including artiﬁcial intelligence.

2.4   The web of reductions

Cook and Levin had to show how every NP language can be reduced to SAT.  To prove the NP-
completeness of any other languageL, we do not need to work as hard:  it suﬃces to reduce SAT or
3SAT to L.  Once we know that L is NP-complete we can show that an NP-language L′ is in fact
NP-complete by reducing L to L′.  This approach has been used to build a “web of reductions”
and  show  that  thousands  of  interesting  languages  are  in  fact NP-complete.   We  now  show  the
NP-completeness of a few problems.  More examples appear in the exercises (see Figure                        2.4).  See
the classic book by Garey and Johnson [GJ79] and the Internet site [?] for more.
Theorem 2.16 (Independent set is NP-complete)
Let INDSET ={⟨G,k⟩ :G has independent set of size k}.  Then INDSET is NP-complete.

Proof: Since INDSET is clearly in NP, we only need to show that it is NP-hard, which we do by
reducing 3SAT to INDSET.  Let ϕ be a 3CNF formula on n variables with m clauses.  We deﬁne a
graph G of 7m vertices as follows:  we associate a cluster of 7 vertices in G with each clause of ϕ.
The vertices in cluster associated with a clauseC correspond to the 7 possible partial assignments to
the three variablesC depends on (we call these partial assignments, since they only give values for
some of the variables).  For example, ifC is         u2∨u5∨u7 then the 7 vertices in the cluster associated

                                                                                  Web  draft  2007-01-08  21:59
DRAFT

<!-- pdf-page: 67 -->
2.4.   THE WEB OF REDUCTIONS                                                                                                p2.13 (51)

                                                                       ∀L∈ NP
                   Theorem              2.10       (Lemma             2.12)
                                                                                   SAT?     X                         X                         X                         X                         X                         X                         X                         X                         X                         X                         X                         X                         X                         X                         X                         X X
                                                                                                       Theorem              2.10      (Lemma              2.15)
   Theorem              2.18                                                        
                        9                                                            ?Theorem              2.17
     dHAMPATH                                                                   INTEGERPROG                                                                z
                                                                                                                                                                 3SAT
                                                                                                Theorem              2.16                                           ~ Z       ZEx  16
                           ?    Ex     17                                                             9                                                       Exactone3SAT
     HAMPATH                                                          
                               H                         H                         H                         H            HINDSET                   Ex     16
                                                                                                          @
                       Ex      17         j                                                                    @                         @                         @                         @?
 TSP                   HAMCYCLE                                                                                                                            SUBSETSUM
                                                                                              Ex      14
                                                                                       
              Ex      6                                                                                                        R@                 @
                                                                                                                          VERTEXCOVER
    THEOREMS                                                           CLIQUE
                                                                                                                                          Ex      15
                                                                                                                                        ?
             Ex      18                                                                                                      MAXCUT
                                         
            QUADEQ

Figure 2.4:  Web of reductions between the NP-completeness problems described in this chapter
and the exercises.  Thousands more are known.

Web  draft  2007-01-08  21:59
DRAFT

<!-- pdf-page: 68 -->
p2.14 (52)                                                                                 2.4.   THE WEB OF REDUCTIONS
with C correspond to all partial assignments of the form u1 =a,u2 =b,u3 =c for a binary vector
⟨a,b,c⟩⁄=⟨1, 1, 1⟩.  (If C  depends on less than three variables then we repeat one of the partial
assignments and so some of the 7 vertices will correspond to the same assignment.)  We put an
edge between two vertices ofG if they correspond to inconsistent partial assignments.  Two partial
assignments are consistent if they give the same value to all the variables they share.  For example,
the assignment u1 = 1,u2 = 0,u3 = 0 is inconsistent with the assignment u3 = 1,u5 = 0,u7 = 1
because they share a variable (u3) to which they give a diﬀerent value.  In addition, we put edges
between every two vertices that are in the same cluster.
    Clearly transformingϕ intoG can be done in polynomial time.  We claim thatϕ is satisﬁable if
and only if G has a clique of size m.  Indeed, suppose that ϕ has a satisfying assignment u.  Deﬁne
a setS ofm vertices as follows: for every clauseC ofϕ put inS the vertex in the cluster associated
with C  that corresponds to the restriction of u to the variables C  depends on.  Because we only
choose vertices that correspond to restrictions of the assignmentu, no two vertices ofS correspond
to inconsistent assignments and hence S is an independent set of size m.
    On  the  other  hand,  suppose  that G  has  an  independent  set S  of  size m.   We  will  use S  to
construct a satisfying assignment u for ϕ.  We deﬁne u as follows:  for every i∈ [n], if there is a
vertex in S whose partial assignment gives a value a to ui, then set ui = a; otherwise set ui = 0.
This is well deﬁned because S  is an independent set, and hence each variable ui can get at most
a single value by assignments corresponding to vertices in S.  On the other hand, because we put
all the edges within each cluster, S can contain at most a single vertex in each cluster, and hence
there is an element of S in every one of the m clusters.  Thus, by our deﬁnition of u, it satisﬁes all
of ϕ’s clauses. ■
    We see that, surprisingly, the answer to the famous NP vs. P question depends on the seemingly
mundane question of whether one can eﬃciently plan an optimal dinner party.  Here are some more
NP-completeness results:

Theorem 2.17 (Integer programming is NP-complete)
We  say  that  a  set  of  linear  inequalities  with  rational  coeﬃcients  over  variables u1,...,un  is  in
IPROG if there is an assignment of integer numbers in{0, 1, 2,...} to u1,...,un  that satisﬁes it.
Then, IPROG is NP-complete.

Proof: IPROG is clearly in NP.  To reduce SAT to IPROG note that every CNF formula can be
easily expressed as an integer program:  ﬁrst add the constraints 0≤ ui≤ 1 for every i to ensure
that  the  only  feasible  assignments  to  the  variables  are  0  or  1,  then  express  every  clause  as  an
inequality.  For example, the clauseu1∨         u2∨   u3 can be expressed asu1 + (1−u2) + (1−u3)≥ 1. ■

Theorem 2.18 (Hamiltonian path is NP-complete)
Let dHAMPATH denote the set of all directed graphs that contain a path visiting all of their vertices
exactly once.  Then dHAMPATH is NP-complete.

Proof: Again, dHAMPATH is clearly in NP.  To show it’s NP-complete we show a way to map
every CNF formula ϕ into a graph G such that ϕ is satisﬁable if and only if G has a Hamiltonian
path (i.e.  path that visits all of G’s vertices exactly once).

                                                                                 Web  draft  2007-01-08  21:59
DRAFT

<!-- pdf-page: 69 -->
2.4.   THE WEB OF REDUCTIONS                                                                                                p2.15 (53)

Figure 2.5:  Reducing SAT to dHAMPATH.  A formula ϕ with n variables and m clauses is mapped to a graph G
that has m vertices corresponding to the clauses and n doubly linked chains, each of length 6m, corresponding to
the variables.  Traversing a chain left to right corresponds to setting the variable to True, while traversing it right
to left corresponds to setting it to False.  Note that in the ﬁgure every Hamiltonian path that takes the edge from
u to c10 must immediately take the edge from c10 to v, as otherwise it would get “stuck” the next time it visits v.

     The reduction is described in Figure           2.5.  The graphG has (1)m vertices for each ofϕ’s clauses
c1,...,cm, (2) a special starting vertex vstart  and ending vertex vend  and (3) n “chains” of 6m
vertices corresponding to then variables ofϕ.  A chain is a set of verticesv1,...,v6m such that for
every i∈ [6m− 1], vi and vi+1 are connected by two edges in both directions.
     We put edges from the starting vertex vstart to the two extreme points of the ﬁrst chain.  We
also put edges from the extreme points of the jth chain to the extreme points to the j + 1th chain
for everyj∈ [n− 1].  We put an edge from the extreme points of thenth chain to the ending vertex
vend.
     In addition to these edges, for every clauseC ofϕ, we put edges between the chains correspond-
ing to the variables appearing in C and the vertex vC  corresponding to C in the following way:  if
C contains the literaluj then we take two neighboring verticesvi,vi+1 in thejth chain and put an
edge from vi to C and from C to vi+1.  If C contains the literal                   uj  then we connect these edges in
the opposite direction (i.e., vi+1  to C  and C  to vi).  When adding these edges, we never “reuse”
a link vi,vi+1 in a particular chain and always keep an unused link between every two used links.
We can do this since every chain has 6m vertices, which is more than suﬃcient for this.
(ϕ∈ SAT⇒ G∈ dHAMPATH.)  Suppose that ϕ has a satisfying assignment u1,...,un.  We will
show a path that visits all the vertices of G.  The path will start at vstart, travel through all the
chains in order, and end at vend.  For starters, consider the path that travels the jth chain in left-
to-right order ifuj = 1 and travels it in right-to-left order ifuj = 0.  This path visits all the vertices
except for those corresponding to clauses.  Yet, ifu is a satisfying assignment then the path can be
easily modiﬁed to visit all the vertices corresponding to clauses:  for each clause C there is at least
one literal that is true, and we can use one link on the chain corresponding to that literal to “skip”
to the vertex vC  and continue on as before.

Web  draft  2007-01-08  21:59
DRAFT

<!-- pdf-page: 70 -->
p2.16 (54)                                                                                 2.4.   THE WEB OF REDUCTIONS
(G∈ dHAMPATH⇒ ϕ∈ SAT.)  Suppose that G has an Hamiltonian path P.  We ﬁrst note that
the pathP  must start invstart (as it has no incoming edges) and end atvend (as it has no outgoing
edges).  Furthermore, we claim that P  needs to traverse all the chains in order, and within each
chain traverse it either in left-to-right order or right-to-left order.  This would be immediate if the
path did not use the edges from a chain to the vertices corresponding to clauses.  The claim holds
because if a Hamiltonian path takes the edge u→w, where u is on a chain and w corresponds to
a clause, then it must at the next step take the edge w→v where v is the vertex adjacent to u in
the link.  Otherwise, the path will get stuck the next time it visits v (see Figure               2.1).  Now, deﬁne
an assignment u1,...,un to ϕ as follows: uj = 1 if P  traverses the jth chain in left-to-right order,
and uj = 0 otherwise.  It is not hard to see that because P  visits all the vertices corresponding to
clauses, u1,...,un is a satisfying assignment for ϕ. ■

In praise of reductions
Though  originally  invented  as  part  of  the  theory  of NP-completeness,  the  polynomial-time  re-
duction (together with its ﬁrst cousin, the randomized polynomial-time reduction deﬁned in Sec-
tion 7.9) has led to a rich understanding of complexity above and beyond NP-completeness.  Much
of complexity theory and cryptography today (thus, many chapters of this book) consists of using
reductions to make connections between disparate complexity theoretic conjectures.  Why do com-
plexity theorists excel at reductions but not at actually proving lower bounds on Turing machines?
A possible explanation is that humans have evolved to excel at problem solving,  and hence are
more adept at algorithms (after all, a reduction is merely an algorithm to transform one problem
into another) than at proving lower bounds on Turing machines.

Coping with NP hardness.
NP-complete problems turn up in great many applications, from ﬂight scheduling to genome se-
quencing.  What do you do if the problem you need to solve turns out to be NP-complete?  On the
outset, the situation looks bleak: if P⁄= NP then there simply does not exist an eﬃcient algorithm
to solve such a problem.  However, there may still be some hope:  NP completeness only means
that (assuming P⁄= NP) the problem does not have an algorithm that solves it exactly  on every
input.  But for many applications, an approximate  solution on some  of the inputs might be good
enough.
    A case in point is the traveling salesperson problem (TSP), of computing, given a list of pairwise
distances between n cities, the shortest route that travels through all of them.  Assume that you
are indeed in charge of coming up with travel plans for traveling salespersons that need to visit
various cities around your country.  Does the fact that TSP is NP-complete means that you are
bound to do a hopelessly suboptimal job?  This does not have to be the case.
    First note that you do not need an algorithm that solves the problem on all  possible lists of
pairwise distances.  We might model the inputs that actually arise in this case as follows:  the n
cities are points on a plane, and the distance between a pair of cities is the distance between the
corresponding points (we are neglecting here the diﬀerence between travel distance and direct/arial
distance).  It is an easy exercise to verify that not all possible lists of pairwise distances can be

                                                                                 Web  draft  2007-01-08  21:59
DRAFT

<!-- pdf-page: 71 -->
2.5.   DECISION VERSUS SEARCH                                                                                                p2.17 (55)
generated in such a way.  We call those that do Euclidean  distances.  Another observation is that
computing the exactly optimal travel plan may not be so crucial.  If you could always come up with
a travel plan that is at most 1% longer than the optimal, this should be good enough.
    It  turns  out  that  neither  of  these  observations  on  its  own  is  suﬃcient  to  make  the  problem
tractable.   The  TSP  problem  is  still NP  complete  even  for  Euclidean  distances.   Also  if P ⁄=
NP then TSP is hard to approximate within any constant factor.  However,  combining  the two
observations together actually helps:  for everyϵ there is a poly(n(logn)O(1/ϵ))-time algorithm that
given Euclidean distances betweenn cities comes up with a tour that is at most a factor of (1 +ϵ)
worse than the optimal tour [Aro98].
    We see that discovering the problem you encounter is NP-complete should not be cause for
immediate  despair.   Rather  you  should  view  this  as  indication  that  a  more  careful  modeling  of
the problem is needed, letting the literature on complexity and algorithms guide you as to what
features might make the problem more tractable.  Alternatives to worst-case exact computation
are explored in Chapters        15  and  18, that investigate average-case  complexity  and approximation
algorithms respectively.

2.5   Decision versus search

We  have  chosen to  deﬁne  the  notion of NP  using  Yes/No  problems  (“Is  the  given formula  sat-
isﬁable?”)   as  opposed  to  search  problems  (“Find  a  satisfying  assignment  to  this  formula  if  one
exists”).  Clearly, the search problem is harder than the corresponding decision problem, and so
if P⁄= NP then neither one can be solved for an NP-complete problem.  However, it turns out
that for NP-complete problems they are equivalent in the sense that if the decision problem can
be solved (and hence P = NP) then the search version of any NP problem can also be solved in
polynomial time.
Theorem 2.19
Suppose that P = NP.  Then, for every NP languageL there exists a polynomial-time TMB that
on input x∈ /suppressL outputs a certiﬁcate forx.
    That is, if, as per Deﬁnition       2.1, x∈ L iﬀ∃u∈{0, 1}p(|x|)  s.t. M(x,u) = 1 where p is some
polynomial  and M  is  a  polynomial-time  TM,  then  on  input x∈ L, B(x)  will  be  a  string u∈
{0, 1}p(|x|) satisfying M(x,B(x)) = 1.

Proof: We start by showing the theorem for the case of SAT.  In particular we show that given
an algorithmA that decides SAT, we can come up with an algorithmB that on input a satisﬁable
CNF formula ϕ with n variables, ﬁnds a satisfying assignment for ϕ using 2n + 1 calls to A and
some additional polynomial-time computation.
    The algorithmB works as follows: we ﬁrst useA to check that the input formulaϕ is satisﬁable.
If so, we substitute x1 = 0 and x1 = 1 in ϕ (this transformation, that simpliﬁes and shortens the
formula a little, leaving a formula with n− 1 variables, can certainly be done in polynomial time)
and then useA to decide which of the two is satisﬁable (it is possible that both are).  Say the ﬁrst is
satisﬁable.  Then we ﬁx x1 = 0 from now on and continue with the simpliﬁed formula.  Continuing
this way we end up ﬁxing alln variables while ensuring that each intermediate formula is satisﬁable.
Thus the ﬁnal assignment to the variables satisﬁes ϕ.

Web  draft  2007-01-08  21:59
DRAFT

<!-- pdf-page: 72 -->
p2.18 (56)                                                                                     2.6.  CONP, EXP AND NEXP
     To solve the search problem for an arbitrary NP-languageL, we use the fact that the reduction
of Theorem    2.10  fromL to SAT is actually a Levin reduction. This means that we have a polynomial-
time computable function f  such that not only x∈ L⇔ f(x)∈ SAT but actually we can map a
satisfying assignment off(x) into a certiﬁcate forx.  Therefore, we can use the algorithm above to
come up with an assignment for f(x) and then map it back into a certiﬁcate for x. ■

Remark 2.20
The proof above shows that SAT is downward self-reducible, which means that given an algorithm
that solves SAT on inputs of length smaller than n we can solve SAT on inputs of length n.  Using
the Cook-Levin reduction, one can show that all NP-complete problems have a similar property,
though we do not make this formal.

2.6   coNP, EXP and NEXP

Now we deﬁne some related complexity classes that are very relevant to the study of the P versus
NP question.

2.6.1   coNP
If L⊆{0, 1}∗ is a language, then we denote by             L the complement  of L.  That is,       L ={0, 1}∗\L.
We make the following deﬁnition:
Definition 2.21
coNP ={L :       L∈ P}.

     It is important to note that coNP is not  the complement of the class NP.  In fact, they have
a  non-empty  intersection,  since  every  language  in P  is  in NP∩ coNP  (see  Exercise                19).   The
following is an example of a coNP language:           SAT ={ϕ :ϕ is not satisﬁable}. Students sometimes
mistakenly  convince  themselves  that        SAT  is  in NP.   They  have  the  following  polynomial  time
NDTM  in  mind:  on  input ϕ,  the  machine  guesses  an  assignment.   If  this  assignment  does  not
satisfy ϕ then it accepts (i.e., goes into qaccept and halts) and if it does satisfy ϕ then the machine
halts without accepting.  This NDTM does not do the job:  indeed it accepts every unsatisﬁable
ϕ but in addition it also accepts many satisﬁable formulae (i.e., every formula that has a single
unsatisfying assignment).  That is why pedagogically we prefer the following deﬁnition of coNP
(which is easily shown to be equivalent to the ﬁrst, see Exercise            20):
Definition 2.22 (coNP, alternative definition)
For  every L⊆{0, 1}∗,  we  say  that L∈ coNP  if  there  exists  a  polynomial p  : N→ N  and  a
polynomial-time TM M  such that for every x∈{0, 1}∗,

                                  x∈L⇔∀u∈{0, 1}p(|x|)  s.t. M(x,u) = 1

     The key fact to note is the use of “∀” in this deﬁnition where Deﬁnition              2.1  used∃.
     We  can  deﬁne  coNP-completeness  in  analogy  to  NP-completeness:   a  language  is  coNP-
complete if it is in coNP and every coNP language is polynomial-time Karp reducible to it.

                                                                                Web  draft  2007-01-08  21:59
DRAFT

<!-- pdf-page: 73 -->
2.6.  CONP, EXP AND NEXP                                                                                                     p2.19 (57)
Example 2.23
In classical logic, tautologies are true statements.  The following language is coNP-complete:

        TAUTOLOGY ={ϕ : ϕ is a Boolean formula that is satisﬁed by every assignment}.

    It is clearly in coNP by Deﬁnition        2.22 and so all we have to show is that for everyL∈ coNP,
L≤p  TAUTOLOGY.  But this is easy:  just modify the Cook-Levin reduction from                      L (which is in
NP) to SAT.  For every input x∈{0, 1}∗ that reduction produces a formula ϕx that is satisﬁable
iﬀ x∈   L.  Now consider the formula¬ϕx.  It is in TAUTOLOGY iﬀ x∈L, and this completes the
description of the reduction.

    It is a simple exercise to check that if P = NP then NP = coNP = P.  Put in the contraposi-
tive, if we can show that NP⁄= coNP then we have shown P⁄= NP.  Most researchers believe that
NP⁄= coNP.  The intuition is almost as strong as for the P versus NP question:  it seems hard to
believe that there is any short certiﬁcate for certifying that a given formula is a TAUTOLOGY, in
other words, to certify that every assignment satisﬁes the formula.

2.6.2   EXP and NEXP
The following two classes are exponential time analogues of P and NP.
Definition 2.24
EXP =∪c≥0DTIME(2nc).
NEXP =∪c≥0NTIME(2nc).

    Because every problem in NP can be solved in exponential time by a brute force search for
the  certiﬁcate,  P⊆ NP⊆ EXP⊆ NEXP.   Is  there  any  point  to  studying  classes  involving
exponential running times?  The following simple result —providing merely a glimpse of the rich
web of relations we will be establishing between disparate complexity questions— may be a partial
answer.
Theorem 2.25
If EXP⁄= NEXP then P⁄= NP.

Proof:  We  prove  the  contrapositive:  assuming P  = NP  we  show EXP  = NEXP.   Suppose
L∈ NTIME(2nc) and NDTM M  decides it.  We claim that then the language
                                                  {                      }
                                         Lpad =     ⟨x, 12|x|c⟩ : x∈L                                           (1)

is in NP. Here is an NDTM forLpad: giveny, ﬁrst check if there is a stringz such thaty =⟨z, 12|z|c⟩.
If not, output REJECT. Ify is of this form, then runM onz for 2|z|c steps and output its answer.
Clearly, the running time is polynomial in|y|, and henceLpad∈ NP.  Hence if P = NP thenLpad
is in P.  But if Lpad is in P then L is in EXP:  to determine whether an input x is in L, we just
pad the input and decide whether it is in Lpad using the polynomial-time machine for Lpad. ■

Web  draft  2007-01-08  21:59
DRAFT

<!-- pdf-page: 74 -->
p2.20 (58)                                         2.7.   MORE THOUGHTS ABOUT P, NP, AND ALL THAT
Remark 2.26
The padding technique used in this proof, whereby we transform a language by “padding” every
string  in  a  language  with  a  string  of  (useless)  symbols,  is  also  used  in  several  other  results  in
complexity theory.  In many settings it can be used to show that equalities between complexity
classes “scale up”; that is, if two diﬀerent type of resources solve the same problems within bound
T(n)  then  this  also  holds  for  functions T ′  larger  than T.   Viewed  contrapositively,  padding  can
be used to show that inequalities between complexity classes involving resurce bound T ′(n) “scale
down” to resource bound T(n).

     Like P and NP, most of the complexity classes studied later are also contained in both EXP
and NEXP.

2.7   More thoughts about P, NP, and all that

2.7.1   The philosophical importance of NP
At  a  totally  abstract  level,  the P  versus NP  question  may  be  viewed  as  a  question  about  the
power of nondeterminism in the Turing machine model.  (Similar questions have been completely
answered for simpler models such as ﬁnite automata.)
     However, the certiﬁcate deﬁnition of NP also suggests that the P versus NP question captures
a widespread phenomenon of some philosophical importance (and a source of great frustration to
students): recognizing the correctness of an answer is often easier than coming up with the answer.
To give other analogies from life:  appreciating a Beethoven sonata is far easier than composing
the sonata; verifying the solidity of a design for a suspension bridge is easier (to a civil engineer
anyway!) than coming up with a good design; verifying the proof of a theorem is easier than coming
up with a proof itself (a fact referred to in G¨odel’s letter mentioned at the start of the chapter),
and so forth.  In such cases, coming up with the right answer seems to involve exhaustive search
over an exponentially large set.  The P versus NP question asks whether exhaustive search can be
avoided in general.  It seems obvious to most people —and the basis of many false proofs proposed
by amateurs— that exhaustive search cannot be avoided:  checking that a given salesperson tour
(provided by somebody else) has length at most k ought to be a lot easier than coming up with
such a tour by oneself.  Unfortunately, turning this intuition into a proof has proved diﬃcult.

2.7.2   NP and mathematical proofs
By deﬁnition, NP is the set of languages where membership has a short certiﬁcate.  This is remi-
niscent of another familiar notion, that of a mathematical proof.  As noticed in the past century, in
principle all of mathematics can be axiomatized, so that proofs are merely formal manipulations of
axioms.  Thus the correctness of a proof is rather easy to verify —just check that each line follows
from the previous lines by applying the axioms.  In fact, for most known axiomatic systems (e.g.,
Peano arithmetic or Zermelo-Fraenkel Set Theory) this veriﬁcation runs in time polynomial in the
length of the proof.  Thus the following problem is in NP for any of the usual axiomatic systems
A:
               theorems ={(ϕ, 1n) : ϕ has a formal proof of length≤n in systemA}.

                                                                                 Web  draft  2007-01-08  21:59
DRAFT

<!-- pdf-page: 75 -->
2.7.   MORE THOUGHTS ABOUT P, NP, AND ALL THAT                                                 p2.21 (59)
    In fact, the exercises ask you to prove that this problem is NP-complete.  Hence the P versus
NP question is a rephrasing of G¨odel’s question (see quote at the beginning of the chapter), which
asks whether or not there is a algorithm that ﬁnds mathematical proofs in time polynomial in the
length of the proof.
    Of  course,  all  our  students  know  in  their  guts  that  ﬁnding  correct  proofs  is  far  harder  than
verifying their correctness.  So presumably, they believe at an intuitive level that P⁄= NP.

2.7.3   What if P = NP?

If P  = NP  —speciﬁcally,  if  an NP-complete  problem  like  3SAT  had  a  very  eﬃcient  algorithm
running  in  say O(n2)  time—  then  the  world  would  be  mostly  a  Utopia.   Mathematicians  could
be  replaced  by  eﬃcient  theorem-discovering  programs  (a  fact  pointed  out  in  Kurt  G¨odel’s  1956
letter and discovered three decades later).  In general for every search problem whose answer can be
eﬃciently veriﬁed (or has a short certiﬁcate of correctness), we will be able to ﬁnd the correct answer
or the short certiﬁcate in polynomial time.  AI software would be perfect since we could easily do
exhaustive searches in a large tree of possibilities.  Inventors and engineers would be greatly aided
by software packages that can design the perfect part or gizmo for the job at hand.  VLSI designers
will be able to whip up optimum circuits, with minimum power requirements.  Whenever a scientist
has some experimental data, she would be able to automatically obtain the simplest theory (under
any reasonable measure of simplicity we choose) that best explains these measurements;  by the
principle of Occam’s Razor the simplest explanation is likely to be the right one.  Of course,  in
some cases it took scientists centuries to come up with the simplest theories explaining the known
data.  This approach can be used to solve also non-scientiﬁc problems:  one could ﬁnd the simplest
theory that explains, say, the list of books from the New York Times’ bestseller list.  (NB: All these
applications will be a consequence of our study of the Polynomial Hierarchy in Chapter                      5.)
    Somewhat intriguingly, this Utopia would have no need for randomness.  As we will later see, if
P = NP then randomized algorithms would buy essentially no eﬃciency gains over deterministic
algorithms; see Chapter       7.  (Philosophers should ponder this one.)
    This Utopia would also come at one price:  there would be no privacy in the digital domain.
Any encryption scheme would have a trivial decoding algorithm.  There would be no digital cash,
no SSL, RSA or PGP (see Chapter             10).  We would just have to learn to get along better without
these, folks.
    This utopian world may seem ridiculous, but the fact that we can’t rule it out shows how little
we know about computation.  Taking the half-full cup point of view, it shows how many wonderful
things are still waiting to be discovered.

2.7.4   What if NP = coNP?

If NP = coNP, the consequences still seem dramatic.  Mostly, they have to do with existence of
short certiﬁcates for statements that do not seem to have any.  To give an example, remember the
NP-complete problem of ﬁnding whether or not a set of multivariate polynomials has a common

Web  draft  2007-01-08  21:59
DRAFT

<!-- pdf-page: 76 -->
p2.22 (60)                                         2.7.   MORE THOUGHTS ABOUT P, NP, AND ALL THAT
root, in other words, deciding whether a system of equations of the following type has a solution:
                                                 f1(x1,...,xn) = 0
                                                 f2(x1,...,xn) = 0
                                                                ...

                                                fm(x1,...,xn) = 0
where each fi is a quadratic polynomial.
     If a solution exists, then that solution serves as a certiﬁcate to this eﬀect (of course, we have to
also show that the solution can be described using a polynomial number of bits, which we omit).
The problem of deciding that the system does not  have a solution is of course in coNP.  Can we
give a certiﬁcate to the eﬀect that the system does not have a solution?  Hilbert’s Nullstellensatz
Theorem seems to do that: it says that the system is infeasible iﬀ there is a sequence of polynomials
g1,g2,...,gm such that∑ifigi = 1, where 1 on the right hand side denotes the constant polynomial
1.
     What is happening?  Does the Nullstellensatz prove coNP = NP?  No, because the degrees of
the gi’s —and hence the number of bits used to represent them— could be exponential in n,m.
(And it is simple to construct fi’s for which this is necessary.)
     However, if NP = coNP then there would be some other notion of a short certiﬁcate to the
eﬀect that the system is infeasible.  The eﬀect of such a result on mathematics would probably be
even greater than the eﬀect of Hilbert’s Nullstellensatz.  Of course, one can replace Nullstellensatz
with any other coNP problem in the above discussion.

  What have we learned?

      •  The class NP consists of all the languages for which membership can be cer-
         tiﬁed to a polynomial-time algorithm.  It contains many important problems
         not known to be in P. NP can also be deﬁned using non-deterministic Turing
         machines.

      •  NP-complete  problems  are  the  hardest  problems  in NP,  in  the  sense  that
         they have a polynomial-time algorithm if and only if P =NP.  Many natural
         problems that seemingly have nothing to do with Turing machines turn out
         to  be NP-complete.   One  such  example  is  the  language  3SAT  of  satisﬁable
         Boolean formulae in 3CNF  form.

      •  If P = NP then for every search problem for which one can eﬃciently verify
         a given solution, one can also eﬃciently ﬁnd such a solution from scratch.

Chapter notes and history

In the 1950’s, Soviet scientists were aware of the undesirability of using exhaustive or brute force
search, which they called perebor, for combinatorial problems, and asked the question of whether

                                                                                Web  draft  2007-01-08  21:59
DRAFT

<!-- pdf-page: 77 -->
2.7.   MORE THOUGHTS ABOUT P, NP, AND ALL THAT                                                 p2.23 (61)
certain  problems  inherently  require  such  search  (see  [Tra84]).   In  the  west  the  ﬁrst  published
description  of  this  issue  is  by  Edmonds  [Edm65],  in  the  paper  quoted  in  the  previous  chapter.
However, on both sides of the iron curtain it took some time to realize the right way to formulate
the problem and to arrive at the modern deﬁnition of the classes NP and P. Amazingly, in his 1956
letter to von Neumann we quoted above, G¨odel essentially asks the question of P vs. NP, although
there is no hint that he realized that one of the particular problems he mentions is NP-complete.
Unfortunately, von Neumann was very sick at the time, and as far as we know, no further research
was done by either on them on this problem, and the letter was only discovered in the 1980’s.
     In 1971 Cook published his seminal paper deﬁning the notion of NP-completeness and showing
that  SAT  is NP  complete  [Coo71].   Soon  afterwards,  Karp  [Kar72]  showed  that  21  important
problems are in fact NP-complete, generating tremendous interest in this notion.  Meanwhile in
the USSR Levin independently deﬁned NP-completeness (although he focused on search problems)
and showed that a variant of SAT is NP-complete.  (Levin’s paper [Lev73] was published in 1973,
but he had been giving talks on his results since 1971, also in those days there was essentially zero
communication between eastern and western scientists.)  See Sipser’s survey [Sip92] for more on
the history of P and NP and a full translation of G¨odel’s remarkable letter.
     The “TSP book” by Lawler et al. [LLKS85] also has a similar chapter, and it traces interest
in the Traveling Salesman Problem back to the 19th century.  Furthermore, a recently discovered
letter by Gauss to Schumacher shows that Gauss was thinking about methods to solve the famous
Euclidean Steiner Tree problem —today known to be NP-hard— in the early 19th century.
     As mentioned above, the book by Garey and Johnson [GJ79] and the web site [CK00] contain
many more examples of NP complete problem.  Also, Aaronson [Aar05] surveys various attempts
to solve NP complete problems via “non-traditional” computing devices.
     Even if NP⁄= P, this does not necessarily mean that all of the utopian applications mentioned
in Section   2.7.3 are gone. It may be that, say, 3SAT is hard to solve in the worst case on every input
but actually very easy on the average, See Chapter              15  for a more detailed study of average-case
complexity.  Also, Impagliazzo [Imp95] has an excellent survey on this topic.

Exercises

   §1  Prove the existence of a non-deterministic Universal TM  (analogously to the deterministic
       universal TM of Theorem         1.13).  That is, prove that there exists a representation scheme of
       NDTMs, and an NDTMNU  such that for every string α, and input x,NU(x,α) =Mα(x).

        (a)  Prove that there exists such a universal NDTMNU  such that if Mα halts on x within
             T  steps, thenNU halts onx,α withinCT logT  steps (whereC is a constant depending
             only on the machine represented by α).

        (b)  Prove that there is such a universal NDTM that runs on these inputs for at most Ct
             steps.

Web  draft  2007-01-08  21:59
DRAFT

<!-- pdf-page: 78 -->
p2.24 (62)                                         2.7.   MORE THOUGHTS ABOUT P, NP, AND ALL THAT

  §2  Prove Theorem     2.

  §3  Let HALT be the Halting language deﬁned in Theorem              1.17.  Show that HALT is NP-hard.
      Is it NP-complete?

  §4  We have deﬁned a relation≤p among languages. We noted that it is reﬂexive (that is,A≤pA
      for all languages A) and transitive (that is, ifA≤pB andB≤pC thenA≤pC).  Show that
      it is not commutative, namely, A≤pB need not imply B≤pA.

  §5  Suppose L1,L2∈ NP.  Then is L1∪L2 in NP?  What about L1∩L2?

  §6  Mathematics can be axiomatized using for example the Zermelo Frankel system, which has a
      ﬁnite description.  Argue at a high level that the following language is NP-complete.

              {⟨ϕ, 1n⟩ :  math statement ϕ has a proof of size at most n in the ZF system}.

      The question of whether this language is in P is essentially the question asked by G¨odel in
      the chapter’s initial quote.

  §7  Show that NP = coNP iﬀ  3SAT and TAUTOLOGY  are polynomial-time reducible to one
      another.

  §8  Can you give a deﬁnition of NEXP without using NDTMs, analogous to the deﬁnition of
      NP in Deﬁnition      2.1?  Why or why not?

  §9  We say that a language is NEXP-complete if it is in NEXP and every language in NEXP
      is polynomial-time reducible to it.  Describe a NEXP-complete language.  Prove that if this
      problem is in EXP then NEXP = EXP.

 §10  Show that for every time constructibleT :N→N, ifL∈ NTIME(T(n)) then we can give a
      polynomial-time Karp reduction fromL to 3SAT that transforms instances of sizen into 3CNF
      formulae of sizeO(T(n) logT(n)). Can you make this reduction also run inO(T(n) logT(n))?

 §11  Recall that a reductionf  from an NP-languageL to an NP-languagesL′ is parsimonious if
      the number of certiﬁcates of f  is equal to the number of certiﬁcates of f(x).

       (a)  Prove that the reduction from every NP-language L to SAT presented in the proof of
            Lemma    2.12  is parsimonious.

                                                                            Web  draft  2007-01-08  21:59
DRAFT

<!-- pdf-page: 79 -->
2.7.   MORE THOUGHTS ABOUT P, NP, AND ALL THAT                                                 p2.25 (63)
        (b)  Show a parsimonious reduction from SAT to 3SAT.

  §12  The notion of polynomial-time reducibility used in Cook’s paper was somewhat diﬀerent:  a
       language A is polynomial-time Cook reducible  to a language B if there is a polynomial time
       TMM that, given an oracle for decidingB, can decideA.  (An oracle forB is a magical extra
       tape given to M, such that whenever M  writes a string on this tape and goes into a special
       “invocation” state, then the string —in a single step!—gets overwritten by 1 or 0 depending
       upon whether the string is or is not in B, see Section ??)
       Show that the notion of cook reducibility is transitive and that 3SAT is Cook-reducible to
       TAUTOLOGY.

  §13  (Berman’s Theorem 1978) A language is called unary if every string in it is of the form 1i
       (the string of i ones) for some i > 0.  Show that if a unary language is NP-complete then
       P = NP.  (See Exercise       6 of Chapter    6 for a strengthening of this result.)

  §14  In the CLIQUE problem we are given an undirected graph G and an integer K  and have to
       decide whether there is a subsetS of at leastK vertices such that every two distinct vertices
       u,v∈S have an edge between them (such a subset is called a clique). In the VERTEX COVER
       problem we are given an undirected graph G and an integer K  and have to decide whether
       there is a subset S of at most K vertices such that for every edge{i,j} of G, at least one of
       i or j is in S.  Prove that both these problems are NP-complete.

  §15  In the MAX CUT  problem we are given an undirected graphG and an integerK and have to
       decide whether there is a subset of vertices S such that there are at least K edges that have
       one endpoint in S and one endpoint in          S.  Prove that this problem is NP-complete.

  §16  In  the  Exactly  One  3SAT  problem,  we  are  given  a  3CNF  formula ϕ  and  need  to  decide  if
       there exists a satisfying assignmentu forϕ such that every clause ofϕ has exactly one True
       literal.  In the SUBSET SUM   problem we are given a list of n numbers A1,...,An  and a
       number T  and need to decide whether there exists a subset S⊆ [n] such that∑i∈SAi =T
       (the problem size is the sum of all the bit representations of all numbers).  Prove that both
       Exactly One3SAT and SUBSET SUM are NP-complete.

Web  draft  2007-01-08  21:59
DRAFT

<!-- pdf-page: 80 -->
p2.26 (64)                                         2.7.   MORE THOUGHTS ABOUT P, NP, AND ALL THAT

 §17  Prove  that  the  language  HAMPATH  of  undirected  graphs  with  Hamiltonian  paths  is NP-
      complete.  Prove that the language TSP described in Example               2.2 is NP-complete.  Prove
      that the language HAMCYCLE of undirected graphs that contain Hamiltonian cycle (a simple
      cycle involving all the vertices) is NP-complete.

 §18  Let quadeq be the language of all satisﬁable sets of  quadratic  equations  over 0/1 variables
      (a quadratic equations over u1,...,un has the form form∑ai,juiuj  = b), where addition is
      modulo 2.  Show that quadeq is NP-complete.

 §19  Prove that P⊆ NP∩ coNP.

 §20  Prove that the Deﬁnitions      2.21 and  2.22  do indeed deﬁne the same class coNP.

 §21  SupposeL1,L2∈ NP∩ coNP.  Then show thatL1⊕L2 is in NP∩ coNP, whereL1⊕L2 =
      {x : x is in exactly one of L1,L2}.

 §22  Deﬁne the language UNARY SUBSET SUM  to be the variant of the SUBSET SUM  problem of
      Exercise  16  where all numbers are represented by the unary representation (i.e., the number
      k is represented as 1k).  Show that UNARY SUBSET SUM is in P.

 §23  Prove that if every unary NP-language is in P then EXP = NEXP. (A languageL is unary
      if it is a subset of{1}∗, see Exercise    13.)

                                                                            Web  draft  2007-01-08  21:59
DRAFT
