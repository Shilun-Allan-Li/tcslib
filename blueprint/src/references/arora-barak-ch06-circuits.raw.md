<!-- generated-by: scoped pypdf extraction (maintainer ingest for EF-H12, 2026-11-19; ruling EF-H12-R4 A / Q-H12-2 A) -->
<!-- source-pdf-sha256: da0881782a35bde6a0779a2eb1a8d480f39fbddf70bbb92824d1dc5550a033b2 -->
<!-- source: S. Arora, B. Barak, "Computational Complexity: A Modern Approach", authors' public web draft (Princeton), https://theory.cs.princeton.edu/complexity/book.pdf, 489 pages, page footers "Web draft 2007-01-08 21:59"; NOT the Cambridge University Press 2009 edition: its chapter, section, theorem and page numbers are the draft's and may differ from CUP 2009 -->
<!-- extractor: pypdf 6.17.0 under python3 -I, extract_text(extraction_mode="layout"); per page the common left indentation is removed, trailing spaces are stripped, runs of blank lines are collapsed and C0 control characters (figure debris) are replaced by U+FFFD; nothing else is edited (the "DRAFT" watermark, running heads, footers and figure debris are kept as extracted) -->
<!-- scope: PDF pages 117-130, the whole of Chapter 6 'Circuits' (chapter title to the end of Exercise 15; Chapter 7 begins on PDF page 131) -->
<!-- note: physical PDF page p is printed draft page p - 16; the draft prints a chapter label as well, "p6.k (N)" with k = p - 116 and N = p - 16 -->
<!-- validation-status: awaiting Codex source review -->

<!-- pdf-page: 117 -->
               Chapter 6

               Circuits

                        “One might imagine that P⁄= NP, but SAT is tractable in the following sense:  for
                        every 𝓁  there  is  a  very  short  program  that  runs  in  time 𝓁2  and  correctly  treats  all
                        instances of size 𝓁.  ”
                        Karp and Lipton, 1982

                   This chapter investigates a model of computation called a Boolean circuit, which is a general-
               ization of Boolean formulae and a rough formalization of the familiar ”silicon chip.” Here are some
               motivations for studying it.
                   First,  it is a natural model for  nonuniform computation,  by which we mean that a diﬀerent
               ”algorithm” is allowed for each input size.  By contrast, our standard model thus far was uniform
               computation: the same Turing Machine (or algorithm) solves the problem for inputs of all (inﬁnitely
               many) sizes.  Nonuniform computation crops up often in complexity theory, and also in the rest of
               this book.
                   Second, in principle one can separate complexity classes such as P and NP by proving lower-
               bounds on circuit size.  This chapter outlines why such lowerbounds ought to exist.  In the 1980s,
               researchers  felt  boolean  circuits  are  mathematically  simpler  than  the  Turing  Machine,  and  thus
               proving circuit lowerbounds may be the right approach to separating complexity classes.  Chap-
               ter 13  describes the partial successes of this eﬀort and Chapter            22  describes where it is stuck.
                   This  chapter  deﬁnes  the  class P/poly  of  languages  computable  by  polynomial-sized  boolean
               circuits and explores its relation to NP.  We also encounter some interesting subclasses of P/poly,
               including NC,  which  tries  to  capture  computations  that  can  be  eﬃciently  performed  on  highly
               parallel  computers.  Finally, we show a (yet another) characterization of the polynomial hierarchy,
               this time using exponential-sized circuits of constant depth.

               6.1   Boolean circuits

               A Boolean circuit is a just a diagram showing how to derive an output from an input by a combi-
               nation of the basic Boolean operations of OR (∨), AND (∧) and NOT (¬).  For example, Figure                         6.1
               shows a circuit computing the XOR function.  Here is the formal deﬁnition.

               Web  draft  2007-01-08  21:59                         p6.1 (101)
               Complexity Theory:  A Modern Approach. © 2006 Sanjeev Arora and Boaz Barak.  References and attributions are
DRAFTstill incomplete.

<!-- pdf-page: 118 -->
p6.2 (102)                                                                                             6.1.   BOOLEAN CIRCUITS

               Figure 6.1:  A circuit C computing the XOR function (i.e., C(x1,x2) = 1 iﬀ x1 ⁄=x2).

 Definition 6.1 (Boolean circuits)
 For every n,m∈N a Boolean circuit C  with n inputs and m outputs1is a directed
 acyclic graph.  It contains n nodes with no incoming edges; called the input nodes
 and m  nodes  with  no  outgoing  edges,  called  the  output  nodes.   All  other  nodes
 are called gates and are labeled with one of∨,∧ or¬ (in other words, the logical
 operations OR, AND, and NOT). The∨ and∧ nodes have fanin (i.e., number of
 incoming edges) of 2 and the¬ nodes have fanin 1.  The size of C, denoted by|C|,
 is the number of nodes in it.
 The circuit is called a Boolean formula if each node has at most one outgoing edge.

    The boolean circuit in the above deﬁnition implements a function from{0, 1}n to{0, 1}m.  This
may be clear intuitively to most readers (especially those who have seen circuits in any setting)
but here is the proof.  Assume that the n input nodes and m output nodes are numbered in some
canonical way.  Thus eachn-bit input can be used to assigned a value in{0, 1} to each input node.
Next, since the graph is acyclic, we can associate an integral depth to each node (using breadth-ﬁrst
search, or the so-called topological sorting  of the graph) such that each node has incoming edges
only from nodes of higher depth.  Now each node can be assigned a value from{0, 1} in a unique
way as follows. Process the nodes in decreasing order of depth. For each node, examine its incoming
edges and the values assigned to the nodes at the other end, and then apply the boolean operation
(∨,∧, or¬) that this node is labeled with on those values.  This gives a value to each node; the
values assigned to the m output nodes by this process constitute an m-bit output of the circuit.
    For every string u∈{0, 1}n, we denote by C(u) the output of the circuit C on input u.
    We recall that the Boolean operations OR, AND, and NOT form a universal basis, by which
we mean that every function from{0, 1}n to{0, 1}m can be implemented by a boolean circuit (in
fact, a boolean formula).  See Claim          2.14.  Furthermore, the “silicon chip” that we all know about
is nothing but2     an implementation of a boolean circuit using a technology called VLSI. Thus if we
have a small circuit for a computational task, we can implement it very eﬃciently as a silicon chip.
Of course, the circuit can only solve problems on inputs of a certain size.  Nevertheless, this may
not be a big restriction in our ﬁnite world.  For instance, what if a small circuit exists that solves

   2Actually, the circuits in silicon chips are not acyclic; in fact the cycles in the circuit are crucial for implementing
”memory.” However any computation that runs on a silicon chip of size C and ﬁnishes in time T  can be performed
by a boolean circuit of size O(C ·T).

                                                                                   Web  draft  2007-01-08  21:59
DRAFT

<!-- pdf-page: 119 -->
6.1.   BOOLEAN CIRCUITS                                                                                                               p6.3 (103)
3SAT instances of up to say 100, 000 variables?  If so,  one could imagine a government-ﬁnanced
project akin to the Manhattan project that would try to discover such a small circuit, and then
implement it as a silicon chip.  This could be used in all kinds of commercial products (recall our
earlier depiction of a world in which P = NP) and in particular would jeopardize every encryption
scheme that does not use a huge key.  This scenario is hinted at in the quote from Karp and Lipton
at the start of the chapter.
    As usual, we resort to asymptotic analysis to study the complexity of deciding a language by
circuits.
Definition 6.2 (Circuit families and language recognition)
LetT :N→N be a function. AT(n)-sized circuit family is a sequence{Cn}n∈N of Boolean circuits,
where Cn has n inputs and a single output, such that|Cn|≤T(n) for every n.
    We say that a language L is in SIZE(T(n)) if there exists a T(n)-size circuit family{Cn}n∈N
such that for every x∈{0, 1}n, x∈L⇔C(x) = 1.

    As noted in Claim       2.14, every language is decidable by a circuit family of size O(n2n), since
the circuit for input lengthn could contain 2n “hardwired” bits indicating which inputs are in the
language.  Given an input, the circuit looks up the answer from this table.  (The reader may wish
to work out an implementation of this circuit.)  The following deﬁnition formalizes what we can
think of as “small” circuits.
Definition 6.3
P/poly is the class of languages that are decidable by polynomial-sized circuit families, in other
words,∪cSIZE(nc).

    Of course, one can make the same kind of objections to the practicality of P/poly as for P:
viz., in what sense is a circuit family of sizen100 practical, even though it has polynomial size.  This
was answered to some extent in Section            1.5.1.  Another answer is that as complexity theorists we
hope (eventually) to show that languages such as SAT are not in P/poly.  Thus the result will only
be stronger if we allow even such large circuits in the deﬁnition of P/poly.
    The class P/poly contains P.  This is a corollary of Theorem                6.7  that we show below.  Can we
give a reasonable upperbound on the computational power of P/poly?  Unfortunately not, since it
contains even undecidable languages.

Example 6.4
Recall that we say that a languageL is unary if it is a subset of{1n :n∈N}. Every unary language
has linear size circuits since the circuit for an input sizen only needs to have a single “hardwired”
bit indicating whether or not 1n is in the language.  Hence the following unary language has linear
size circuits, even though it is undecidable:

                                       {1n :Mn outputs 1 on input 1n} .                                             (1)

where Mn is the machine represented by (the binary expansion of) the number n.

Web  draft  2007-01-08  21:59
DRAFT

<!-- pdf-page: 120 -->
p6.4 (104)                                                                                             6.1.   BOOLEAN CIRCUITS

    This example suggests that it may be fruitful to consider the restriction to circuits that can
actually be built, say using a fairly eﬃcient Turing machine.  It will be most useful to formalize
this using logspace computations.
    Recall that a function f  :{0, 1}∗→{0, 1}∗  is implicitly logspace computable if the mapping
x,i↦→f(x)i can be computed in logarithmic space (see Deﬁnition                   4.14).
Definition 6.5 (logspace-uniform circuit families)
A circuit family{Cn} is  logspace  uniform if there is an implicitly logspace computable function
mapping 1n to the description of the circuit Cn.

    Actually, to make this concrete we need to ﬁx some representation of the circuits as strings.  We
will assume that the circuit of sizeN is represented by itsN×N adjacency matrix and in addition
an array of size N  that gives the labels (gate type and input/output) of each node.  This means
that{Cn} is  logspace  uniform  if and only if the  following  functions  are  computable  in O(logn)
space:

    •  SIZE(n) returns the size m (in binary representation) of the circuit Cn.

    •  TYPE(n,i), wherei∈ [m], returns the label and type of theith node ofCn.  That is it returns
       one of{∨,∧,¬,NONE} and in addition⟨OUTPUT,j⟩ or⟨INPUT,j⟩ if i is the jth input
       or output node of Cn.

    •  EDGE(n,i,j) returns 1 if there is a directed edge inCn between theith node and thejth node.

    Note that both the inputs and the outputs of these functions can be encoded using a logarithmic
(in|Cn|) number of bits.  The requirement that they run in O(logn) space means that we require
that log|Cn| =O(logn) or in other words that Cn is of size at most polynomial in n.
Remark 6.6
Exercise  7 asks you to prove that the class of languages decided by such circuits does not change if we
use the adjacency list (as opposed to matrix) representation.  We will use the matrix representation
from now on.

    Polynomial circuits that are logspace-uniform correspond to a familiar complexity class:
Theorem 6.7
A language has logspace-uniform circuits of polynomial size iﬀ it is in P.

Remark 6.8
Note that this implies that P⊆ P/poly.

Proof  sketch:    The  only  if  part  is  trivial.   The  if  part  follows  the  proof  of  the  Cook-Levin
Theorem (Theorem        2.10).  Recall that we can simulate every timeO(T(n)) TMM  by an oblivious
TM   ˜M  (whose  head  movement  is  independent  of  its  input)  running  in  time O(T(n)2)  (or  even
O(T(n) logT(n)) if we are more careful).  In fact, we can ensure that the movement of the oblivious
TM  ˜M do not even depend on the contents of its work tape, and so, by simulating  ˜Mwhile ignoring

                                                                                 Web  draft  2007-01-08  21:59
DRAFT

<!-- pdf-page: 121 -->
6.1.   BOOLEAN CIRCUITS                                                                                                               p6.5 (105)
its read/write instructions, we can compute in O(logT(n)) space for every i the position its heads
will be at the ith step.3
    Given this insight, it is fairly straightforward to translate the proof of Theorem                    2.10  to prove
that every language in P has a logspace-uniform circuit family.  The idea is that ifL∈ P then it is
decided by an oblivious TM  ˜M of the form above.  We will use that to construct a logspace uniform
circuit family{Cn}n∈N such that for every x∈{0, 1}n, Cn(x) =  ˜M(x).
    Recall that, as we saw in that proof, the transcript of  ˜M’s execution on inputx is the sequence
z1,...,zT  of snapshots  (machine’s state and symbols read by all heads) of the execution at each
step in time.  Assume that each such zi is encoded by a string (that needs only to be of constant
size).  We can compute the string zi  based the previous snapshots zi−1  and zi1,...,zik  where zij
denote the last step that  ˜M’sjth head was in the same position as it is in theith step. Because these
are only a constant number of strings of constant length, we can compute zi from these previous
snapshot using a constant-sized circuit.  Also note that,  under our assumption above,  given the
indices i and i′<i we can easily check whether zi depends on zi′.
    The composition of all these constant-sized circuits gives rise to a circuit that computes from
the inputx, the snapshotzT of the last step of  ˜M’s execution onx. There is a simple constant-sized
circuit that, given zT  outputs 1 if and only if zT  is an accepting snapshot (in which   ˜M  outputs 1
and halts).  Thus, we get a circuit C such that C(x) =  ˜M(x) for every x∈{0, 1}n.
    Because  our  circuit C  is  composed  of  many  small  (constant-sized)  circuits,  and  determining
which small circuit is applied to which nodes can be done in logarithmic space, it is not hard to see
that we can ﬁnd out every individual bit of C’s representation in logarithmic space.  (In fact, one
can show that the functions SIZE, TYPE and EDGE above can be computed using only logarithmic
space and polylogarithmic time.) ■

6.1.1   Turing machines that take advice
There is a way to deﬁne P/poly using Turing machines that ”take advice.”
Definition 6.9
Let T,a  : N→ N  be  functions.   The  class  of  languages  decidable  by  time-T(n)  TM’s  with a(n)
advice, denoted DTIME(T(n))/a(n), contains every L such that there exists a sequence{αn}n∈N
of strings with αn∈{0, 1}a(n) and a TM M  satisfying
                                               M(x,αn) = 1⇔x∈L
for every x∈{0, 1}n, where on input (x,αn) the machine M  runs for at most O(T(n)) steps.

Example 6.10
Every unary language can be be decided by a polynomial time Turing machine with 1 bit of advice.
The advice string for inputs of length n is the single bit indicating whether or not 1n  is in the
language.  In particular this is true of the language of Example                6.4.

   3In fact, typically the movement pattern is simple enough (for example a sequence of T(n) left to right and back
sweeps of the tape) that for every i we can compute this information using only O(logT(n)) space and polylogT(n)
time.

Web  draft  2007-01-08  21:59
DRAFT

<!-- pdf-page: 122 -->
p6.6 (106)                                                                                     6.2.   KARP-LIPTON THEOREM

     This is an example of a more general phenomenon described in the next theorem.
Theorem 6.11
P/poly =∪c,dDTIME(nc)/nd

Proof: If L∈ P/poly,  we can provide the polynomial-sized description of its circuit family as
advice to a Turing machine.  When faced with an input of size n, the machine just simulates the
circuit for this circuit provided to it.
     Conversely, if L is decidable by a polynomial-time Turing machine M  with access to an advice
family{αn}n∈N of sizea(n) for some polynomiala, then we can use the construction of Theorem                       6.7
to construct for everyn, a polynomial-sized circuitDn such that on everyx∈{0, 1}n,α∈{0, 1}a(n),
Dn(x,α) = M(x,α).  We let the circuit Cn  be the polynomial circuit that maps x to Dn(x,αn).
That is, Cn is equal to the circuit Dn with the string αn “hardwired” as its second input. ■

Remark 6.12
By “hardwiring” an input into a circuit we mean taking a circuitC with two inputsx∈{0, 1}n,y∈
{0, 1}m and transforming it into the circuitCy that for everyx returnsC(x,y).  It is easy to do so
while ensuring that the size of Cy is not greater than the size of C.  This simple idea is often used
in complexity theory.

6.2   Karp-Lipton Theorem

Karp and Lipton formalized the question of whether or not SAT has small circuits as:  Is SAT in
P/poly?  They showed that the answer is “NO” if the polynomial hierarchy does not collapse.
Theorem 6.13 (Karp-Lipton, with improvements by Sipser)
If NP⊆ P/poly then PH = Σp2.

Proof: To show that PH = Σp2  it is enough to show that Πp2⊆ Σp2  and in particular it suﬃces
to show that Σp2 contains the Πp2-complete language Π2SAT consisting of all true formulae of the
form
                                     ∀u∈{0, 1}n∃v∈{0, 1}nϕ(u,v) = 1.                                           (2)
where ϕ is an unquantiﬁed Boolean formula.
     If NP⊆ P/poly then there is a polynomialp and ap(n)-sized circuit family{Cn}n∈N such that
for every Boolean formula ϕ and u∈{0, 1}n, Cn(ϕ,u) = 1 if and only if there exists v∈{0, 1}n
such that ϕ(u,v) = 1.  Yet, using the search to decision reduction of Theorem                    2.19, we actually
know  that  there  is  a q(n)-sized  circuit  family{C′n}n∈N  such  that  for  every  such  formula ϕ  and
u∈{0, 1}n, if there is a stringv∈{0, 1}n such thatϕ(u,v) = 1 thenC′n(ϕ,u) outputs such a string
v.  Since C′n can be described using 10q(n)2 bits, this implies that if (2) is true then the following
quantiﬁed formula is also true:

             ∃w∈{0, 1}10q(n)2∀u∈{0, 1}nw describes a circuit C′ s.t. ϕ(u,C′(ϕ,u)) = 1.              (3)

                                                                                Web  draft  2007-01-08  21:59
DRAFT

<!-- pdf-page: 123 -->
6.3.   CIRCUIT LOWERBOUNDS                                                                                                     p6.7 (107)
    Yet if (2) is false then certainly (regardless of whether P = NP) the formula (3) is false as well,
and hence (3) is actually equivalent  to (2)!  However, since evaluating a circuit on an input can be
done in polynomial time, evaluating the truth of (3) can be done in Σp2. ■
    Similarly the following theorem can be proven, though we leave the proof as Exercise                    3.
Theorem 6.14 (Karp-Lipton, attributed to A. Meyer)
If EXP⊆ P/poly then EXP = Σp2.

    Combining the time hierarchy theorem (Theorem                3.1) with the previous theorem implies that
if P = NP then EXP⁄⊆ P/poly.  Thus upperbounds (in this case, NP⊆ P) can potentially be
used to prove circuit lowerbounds.

6.3   Circuit lowerbounds

Since P⊆ P/poly, if NP ⊈ P/poly then P⁄= NP.  The Karp-Lipton theorem gives hope that
NP⁄⊆ P/poly.   Can  we  resolve P  versus NP  by  proving NP ⊈ P/poly?   There  is  reason  to
invest hope in this approach as opposed to proving direct lowerbounds on Turing machines.  By
representing computation using circuits we seem to actually peer into the guts of it rather than
treating it as a blackbox. Thus we may be able to get around the limitations of relativizing methods
shown in Chapter      3.
    Sadly, such hopes have not yet come to pass. After two decades, the best circuit size lowerbound
for an NP language is only 5n.  (However, see Exercise            1  for a better lowerbound for a language in
PH.)  On the positive side, we have had notable success in proving lowerbounds for more restricted
circuit models, as we will see in Chapter        13.
    By the way,  it is easy to show that for large enough n,  almost every boolean function on n
variables requires large circuits.
Theorem 6.15
For n≥ 100, almost all boolean functions on n variables require circuits of size at least 2n/(10n).

Proof: We use a simple counting argument.  There are at most s3s circuits of size s (just count
the number of labeled directed graphs, where each node has indegree at most 2).  Hence this is an
upperbound on the number of functions on n variables with circuits of size s.  For s = 2n/(10n),
this number is at most 22n/10, which is miniscule compared 22n, the number of boolean functions
on n variables.  Hence most Boolean functions do not have such small circuits. ■

Remark 6.16
Another way to present this result is as showing that with high probability, a random function from
{0, 1}n  to{0, 1} does not have a circuit of size 2n/10n.  This kind of proof method, showing the
existence of an object with certain properties by arguing that a random object has these properties
with high probability, is called the probabilistic method, and will be repeatedly used in this book.

    The problem with the above counting argument is of course, that it does not yield an explicit
Boolean function (say an NP language) that requires large circuits.

Web  draft  2007-01-08  21:59
DRAFT

<!-- pdf-page: 124 -->
p6.8 (108)                                                            6.4.   NON-UNIFORM HIERARCHY THEOREM
6.4   Non-uniform hierarchy theorem

As in the case of deterministic time, non-deterministic time and space bounded machines, Boolean
circuits also have a hierarchy theorem.  That is, larger circuits can compute strictly more functions
than smaller ones:
Theorem 6.17
For  every  functions T,T ′  : N→ N  with  2n/(100n) > T ′(n) > T(n) > n  and T(n) logT(n)  =
o(T ′(n)),
                                          SIZE(T(n))⊊ SIZE(T ′(n))

Proof: The diagonalization methods of Chapter               3  do not seem to work for such a function, but
nevertheless, we can prove it using the counting argument from above.  To show the idea, we prove
that SIZE(n)⊊ SIZE(n2).
    For every 𝓁, there is a function f  :{0, 1}𝓁→{0, 1} that is not computable by 2𝓁/(10𝓁)-sized
circuits.  On the other hand, every function from{0, 1}𝓁  to{0, 1} is computable by a 2𝓁10𝓁-sized
circuit.
    Therefore, if we set 𝓁 = 1.1 logn and let g :{0, 1}n→{0, 1} be the function that applies f  on
the ﬁrst 𝓁 bits of its input, then

          g∈               SIZE(2𝓁10𝓁) =               SIZE(11n1.1 logn)⊆           SIZE(n2)
          g⁄∈           SIZE(2𝓁/(10𝓁)) =           SIZE(n1.1/(11 logn))⊇             SIZE(n)

■

6.5   Finer gradations among circuit classes

There are two reasons why subclasses of P/poly are interesting.  First,  proving lowerbounds for
these subclasses may give insight into how to separate NP from P/poly.  Second, these subclasses
correspond to interesting computational models in their own right.
    Perhaps the most interesting connection is to massively parallel computers.  In such a computer
one uses simple oﬀ-the-shelf microprocessors and links them using an interconnection network that
allows them to send messages to each other.  Usual interconnection networks such as the hypercube
allows linking n processors such that interprocessor communication is possible —assuming some
upperbounds  on  the  total  load  on  the  network—in O(logn)  steps.   The  processors  compute  in
lock-step (for instance,  to the ticks of a global clock) and are assumed to do a small amount of
computation in each step, say an operation on O(logn) bits.  Thus each processor computers has
enough memory to remember its own address in the interconnection network and to write down
the address of any other processor, and thus send messages to it.  We are purposely omitting many
details of the model (Leighton [Lei92] is the standard reference for this topic) since the validity
of Theorem     6.24  below does not depend upon them.  (Of course, we are only aiming for a loose
characterization of parallel computation, not a very precise one.)

                                                                                Web  draft  2007-01-08  21:59
DRAFT

<!-- pdf-page: 125 -->
6.5.   FINER GRADATIONS AMONG CIRCUIT CLASSES                                                     p6.9 (109)
6.5.1   Parallel computation and NC
Definition 6.18
A computational task is said to have eﬃcient parallel algorithms if inputs of size n can be solved
using a parallel computer with nO(1) processors and in time logO(1)n.

Example 6.19
Given twon bit numbersx,y we wish to computex +y fast in parallel.  The gradeschool algorithm
proceeds  from  the  least  signiﬁcant  bit  and  maintains  a  carry  bit.   The  most  signiﬁcant  bit  is
computed  only  after n  steps.   This  algorithm  does  not  take  advantage  of  parallelism.   A  better
algorithm called carry  lookahead assigns each bit position to a separate processor and then uses
interprocessor communication to propagate carry bits.  It takesO(n) processors andO(logn) time.
     There are also eﬃcient parallel algorithms for integer multiplication and division (the latter is
quite nonintuitive and unlike the gradeschool algorithm!).

Example 6.20
Many matrix computations can be done eﬃciently in parallel: these include computing the product,
rank, determinant, inverse, etc.  (See exercises.)
     Some graph theoretic algorithms such as shortest paths and minimum spanning tree also have
fast parallel implementations.
     But many well-known polynomial-time problems such as minimum matching, maximum ﬂows,
and linear programming are not known to have any good parallel implementations and are conjec-
tured not to have any; see our discussion of P-completeness below.

     Now we relate parallel computation to circuits. The depth of a circuit is the length of the longest
directed path from an input node to the output node.
Definition 6.21 (Nick’s class or NC)
A language is in NCi  if there are constants c,d > 0 such that it can be decided by a logspace-
uniform family of circuits{Cn} where Cn  has size O(nc) and depth O(logdn).  The class NC is
∪i≥1NCi.

     A related class is the following.

Definition 6.22 (AC)
The class ACi is deﬁned similarly to NCi except gates are allowed to have unbounded fanin.  The
class AC is∪i≥0ACi.

Web  draft  2007-01-08  21:59
DRAFT

<!-- pdf-page: 126 -->
p6.10 (110)                                           6.5.   FINER GRADATIONS AMONG CIRCUIT CLASSES
     Since  unbounded  (but  poly(n))  fanin  can  be  simulated  using  a  tree  of  ORs/ANDs  of  depth
O(logn), we have NCi⊆ ACi⊆ NCi+1, and the inclusion is known to be strict for i = 0 as we
will see in Chapter     13.  (Notice, NC0 is extremely limited since the circuit’s output depends upon
a constant number of input bits, but AC0 does not suﬀer from this limitation.)

Example 6.23
The language PARITY ={x : x has an odd number of 1s} is in NC1.  The circuit computing it
has the form of a binary tree.  The answer appears at the root; the left subtree computes the parity
of the ﬁrst|x|/2 bits and the right subtree computes the parity of the remaining bits.  The gate
at the top computes the parity of these two bits.  Clearly, unwrapping the recursion implicit in our
description gives a circuit of dept O(logn).

     The classes AC, NC are important because of the following.
Theorem 6.24
A language has eﬃcient parallel algorithms iﬀ it is in NC.
Proof: Suppose a language L∈ NC and is decidable by a circuit family{Cn} where Cn has size
N  = O(nc) and depth D  = O(logdn).  Take a general purpose parallel computer with N  nodes
and conﬁgure it to decide L as follows.  Compute a description of Cn and allocate the role of each
circuit node to a distinct processor.  (This is done once, and then the computer is ready to compute
on any input of length n.)  Each processor, after computing the output at its assigned node, sends
the resulting bit to every other circuit node that needs it.  Assuming the interconnection network
delivers all messages in O(logN) time, the total running time is O(logd+1N).
     The reverse direction is similar, with the circuit having N·D nodes arranged in D layers, and
the ith node in the tth layer performs the computation of processor i at time t.  The role of the
interconnection network is played by the circuit wires. ■

6.5.2   P-completeness
A  major  open  question  in  this  area  is  whether P  =  NC.   We  believe  that  the  answer  is  NO
(though we are currently even unable to separate PH from NC1).  This motivates the theory of
P-completeness, a study of which problems are likely to be in NC and which are not.
Definition 6.25
A language is P-complete if it is in P and every language in P is logspace-reducible to it (as per
Deﬁnition    4.14).

     The following easy theorem is left for the reader as Exercise           12.
Theorem 6.26
If language L is P-complete then

    1. L∈ NC iﬀ P = NC.

                                                                                Web  draft  2007-01-08  21:59
DRAFT

<!-- pdf-page: 127 -->
6.6.   CIRCUITS OF EXPONENTIAL SIZE                                                                                 p6.11 (111)
    2. L∈ L iﬀ P = L.  (Where L is the set languages decidable in logarithmic space, see Deﬁni-
       tion  4.5.)

     The following is a fairly natural P-complete language:
Theorem 6.27
Let CIRCUIT-EVAL denote the language consisting of all pairs⟨C,x⟩ such that C  is an n-inputs
single-output circuit and x∈{0, 1}n satisﬁes C(x) = 1.  Then CIRCUIT-EVAL is P-complete.

Proof: The language is clearly in P.  A logspace-reduction from any other language in P to this
language is implicit in the proof of Theorem          6.7. ■

6.6   Circuits of exponential size

As noted, every language has circuits of size O(n2n).  However, actually ﬁnding these circuits may
be diﬃcult— sometimes even undecidable.  If we place a uniformity condition on the circuits, that
is, require them to be eﬃciently computable then the circuit complexity of some languages could
exceedn2n.  In fact it is possible to give alternative deﬁnitions of some familiar complexity classes,
analogous to the deﬁnition of P in Theorem            6.7.
Definition 6.28 (DC-Uniform)
Let{Cn}n≥1 be a circuit family.  We say that it is a Direct Connect uniform (DC uniform) family if,
given⟨n,i⟩, we can compute in polynomial time theith but of (the representation of) the circuitCn.
More concretely, we use the adjacency matrix representation and hence a family{Cn}n∈N  is DC
uniform iﬀ the functions SIZE, TYPE and EDGE deﬁned in Remark ?? are computable in polynomial
time.

     Note that the circuits may have exponential size,  but they have a succinct representation in
terms of a TM which can systematically generate any required node of the circuit in polynomial
time.
     Now we give a (yet another) characterization of the class PH, this time as languages computable
by uniform circuit families of bounded depth.  We leave it as Exercise              13.
Theorem 6.29
L∈PH iﬀ L can be computed by a DC uniform circuit family{Cn} that

    •  uses AND, OR, NOT gates.

    •  has size 2nO(1)  and constant depth (i.e., depth O(1)).

    •  gates can have unbounded (exponential) fanin.

    •  the NOT gates appear only at the input level.

     If we drop the restriction that the circuits have constant depth, then we obtain exactly EXP
(see Exercise    14).

Web  draft  2007-01-08  21:59
DRAFT

<!-- pdf-page: 128 -->
 6.7.   CIRCUIT SATISFIABILITY AND AN ALTERNATIVE PROOF OF THE COOK-LEVIN
p6.12 (112)                                                                                        THEOREM
6.7   Circuit  Satisﬁability  and  an  alternative  proof  of  the  Cook-
         Levin Theorem

Boolean circuits can be used to deﬁne the following NP-complete language:

Definition 6.30
The  circuit  satisﬁability  language  CKT-SAT  consists  of  all  (strings  representing)  circuits  with  a
single output that have a satisfying assignment.  That is, a string representing an n-input circuit
C is in CKT-SAT iﬀ there exists u∈{0, 1}n such that C(u) = 1.

    CKT-SAT is clearly in NP because the satisfying assignment can serve as the certiﬁcate.  It is
also clearly NP-hard as every CNF formula is in particular a Boolean circuit.  However, CKT-SAT
can also be used to give an alternative proof (or, more accurately, a diﬀerent presentation of the
same proof) for the Cook-Levin Theorem by combining the following two lemmas:

Lemma 6.31
CKT-SAT is NP-hard.

Proof: Let L be an NP-language and let p be a polynomial and M  a polynomial-time TM such
that x∈ L iﬀ M(x,u) = 1 for some u∈{0, 1}p(|x|).  We reduce L to CKT-SAT by mapping (in
polynomial-time)x to a circuitCx withp(|x|) inputs and a single output such thatCx(u) =M(x,u)
for  every u∈{0, 1}p(|x|).   Clearly, x∈ L⇔ Cx ∈  CKT-SAT  and  so  this  suﬃces  to  show  that
L≤P  CKT-SAT.
    Yet, it is not hard to come up with such a circuit.  Indeed, the proof of Theorem               6.7 yields a
way to map M,x into the circuit Cx in logarithmic space (which in particular implies polynomial
time). ■

Lemma 6.32
CKT-SAT≤p 3SAT

Proof: As mentioned above this follows from the Cook-Levin theorem but we give here a direct
reduction.  If C is a circuit, we map it into a 3CNF formula ϕ as follows:
    For every nodevi ofC we will have a corresponding variablezi inϕ. If the nodevi is an AND of
the nodesvj andvk then we add toϕ clauses that are equivalent to the condition “zi = (zj∧zk)”.
That is, we add the clauses

                      (zi∨  zj∨zk)∧ (zi∨zj∨        zk)∧ (zi∨zj∨zk)∧ (zi∨         zj∨  zk).

Similarly, if vi is an OR of vj  and vk then we add clauses equivalent to “zi = (zj∨zk)”, and if vi
is the NOT of vj then we add the clauses (zi∨zj)∧ (zi∨             zj).
    Finally, if vi is the output node of C then we add the clause zi to ϕ.  It is not hard to see that
the formula ϕ will be satisﬁable if and only if the circuit C is. ■

                                                                             Web  draft  2007-01-08  21:59
DRAFT

<!-- pdf-page: 129 -->
6.7.   CIRCUIT SATISFIABILITY AND AN ALTERNATIVE PROOF OF THE COOK-LEVIN
THEOREM                                                                                                                                            p6.13 (113)
  What have we learned?

      •  Boolean circuits can be used as an alternative computational model to TMs.
         The class P/poly of languages decidable by polynomial-sized circuits is a strict
         superset of P but does not contain NP unless the hierarchy collapses.

      •  Almost every function from{0, 1}n to{0, 1} requires exponential-sized circuits.
         Finding even one function in NP with this property would show that P⁄= NP.

      •  The class NC of languages decidable by (uniformly constructible) circuits with
         polylogarithmic depth and polynomial size corresponds to computational tasks
         that can be eﬃciently parallelized.

Chapter notes and history

Karp-Lipton theorem is from [KL82]. Karp and Lipton also gave a more general deﬁnition of advice
that can be used to deﬁne the classC/a(n) for every complexity classC and function a.  However,
we do not use this deﬁnition here since it does not seem to capture the intuitive notion of advice
for classes such as NP∩ coNP, BPP and others.
     The class of NC algorithms as well as many related issues in parallel computation are discussed
in Leighton [?].

Exercises

   §1  [Kannan [Kan82]] Show for everyk> 0 that PH contains languages whose circuit complexity
       is Ω(nk).

   §2  Solve the previous question with PH replaced by Σp2.

   §3  ([KL82], attributed to A. Meyer) Show that if EXP⊆ P/poly then EXP = Σp2.

   §4  Show that if P = NP then there is a language in EXP that requires circuits of size 2n/n.

   §5  A language L⊆{0, 1}∗ is sparse if there is a polynomial p such that|L∩{0, 1}n|≤p(n) for
       every n∈N.  Show that every sparse language is in P/poly.

   §6  (X’s Theorem 19??)  Show that if a sparse language is NP-complete then P = NP.  (This is
       a strengthening of Exercise      13  of Chapter    2.)

Web  draft  2007-01-08  21:59
DRAFT

<!-- pdf-page: 130 -->
 6.7.   CIRCUIT SATISFIABILITY AND AN ALTERNATIVE PROOF OF THE COOK-LEVIN
p6.14 (114)                                                                                       THEOREM

  §7  Show a logspace implicitly computable functionf that maps anyn-vertex graph in adjacency
      matrix representation into the same graph in adjacency list representation.  You can think
      of the adjacency list representation of an n-vertex graph as a sequence of n strings of size
      O(n logn) each,  where the ith  string contains the list of neighbors of the ith  vertex in the
      graph (and is padded with zeros if necessary).
  §8  (Open) Suppose we make a stronger assumption than NP⊆ P/poly:  every language in NP
      has linear size circuits.  Can we show something stronger than PH = Σp2?
  §9   (a)  Describe an NC circuit for the problem of computing the product of two given n×n
            matrices A,B.
       (b)  Describe an NC circuit for computing, given an n×n matrix, the matrix An.

       (c)  Conclude that the PATH problem (and hence every NL language) is in NC.

 §10  A formula is a circuit in which every node (except the input nodes) has outdegree 1.  Show
      that a language is computable by polynomial-size formulae iﬀ it is in (nonuniform) NC1.

 §11  Show that NC1 = L.  Conclude that PSPACE⁄= NC1.
 §12  Prove  Theorem     6.26.   That  is,  prove  that  if L  is P-complete  then L∈ NC  (resp.  L)  iﬀ
      P = NC (resp. L).
 §13  Prove Theorem      6.29 (that PH is the set of languages with constant-depth DC uniform cir-
      cuits).
 §14  Show that EXP is exactly the set of languages with DC uniform circuits of size 2nc where c
      is some constant (c may depend upon the language).
 §15  Show that if linear programming has a fast parallel algorithm then P = NC.

                                                                            Web  draft  2007-01-08  21:59
DRAFT
