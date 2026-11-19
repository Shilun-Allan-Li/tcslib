<!-- generated-by: scoped pypdf extraction (EF-H12 ingest, ruling EF-H12-R4 A / Q-H12-2 A, 2026-11-19); awaiting Codex source review -->
<!-- source-pdf-sha256: f17c4a237263d340af14431df9a377bed1f5f1c3f9d5a28f7d0d05c1422989bf -->
<!-- extractor: pypdf 6.17.0, extract_text() (default plain mode) under python3 -I; the layout mode interleaves the two text columns line by line on this scan, the plain mode reads them column by column; trailing spaces removed; one DEL control character (p. 14, Table II header) replaced by U+FFFD -->
<!-- scope (physical pages): 1-17, the whole paper (printed pp. 47-63); the .md transcribes pp. 1-2, 6-8, 16-17 in part and summarises the rest, see its header -->
<!-- note: physical page p is printed page p+46; the text layer is OCR of a scanned typescript and keeps its recognition errors (e.g. 'kBSTRACT', '~' for the reduction sign alpha); the .md was checked against the page images, not this layer -->

<!-- pdf-page: 1 -->
SOME SIMPLIFIED NP-COMPLETE PROBLEMS
by
M. R. Garey and D. S. Johnson
Bell Laboratories
Murray Hill, New Jersey
and
L. Stockmeyer t
Massachusetts Institute of Technology
Cambridge, Massachusetts
kBSTRACT
It is widely believed that showing a
problem to be NP-complete is tantamount
to proving its computational intracta-
bility. In this paper we show that a
number of NP-complete problems remain
NP-complete even when their domains are
substantially restricted. First we show
the completeness of SIMPLE MAX CUT (MAX
CUT with edge weights restricted to
value i), and, as a corollary, the com-
pleteness of the OPTIMAL LINEAR
ARRANGEMENT problem. We then show that
even if the domains of the NODE COVER
and DIRECTED HAMILTONIAN PATH problems
are restricted to planar graphs, the two
problems remain NP-complete, and that
these and other graph problems remain
NP-complete even when their domains are
restricted to graphs with low node de-
grees. For GRAPH 3-COLORABILITY, NODE
COVER, and UNDIRECTED HAMILTONIAN
CIRCUIT, we determine essentially the
lowest possible upper bounds on node
degree for which the problems remain
NP-complete.
INTRODUCTION
Certain combinatorial problems, such as
the traveling salesman problem and
theorem proving in the propositional
calculus, have long been notorious for
their computational intractability, in
that, despite the effort of many clever
people, no algorithms have been found
for them which can be guaranteed to
require time bounded by a polynomial
in the length of the input. The belief
in the inherent difficulty of these
problems has been strengthened by results
of Cook and Karp [C71,K72]. These show
that simple forms of the above problems,
together with a wide variety of other
combinatorial problems, form a class, the
NP-complete* problems, no member of which
is known to have a polynomial time
algorithm, but such that if any one of
the problems does have such an algorithm,
then they all do.
These results have stimulated many
researchers to examine other combinatorial
problems for which no polynomial time
algorithms are known, to determine whether
they too are NP-complete, and their
efforts have resulted in the discovery of
additional members of this class [Sa72,
Se73,U73]. Such results have considerable
practical significance. If one knows that
the problem he wishes to solve is NP-
complete, and thus is unlikely to have
any polynomial time algorithm, he may
feel justified in concentrating on more
hopeful alternative approaches.
He can look for algorithms which, although
admittedly exponential in the worst case,
seem to work quickly on most practical
problems [K70,L73], or even which are
just "less exponential" than previous
algorfthms, and hence extend somewhat the
maximum size problem which can be solved
within practical time limits [Sa73].
Alternatively, he can look for fast
algorithms which, although they do not
actually find optimal solutions for the
problem, are guaranteed to yield solutions
which are "close" to optimal [Ga72,Gr72,
Jo72, Jo73 ] .
A third approach, which motivates this
paper, relates to the fact that the prac-
tical situation of concern often imposes
additional restrictions on the domain of
the problem, which may or may not make
the problem easier to solve. We examine
The work of this author was done, in
part, at Project MAC, and supported by
The National Science Foundation under
research grant GJ-34671.
"polynomial complete" problems, in the
terminology of Karp [K72].
47

<!-- pdf-page: 2 -->
certain natural restrictions on the
domains of a number of known NP-complete
problems, to determine whether the re-
sultant subproblems are still NP-complete,
or if they do have polynomial time
algorithms.
Our results indicate that many known NP-
complete problems remain NP-complete,
even when their domains are substantially
restricted. In addition to the immediate
significance of knowing that these re-
stricted problems are NP-complete, the
nature of the restrictions makes the com-
pleteness results useful in two other
ways. First, they increase our know-
ledge of the essential elements which
made the original problems NP-complete.
Second, they give us valuable tools for
proving other completeness results. For
instance, by observing that SATISFI-
ABILITY WITH AT MOST 3 LITERALS FER
CLAUSE, a restricted form of SATISFI-
ABILITY, is still NP-complete, Karp
[K72] was able to derive the NP-complete-
ness of CHROMATIC NUMBER, EXACT COVER,
MAX CUT, and a number of other problems.
In the first half of this paper, we show
that an important restricted version of
MAX CUT is still NP-complete, and from
that derive the completeness of the
(until now) intransigent OPTIMAL LINEAR
ARRANGEMENT problem, as well as a number
of more closely related problems. The
second hail of the paper considers the
effect of restricting the allowable types
of graphs for NP-complete graph problems
such as NODE COVER, CHROMATIC NUMBER, and
HAMILTONIAN CIRCUIT, by either restrict-
ing the maximum degree of the nodes, or
allowing only planar graphs, or both.
We summarize here the basic definitions,
referring the reader to [K72] for a more
complete discussion. Let B = [0,i] and
let B* denote the set of all finite
strings of elements from B. Any subset
L of B* is called a language. Let ~ be
the class of functions f:B* ~B* which
are computable in polynomial time by one-
tape deterministic Turing machines. If
L and M are languages, we say that L is
polynomial reducible to M, written L ~ M,
when there is a function f¢~ such that
f(x)~M if and only if xeL. M is NP-
complete if MeNP (the class of languages
recognizable in polynomial time by one-
tape nondeterministic Turing machines)
and every language in NP is polynomial
reducible to M. In fact, if L is NP-
complete and L ~ M, then MeNP implies
that M is NP-complete.
In accord with the above definitions,
the "problems" we shall consider in this
paper, although many are more naturally
thought of as optimization problems,
shall be presented as recognition problems
(with the straightforward details of the
encoding of entities such as graphs and
integers into strings of O's and l's
omitted). Our proofs can then consist
of showing that known NP-complete
languages reduce to the ones we are con-
sidering. (A list of the known NP-com-
plete languages we shall use, together
with their definitions, is given in the
Appendix). In general, we leave to the
reader the straightforward verification
that (a) the language is in NP and (b)
the described mapping can be performed in
polynomial time.
I. SIMPLE MAX CUT AND RELATED PROBLEMS
In [K72], the following problem was shown
to be NP-complete:
MAX CUT
~: Graph t G = (N,A), weighting
function w: A ~ Z, positive
integer W.
PROPERTY: There is a set S C N such that
w(lu,vl) ~ w.
[u,v]~A
ucS,veN-S
Karp proved the NP-completeness of this
problem by a reduction from the PARTITION
problem. Thus, his proof relies on the
fact that the edge weights can be repre-
sented in space proportional to the log-
arithm of their magnitudes, since there
is a dynamic programming algorithm for
PARTITION which runs in time polynomial
in the input length, if those inputs are
expressed in unary (i.e., in length pro-
portional to their magnitudes).
One might conjecture, therefore, that if
we restricted MAX CUT by requiring each
edge weight to be exactly i, the new
problem, which we call SIMPLE MAX CUT,
might become easy. As added support for
this view, notice that if W = IAI, then
this problem simply asks whether G is
bipartite, which can be determined quite
easily.
In fact, however, SIMPLE MAX CUT is
NP-complete, as we show using a two-step
reduction from SATISFIABIL!TY WITH AT MOST
3 LITERALS PER CLAUSE (SAT3-- for formal
definition, see the Appendix). We first
consider the following restricted version
of the MAXIMUM SATISFIABILITY problem of
[JOY3]:
MAXIMUM SATISFIABILITY WITH AT MOST 2
LITERALS PER CLAUSE
INPUT: Disjunctive clauses C~,C~, .... Cp,
each containing at mo~t ~wo
literals, positive integer k.
PROPERTY: There is a truth assignment to
the variables which satisfies
k or more clauses.
We use the ordered pair (N,A) to denote
a graph G having node set N and edge set
A.
48

<!-- pdf-page: 3 -->
We use the abbreviation MAX SAT2 to
denote this problem. Observe that,
when k:p, this problem can be solved in
polynomial time [Co71]. However, we now
show that SAT3 can be reduced to MAX SAT2,
proving that MAX SAT2 is NP-complete.
Theorem I.i: SAT 3 ~ MAX SAT2
Proof. Suppose we are given an input for
SAT~, that is, a set S of disjunctive
clauses, each containing at most 3 literals.
If any clause has fewer than 3 literals, we
may replace it by an equivalent clause
which has exactly 3 literals merely by
repeating one of the literals which it
contains. Hence, we may assume that each
clause in S contains exactly 3 literals,
and we label them (alVblVCl) through (avb~c~
.... r~bi~ where e~ch ai, b i, andci represents either a varmao~e
or its negation. The corresponding set S r
of clauses and value k forMAX SAT2 are given by :
S' : ~ [(ai), (bi), (°i), (di),
i=i
(a, ivbi), (aivci), (bi,,~i) ,
(air'i), (bivdi), (ci~d i) ],
k : 7m.
7m or more of the clauses in S' can be
satisfied simultaneously if and only if
the original set S is satisfiable. For
note that, if we have any satisfying
assignment for S, then either one, two,
or three of ai,bi,ci must be set true
for each i. The reader may verify that,
in all three cases, there is a truth
setting for d i causing precisely seven
of the clauses in S' arising from clause
i to be satisfied. Furthermore, no sett-
ing of d. will permit more than seven m of the ten clauses to be satisfied,
~nd at most six of the clauses can be
satisfied if all of a i, bi, and c i are
"false. "•
We now prove the completeness of SIMPLE
MAX CUT by reducing MAX SAT2 to it.
Theorem 1.2: MAX SAT2 ~ SIMPLE MAX CUT.
Proof: Let clauses CI,C2,...,C and
~-~er k be given as input forPMAX
SAT2. In analogy with the proof of
Theorem i, we may assume that each clause
contains exactly two literals, not
necessarily distinct, and label them as
(~n )r We shall (a l~bl) , !a2~b2) ..... bp a cons~ruc~ a correspon g g p , as in-
put to SIMPLE MAX CUT, in two steps,
first giving the nodes and a basic frame-
work of edges, and then adding in some
additional problem-specific edges. Let
Xl,Xg, .... ,x n be the variables occurring
(either complemented or uncomplemented)
in the p clauses. The set N of nodes
for the graph G is
N = [Ti:O<i<3p] <9 [Fi:O!i£3p]
%) [tij:l!i<_n,O<j<3P]
<* [fij:lii<_n,OiJi3P]
k) [xi:l!i<_n] k~ [xi:l!i<_n].
The basic framework A I of edges is
A 1 : [[Ti,Fj]:Oiii3p,0<Ji3P]
[[tij,fij]:l<i<_n,O<j<3P]
k9 [(xi,fij]:l!i<_n,O!j!3P]
[[xi,tij]:l~i<_n,O<j<3P]"
For any given partition N = SI~ S 2,
SI~ S~ = ~, we will say that edge [u,v]
is "ha~" if both u and v belong t~ the,,
same set in the partition and is go~a
otherwise. Notice that all edges in A 1
will be good for any partition
N : SI~ S 2 which obeys (a) all T~ belong
to the same set in the partition ~nd all
F i belong to the other set, and (b) for
each i, x i and all ti~ belong to the same
set in the partition ~nd x~ and all f-. • ' i i O
belong to the other set. Furthermore,
if any pair F$,F. belong to different sets
in the partitmon~ then at least 3p+l edges
from A I will be bad, since each such pair
of nodes are mutually adjacent to 3p+l
other nodes. Similarly, if any pair
xi,~ i belong to the same set in the parti-
tlon, then at least 3p+l edges from A~
will be bad, since there are_3p+l disjoint
3-edge paths between x i and x i.
The following additional edges are
included in G:
A 2 = ([ai,bi]:l~i<p and a i ~ b i]
[[ai,F2i_l]:l<i<P]
tO [[bi,F2i]:l<i<P].
The input for SIMPLE MAX CUT is the graph
G = (N,AIkOA2) and W =IA I] + 2k.
Given a truth assignment for the n
variables which satisfies k or more
clauses, construct the partition
N = Sl<9 S 2 as follows:
S I : [Fi:O!i£3p] <3 [xi:x i is false,l<i<n]
[tij:x i is false,
l<i<n, OiJi3P]
[xi:xi is true,l<i<n]
(fij:xi is true,
l!i<n, O!j!3P],
S 2 = N - S I .
49

<!-- pdf-page: 4 -->
Since, for each satisfied clause, one or
both of a. and b~ belong to S~, exactly
two edges in A~ ariszng from ~hat clause
must be good. -Furthermore, by our pre-
vious comments every edge in A I is good.
Thus we have a~ least W = IAII+ 2k good
edges.
Now, suppose we have a partition
N = SI~ S 2 for which W or more edges are
good. Since k > 0 and IAoI < 3P, the
number of bad edges cannoZ e~ceed 3P.
By our previous discussion, this implies
that all the F. must belong to the same
set, say S~. ~or the same reason,
exactly on~ of each pair xi,~ i must be-
long to S I. Thus, a consistent truth
assignmen~ is obtained by setting x i
"true" if and only if x~ belongs to S~
For this truth assignment, clause i is
satisfied whenever a~ or b i or both
belong to S 2. HowevSr, it is not diffi-
cult to see that, of the edges in A 2
arising from clause i, exactly two are
good if one or both of a. and b i belong
to S 2 and none are good ~f a~ and b~
both belong to S I. Therefor@, sinc@ at
least 2k edges from A 2 must be good,
this truth assignment must satisfy at
least k clauses.~
An easy corollary to the completeness of
SIMPLE MAX CUT concerns the following
problem:
MINIMUM CUT INTO EQUAL-SIZED SUBSETS
INPUT: Graph G : (N,A), two distin-
guished nodes s and t, posi-
tive integer W.
PROPERTY: There is a partition
N = $7<2 S 2 with Slgh S 2 =
I Sll =~S I, scaT, tgSo, and
l![u,v]~:UCSl,~s2]l ~ w.
Observe that this problem can be solved
in polynomial time if no restriction is
made as to the sizes of the subsets
[K72]. However, as defined, the problem
is NP-complete, as we can conclude from
the completeness of SIMPLE MAX CUT and
the following:
Theorem 1.3: SIMPLE MAX CUT a MINIMUM
~AL-ZIZED SUBSETS
Proof. Given a graph G = (N,A) and posi-
mZi-V~--integer W, as input for SIMPLE MAX
CUT, let n =IN'I and U = [Ul,U 2 ..... Un]
satisfy U(-h N = ~. The corresponding in-
put for MINIMUM CUT INTO EQUAL-SIZED SUB-
SETS is the graph G r = (Nt,A'), nodes u l
and u_, and positive integer W ~, define~
as fo~lows:
N t = N QDU;
At = [ [u, v] :u, vcN ~ and [u,v] ~ A];
W t = n 2 - W.
Suppose there is a partition N = S L-) S
that l[[u,v]cA:U~Sl,V~S2]l ~ W. Since W 2
is positive, both S I and S 2 are nonempty.
Let j = n -ISll. Form , ,
S~ = S~<) [ul,u o ..... u.] and S^ = N' - S I.
r n
T~en N = S~<-) ~ is aJpartiti~n for G'
with 1 4j = I~21 : ~, u I c S~, Un ~ S~, and
I I
I[[u,v]¢A':u~SI,VCS2]I
= n 2 -l[[u,v]6A':ucS~,v¢So]l
: n 2 - l[[u,v]~A:UCSl,V¢S2]l
< n 2 -W :W'.
Ngw, suppose there i9 a partition N' =
$7 k9 S~,, with u~ e S~, u n ~ $2, and
I S~II = I~-I = n,sdch, t~at
I[[u,v]c~':ucST,vcSo]I < n 2 - W = W'.
Then N : S~ <9~S~, ~her~ S~ : S~ (-l N and
S o = S~(-~ ~, isma partitiSn fo~ G satis-
fying
l[[u,v]eA:UeSl,VeS2]l
=l Cu, vlZA,:u S;,v S;l,
I I
= n 2 - l[[u,v]~A' :UCSl,VCS2] I
n 2 - (n2-W) = W.
Thus G has a cut of weight greater than
or equal to W if and only if G' has a cut
with weight not exceeding W', which
separates u I and u and divides the nodes
of the grap~ into ~wo equal sized subsets.
The reduction is proved.|
A useful restatement of SIMPLE MAX CUT is:
MINIMUM EDGE-DELETION BIPARTITE SUBGRAPH
INPUT: Graph G = (N,A), positive integer
k.
PROPERTY: G has a bipartite subgraph
formed by deleting k or fewer
edges.
That the following node-deletion version
of this problem is also NP-complete
follows from Theorem 1.4 below.
MINIMUM NODE-DELETION BIPARTITE SUBGRAPH
INPUT: Graph G = (N,A), positive integer
k.
PROPERTY: G has a bipartite subgraph
formed by deleting k or fewer
nodes.
Theorem 1.4: CLIQUE ~ MINIMUM NODE-
DELETION BIPARTITE SUBGRAPH.
Proof: Given a graph G = (N,A) and
pos-~ive integer j as input to CLIQUE
(for a formal definition of CLIQUE See
the Appendix), let n = I NI and
U = [u ,u2, ,u ] where U(~ N = ~ The 1 .'''. n correspondmng input for MINIMUM NODE-
DELETION BIPARTITE SUBGRAPH is the graph
G, = (N',A') and integer k defined as
follows:
N' = N tJU;
A' : ([u,v]:u,v~N',fu,v]6A, and
Ifu,v]gh ul < i];
k = n - j.
50

<!-- pdf-page: 5 -->
The reader may verify that G contains a
clique of j nodes if and only if G' has a
bipartite subgraph formed by deleting
n-j or fewer nodes.|
The final result of this section concerns
the OPTIMAL LINEAR ARRANGEMENT problem
[A73], defined as follows:
OPTIMAL LINEAR ARRANGEMENT
INPUT: Graph G = (N,A), weighting
function w:A ~Z, positive
integer W.
PROPERTY: There is a i-i function
f:N ~ Z such that
w({u,v]). If(u)-f(v)l i W.
(u,v]~A
This problem is a special case of the
well-known quadratic assignment problem
and a number of related facility location
and component placement problems. We use
a reduction from SIMPLE MAX CUT to show
that this problem is NP-complete, even
in the restricted case where all edge
weights are required to be i (which we
call SIMPLE OPTIMAL LINEAR ARRANGEMENT).
Theorem 1.5: SIMPLE MAX CUT ~ SIMPLE
~AR ARRANGEMENT
Proof: Given a graph G = (N,A) and
pos--~ive integer k as inpu~ for SIMPLE
MAX CUT, let n = INI, r = n-, and
U = fuq,u o .... ,Ur] where U~ N = ~. The
corresDonding input for SIMPLE OPTIMAL
LINEAR ARRANGEMENT is the graph
G' = (N',A ' ) and positive integer W
defined as follows:
N' = N <J U;
A' : [[u,v]:u,v~N' and [u,v]6A];
(Notice th;t-(t~: >-]
l<u<v<t
the minimum W achievable--for a complete
graph on t nodes.)
(v-u) which is
Suppose we have a partition N : SItN
which satisfies l[[u,v]~A:u~Sl,v~S~]1%2k.
Let S~ = [al,a 2 ..... at] and ~ ~ --
S o = ~bq,b o ..... b t]. Define f as
fbllows? - n-_
f(ai) = i, 1 < i < t
4 f(ui) = t + i, 1 <_ i <_ n
f(bi) : n ~4 + t + i, 1 <_ i <_ n - t.
n~+n+l h ~ If If(u)-f(~)l : ( - (u)-f(~)l : 3
{U, v}[A'
= 3 /
_ V If(u)-f(~)l
{u,~}~A
< < nS+n+lh _kn ~ = - 3 y w.
Now suppose there exists a 1-1 function
f:N'---~Z such that ~ Jf(u)-f(v)l < W.
Then there exists such an f having range
[i 2 n~+n]. Let F denote the set of
±-{ ~d~ions f:~,' ~ [1,2 ..... n'+nl.
Observe that for any f[F
Z
[u,v]~A'
I f(u)-f(v)l + )~ If(u)-f(v)q
[u,vI~A/ \
l<_i<j~<__~n~+n'J-i1: ~ 3 /"
There fore, there exists an fcF such that
~' If(u)-f(v) I > kn 4
(u,,,T]~A
Define
'- q f (u)-f(v) I W* = max /,
f~F [U,V]cA
and
F* = IfcF: £ If(u)-f(v)l = W* I "
[u,v]~A
Clearly W* > kn 4 and F* is nonempty. For
each f~F*, ~efine the set
S(f) : [vcN:zui,uj~U with
f(ui) < f(v) < f(uj)]
and let m(f) : I S (f)l. Then there exists
a function g~F* such that m(g) < m(f) for
all fcF*. We first show that m~g) : O.
51

<!-- pdf-page: 6 -->
Suppose m(g) > O. Let v eS(g) be such
that g(v~) > g(v) for alY yeS(g). For
each yen w, ~efine
L(v) = l[ueN':[u,v]¢A and g(u)<g(v)] I
and
R(v) = l~ueN':[u,v]eA and g(u)>g(v)]l .
~ote that veU implies L(v) = R(v) = O.
Suppose L(v ) > R(Vo). Let UoeU be such
that g(u ) J g~u) for all ueU. Then by
definition ~f v , g(v ) < g(v) < g(u )
implies that veU. CoNsider the--function
gcF which is identical to g except that
g(Vo) = g(u ) and g(u ) : g(Vo). It is
not difficult to see Zhat
Ig(u)-g(v)l ~ W* and m(g)<m(g) which
5]
{u, hA
contradicts either the definition of W*
or the choice of g. Thus, L(v ) < R(v ~
Let t = max[g(v):veN',g(v) < g~v )~ :d
L(v) > R(v)]. The value of t is~we~! -
defined since there exists a ueU with
g(u) < g(vo) and L(u) : R(u) = O. Thus,
if g(v]) = t and g(v2) = t + i, we must
have L~v2) < R(v2). The function ~eF,
which is identical to g except that
~(Vl) : g(v 2) and ~(v2) : g(vl),
satisfies
> g(u)-g(v)l l~(u)-~(v)I >
[u,v[cA (u,v]~A
:W @ ,
contradicting the definition of W*.
Therefore, we must have m(g) = O.
Since m(g) = O, the elements of U are
mapped by g to a set of consecutive
integers. Define a partition N = SIk3S 2
by
S I = [vcN:g(v)<g(u) for all ueU],
S 2 : [veN:g(v)>g(u) for all ueU].
We now have
kn 4
v~
< ~ Ig (u)-g(v) I
[u,v]~A
L,,,
[u,vlzA
u,veS 1
Ig(u)-g(v) I
[u,v]cA
U, V6 S 2
Ig(u)-g(v)l
<
+ 2, I g(u)-g(v) 1
(u,v]cA
ue S I , ve S 2
+ \3/
n 3 n 3 n 3 < -~- + -6- + -~
+ (nh+n)l[ [u, v]eA :UeSl,
veS2]l
+ n 4.1 [[u,v]eA:neSl,VeS2]l
which, since k is an integer, implies
l[[u,v]eA:UeSl,VeS2] I ~ k.
This completes the proof of Theorem 1.5.
II, Restricted Graph Problems
Many of the reductions which were first
used to show certain graph theoretic
problems to be NP-complete involved the
construction of rather complicated graphs,
highly non-planar and with nodes having
arbitrarily high degree. Since in many
practical problems node degree may be
bounded (e.g., fan-in, fan-out restric-
tions on circuit elements), or graphs may
be planar, it is worthwhile to determine
whether the complexity of the graphs
involved in these reductions was necessary.
In certain eases, we can observe trivially
that it is. For example, consider the
problem CLIQUE [K72]. Since the largest
clique possible in a planar graph has
size 4, and the largest clique possible
in a graph with maximum node degree k has
size k + i, we can find the largest
clique in either case in polynomial time
by examining all subsets of 5 or fewer
(k+l or fewer) nodes~ in time proportional
to at most n ~ or n K+±, respectively.
More interesting are the cases where the
answer is not readily apparent. For
instance, it is implicit in the literatu~
that MAX CUT, when restricted to planar
~ raphs, can be solved in polynomial time.
072] presents a polynomial time proce-
dure for reducing the problem of finding
the maximum cut in a weighted planar
graph to that of finding a minimum
weighted matching in a complete graph
derived from the dual of the original
graph. Although [072] then resorts to a
non-polynomial branch and bound technique,
the weighted matching can be found in
polynomial time using a method of Edmonds
[E70].
On the other hand, one of the authors has
shown [St73] that the question of whether
a graph is 3-colorable (GRAPH 3-COLOR-
ABILITY, itself a restriction of CHROMATIC
NUMBER) is NP-complete, even when the
domain is restricted to include only
planar graphs. In this section, we shall
present further completeness results,
52

<!-- pdf-page: 7 -->
concerning GRAPH 3-COLORABILITY, NODE
COVER, and HAMILTONIAN CIRCUIT. The
formal definitions of these problems
appear in the appendix.
The following table gives the principal
restricted versions of these problems
which we prove to be polynomial complete:
PROBLEM
i. PLANAR GRAPH 3-COLORABILITY
2. UNDIRECTED HAMILTONIAN CIRCUIT
3. PLANAR DIRECTED HAMILTONIAN PATH
4. NODE COVER
5. PLANAR NODE COVER
NODE DEGREE AT MOST
i. 4
2. 3
3. }~-OUT, 3-1N
4. 3
5. 6
For results 3 and 5, it was not previously
known if the planar problems were com-
plete, even if no restrictions were
placed on node d-~grees. The degree con-
straints in 1,2, and ;~ are all best
possible, in that each of the problems
becomes easy if the restriction on node
degree is reduced by I. NODE COVER and
UNDIRECTED }~MILTONIAN CIRCUIT are
clearly trivial for graphs with maximum
degree 2, and a well-known result of
Brooks [B!$1] implies that a connected
graph with maximum degree 3 is 3-color-
able if and only if it differs from K~4,
the complete graph on four nodes, which
is easy to determine.
In addition to the above results, there
are a number of more or less immediate
corollaries. Result 2 implies that
DIRECTED !~HILTONIAN CIRCUIT with node
degree bounded by 3-OUT, 3-1N is NP-
complete; however, the largest degree
bounds for which we know this problem to
be easy are 2-OUT, I-IN or 2-1N, 1-OUT.
Also, we may substitute PATH for CIR-
CUIT in result 2. However, we do not
know whether PLANAR DIRECTED I~MILTONIAN
CIRCUIT, PLANAR UNDIRECTED HAMILTONIAN
CIRCUIT, or PLANAR UNDIRECTED ~MILTONIAN
PATH are NP-complete, and these remain
significant open problems.
The proofs of the results given in the
table follow. For each problem, we show
that there is a known NP-complete problem
which reduces to it.
Theorem 2.1. PLANAR GRAPH 3-COLORABILITY
PLANAR GRAPH 3-COLORABILITY WITH NODE
DEGREE AT MOST ~.
Proof: The key to our construction will
~e use of "node substitutes." Figure
I(A) shows the 3-outlet node substitute
H3, with its first, second, and third
output nodes labelled. For k > 4, the k-
outlet node substitute H k is formed by
adjoining to Hk_ I a copy of H~ having its
first outlet coinciding with 5utlet k-i
of H~ 7. The outlet nodes of H k are the
node~-~aving degree 2. The outlets which
originally belonged to H k I retain the
same labels, with the second outlet of th~
adjoined HR becoming outlet k-i and its
third outl~t becoming outlet k. Figure
I(B) shows H 5.
It is easy to prove by induction that,
for all k > 3, the following facts hold:
(2.1A) H~ has 7(k-2) + i nodes,
i~cluding k outlets.
(2.1B) No node of H k has degree
exceeding ~.
(2.1C) H k is planar.
(2.1D) Hb is 3-colorable, but not
2Ucolorable, and every valid
3-coloring of H k assigns the
same color to every outlet
node.
Given any planar graph G, we show how to
construct a planar graph G', using node
substitutes, which has maximum degree I~
and which is 3-colorable if and only if G
is 3-colorable.
Fix a planar embedding of G and arbitrari-
ly index the nodes of G which have degree
exceeding 4 as Vl,Vo,...,v r. We construct
a sequence of graph~ G = G~,G~, ,G = G'
i "'" r
as follows: G i is constructed from Gi_ I.
2 2 3 4
(A) (B)
Figure I. Hode substitutes H 3 and H 5
53

<!-- pdf-page: 8 -->
Let d be the degree of v~ in Gi_ I and
let {u_,v.],[u2,v.], ,~Ud,Vi] be the % ...
edges ineldent with vi, taken in clock-
wise order. To form Gi, delete node v i
from Gi_l, replacing it with a copy of
H~, and replace each edge [ui,vi] by an
ecge joining ui to outlet j ~f the node
substitute.
It follows from the construction and
previously stated facts that, for
0 < k < r, G k is planar, G k has r-k
no~es ~ith degree exceeding )~, and G k
is 3-colorable if and only if G is 3-
colorable. Thus, G' : G r satisfies all
the required properties, completing the
proof.
Theorem 2.2. UNDIRECTED HAMILTONIAN
CIRCUIT ~ UNDIRECTED HAMILTONIAN CIRCUIT
WITH VERTEX DEGREE AT MOST 3
Proof. This construction will also use a
"node substitute," which is formed from
a special graph, called a fan. The one-
outlet fan F I consists simply of a sin--
gle node. The single node, labelled
Uq I, is both the inlet and the outlet
• T .... or PI. _nductively, assume we have
defiffed the k-outlet fan Fk, k > i, with
inlet U I i and outlets U~ I through
U~ ~. T~e (k+l)-outlet ~&n Fk+ I is
fb£Red from F k by adding the following
nodes and edges:
Nodes: Uk+l,i, i <_ i <_ k + i; Sk+l,i,
i< i<k+l.
Edges: [Uk, i,Sk+l,i] , i <_ i < k;
[Uk+l,i,Sk+l,i], 1 <_ i <_ k + i;
[Uk+l,i+l,Sk+l,i], i <_ i <__ k;
[ Sk+l,k+l'Uk+l, i ] "
The inlet of Fk+ I is UI, I and its outle~
are Uw~ l I through U Figure 2 _, k+l,k+l"
shows Pi,92, and F 3.
It is easy to prove by induction that the
following facts hold for all k > i:
(2.2A) F k contains k 2 + k - i nodes,
none with degree exceeding 3.
(2.2B) Fb has one inlet node of degree
1-and k outlet nodes, none with
degree exceeding 2.
(2.2C) For any outlet node of Fw, there
exists a path from the inlet to
that outlet which includes each
node of F k exactly once.
One more property of F~ will be required
and, since its proof iZ not quite as
straightforward, we present it as a lemma.
Lemma 2.2.1. Suppose a graph G contains
a subgraph H isomorphic to Fk• k ~ i, in
such a way that
(i) no two nodes of H are adjacent in
G unless the corresponding nodes
of F~ are adjacent• and
(ii) any ~ode of H which is adjacent to
a node of G not belonging to H
corresponds to either an inlet or
outlet node of F k.
Then, any Hamiltonian circuit of G con-
tains a path from the "inlet" of H to
some "outlet" of H, consisting precisely
of all the nodes of H.
Proof of Lemma. The Lemma holds
trivially for k = i. Suppose it holds
for F k i, k > i, and consider a graph G
which ~ontains a subgraph H isomorphic to
Fk in the specified manner, and which
contains a Hamiltonian circuit C. We con-
sider the nodes of H as being labelled
identically with the corresponding nodes
of F~. Observe that H, and hence G, con-
tain~ a subgraph H' isomorphic to Fk_ I
which has inlet node U I i and which
satisfies the two conditions of the
Lemma. By the induction hypothesis, C
contains a path from U1 1 to some U k i "
which includes precisei# the nodes - 'J
belonging to H'. The node Uk_ I j and the
remaining nodes of H are shown ~n Fig. 3.
U1,1
tl
{ 'ho~ $2,2
U2,2 U1,1
• I ~ $2' t
U2, 1
U1,1
~C]i S 3, 3
~oS2, 2 U
I ~ U2, 3, 3 2 - S3, 2
e I ] S3' 1
U3, 1
F~ F2 F3
Figure 2. Fans FI, F2, and F 3
54

<!-- pdf-page: 9 -->
Uk,1 Sk, 1
Uk-1, j
--0-- ' • .... --0 • D
Uk, j Sk, j Uk, j+l Uk,k Sk,k
Figure 3. Remaining nodes of H
Consider the set T of nodes of the form
Uv i and S~ ~, i < i < k. By the con-
s~guction ~f~F k aid t~e assumptions on H,
there are only two ways by which the
nodes of T can be accessed by circuit C:
(a) From nodes of G not in H via an
outlet U- •
K
From an od~let U- ~ • of H' via (b)
~- i.,l •
the corresponding ~k,i"
Since C contains a path from U I to
U~ i . which uses all the node~'~f H',
t~e 6~ly way that (b) can occur is via
the edge [Uk_ 1 4,S k ~]. Using this edge,
the path from ~ ~ £~ U, ~ . can be
i ~-i,J .
extended to a pat~ from U~ ~ to either I% or
• . . I ~ ~,j
Uk ~+i consisting preclse~ of th_ nodes
bei6nging to H. If this is not what
occurs in C, then either that edge is not
used, or it is used and C exits from the
set of nodes T before all nodes of T have
been covered. In either case, a non-zero
and equal number of U-type and S-type
nodes from T will remain to be covered by
subsequent visits of the Hamiltonian cir-
cuit to the set T. However each such
visit of T by C must both enter and leave
via U-type node, and hence must use one
more U-type node than S-type node. Thus,
not all the S-type nodes could be covered
by C, contradicting the fact that C is a
Hamiltonian circuit. Therefore, C must
contain a path from U 1 I to some outlet
Uk i consisting preci~@ly of all the
no~es of H, as claimed. The Lemma fol-
lows by induction.~
Given a graph G = (N,A), we now show how
to construct a graph G' = (N',A~), having
maximum node degree 3, such that G' con-
tains a Hamiltonian circuit if and only
if G does.
Let N = [Vl,V 2 ..... Vn] where n = INf.
Let D n denote the double-fan formed by
joining two copies of F n with an edge
connecting their inlet nodes. The out-
let nodes of one of the copies of F n are
the inlet nodes for Dn, and the outlet
nodes of the other are the outlet nodes
of D_ For each node v. in N, the graph
Sr ~° contains a copy Dn(i ~ of D n. The
inlets of Dn(i ) will be denoted by
vl(i),v2(i ) ..... Vn(i ) and its outlets by
ul(i),u2(i), ,un(i ). The specification
of G' is completed by including in G',
for each edge [vl,vi]eA the two edges
[uj(i),vi(J) ] an~ [~i(Ji,vj(i)].
The following useful properties of
double-fans D n are immediate consequences
of the corresponding properties for Fn:
(2.2a) D n contains 2(n2+n-l) nodes,
none with degree exceeding 3.
(2.2b) The n inlet nodes and n outlet
nodes of D each have degree not
exceeding ~.
2.2c) For each outlet and each inlet
of D_, there is a path between
them which includes every node
of D n exactly once.
2.2d) Suppose an undirected graph G
contains a subgraph H isomorphic
to D n in the manner specified in
Lemma 2.2.1. Then every
Hamiltonian circuit of G con-
tains a path from an "inlet" of
H to an "outlet" of H, contain-
ing precisely all the nodes of H.
Observe that G' has maximum degree 3,
since each inlet or outlet of a Dn(i ) has
at most one edge joining it to a node not
belonging to Dn(i), using properties
(2.2a) and (2.2b).
Suppose G' has a Hamiltonian circuit C,
i.e., an ordering of the nodes as
YT,Y2, .... Ym, where m = INrl, such that
f6r all j, i < j < m, [y~,y._~]~A' and
such that [y_~y~]c--A'. W$ m~massume with-
m ± .
out loss of generality that Y7 and Ym do
not belong to the same double'fan Dn~i ).
Thus, by construction of G', one of Yl,Ym
must be an inlet of some fan Dn(i ) an~ t~e
other must be an outlet of anoZher fan
Dn(j). Since G' is an undirected graph,
we may assume that Yl is an inlet of some
fan D_(i). Then, by-(2.2d), C determines
an ordering Dn(il),Dnli2) ..... Dn(in) of
the double-fans such that all the nodes
of Dn(ik) precede all the nodes of Dn(i. )
in C whenever i < k < j < n. But the J
construction of G' impli[s that
vil,vio,...,Vin must then be a Hamiltonian
circuit of G. (Notice that this argument
55

<!-- pdf-page: 10 -->
fails when n = 2, however, in this case
we may let G' = G.)
Conversely, suppose vi~,vio,._.,Vin is a
Hamiltonian circuit C 6f G? By construc-
tion of G some outlet of Dn(i~ ) must be
connected to some inlet of Dn@i~+~,, in
G', for i < j < n, and similarl9 ~or
Dn(in) and--Dn(il). It is then a simple
matter to construct a Hamiltonian cir-
cuit in G' using (2.2c).
Therefore, we have shown that G' con-
tains a Hamiltonian circuit if and only
if G does, completing the proof of
Theorem 2.2.I
Theorem 2.3: EXACT COVER ~ PLANAR
D-J~MILTONIAN PATH.
Proof: Given any collection S of sets,
we must construct a planar directed
graph G which has a Hamiltonian path if
and only if S contains an exact cover.
We first introduce some terminology.
Let G = (N,A) be a directed graph with
nodes Pl,Po,-..Pm. The edges in A are
ordered pa~rs <Pi,Pj>" We will call Pi
and pjadjacent whenever either
<Pi,p~eA or <,pi,Pi>eA. Any Hamiltonian
path ~H-path) of G can be identified
with a s--~g pj (l~Pi(2],. ~..pi(-) ~ _°f nodes
such that n = m~<' t P4filJ \PI(ii, and
Pi(j+l)>CA forJ~l i ! ~ < m.
Let N* denote the set of all finite
strings of elements from N. A partial
H-path oJ for G is an element of N* which
is a ~refix of some H-path for G. For
any partial H-path ~ for G, ~eN* is a
k-extension of ~ if the length of • is k
and m~ is a partial H-path for G.
For any string ~ = blbp...bkeN* , we say
that yeN belongs to ~ if and only if
v = b i for some i,i---< i < k, and <u,v>eA
belongs to ~ if and ~nly--if u = b i and
v = bi+ I for some i, I <_ i < k.
Now suppose we are given a collection
S = [SI,S 2 ..... Sn] of sets with ~ S i 5=1
= '1 = (Ul, U2, .... u~:. ,The planar
directed graph G ~,~,A) is specified
as follows:
The set N of nodes, which depends on'ly
on n and t, is
N = [bi,j,ci, j: i < i i n, i <__ j < t]
~ [a. .: 0 < i < n + I, i < j < t] l,O ....
LO [Yi,j: 0 <__ i <_ n, i <_ j <_ t]
k9 [di,ei,fi: i < i <_ n] t_) [fn+l].
The set of edges is made up of two parts,
A : A] L_)Ao, the first of which depends
only Dn n Znd t and forms a skeleton for
G (see Figure 4):
A I = <ao,j,Y0,j>, <Yn, j,an+l,j>: l<j<t]
L3 [<Y0,j~a0, j+l> ' <an+l,j,Yn+l,j+l> :
l<j<t-l]
U <Yo,t,fl ~' <fn+l'yn,l ~]
< fi' di>' < fi' el>' < di' fi+l>"
<ei,fi+l>, <di,ai,l>, <ai,l,di>,
<ei,ci,t) , <ci,t,ei>: l<i<n]
< ci, j,ai,j+l>, <ai,j+l,Ci,j> :
l<i<n,l<j<t-l}.
The remaining edges in A = A ~A
connect, for each i and j, ±i\ ~ ~ n,
I < j < t, certain nodes from
[a~ ",~i -,c- .y- - .,y- .], depending on
whe~er 6~ n~t0u~-@$1on~Jto S i. If
u. ~ S~, then A~Ucontains the eight edges
s~own in Fig. 5~. If u~ e S~, then Ao
contains the seven edge~ sho~n in
Fig. 5B.
This completes the description of G. The
reader should observe from Figs. 4 and 5
that G is planar.
Informally, the relationship between G
and the covering problem is as follows.
Suppose that we are building an H-path
for G, in step-by-step fashion, and, at
the same time, generating an exact cover
for U. Clearly, the H-path must begin
with a n I,Yo 1,an o,Yn o,...,ao t,Yn ,,
f]. F~eac~k,~l~< ~'< n, at the ~@p
t~e H-path reaches Z~, We choose edge
<f,.,ek> if S,. is to ~e included in the
coger, and e~ge <f~,dk> if it is not to
be included. We t~en proceed left (right)
along the a k ~,b- .,c. line of the ,J K K " graph, exiting fr$~ dk($k) , and finally
arriving at fk+1" Helping us in the
--- t choice of which direction to travel tha
line is the fact that the nodes Y~_]
i < j < t, "remember" which eleme~t~'~f U
ha~e b~en covered by previously selected
sets. Specifically, Yk-i ~ has already
been visited by the parti$~ H-path if and
only if element u. has not been covered
yet. Note that, ~hen w~ ~re about to
make our first choice, at fl, all nodes
YO . are already in the path and no ele-
mefl~ from U has been covered. When we
reach fn+l, after having made a decision
for each set Sk, none of the y . can have
been visited by the partial H-~&@h (or it
could not be extended to an H-path), so
all elements of U have been covered by the
56

<!-- pdf-page: 11 -->
C
C
~.o, • . . i
/ \./\./
-t~ f''u . . • ~'~. • .~--~.- .... .,#r-'--" •
,, "~.~. • ~. • ~ ~ ~.v"
J
4b~ --0 .... Q (~--- • • •
&z &~ I~%~ c~o .~%~ ~ C~.~ 8~.~ ~z,+. c~ e z
• • • q~ • ~ • -. • • O( •
a~|a,~,l %,i c,,,i a~,~. b',,,., c.,,.+.
L
~÷1
• q~ b~ c~,~
~j/ "",jl, o
~1 ~,1 ~"t.-I a..,~h,, t
J
en
Figure 4. The Skeleton of G.
CA) \ ,,'~
ci.,3 ai,~ • . ci,~
" Jt~3 B
Figure 5. Edges in A 2
57

<!-- pdf-page: 12 -->
selected sets. The edges of Ap force the
transmission of information from one row
of Yk ~ nodes to the next, and also pre-
vent £~t S~ from being chosen whenever
any of its-members has already been
covered. This latter property insures
that the sets in the cover are disjoint,
as required by EXACT COVER.
The following Lemma-shows how the edges in
A 2 force the desired paths, by giving the
relevant oroperties of Figs. 5A and 5B.
Figures 6A and 6B show all edges of G
which are incident with nodes of interest.
Lemma 2.3.1: Fix i and j, i < i < n,
1 < j <_ t. Let x = d i if j =--i a~d
x = c i . i otherwise; x I = e i if J n and
x I = a~-+l otherwise. Let co be
partiam J-path of G satisfying: any
(i) every yeN - [a. .,b~ ..,c. .] l,J , 1 J adjacent to Yi-l,j ~e~ong~ to co,
and
(ii) None of ai•j,bi,j,ci, j belongs to
co.
Then the following hold:
Case i. uj~S i (Figure 6A)
(IL) if • = coxa i ~ is a partial H-path
of G, the o~Yy possible 4-exten-
.x t and sions of T are bi,jYi_l, jCi, j
b. "Yi .c. .x' .
(IR) I~'@ ='~x~'~ ~ is a partial
H-path of G,-tNe only possible
%-extensions of • are
bi,jYi_l, jai,jx and bi,jYi,jai,jx.
Case 2. uieS i (Figure 6B)
2R If • = o~x'c, i is a partial
H-path of G,~'the only possible
3-extension of • is bi,jai,jx.
Proof of Lemma: (Case IL) Let 7 be an
H-path with prefix T. The last node of
7 must be a .... . The only possible
iI~" • O
4-extension o~ • which has been excluded
is b i ~y. .vv, where v ~ c- .. But then
c.. @gula0have to be the ~t node of 7, i smf~@e properties (i) and (ii) of co
x,<-'Y" . x'
ai,] <!/bi'j ci,j
insure that <x,,c i .> belongs to 7; that
is, c. • does not ~$t belong to the H-path
and t~@Jonly way that path can reach c. .
is through x'. This contradiction pro~@~
(iS).
The other eases follow similarly.|
Using Lemma 2.3.1 and our informal
description of the correspondence between
H-paths and exact covers, the reader
should have no difficulty in verifying
that G has an H-path whenever S contains
an exact cover. To complete the proof of
Theorem 2.3, we must show the converse.
Suppose that G has an H-path 7. Let
T = [kl <fk,ek> belongs to Z]. We shall
show that S' = [Skl keT] forms an exact
cover for U. Define the partial unions
U o : ~ and U k : l~<k Si• 1 ! k ! n.
leT
Then we have the following:
Lemma 2.3.2: For each k, 1 < k < n + i,
if co(N* and cofk is a partial--H-p~th of G,
then
(i) None of {ai,~,b- .,c~ ~,d~,eJ :
k<i<n, ~<j<t~ bel~ng t~ co,
(ii) ATl-of 1[~--~,b~ ~,c. .,d.,e. •
. ~ • i i i"
l<l<k-l, i<J<t} 6eloh~ to co,
(iii) For each j, 1 < j < t• Y~Yi{]'J
belongs to co i~ an~ on uj~Uk_ ~ (iv) If there exists j such that
ulcUw_lfh Sk, then dv is the only
iZexZensi°n-°f cofk"
Proof of Lemma. The proof is by induction.
The basis k=l is immediate since any H-path
y f . must begin with a 0 ~YO~laO,2~..ao ~n~i~e~y The induction step'zoilows almost'
by Lemma 2.3.1. The only other possibility
is that cofv might be extended by d k f~+l
(or by ek ~k.~). But then an argumen~
similar ~o Z~$ proof of Lemma 2.3.1 shows
that e k (respectively dk) must be the last
node oT the H-path• which is impossible.~
It is now clear that [SwIkeT ] is an exact
Figure 6. Cases for Lemma 2.3.1
58

<!-- pdf-page: 13 -->
cover for U! Since any H-path must have
the form ~fn ly n i a +- -Yn -a +I ....
Yn tan+l t' ~emmd 2.~.~'~imi~ ~or'{=n+l
in{ures t~at <9~ S~ = U = U, and (iv)
%nsures the dmsjolntness of the sets in
~ne cover. This completes the proof of
Theorem 2.3.2. I
Observe that the directed graph G con-
structed in the proof need not have
arbitrarily large degree, in fact, no
node has in-degree exceeding 3 or out-
degree exceeding 4. It is not known,
however, whether these are the strongest
possible degree constraints for which
PLANAR DIRECTED HAMILTONIAN PATH remains
NP-complete.
Theorem 2.4: SAT3 ~ NODE COVER WITH
~YO~~ AT MOST 3.
Proof. Suppose we are given a set
U--/-TC],C O ..... Cn] of disjunctive
clauseZ, ~ach containing no more than 3
literals. As in the proof of Theorem
i.i, we may assume that each clause
contains exactly 3 literals, possibly
with duplication. Index the literals
occurring in clause C h as ah,l,a h 2'
and a h ~, i < h < p. Let xl,xo,.~.,x~
denote'~he va--ria[les occurrlng~in the~p
clauses, and for each i, 1 < i < n, let
m(i) denote the number of o~curTences of
variable x i (as literal x~ or literal
xi) in the clauses. Arbitrarily index
t~e m(i) occurrences of variable x i as
occurrence i, occurrence 2,..., occurr-
ence m(i). We shall construct a graph
G, having node degree at most 3, and
give an integer k > O, such that C is
satisfiable if and only if G has a node
cover of size k.
We describe the graph G : (N,A) in
several steps. First, for each variable
x., we have a subgraph H. = (N.,A.), a 1 ' ' i i i simple circuit with l N.I = IAil = 2m(i),
as shown in Fig. 7. O~serve the alter-
nate labelling of the nodes. For each
clause Ch, we have a subgraph
H~ = (Nh,Ah) where Nh = [Vh, l,Vh,2,Vh,3]
and A~ consists of an edge joining each
pair of nodes belonging to N h. The
remaining edges, which each join a node
from some set N. to a node from some set
Nh, are as foll~ws:
B I : [[Ti,j,Vs,t]: as, t = x i is the jth
occurrence of variable
x i in C]
and
B2 = [[Fi,j'Vs,t]: as,t = xi is the jth
occurrence of
variable x i in
C].
The graph G = (N,A i is defined by:
P
N : ~ NiQJ h<9=l Nh , i=l
A= AiU C  BIUB 2.
i=l h=l
Observe that every node of G has degree
at most 3. We show that the set C of
clauses is satisfiable if and only if G
has a node cover of size 5P.
The following properties of the subgraphs
H i are easy to verify:
(2.4A) There exists a node cover for
~i containing m(i) nodes,
including all nodes T. • and no
nodes F. . There al~6Jexists i " such a n6~e cover which includes
all nodes F. . and no nodes
T. i,j i,j"
(2.~B) No node cover for H i contains
fewer than m(i) nodes, and
every node cover for H i which
includes both a node F i . and a
node T. _ must contain ~@re than
m(i) n~d~s.
Now, suppose we are given a truth
assignment to the n variables which satis-
fies the set C of clauses. The corres-
ponding node cover S contains the follow-
ing nodes:
(i] for each variable x~ which is set T, . ± "true the cover of m(1) nodes for H i
which includes all T i ~.
(ii) For each varia6~e x i which is set
"false," the cover of m(i) nodes for H i
which includes all F. l,j"
C • •
Ti, 1 Fi, 1 Ti, 2 Fi,2 Ti,m(i) Fi, re(i)
Figure 7. A Subgraph H i
59

<!-- pdf-page: 14 -->
(iii) For each clause C h, all the nodes
of Nh except some one of-them V- • such
that literal a h . is true for t~i{ truth
assignment (at lSast one such literal
exists since the clause is satisfied).
Clearly, these nodes cover all of the
edges belonging to the sets A~, i < i < n,
and AI~ , i < h < p. Each edge~[Ti 7, VsTt ]
in B~ is a~so ~overed since eitheg~V~ t
belongs to S or a = x. is true an
T. . belongs to S~'tSimi~arly, each edge
i~'~ o is covered by S. Thus, S is a node
coveg. Furthermore, the number of nodes
in S is
Now for each i,j, 0 < i,j < 2, let c[i,j]
be the minimum cardi~ality--for all node
covers C of H obeying
I [V1,V{] ~h C I = i and I[V2,V2] (-'/ C I = j.
Observe that, by symmetry, when i or j
equals i, the value of c[i,j] is indepen-
dent of which element of the corresponding
pair is i~. Table II gives the values
of c[i,j]. We leave to the reader the
straightforward but tedious verification
of the entries.
n
2p + >. (m(i)) = 2p + 3P = 5P,
i=l
a.s required.
Conversely, suppose we have a node cover
S for G such that ISt = 5P. S must con-
tain at least two nodes from each N h in
order to cover the edges in Ah, for a
total of at least 2p such nodes.
Similarly, by (2.4B) S must contain at
least ~ (m(i)) = 3P nodes from the N i.
i=l
Hence S must contain exactly 2 nodes from
each N', and exactly ~des from each
N i. T~us by ~-A~-and (2.4B), S must
contain, from each N_., either all the
T. • nodes and none Sf the F~ ~. nodes, i, ±,d or ~ii the F. . nodes and none of the
T i ~ nodes, iA3consistent truth assign-
me~ can be obtained by setting xl
"true" if S contains all the T.. ,.-nodes,
and setting x_. "false" otherwi~& d. The
reader may verify that, because of the
edges in B I and B2, this truth setting
satisfies %he set C of clauses.~
Remark. Theorem 2.4 was obtained
~ndently by Peter Herrmann [H73].
Theorem 2.5: NODE COVER ~ PLANAR NODE
UDVE~
Proof. The key structure used in this
p~ is the graph H pictured in Fig. 8,
which will b e called a crossover, with
outlets Vl,Vl, V2, and v2, as labelled.
j� 0 i 2
0 13 14 15
1 13 13 14
2 14 14 15
TABLE II. Values of c[i,j].
From the table, we observe that the
following properties hold:
(2.5A) For 0 ~ j S 2, c[l,j] - c[0,j]
< i and c[j~l] - e[jfO] < O.
(2.5B) For 0 ! J ! 2, c[2,j] - c[l,j] =
c[j,2] - c[j,1] = 1
Given a graph G = (N,A) we construct a
planar graph G' (NJ,A ') using these
crossovers as follows:
(i) Draw G in the plane, allowing
edges to cross each other.
(ii) Replace each crossing by a copy of
H, as-shown in Fig. 9.
The crossovers which replace crossings on
the edge [x,y] will be called crossovers
on the x-y line. The edges connecting
~Tf~ese crossovers to each other and to x
and y will be called edges on the x-y line.
The endpoints of these edges will be
called the nodes on the x-y line. Such
nodes which are aT~o crossover outlets
will be called the x-y outlets of their
crossover. The one which is nearest x
will be the crossover's y outlet, the one
nearest y its x outlet, fo~ cross-
~ over on the x-~ TT~.
~i Va"
v;
Figure 8. Crossover H.
60

<!-- pdf-page: 15 -->
/i \
Jy
BEFORE (G) AFTER (G')
Figure 9. Construction of G" (only outlets of crossovers shown).
Let d be the number of copies of H used
in constructing G'. Observe that the
edges of G" can be partitioned into two
sets: line edges, those which are on
the x-y line for some [x,y]¢A, and cross-
over edges, those which are part of one
o~' the d crossovers. All the edges on
the x-y line can be covered by taking
either x and all the x-outlets of cross-
overs on the line, or y and all the y
outlets. The edges in the crossovers
can only be covered by crossover nodes.
Now, since in G ~ each edge-crossing of
the planar representation of G has been
replaced by a planar graph which itself
contains no crossings, G t is planar. More-
over, the size of G t is clearly at most a
polynomial in the size of G. The proof
of the Theorem will thus be concluded
by showing that, for any k, G has a node
cover of size k if and only if G" has a
node cover of size k + 13d.
Suppose there is a node cover S of G =
(N,A) with lSl = k. We construct a node
cover of G" from S as follows. For each
edge [x,y]eA, let f(x,y) be an endpoint
of that edge which is in S. Then define
S" = [v:v is the f(x,y) outlet for a
crossover on the x-y line for
some [x,y]eA].
Since S is a node cover for G, f is
defined for all edges in A, and so S<3S"
covers all the line edges of G". More-
over, since each crossover is on two
lines in G', S" contains exactly two
outlets for each crossover, one from each
outlet pair, and so I S'I = 2d. All that
remains is to cover the as yet uncovered
crossover edges. For these, observe
from Table II that any set which con-
tains two nodes from a crossover, one
from each outlet pair, can be extended,
by adding ii of the crossover's internal
nodes, to form a node cover of the cross-
over made up of c[l,l] = 13 nodes. Let
S" be the set containing, for each
crossover, and 11 additional nodes needed
to extend S" to a node cover for that
crossover. Thus S<9 S' <9 S,, is a node
cover of G' having k + 2d + lid : k + 13d
nodes.
Conversely, suppose there is a node cover
of G having k + 13d nodes. Let
K* = min[[ S I : S is a node cover of G'],
and
M = IS: S is a node cover of G" and
ISI = k*]
For each S~M, define
~(S) = I [xeS: x is an outlet node for some
crossover in G']I ,
m* : min[m(S): SEMI,
and let S*eM be some node cover with
m(S*) = m *. Since S* must contain 13
nodes from each of the crossovers in
order for it to cover all the crossover
edges (see Table II), we know that
I S*(~ N I < k. we conclude our proof by
showing t~at S = S*(-~ N is a node cover
of G.
Suppose it is not. Then there exists
some [x,y]eA such that S(-~[x,y] : ~ and
hence S*~[x,y] = @. Let the number of
crossovers on the x-y line be £. Then
there are £ + i edges on the x-y line,
and hence at least £ + i of the nodes on
the line must be in S*, and since neither
x or y is, all £ + i must be outlets. If
we let n(i) be the number of crossovers
on the x-y line with i of their x-y out-
lets in S*, we thus have n(2)-n(O) ~ i.
We shall show that this leads to a contra-
diction.
Let X i be the set of nodes in the i th
crossover on the x-y line, 1 < i < £, and
let S i = X~(~ S*. Let TiC X~ be--a node
cover of t~e crossover coh-%-~ihing its x
outlet (but not the y outlet) and the same
non x-y outlets as does Si, and has mini-
mum cardinality for such node eovers. For
each i, let r(i) be the number of x-y
61

<!-- pdf-page: 16 -->
outlets of the i th crossover which are in
S*. Then we have, by (2.5A) and (2.5B)
r(i) = 0 implies Til <_I S i I + i,
r(i) = I implies Ti I <__I Si I , and
r(i) = 2 implies Ti I i l Sil - i.
Let T = k9 Ti, S = 6 S i. Since
i=l i=l
n(2)-n(O) > i we have by the above that
I TI <I sl - 1
Moreover, T contains at least one fewer
x-y outlet than does S, and exactly the
same number of non-x-y outlets. Further-
more, T ~9[x] will cover all the line
edges that S did, and so T* = (S*-S)
~9 T ~-J[x] is a node cover of G with
[ T~I =I S* -I Sl +I TI + 1 <I S*I = k*,
and
m(T*) = m(S* - 1 = m* - 1,
contradicting the definition of m*. Thus
S* k_J N is a node cover of G and the
theo rem--fs proved.~
Notice that, if the graph G given as
input for NODE COVER has no node degree
exceeding 3, the graph G" constructed in
the proof as input for PLANAR NODE COVER
will have no node degree exceeding 6.
This implies that PLANAR NODE COVER WITH
NODE DEGREE AT MOST 6 is NP-complete. It
is not known whether this degree bound is
best possible.
III. Concluding Remarks
We have seen that a number of graph-
theoretic NP-complete problems remain
NP-complete when the structure of the
allowed inputs is substantially restric-
ted. Similar questions can be asked for
restricted versions of other NP-complete
problems. For example, it is not yet
known whether STEINER TREE [K72] for
planar graphs or multiprocessor scheduling
with 3 processors, unit time tasks, and
an arbitrary partial order [U73] are NP-
complete. The open status of UNDIRECTED
HAMILTONIAN CIRCUIT for planar graphs has
been mentioned previously.
In examining such problems, it is impor-
tant to keep in mind that two types of
results are possible. Not only is it
important to find simple subcases which
are still NP-complete, but it is also
important to find large subdomains for
which the problem can be solved in poly-
nomial time. We have given one example
in this latter direction, the case of MAX
CUT for planar graphs. Other recent
papers [E72,Gav72,Gav73] have shown ~hat
CLIQUE and CHROMATIC NUMBER can be solved
in polynomial time for "transitively
orientable" graphs, "chordal" graphs, and
"circle" graphs.
Both types of results should prove useful
to designers of practical combinatorial
algorithms.
APPENDIX: Definitions of Polynomial
Complete Problems
SATISFIABILITY WITH AT MOST 3 LITERALS PER
CLAUSE .(SAT3) [K72]
INPUT: Set of clauses C = fCI, C2, .... C-} ~n
variables x~,x-, ,x-, @ach cl[use • l .~ "': n belng the dlsounctlon of 3 or fewer
literals, where a literal is either
a variable x i or its negation xi"
PROPERTY: There is a truth assignment to
the variables which simUltan-
eously satisfies all the clauses
in C (a clause is satisfied if
any one of its disjuncts is x i
for some "true" variable xi, or
Z. for some "false" xj).
CLIQUE [K721
INPUT: GRAPH G = (N,A), positive integer k
PROPERTY: G has a clique of size greater
than or equal to k, i.e., a set
N" C N with I N" J > k and such
that for all nl,n~N" ,_ [nl,n2]¢A.
EXACT COVER [K72]
INPUT: Collection of sets S = [SI,$2,... ,
S n ]
PROPERTY: S has an exact cover, i.e., a
subcollection S" ~ S suc h that
and for U S i : O S~, all
S]eS" i=l
Si, SjeS', Sifh Sj : 9.
GRAPH 3-COLORABILITY [St73]
INPUT: Graph G = (N,A)
PROPERTY: G has a legal 3-coloring of its
nodes i.e., there is a map
f: N ~ [1,2,3] such that
[nl,n2]cA implies f(nl) ~ f(n2).
UNDIRECTED (DIRECTED) HAMILTONIAN PATH
(CIRCUIT) [ K72 ]
INPUT: Graph G = (N,A). (Directed graph
0 = (N,A)).
PROPERTY: G has a Hamiltonian path
(circuit), i.e., an ordering of
the nodes = in ,n,, .... n I N I ]
such that ~or ~ i~< I NI ,
[ni,n~±1]eA ~n~n~7>eA ), and
{in th@~circuit-ca~@-only)
Ln I N I 'nl]eA ~nl N I 'nl)eA)"
NODE COVER [K72]
INPUT: Graph G = (N,A), positive integer k.
PROPERTY: G has a node cover of size less
than-or equal to k, i.e., a sub-
set N'C N with IN'I< k and such
62

<!-- pdf-page: 17 -->
that for all (x,y]cA, (x,y]gh N" ~ ~.
REFERENCES
A73.
B41.
C71.
E70.
D. Adolphson and T. C. Hu, KT0.
"Optimal Linear Ordering," SIAM J.
Applied Math. 25 (1973), 403-423.
R. L. Brooks, "On Coloring the
Nodes of a Network," Proc. Cambridge L73.
Philos. Soc., 37 (1941), 194-197.
S. A. Cook, "The Complexity of
Theorem-Proving Procedures," STOC
(1971), 151-158. 072.
J. Edmonds and E. L. Johnson,
"Matching: A Well-Solved Class of
Integer Linear Programs," Combi~&-
torial Structures and Their Sa72.
Applications, Gordon and Breach
(1970), 89-92.
E72. S. Even, A. Lempel, and A. Pnueli,
"Permutation Graphs and Transitive
Graphs," JACM 19 (1972), 400-410.
Ga72. M. R. Garey, R. L. Graham, J. D.
Ullman, "Worst-Case Analysis of
Memory Allocation Algorithms,"
STOC (1972), 143-150.
G&v72. F. Gavril, "Algorithms for Minimum
Coloring, Maximum Clique, Minimum
Covering by Cliques, and Maximum
Independent set of a Chordal Graph,"
SIAM J. Computing i (1972), 180-
187.
Gay73.
Gr72.
F. Gavril, "Algorithms for a Maxi-
mum Clique and a M~ximum Indepen-
dent Set of ~Circle Graph,"
Networks 3 (1973), 261-273.
R. L. Graham, "Bounds on Multipro-
cessing Anomalies and Related
Packing Algorithms," SJCC (1972),
205-217.
H73.
Jo72.
Jo73.
K72.
P. Herrmann, Reducibility among
Combinatorial Problems, Masters
Thesis, Massachusetts Institute of
Technology (1973).
D. S. Johnson, 'Fast Allocation
Algorithms," SWAT (1972), 144-154.
D. S. Johnson, "Approximation
Algorithms for Combinatorial Prob-
lems," STOC (1973), 38-49.
R. M. Karp, "Reducibility Among
Combinatorial Problems," Complexity
of Computer Computations, R. E.
Miller and J. W. Thatcher, eds.,
Plenum Press, New York (1972), 85-
lO4.
Sa73.
Se73.
St73.
U73.
B. W. Kernighan and S. Lin, "An
Efficient Heuristic For Partition-
ing Graphs," BSTJ 49 (1970), 291-
308.
S. Lin and B. W. Kernighan, "An
Effective Heuristic Algorithm for
the Traveling-Salesman Problem,"
BSTJ 21 (1973), 498-516.
G. I. Orlova and Y. G. Dorfman,
"Finding the Maximum Cut in a
Graph, ' Eng. Cybernetics I0 (1972),
502-506.
S. Sahni, "Some Related Problems
From Network Flows, Game Theory,
and Integer Programming," SWAT
(1972), 130-138.
S. Sahni, On the Knapsack and Other
Computationally Related Problems,
Doctoral thesis, Cornell University
(1973) •
R. Sethi, "Complete Register Alloca-
tion Problems," STOC (1973), 182-195.
L. Stockmeyer, "Planar 3-Colorabil-
ity is Polynomial Complete," SIGACT
News 5, No. 3 (1973), 19-25.
J. D. Ullman, "Polynomial Complete
Scheduling Problems," 4th Symp. on
Operating System Principles (1973),
96-101.
63
