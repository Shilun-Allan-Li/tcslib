<!-- generated-by: pypdf extraction of the whole paper (EF-H12 ingest of [St73], Seyoon's ruling to ingest the actual proof, 2026-11-19); awaiting Codex source review -->
<!-- source-pdf-sha256: ecfb8ec9f7b38708e0b8486287cfbcce6369b92feffd8abd8201b062829dd287 -->
<!-- extractor: pypdf 6.17.0, extract_text() (default plain mode) under python3 -I, as for GJS74; trailing spaces removed; no control characters were present -->
<!-- scope (physical pages): 1-7, the whole paper (printed SIGACT News pp. 19-25); the .md transcribes all of the text and describes Figures 1-4 -->
<!-- note: physical page p is printed page p+18; the text runs in the order of printed pp. 19, 22, 21, 20, 23 (physical 1, 4, 3, 2, 5): printed pp. 20 and 22 are interchanged in the issue, while the running heads are in sequence; the figures are on pp. 24-25 -->
<!-- note: the text layer is OCR of a scanned typescript and keeps its recognition errors (e.g. 'July 1923' for 'July 1973', 'o~' for the reduction sign, 'I.'/'[I]' for '1.'/'[1]', and figure labels scattered as text); the .md was checked against the page images, not this layer -->

<!-- pdf-page: 1 -->
SIGACT News 19 July 1923
PLANAR 3-COLORABILITY IS POLYNOMIAL COMPLETE t
Larry Stockmeyer
Massachusetts Institute of Technology
Cambridge, Massachusetts
March 1973
The general problem of recognizing the set of pairs (G,k), where
k is a positive integer and G is a graph which is k-colorable, is
polynomial complete as defined by Karp [I]. It is shown here that this
problem is still complete even for pairs (G,k) where k = 3 and G is a
planar graph. We assume that the reader is familiar with the definitions
and notation of [1].
The problems to be considered are the following.
3-COLORABILITY
INPUT: Gra~.h G with nodes N and arcs A.
PROPERTY: There is a function f: N-~ [1,2,3] such that if u, v are
adjacent then f(u) # f(v).
PLANAR 3-COLORABILITY
INPUT: Planar graph G.
PROPERTY: Same as above.
tWork reported here in was supported in part by Project MAC, an M.I.T.
research program sponsored by the Advanced Research Projects Agency,
Department of Defense, under Office of Naval Research Contract Number
N00014-70-A-0362-0006 and theNational Science Foundation under contract
number GJ00-4327. Reproduction in whole or in part is permitted for any
purpose the the United States Government.

<!-- pdf-page: 2 -->
20 July 1973 SIGACT News
2a) Vl,V2,Vl', v2' are nodes of some face of G (for some
embedding of G in the plane) and they appear in that
order as the cycle of edges bounding the face is
traversed in some direction.
!
2b) v I and Wl' are bound and v 2 and v 2 are bound.
A cross-over graph G C is shown in Fig. 2, although it may not be
the simplest example. G C is planar and satisfies condition (2a) by
inspection. To verify that G C is 3-colorable and satisfies (2b), consider
the subgraph G F of G C shown in Fig. 3. Clearly G F is 3-colorable and
u and v are bound. This implies that v 2 and v 2' are bound in G C. We
leave it to the reader to convince himself that if v I and v I' are also
colored the same then a 3-coloration is possible, and if v I and v I' are
colored differently then a 3-coloration is impossible.
Now let G be a given graph with nodes [Ul,...,Un}. A planar graph
G' is constructed such that G' is 3-colorable iff G is 3-colorable. The
nodes of G' include a p(n) by n array of nodes [vij I i = l,...,p(n),
j = l,...,nl, for some polynomial p(n) _< 0(n2).
G' has the property that for each row i = 2,3,...,p(n), there is a
permutation a.~: II,...,n} -~ II,...,n} such that Vlj and vi,ai(j ) are bound
for all j = l,...,n. Each row [Vil,...,Vin ] of nodes is "connected" to the
next row [Vi+l,l,...,Vi+l,n} by copies of G C and G F. The rows are connected
in such a way that for each arc lUk,U~] in G, there is some row i and some j,

<!-- pdf-page: 3 -->
SIGACT News 21 July 1973
Now G is 3-colorable iff Di,...,D is satisfiable. Suppose G is r
3-colorable and let f: N-~ ~1,2,3} be a coloring. The arc ~tl,t2} ensures
that f(tl) # f(t2) so we may assume that f(tl) = 1 and f(t2) = 2. Now
f(a) E ~2,3} for all literals a E L because of the arcs Itl,a], and
f(ui) # f(ui) for all i because of the arcs lui,ui]. The graphs G i
ensure that no clause contains literals all colored 2. Therefore S =
~a E L I f(a) = 3} is a consistent truth assignment which satisfies Di,...,D r .
The converse is similar. This completes the proof of I).
The proof above can easily be extended to show that k-eolorability is
complete for any fixed k ~ 3. In particular, let G = (Ni,A I) be any
graph and Km = (N 2,A 2) be the complete graph on m nodes. If G' = (N',A')
is defined as N' = N I U N 2 and A' = A I U A 2 U (lu,v} I u ~ Ni, v ~ N2} ,
then G' is (k+m)-colorable iff G is k-colorable.
2). 3-COLORABILITY o~ PLANAR 3-COLORABILITY
The proof follows from the existence of a "cross-over" graph which
enables one to eliminate cross-overs, thereby converting an arbitrary
graph into a planar graph, while preserving 3-colorability.
We say that two nodes u,v of a given graph G are 3-color bound
(or simply bound) if u and v must be assigned the same color in any
3-coloration of G.
A cross-over graph is defined to be a finite graph G with the
properties that
i) G is planar and 3-colorable.
! !
2) There are four distinct nodes Vl,Vl,V2,V 2 of G such that

<!-- pdf-page: 4 -->
SIGAGT News 22 July 1973
Theorem. 3-COLORABILITY and PLANAR 3-COLORABILITY are polynomial
complete.
Proof. i) SATISFIABILITY WITH AT MOST 3 LITERALS PER CLAUSE o~ 3-
COLORABILITY.
Let Di,D2,...,D r be the clauses and L = (Ul,...,Um, Ul,...,Um] the literals
of a given satisfiability problem. Let D. = r l [~ii,(7i2,~i3 ] c L, i = i,..., .
Consider the graph G with nodes N = [Vl,V2,...,v6] and arcs A shown as
solid lines in Fig. I. Suppose G is connected to nodes Sl,S2,S 3 as shown.
G has the following properties:
i) If Sl,S2,S 3 are constrained to have the same color c, then v 6
,
must be colored c in any 3-coloring of G
ii)
= ,A i Let G i (N.1 ), i = 1,...,r, be r copies of G
If Sl,S2,S3 are constrained to be colors at least two of
which are different, then for all c 6 {1,2,3} there is a
3-coloring of G in which v 6 is colored c.
Let N.l = (Vil'''''vi6]
as in Fig. i. G = (N,A) is the following.
. i
N = [tl,t2] U [Ul,...,Um,Ul,...,u m]
r ,
U U N i .
A = [(tl,t2] } U [[tl,@}la E L] U [[ui,ui] I i = l,...,m] ~[[aij,vij}l
i = l,...,r; j = 1,2,3] U [{t2,vi6 ] 1 i = 1,...,r] U t A~ •
i=l

<!-- pdf-page: 5 -->
SIGACT News 23 July 1973
I ~ j ~ n-l, such that Vlk and vii. are bound and Vl~ and v.l,j+l are bound.
The arc [Uk,U~} in G can be added as the arc [~ij' vi,j+l} in G' without
destroying the planarity of G'.
A careful description of G' is somewhat tedious. Fig. 4 illustrates
how G' is constructed for G = K 5. Copies of G C and G F have been abbreviated
as in Fig. 2 and 3. Numbers written next to nodes indicate the bindings.
All nodes with the same number are bound. The reader should have no
trouble generalizing this construction to an arbitrary non-planar graph G.
G F has been used in the above construction only to simplify the
description of G' Nodes in the array which are bound by a chain of
copies of G F can be merged into a single node while keeping G' planar.
This completes the proof of 2).
It is known that 2-colarability can be checked in polynomial time
for any graph [2] and that k-colorability, k ~ 5, is trivial in the planar
case. The only open question, planar 4-colorability, hinges on the 4 color
conjecture. However, it might be possible to show that any algorithm, A,
which actually produces a 4-coloring of a planar graph input (or states that
none exists if that is the case) is polynomial complete in the sense that
some complete problem becomes deterministic polynomial time recognizable
in the presence of an A subroutine.

<!-- pdf-page: 6 -->
SIGACT News 24 July 1973
References
I.
.
Karp, R.M. Reducibility Among Combinatorial Problems, in Complexity
of Computer Cpmputations, R.E. Miller and J.W. Thatcher, ed.,
Plenum Press, N.Y., 85-104.
Berge, C. The Theor~ of Graphs an___d It__~ Applications, John Wiley and
Sons, N.Y., 1962.
s 2 ~-
I
s 3
.... q
v 2
I
i
I
v 5
v 3
G
Figure i.
V.
I
v 2
G C
Figure 2.
v 2
p
v 1
Vl v 2
Modular
Representation

<!-- pdf-page: 7 -->
SIGACT News 25 July 1973
U
V
Figure 3.
u
Modular
Representation
1 2 3 4 5
Figure 4.
4~
li /
3 4
3 4
4
~5
G'
~5
