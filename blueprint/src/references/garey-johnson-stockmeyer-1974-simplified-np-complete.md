<!-- generated-by: maintainer transcription and summary of the passages used (EF-H12 ingest, ruling EF-H12-R4 A / Q-H12-2 A, 2026-11-19) -->
<!-- source-pdf-sha256: f17c4a237263d340af14431df9a377bed1f5f1c3f9d5a28f7d0d05c1422989bf -->
<!-- validation-status: scoped reference for EF-H12 (3-colourability); awaiting Codex source review -->

# Some Simplified NP-Complete Problems

M. R. Garey, D. S. Johnson (Bell Laboratories) and L. Stockmeyer (MIT), *Proceedings of the
Sixth Annual ACM Symposium on Theory of Computing (STOC '74)*, pp. 47–63, 1974,
doi:10.1145/800119.803884 (tag `GJS74`). The PDF is a 17-page scan of the typescript with an OCR
text layer. Its title page gives the title, the authors and their affiliations. Its pages carry
the printed page numbers 47–63, which match the proceedings page range. It has no running header
or footer, and it does not print the venue, the year or the DOI. Those three are taken from the
uploader's citation and are not confirmed by the PDF. Physical page $p$ is printed page $p+46$.

**Scope (EF-H12, 2026-11-19).** The blocks below cover these pages:

- **Front matter (PDF pp. 1–2, printed pp. 47–48).** The title page, the abstract, the
  introduction (summarised) and the basic definitions (transcribed).
- **3-colourability material (PDF pp. 6–8, printed pp. 52–54, transcribed).**
  - the opening of §II with the statement, attributed to [St73], that GRAPH 3-COLORABILITY is
    NP-complete even for planar graphs;
  - the table of results;
  - Theorem 2.1 (planar 3-colourability with node degree at most 4), with its node substitutes,
    Facts (2.1A)–(2.1D) and the proof.
- **Appendix and references (PDF pp. 16–17, printed pp. 62–63).** The definitions of SAT3 and
  GRAPH 3-COLORABILITY (transcribed), the other definitions (summarised), and the references
  that the colouring material uses (transcribed).
- **One summary block each** for the MAX CUT family (§I, pp. 48–51), optimal linear arrangement
  (p. 51–52), the Hamiltonian path and circuit results (pp. 54–59), the node cover results
  (pp. 59–62) and the concluding remarks (p. 62).

**The paper does not prove that 3-colourability is NP-complete, and it gives no reduction from
SAT3 to 3-colourability.** It attributes the NP-completeness of GRAPH 3-COLORABILITY, even
restricted to planar graphs, to [St73] (Stockmeyer, "Planar 3-Colorability is Polynomial
Complete", SIGACT News 5(3), 1973). Its only colouring reduction is Theorem 2.1, from planar
3-colourability to planar 3-colourability with node degree at most 4.

**Conventions.** Transcribed blocks follow the paper's wording, checked against the page images
rather than the OCR layer. Mathematics is in LaTeX. The paper's reduction sign, typed as a Greek
$\alpha$ (Karp's $\propto$), is written $\mathrel{\alpha}$. Edges $\{u,v\}$ are written with
braces, as in the typescript. Underlined words are written as emphasis. Problem names keep the
paper's capitals. Blocks marked "summary" are the maintainer's condensation. The bold block
labels, and the notes marked *Transcription note* or *Maintainer note*, are not part of the
source.

<a id="pdf-f17c4a237263-p001-b001"></a>
<!-- pdf-source: page=1; block=1; confidence=0.97 -->

**Title page (printed p. 47).** SOME SIMPLIFIED NP-COMPLETE PROBLEMS, by M. R. Garey and
D. S. Johnson, Bell Laboratories, Murray Hill, New Jersey, and L. Stockmeyer$^{\dagger}$,
Massachusetts Institute of Technology, Cambridge, Massachusetts.

$^{\dagger}$ The work of this author was done, in part, at Project MAC, and supported by The
National Science Foundation under research grant GJ-34671.

<a id="pdf-f17c4a237263-p001-b002"></a>
<!-- pdf-source: page=1; block=2; confidence=0.96 -->

**Abstract (printed p. 47).** It is widely believed that showing a problem to be NP-complete is
tantamount to proving its computational intractability. In this paper we show that a number of
NP-complete problems remain NP-complete even when their domains are substantially restricted.
First we show the completeness of SIMPLE MAX CUT (MAX CUT with edge weights restricted to value
1), and, as a corollary, the completeness of the OPTIMAL LINEAR ARRANGEMENT problem. We then show
that even if the domains of the NODE COVER and DIRECTED HAMILTONIAN PATH problems are restricted
to planar graphs, the two problems remain NP-complete, and that these and other graph problems
remain NP-complete even when their domains are restricted to graphs with low node degrees. For
GRAPH 3-COLORABILITY, NODE COVER, and UNDIRECTED HAMILTONIAN CIRCUIT, we determine essentially
the lowest possible upper bounds on node degree for which the problems remain NP-complete.

<a id="pdf-f17c4a237263-p001-b003"></a>
<!-- pdf-source: page=1; block=3; confidence=0.90 -->

**Introduction, summary (printed pp. 47–48).** The results of Cook and Karp [C71, K72] show that
simple forms of notoriously hard problems, such as the travelling salesman problem and
propositional theorem proving, form a class: the *NP-complete* problems ("polynomial complete"
problems in the terminology of Karp [K72], footnote $^{*}$). No member of the class is known to
have a polynomial-time algorithm, but if one has, all do. Knowing that a problem is NP-complete
justifies turning to heuristics, to less exponential exact algorithms, or to approximation
algorithms. The approach of this paper is to restrict the domains of known NP-complete problems
and to ask whether the subproblems remain NP-complete.

<a id="pdf-f17c4a237263-p002-b001"></a>
<!-- pdf-source: page=2; block=1; confidence=0.95 -->

**Introduction: restricted problems as tools (printed p. 48).** Second, they give us valuable
tools for proving other completeness results. For instance, by observing that SATISFIABILITY
WITH AT MOST 3 LITERALS PER CLAUSE, a restricted form of SATISFIABILITY, is still NP-complete,
Karp [K72] was able to derive the NP-completeness of CHROMATIC NUMBER, EXACT COVER, MAX CUT, and
a number of other problems. … The second half of the paper considers the effect of restricting
the allowable types of graphs for NP-complete graph problems such as NODE COVER, CHROMATIC
NUMBER, and HAMILTONIAN CIRCUIT, by either restricting the maximum degree of the nodes, or
allowing only planar graphs, or both.

*Transcription note.* Two sentences from the same column; the ellipsis omits the paragraph on
the first half of the paper (summarised in `pdf-f17c4a237263-p002-b004`).

<a id="pdf-f17c4a237263-p002-b002"></a>
<!-- pdf-source: page=2; block=2; confidence=0.95 -->

**Basic definitions (printed p. 48).** We summarize here the basic definitions, referring the
reader to [K72] for a more complete discussion. Let $B=\{0,1\}$ and let $B^*$ denote the set of
all finite strings of elements from $B$. Any subset $L$ of $B^*$ is called a *language*. Let
$\pi$ be the class of functions $f:B^*\to B^*$ which are computable in polynomial time by
one-tape deterministic Turing machines. If $L$ and $M$ are languages, we say that $L$ is
*polynomial reducible* to $M$, written $L\mathrel{\alpha}M$, when there is a function
$f\in\pi$ such that $f(x)\in M$ if and only if $x\in L$. $M$ is NP-complete if $M\in NP$ (the
class of languages recognizable in polynomial time by one-tape *nondeterministic* Turing
machines) and *every* language in NP is polynomial reducible to $M$. In fact, if $L$ is
NP-complete and $L\mathrel{\alpha}M$, then $M\in NP$ implies that $M$ is NP-complete.

<a id="pdf-f17c4a237263-p002-b003"></a>
<!-- pdf-source: page=2; block=3; confidence=0.95 -->

**Problems as recognition problems (printed p. 48).** In accord with the above definitions, the
"problems" we shall consider in this paper, although many are more naturally thought of as
optimization problems, shall be presented as recognition problems (with the straightforward
details of the encoding of entities such as graphs and integers into strings of 0's and 1's
omitted). Our proofs can then consist of showing that known NP-complete languages reduce to the
ones we are considering. (A list of the known NP-complete languages we shall use, together with
their definitions, is given in the Appendix). In general, we leave to the reader the
straightforward verification that (a) the language is in NP and (b) the described mapping can be
performed in polynomial time.

*Transcription note.* A footnote on the same page reads: "We use the ordered pair $(N,A)$ to
denote a graph $G$ having node set $N$ and edge set $A$."

<a id="pdf-f17c4a237263-p002-b004"></a>
<!-- pdf-source: page=2; block=4; confidence=0.90 -->

**§I, SIMPLE MAX CUT and related problems, summary (printed pp. 48–51).**

- MAX CUT is a graph $G=(N,A)$ with weights $w:A\to\mathbb Z$ and a bound $W$. It asks whether
  some $S\subseteq N$ has $\sum_{\{u,v\}\in A,\,u\in S,\,v\in N-S}w(\{u,v\})\ge W$. Karp showed
  it NP-complete by a reduction from PARTITION [K72].
- SIMPLE MAX CUT fixes every edge weight to 1. With $W=|A|$ it asks whether $G$ is bipartite.
- The paper proves:
  - **Theorem 1.1** $\mathrm{SAT3}\mathrel{\alpha}\mathrm{MAX\ SAT2}$ (p. 49). Each 3-clause
    becomes ten clauses of at most two literals, with $k=7m$.
  - **Theorem 1.2** $\mathrm{MAX\ SAT2}\mathrel{\alpha}\mathrm{SIMPLE\ MAX\ CUT}$
    (pp. 49–50).
  - **Theorem 1.3** SIMPLE MAX CUT $\mathrel{\alpha}$ MINIMUM CUT INTO EQUAL-SIZED SUBSETS
    (p. 50).
  - **Theorem 1.4** CLIQUE $\mathrel{\alpha}$ MINIMUM NODE-DELETION BIPARTITE SUBGRAPH
    (pp. 50–51). SIMPLE MAX CUT itself is restated as MINIMUM EDGE-DELETION BIPARTITE SUBGRAPH.
- None of §I concerns colouring.

<a id="pdf-f17c4a237263-p005-b001"></a>
<!-- pdf-source: page=5; block=1; confidence=0.90 -->

**§I, OPTIMAL LINEAR ARRANGEMENT, summary (printed pp. 51–52).**

- OPTIMAL LINEAR ARRANGEMENT [A73] is a graph $G=(N,A)$ with weights $w$ and a bound $W$. It
  asks whether some one-to-one $f:N\to\mathbb Z$ has
  $\sum_{\{u,v\}\in A}w(\{u,v\})\,|f(u)-f(v)|\le W$. It is a special case of the quadratic
  assignment problem.
- **Theorem 1.5** SIMPLE MAX CUT $\mathrel{\alpha}$ SIMPLE OPTIMAL LINEAR ARRANGEMENT (p. 51;
  the proof ends on p. 52).
  - The reduction adds $n^4$ new nodes to $G$ and compares arrangements with cuts.
  - So the problem is NP-complete even with all edge weights 1.

<a id="pdf-f17c4a237263-p006-b001"></a>
<!-- pdf-source: page=6; block=1; confidence=0.94 -->

**§II, Restricted Graph Problems: opening (printed p. 52).** Many of the reductions which were
first used to show certain graph theoretic problems to be NP-complete involved the construction
of rather complicated graphs, highly non-planar and with nodes having arbitrarily high degree.
Since in many practical problems node degree may be bounded (e.g., fan-in, fan-out restrictions
on circuit elements), or graphs may be planar, it is worthwhile to determine whether the
complexity of the graphs involved in these reductions was necessary.

In certain cases, we can observe trivially that it is. For example, consider the problem CLIQUE
[K72]. Since the largest clique possible in a planar graph has size 4, and the largest clique
possible in a graph with maximum node degree $k$ has size $k+1$, we can find the largest clique
in either case in polynomial time by examining all subsets of 4 or fewer ($k+1$ or fewer) nodes,
in time proportional to at most $n^4$ or $n^{k+1}$, respectively.

More interesting are the cases where the answer is not readily apparent. For instance, it is
implicit in the literature that MAX CUT, when restricted to planar graphs, can be solved in
polynomial time. [O72] presents a polynomial time procedure for reducing the problem of finding
the maximum cut in a weighted planar graph to that of finding a minimum weighted matching in a
complete graph derived from the dual of the original graph. Although [O72] then resorts to a
non-polynomial branch and bound technique, the weighted matching can be found in polynomial time
using a method of Edmonds [E70].

*Transcription note.* "we can observe trivially that it is" is printed as given.

<a id="pdf-f17c4a237263-p006-b002"></a>
<!-- pdf-source: page=6; block=2; confidence=0.97 -->

**§II, NP-completeness of GRAPH 3-COLORABILITY, attributed to [St73] (printed p. 52).** On the
other hand, one of the authors has shown [St73] that the question of whether a graph is
3-colorable (GRAPH 3-COLORABILITY, itself a restriction of CHROMATIC NUMBER) is NP-complete, even
when the domain is restricted to include only planar graphs. In this section, we shall present
further completeness results,

*Transcription note.* The sentence continues on p. 53 (`pdf-f17c4a237263-p007-b001`). This is
the paper's only statement that GRAPH 3-COLORABILITY is NP-complete. It has no theorem number
and no proof in this paper. "One of the authors" is Stockmeyer: [St73] is L. Stockmeyer, "Planar
3-Colorability is Polynomial Complete" (`pdf-f17c4a237263-p017-b001`). The appendix entry of
GRAPH 3-COLORABILITY also carries the tag [St73] (`pdf-f17c4a237263-p016-b003`).

<a id="pdf-f17c4a237263-p007-b001"></a>
<!-- pdf-source: page=7; block=1; confidence=0.96 -->

**§II, the table of results (printed p. 53).** concerning GRAPH 3-COLORABILITY, NODE COVER, and
HAMILTONIAN CIRCUIT. The formal definitions of these problems appear in the appendix.

The following table gives the principal restricted versions of these problems which we prove to
be polynomial complete:

| | PROBLEM | NODE DEGREE AT MOST |
|---|---|---|
| 1. | PLANAR GRAPH 3-COLORABILITY | 4 |
| 2. | UNDIRECTED HAMILTONIAN CIRCUIT | 3 |
| 3. | PLANAR DIRECTED HAMILTONIAN PATH | 4-OUT, 3-IN |
| 4. | NODE COVER | 3 |
| 5. | PLANAR NODE COVER | 6 |

*Transcription note.* The typescript prints the problem list and the degree list as two separate
numbered lists; they are joined here into one table.

<a id="pdf-f17c4a237263-p007-b002"></a>
<!-- pdf-source: page=7; block=2; confidence=0.95 -->

**§II, optimality of the degree bounds; corollaries and open problems (printed p. 53).** For
results 3 and 5, it was not previously known if the planar problems were complete, even if *no*
restrictions were placed on node degrees. The degree constraints in 1, 2, and 4 are all best
possible, in that each of the problems becomes easy if the restriction on node degree is reduced
by 1. NODE COVER and UNDIRECTED HAMILTONIAN CIRCUIT are clearly trivial for graphs with maximum
degree 2, and a well-known result of Brooks [B41] implies that a connected graph with maximum
degree 3 is 3-colorable if and only if it differs from $K_4$, the complete graph on four nodes,
which is easy to determine.

In addition to the above results, there are a number of more or less immediate corollaries.
Result 2 implies that DIRECTED HAMILTONIAN CIRCUIT with node degree bounded by 3-OUT, 3-IN is
NP-complete; however, the largest degree bounds for which we know this problem to be easy are
2-OUT, 1-IN or 2-IN, 1-OUT. Also, we may substitute PATH for CIRCUIT in result 2. However, we do
not know whether PLANAR DIRECTED HAMILTONIAN CIRCUIT, PLANAR UNDIRECTED HAMILTONIAN CIRCUIT, or
PLANAR UNDIRECTED HAMILTONIAN PATH are NP-complete, and these remain significant open problems.

<a id="pdf-f17c4a237263-p007-b003"></a>
<!-- pdf-source: page=7; block=3; confidence=0.97 -->

**Theorem 2.1 (printed p. 53).** The proofs of the results given in the table follow. For each
problem, we show that there is a known NP-complete problem which reduces to it.

*Theorem 2.1.* PLANAR GRAPH 3-COLORABILITY $\mathrel{\alpha}$ PLANAR GRAPH 3-COLORABILITY WITH
NODE DEGREE AT MOST 4.

*Transcription note.* The "known NP-complete problem" in Theorem 2.1 is PLANAR GRAPH
3-COLORABILITY, whose completeness the paper takes from [St73]
(`pdf-f17c4a237263-p006-b002`).

<a id="pdf-f17c4a237263-p007-b004"></a>
<!-- pdf-source: page=7; block=4; confidence=0.94 -->

**Proof of Theorem 2.1: node substitutes $H_k$ (printed p. 53).** *Proof:* The key to our
construction will be the use of "node substitutes." Figure 1(A) shows the 3-outlet node
substitute $H_3$, with its first, second, and third output nodes labelled. For $k>4$, the
$k$-outlet node substitute $H_k$ is formed by adjoining to $H_{k-1}$ a copy of $H_3$ having its
first outlet coinciding with outlet $k-1$ of $H_{k-1}$. The outlet nodes of $H_k$ are the nodes
having degree 2. The outlets which originally belonged to $H_{k-1}$ retain the same labels, with
the second outlet of the adjoined $H_3$ becoming outlet $k-1$ and its third outlet becoming
outlet $k$. Figure 1(B) shows $H_5$.

*Transcription note.* "For $k>4$" is printed so (checked on a 6× crop). The recursion must also
produce $H_4$, and Facts (2.1A)–(2.1D) are stated "for all $k\ge3$". So the intended range is
evidently $k\ge4$.

<a id="pdf-f17c4a237263-p007-b005"></a>
<!-- pdf-source: page=7; block=5; confidence=0.96 -->

**Proof of Theorem 2.1: Facts (2.1A)–(2.1D) (printed p. 53).** It is easy to prove by induction
that, for all $k\ge3$, the following facts hold:

- (2.1A) $H_k$ has $7(k-2)+1$ nodes, including $k$ outlets.
- (2.1B) No node of $H_k$ has degree exceeding 4.
- (2.1C) $H_k$ is planar.
- (2.1D) $H_k$ is 3-colorable, but not 2-colorable, and every valid 3-coloring of $H_k$ assigns
  the same color to every outlet node.

<a id="pdf-f17c4a237263-p007-b006"></a>
<!-- pdf-source: page=7; block=6; confidence=0.95 -->

**Proof of Theorem 2.1: the construction of $G'$ (printed p. 53).** Given any planar graph $G$,
we show how to construct a planar graph $G'$, using node substitutes, which has maximum degree 4
and which is 3-colorable if and only if $G$ is 3-colorable.

Fix a planar embedding of $G$ and arbitrarily index the nodes of $G$ which have degree exceeding
4 as $v_1,v_2,\dots,v_r$. We construct a sequence of graphs $G=G_0,G_1,\dots,G_r=G'$ as follows:
$G_i$ is constructed from $G_{i-1}$.

*Transcription note.* The paragraph continues on p. 54 (`pdf-f17c4a237263-p008-b001`).

<a id="pdf-f17c4a237263-p007-b007"></a>
<!-- pdf-source: page=7; block=7; confidence=0.85 -->

**Figure 1, node substitutes $H_3$ and $H_5$ (printed p. 53), described.** The figure is a
drawing. This description is the maintainer's reading of the page image.

**(A) $H_3$.** It has 8 nodes:

- outlet 1 at the bottom left, outlet 2 at the apex, outlet 3 at the bottom right;
- the internal nodes $a$ (left side), $b$ (right side), $c$ (centre), $d$ (bottom, left inner)
  and $e$ (bottom, right inner).

Its 13 edges are $1a$, $a2$, $2b$, $b3$ (the two upper sides), $1d$, $de$, $e3$ (the base), $ad$,
$be$, and the crossing pair $ac, ce$ and $bc, cd$. The internal nodes have degree 4 and the
outlets degree 2.

**(B) $H_5$.** Three copies of $H_3$ stand side by side on a common base line. The bottom right
outlet of each copy is identified with the bottom left outlet of the next, so the two shared nodes
have degree 4. The outlets are labelled 1 (bottom left), 2, 3, 4 (the three apexes) and 5 (bottom
right).

*Maintainer note (not part of the source).*

- **The node labels.** $a$–$e$ are not in the paper.
- **(2.1D) for $H_3$.** It can be read off this edge list, as follows.
  - The triangles $1ad$, $adc$, $dce$, $ceb$ and $eb3$ form a chain in which consecutive
    triangles share an edge. So any 3-colouring gives $1$ and $c$ the same colour, $a$ and $e$
    the same colour, $d$ and $b$ the same colour, and $c$ and $3$ the same colour.
  - Outlet 2 is adjacent to $a$ and $b$, which get different colours, while $c$ is adjacent to
    both. So outlet 2 gets the colour of $c$.
  - So all three outlets share one colour. The colouring $1,2,3,c\mapsto1$, $a,e\mapsto2$,
    $b,d\mapsto3$ is proper.

<a id="pdf-f17c4a237263-p008-b001"></a>
<!-- pdf-source: page=8; block=1; confidence=0.95 -->

**Proof of Theorem 2.1, concluded (printed p. 54).** Let $d$ be the degree of $v_i$ in
$G_{i-1}$ and let $\{u_1,v_i\},\{u_2,v_i\},\dots,\{u_d,v_i\}$ be the edges incident with $v_i$,
taken in clockwise order. To form $G_i$, delete node $v_i$ from $G_{i-1}$, replacing it with a
copy of $H_d$, and replace each edge $\{u_j,v_i\}$ by an edge joining $u_j$ to outlet $j$ of the
node substitute.

It follows from the construction and previously stated facts that, for $0\le k\le r$, $G_k$ is
planar, $G_k$ has $r-k$ nodes with degree exceeding 4, and $G_k$ is 3-colorable if and only if
$G$ is 3-colorable. Thus, $G'=G_r$ satisfies all the required properties, completing the
proof. $\blacksquare$

<a id="pdf-f17c4a237263-p008-b002"></a>
<!-- pdf-source: page=8; block=2; confidence=0.88 -->

**§II, Hamiltonian circuit and path, summary (printed pp. 54–59).**

- **Theorem 2.2** UNDIRECTED HAMILTONIAN CIRCUIT $\mathrel{\alpha}$ UNDIRECTED HAMILTONIAN
  CIRCUIT WITH VERTEX DEGREE AT MOST 3 (pp. 54–56).
  - Each node of degree $k$ is replaced by a node substitute built from *fans* $F_k$, which have
    one inlet and $k$ outlets.
  - Facts (2.2A)–(2.2C) and Lemma 2.2.1 (p. 54) show that every Hamiltonian circuit traverses a
    fan from its inlet to an outlet.
- **Theorem 2.3** EXACT COVER $\mathrel{\alpha}$ PLANAR DIRECTED HAMILTONIAN PATH (pp. 56–59,
  with Lemmas 2.3.1 and 2.3.2).
  - In the constructed digraph, no node has in-degree above 3 or out-degree above 4. This gives
    result 3 of the table.
  - The proof's closing line on p. 59 reads "Theorem 2.3.2", apparently a misprint for
    Theorem 2.3.

<a id="pdf-f17c4a237263-p013-b001"></a>
<!-- pdf-source: page=13; block=1; confidence=0.88 -->

**§II, node cover, summary (printed pp. 59–62).**

- **Theorem 2.4** SAT3 $\mathrel{\alpha}$ NODE COVER WITH NODE DEGREE AT MOST 3 (pp. 59–60).
  The construction indexes the occurrences of each variable separately. A remark says
  that the theorem was obtained independently by P. Herrmann [H73].
- **Theorem 2.5** NODE COVER $\mathrel{\alpha}$ PLANAR NODE COVER (pp. 60–62).
  - Every edge crossing of a drawing of $G$ is replaced by a planar *crossover* $H$ (Figure 8),
    with Table II giving the minimum covers $c[i,j]$.
  - $G$ has a node cover of size $k$ iff the new graph has one of size $k+13d$, where $d$ is the
    number of crossovers.
  - When $G$ has degree at most 3, the new graph has degree at most 6. So PLANAR NODE COVER WITH
    NODE DEGREE AT MOST 6 is NP-complete (p. 62); whether 6 is best possible is open.

<a id="pdf-f17c4a237263-p016-b001"></a>
<!-- pdf-source: page=16; block=1; confidence=0.92 -->

**§III, Concluding Remarks, summary (printed p. 62).**

- Similar restriction questions remain open, for example STEINER TREE [K72] for planar graphs,
  and 3-processor unit-time scheduling with an arbitrary partial order [U73]. Planar UNDIRECTED
  HAMILTONIAN CIRCUIT is also open.
- Large polynomial-time subdomains matter as well. MAX CUT for planar graphs is one example.
  Other recent papers [E72, Gav72, Gav73] show that CLIQUE and CHROMATIC NUMBER can be solved in
  polynomial time for "transitively orientable" graphs, "chordal" graphs and "circle" graphs.

<a id="pdf-f17c4a237263-p016-b002"></a>
<!-- pdf-source: page=16; block=2; confidence=0.95 -->

**Appendix: Definitions of Polynomial Complete Problems; SAT3 (printed p. 62).**

SATISFIABILITY WITH AT MOST 3 LITERALS PER CLAUSE (SAT3) [K72]

- INPUT: Set of clauses $C=\{C_1,C_2,\dots,C_p\}$ in variables $x_1,x_2,\dots,x_n$, each clause
  being the disjunction of 3 or fewer literals, where a literal is either a variable $x_i$ or its
  negation $\bar x_i$.
- PROPERTY: There is a truth assignment to the variables which simultaneously satisfies all the
  clauses in $C$ (a clause is satisfied if any one of its disjuncts is $x_i$ for some "true"
  variable $x_i$, or $\bar x_j$ for some "false" $x_j$).

<a id="pdf-f17c4a237263-p016-b003"></a>
<!-- pdf-source: page=16; block=3; confidence=0.97 -->

**Appendix: definition of GRAPH 3-COLORABILITY (printed p. 62).**

GRAPH 3-COLORABILITY [St73]

- INPUT: Graph $G=(N,A)$
- PROPERTY: $G$ has a legal 3-coloring of its nodes i.e., there is a map $f:N\to\{1,2,3\}$
  such that $\{n_1,n_2\}\in A$ implies $f(n_1)\ne f(n_2)$.

<a id="pdf-f17c4a237263-p016-b004"></a>
<!-- pdf-source: page=16; block=4; confidence=0.92 -->

**Appendix: the other definitions, summary (printed pp. 62–63).**

- **CLIQUE [K72].** Does $G$ have a set $N'\subseteq N$ with $|N'|\ge k$ whose nodes are pairwise
  adjacent?
- **EXACT COVER [K72].** Does $S=\{S_1,\dots,S_n\}$ have a subcollection $S'$ of pairwise
  disjoint sets whose union is $\bigcup_{i=1}^nS_i$?
- **UNDIRECTED (DIRECTED) HAMILTONIAN PATH (CIRCUIT) [K72].** Is there an ordering
  $n_1,\dots,n_{|N|}$ of the nodes with $\{n_i,n_{i+1}\}\in A$ ($\langle n_i,n_{i+1}\rangle\in
  A$) for $1\le i<|N|$, and, in the circuit case only, also $\{n_{|N|},n_1\}\in A$
  ($\langle n_{|N|},n_1\rangle\in A$)?
- **NODE COVER [K72].** Is there a subset $N'\subseteq N$ with $|N'|\le k$ such that
  $\{x,y\}\cap N'\ne\varnothing$ for every $\{x,y\}\in A$? The entry ends on p. 63.

<a id="pdf-f17c4a237263-p017-b001"></a>
<!-- pdf-source: page=17; block=1; confidence=0.96 -->

**References used by the colouring material (printed p. 63).**

- B41. R. L. Brooks, "On Coloring the Nodes of a Network," Proc. Cambridge Philos. Soc., 37
  (1941), 194-197.
- C71. S. A. Cook, "The Complexity of Theorem-Proving Procedures," STOC (1971), 151-158.
- Gav72. F. Gavril, "Algorithms for Minimum Coloring, Maximum Clique, Minimum Covering by
  Cliques, and Maximum Independent set of a Chordal Graph," SIAM J. Computing 1 (1972), 180-187.
- K72. R. M. Karp, "Reducibility Among Combinatorial Problems," Complexity of Computer
  Computations, R. E. Miller and J. W. Thatcher, eds., Plenum Press, New York (1972), 85-104.
- St73. L. Stockmeyer, "Planar 3-Colorability is Polynomial Complete," SIGACT News 5, No. 3
  (1973), 19-25.

*Transcription note.* The list has 21 entries. Only these five are transcribed. The others
(A73, E70, E72, Ga72, Gav73, Gr72, H73, Jo72, Jo73, K70, L73, O72, Sa72, Sa73, Se73, U73) are in
the raw text. The NODE COVER definition ends at the top of this page.
