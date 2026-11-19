<!-- generated-by: maintainer transcription of the whole paper, with described figures (EF-H12 ingest of [St73], Seyoon's ruling to ingest the actual proof, 2026-11-19) -->
<!-- source-pdf-sha256: ecfb8ec9f7b38708e0b8486287cfbcce6369b92feffd8abd8201b062829dd287 -->
<!-- validation-status: whole-paper reference for EF-H12 (3-colourability); awaiting Codex source review -->

# Planar 3-Colorability is Polynomial Complete

L. Stockmeyer (MIT), *ACM SIGACT News* 5(3), pp. 19–25, July 1973, doi:10.1145/1008293.1008294
(tag `St73`). The PDF is a 7-page scan of the typescript with an OCR text layer. Its first page
gives the title, the author, his affiliation and the date "March 1973". Every page carries the
running head "SIGACT News", the printed page number (19–25) and "July 1973", so the journal, the
issue date and the page range are confirmed by the PDF. The volume and number (5, No. 3) and the
DOI are not printed. They come from the uploader's citation, and the volume, number and pages agree
with the entry for [St73] in the reference list of [GJS74] (p. 63, anchor
`pdf-f17c4a237263-p017-b001`). Physical page $p$ is printed page $p+18$.

**Page order.** The text runs in the order of printed pp. 19, 22, 21, 20, 23 (physical pages 1, 4,
3, 2, 5). Printed pp. 20 and 22 are interchanged in the issue, while the running heads are in
sequence. The order is forced by the text: p. 19 ends with the problem definitions and p. 22 opens
with the Theorem; p. 22 ends with the construction of $G$ and p. 21 opens with "Now $G$ is
3-colorable iff …"; p. 21 ends with "There are four distinct nodes … such that" and p. 20 opens
with condition 2a); p. 20 ends with "there is some row $i$ and some $j$," and p. 23 opens with
"$1\le j\le n-1$". The figures and the references are on pp. 24–25. **The blocks below are in
reading order.** Each anchor names its physical page, so the anchors are not monotone in the file.

**Scope (EF-H12, 2026-11-19).** Every passage of the paper is transcribed: the title page and
footnote, the introduction, the two problem definitions, the Theorem, the proof of part 1)
(SATISFIABILITY WITH AT MOST 3 LITERALS PER CLAUSE $\propto$ 3-COLORABILITY), the remark on
$k$-colourability, the proof of part 2) (3-COLORABILITY $\propto$ PLANAR 3-COLORABILITY, by the
cross-over graph), the concluding remarks and the references. Figures 1–4 are described from the
page images, at confidence at most 0.85.

**Conventions.** Transcribed blocks follow the paper's wording, checked against the page images
rather than the OCR layer. Mathematics is in LaTeX. The reduction sign, a hand-drawn Karp $\propto$,
is written $\propto$. The overbar of a negated literal is written $\bar u_i$. Underlined words are
written as emphasis. Problem names keep the paper's capitals. Misprints are kept and flagged
"[sic]" in a transcription note. The bold block labels, and the notes marked *Transcription note*
or *Maintainer note*, are not part of the source. Node names in the figure descriptions that the
paper does not print are the maintainer's and are said to be so.

<a id="pdf-ecfb8ec9f7b3-p001-b001"></a>
<!-- pdf-source: page=1; block=1; confidence=0.96 -->

**Title page (printed p. 19).** PLANAR 3-COLORABILITY IS POLYNOMIAL COMPLETE$^{\dagger}$, Larry
Stockmeyer, Massachusetts Institute of Technology, Cambridge, Massachusetts, March 1973.

$^{\dagger}$Work reported here in was supported in part by Project MAC, an M.I.T. research program
sponsored by the Advanced Research Projects Agency, Department of Defense, under Office of Naval
Research Contract Number N00014-70-A-0362-0006 and theNational Science Foundation under contract
number GJ00-4327. Reproduction in whole or in part is permitted for any purpose the the United
States Government.

*Transcription note.* "here in", "theNational" and "purpose the the" are as printed [sic]; "of
the United States Government" is evidently meant. The grant number reads "GJ00-4327" on the
image; whether its third and fourth characters are zeros or capital O's cannot be told on this
typewriter face.

<a id="pdf-ecfb8ec9f7b3-p001-b002"></a>
<!-- pdf-source: page=1; block=2; confidence=0.97 -->

**Introduction (printed p. 19).** The general problem of recognizing the set of pairs $(G,k)$,
where $k$ is a positive integer and $G$ is a graph which is $k$-colorable, is polynomial complete
as defined by Karp [1]. It is shown here that this problem is still complete even for pairs
$(G,k)$ where $k=3$ and $G$ is a planar graph. We assume that the reader is familiar with the
definitions and notation of [1].

<a id="pdf-ecfb8ec9f7b3-p001-b003"></a>
<!-- pdf-source: page=1; block=3; confidence=0.96 -->

**Definitions of the problems (printed p. 19).** The problems to be considered are the following.

3-COLORABILITY

- INPUT: Graph $G$ with nodes $N$ and arcs $A$.
- PROPERTY: There is a function $f:N\to\{1,2,3\}$ such that if $u,v$ are adjacent then
  $f(u)\ne f(v)$.

PLANAR 3-COLORABILITY

- INPUT: Planar graph $G$.
- PROPERTY: Same as above.

<a id="pdf-ecfb8ec9f7b3-p004-b001"></a>
<!-- pdf-source: page=4; block=1; confidence=0.98 -->

**Theorem (printed p. 22).** *Theorem.* 3-COLORABILITY and PLANAR 3-COLORABILITY are polynomial
complete.

*Transcription note.* The Theorem is unnumbered and is the paper's only theorem. "Polynomial
complete" is Karp's notion [1] (the introduction, `pdf-ecfb8ec9f7b3-p001-b002`): membership in NP
together with polynomial reducibility $\propto$ (a polynomial-time many-one map of instances) from
every NP problem. The paper does not argue membership in NP.

<a id="pdf-ecfb8ec9f7b3-p004-b002"></a>
<!-- pdf-source: page=4; block=2; confidence=0.95 -->

**Proof of 1), the clause gadget $G^*$ (printed p. 22).** *Proof.* 1) SATISFIABILITY WITH AT MOST
3 LITERALS PER CLAUSE $\propto$ 3-COLORABILITY.

Let $D_1,D_2,\dots,D_r$ be the clauses and $L=\{u_1,\dots,u_m,\bar u_1,\dots,\bar u_m\}$ the
literals of a given satisfiability problem. Let $D_i=\{\sigma_{i1},\sigma_{i2},\sigma_{i3}\}\subset L$,
$i=1,\dots,r$. Consider the graph $G^*$ with nodes $N^*=\{v_1,v_2,\dots,v_6\}$ and arcs $A^*$ shown
as solid lines in Fig. 1. Suppose $G^*$ is connected to nodes $s_1,s_2,s_3$ as shown. $G^*$ has the
following properties:

- i) If $s_1,s_2,s_3$ are constrained to have the same color $c$, then $v_6$ must be colored $c$ in
  any 3-coloring of $G^*$.
- ii) If $s_1,s_2,s_3$ are constrained to be colors at least two of which are different, then for
  all $c\in\{1,2,3\}$ there is a 3-coloring of $G^*$ in which $v_6$ is colored $c$.

*Transcription note.* Properties i) and ii) are stated without proof; the *Maintainer note* to
Figure 1 (`pdf-ecfb8ec9f7b3-p006-b002`) checks them. The paper writes every clause with three
literals $\sigma_{i1},\sigma_{i2},\sigma_{i3}$, although the source problem allows "at most 3"; a
shorter clause is evidently taken with a repeated literal (not said).

<a id="pdf-ecfb8ec9f7b3-p004-b003"></a>
<!-- pdf-source: page=4; block=3; confidence=0.94 -->

**Proof of 1), the graph $G$ (printed p. 22).** Let $G_i^*=(N_i^*,A_i^*)$, $i=1,\dots,r$, be $r$
copies of $G^*$. Let $N_i^*=\{v_{i1},\dots,v_{i6}\}$ as in Fig. 1. $G=(N,A)$ is the following.

$$N=\{t_1,t_2\}\cup\{u_1,\dots,u_m,\bar u_1,\dots,\bar u_m\}\cup\bigcup_{i=1}^{r}N_i^* .$$

$$\begin{aligned}
A={}&\{\{t_1,t_2\}\}\cup\{\{t_1,\sigma\}\mid\sigma\in L\}\cup\{\{u_i,\bar u_i\}\mid i=1,\dots,m\}
\cup\{\{\sigma_{ij},v_{ij}\}\mid i=1,\dots,r;\ j=1,2,3\}\\
&\cup\{\{t_2,v_{i6}\}\mid i=1,\dots,r\}\cup\bigcup_{i=1}^{r}A_i^* .
\end{aligned}$$

*Transcription note.* The text continues on printed p. 21 (`pdf-ecfb8ec9f7b3-p003-b001`).

<a id="pdf-ecfb8ec9f7b3-p003-b001"></a>
<!-- pdf-source: page=3; block=1; confidence=0.96 -->

**Proof of 1), correctness (printed p. 21).** Now $G$ is 3-colorable iff $D_1,\dots,D_r$ is
satisfiable. Suppose $G$ is 3-colorable and let $f:N\to\{1,2,3\}$ be a coloring. The arc
$\{t_1,t_2\}$ ensures that $f(t_1)\ne f(t_2)$ so we may assume that $f(t_1)=1$ and $f(t_2)=2$. Now
$f(\sigma)\in\{2,3\}$ for all literals $\sigma\in L$ because of the arcs $\{t_1,\sigma\}$, and
$f(u_i)\ne f(\bar u_i)$ for all $i$ because of the arcs $\{u_i,\bar u_i\}$. The graphs $G_i^*$
ensure that no clause contains literals all colored 2. Therefore
$S=\{\sigma\in L\mid f(\sigma)=3\}$ is a consistent truth assignment which satisfies
$D_1,\dots,D_r$. The converse is similar. This completes the proof of 1).

*Maintainer note (not part of the source).* "The graphs $G_i^*$ ensure …" uses property i) with
$c=2$ and the arc $\{t_2,v_{i6}\}$. "The converse is similar" is the direction from a satisfying
assignment to a colouring: colour $t_1\mapsto1$, $t_2\mapsto2$, true literals $\mapsto3$, false
literals $\mapsto2$, and colour each $G_i^*$ with $v_{i6}\mapsto3$, which property i) (all three
literals true) or property ii) (mixed) allows. The paper does not write this colouring out.

<a id="pdf-ecfb8ec9f7b3-p003-b002"></a>
<!-- pdf-source: page=3; block=2; confidence=0.96 -->

**Remark on $k$-colorability (printed p. 21).** The proof above can easily be extended to show
that $k$-colorability is complete for any fixed $k\ge3$. In particular, let $G=(N_1,A_1)$ be any
graph and $K_m=(N_2,A_2)$ be the complete graph on $m$ nodes. If $G'=(N',A')$ is defined as
$N'=N_1\cup N_2$ and $A'=A_1\cup A_2\cup\{\{u,v\}\mid u\in N_1,\ v\in N_2\}$, then $G'$ is
$(k+m)$-colorable iff $G$ is $k$-colorable.

<a id="pdf-ecfb8ec9f7b3-p003-b003"></a>
<!-- pdf-source: page=3; block=3; confidence=0.96 -->

**Proof of 2), bound nodes and the definition of a cross-over graph (printed p. 21).**
2). 3-COLORABILITY $\propto$ PLANAR 3-COLORABILITY

The proof follows from the existence of a "cross-over" graph which enables one to eliminate
cross-overs, thereby converting an arbitrary graph into a planar graph, while preserving
3-colorability.

We say that two nodes $u,v$ of a given graph $G$ are *3-color bound* (or simply *bound*) if $u$ and
$v$ must be assigned the same color in any 3-coloration of $G$.

A cross-over graph is defined to be a finite graph $G$ with the properties that

1) $G$ is planar and 3-colorable.

2) There are four distinct nodes $v_1,v_1',v_2,v_2'$ of $G$ such that

*Transcription note.* The sentence continues on printed p. 20 (`pdf-ecfb8ec9f7b3-p002-b001`).

<a id="pdf-ecfb8ec9f7b3-p002-b001"></a>
<!-- pdf-source: page=2; block=1; confidence=0.96 -->

**Proof of 2), conditions 2a) and 2b) of a cross-over graph (printed p. 20).**

- 2a) $v_1,v_2,v_1',v_2'$ are nodes of some face of $G$ (for some embedding of $G$ in the plane)
  and they appear in that order as the cycle of edges bounding the face is traversed in some
  direction.
- 2b) $v_1$ and $v_1'$ are bound and $v_2$ and $v_2'$ are bound.

<a id="pdf-ecfb8ec9f7b3-p002-b002"></a>
<!-- pdf-source: page=2; block=2; confidence=0.96 -->

**Proof of 2), the cross-over graph $G_C$ (printed p. 20).** A cross-over graph $G_C$ is shown in
Fig. 2, although it may not be the simplest example. $G_C$ is planar and satisfies condition (2a)
by inspection. To verify that $G_C$ is 3-colorable and satisfies (2b), consider the subgraph $G_F$
of $G_C$ shown in Fig. 3. Clearly $G_F$ is 3-colorable and $u$ and $v$ are bound. This implies that
$v_2$ and $v_2'$ are bound in $G_C$. We leave it to the reader to convince himself that if $v_1$
and $v_1'$ are also colored the same then a 3-coloration is possible, and if $v_1$ and $v_1'$ are
colored differently then a 3-coloration is impossible.

<a id="pdf-ecfb8ec9f7b3-p002-b003"></a>
<!-- pdf-source: page=2; block=3; confidence=0.95 -->

**Proof of 2), the planar graph $G'$ (printed p. 20).** Now let $G$ be a given graph with nodes
$\{u_1,\dots,u_n\}$. A planar graph $G'$ is constructed such that $G'$ is 3-colorable iff $G$ is
3-colorable. The nodes of $G'$ include a $p(n)$ by $n$ array of nodes
$\{v_{ij}\mid i=1,\dots,p(n),\ j=1,\dots,n\}$, for some polynomial $p(n)\le O(n^2)$.

$G'$ has the property that for each row $i=2,3,\dots,p(n)$, there is a permutation
$\sigma_i:\{1,\dots,n\}\to\{1,\dots,n\}$ such that $v_{1j}$ and $v_{i,\sigma_i(j)}$ are bound for
all $j=1,\dots,n$. Each row $\{v_{i1},\dots,v_{in}\}$ of nodes is "connected" to the next row
$\{v_{i+1,1},\dots,v_{i+1,n}\}$ by copies of $G_C$ and $G_F$. The rows are connected in such a way
that for each arc $\{u_k,u_\ell\}$ in $G$, there is some row $i$ and some $j$,

*Transcription note.* "$O(n^2)$" is typed with the digit zero, "$0(n^2)$". The sentence continues
on printed p. 23 (`pdf-ecfb8ec9f7b3-p005-b001`).

<a id="pdf-ecfb8ec9f7b3-p005-b001"></a>
<!-- pdf-source: page=5; block=1; confidence=0.95 -->

**Proof of 2), adding the arcs of $G$ (printed p. 23).** $1\le j\le n-1$, such that $v_{1k}$ and
$v_{ij}$ are bound and $v_{1\ell}$ and $v_{i,j+1}$ are bound. The arc $\{u_k,u_\ell\}$ in $G$ can be
added as the arc $\{v_{ij},v_{i,j+1}\}$ in $G'$ without destroying the planarity of $G'$.

<a id="pdf-ecfb8ec9f7b3-p005-b002"></a>
<!-- pdf-source: page=5; block=2; confidence=0.96 -->

**Proof of 2), the example and the end of the proof (printed p. 23).** A careful description of
$G'$ is somewhat tedious. Fig. 4 illustrates how $G'$ is constructed for $G=K_5$. Copies of $G_C$
and $G_F$ have been abbreviated as in Fig. 2 and 3. Numbers written next to nodes indicate the
bindings. All nodes with the same number are bound. The reader should have no trouble
generalizing this construction to an arbitrary non-planar graph $G$.

$G_F$ has been used in the above construction only to simplify the description of $G'$. Nodes in
the array which are bound by a chain of copies of $G_F$ can be merged into a single node while
keeping $G'$ planar. This completes the proof of 2).

<a id="pdf-ecfb8ec9f7b3-p005-b003"></a>
<!-- pdf-source: page=5; block=3; confidence=0.97 -->

**Concluding remarks (printed p. 23).** It is known that 2-colorability can be checked in
polynomial time for any graph [2] and that $k$-colorability, $k\ge5$, is trivial in the planar
case. The only open question, planar 4-colorability, hinges on the 4 color conjecture. However, it
might be possible to show that any algorithm, $A$, which actually produces a 4-coloring of a planar
graph input (or states that none exists if that is the case) is polynomial complete in the sense
that some complete problem becomes deterministic polynomial time recognizable in the presence of
an $A$ subroutine.

<a id="pdf-ecfb8ec9f7b3-p006-b001"></a>
<!-- pdf-source: page=6; block=1; confidence=0.96 -->

**References (printed p. 24).**

1. Karp, R.M. Reducibility Among Combinatorial Problems, in *Complexity of Computer Computations*,
   R.E. Miller and J.W. Thatcher, ed., Plenum Press, N.Y., 85-104.
2. Berge, C. *The Theory of Graphs and Its Applications*, John Wiley and Sons, N.Y., 1962.

*Transcription note.* The Karp entry prints no year (the volume is from 1972).

<a id="pdf-ecfb8ec9f7b3-p006-b002"></a>
<!-- pdf-source: page=6; block=2; confidence=0.85 -->

**Figure 1, the clause gadget $G^*$ (printed p. 24), described.** The figure is a drawing. This
description is the maintainer's reading of the page image.

The six nodes $v_1,\dots,v_6$ are labelled in the figure, and the figure is captioned $G^*$. Its
solid arcs ($A^*$, seven in all) are:

- the triangle $v_1v_2v_4$ (arcs $\{v_1,v_2\}$, $\{v_1,v_4\}$, $\{v_2,v_4\}$);
- the bridge $\{v_4,v_5\}$;
- the triangle $v_5v_6v_3$ (arcs $\{v_5,v_6\}$, $\{v_5,v_3\}$, $\{v_3,v_6\}$).

Three dashed lines join the outside nodes $s_1,s_2,s_3$ to $v_1,v_2,v_3$ respectively. So the two
inputs $s_1,s_2$ feed the first triangle, the third input $s_3$ feeds the second triangle, and
$v_6$ is the output.

*Maintainer note (not part of the source).* Properties i) and ii) of `pdf-ecfb8ec9f7b3-p004-b002`
hold for this reading. By hand: if $s_1,s_2,s_3$ all have colour $c$, then $v_1,v_2\ne c$ forces
$v_4=c$, and then $v_5\ne c$, $v_3\ne c$ and $v_5\ne v_3$ force $v_6=c$. By machine: enumerating
all 3-colourings for each of the 27 colourings of $s_1,s_2,s_3$ confirms i) (the output is forced
to the common colour) and ii) (otherwise all three output colours occur).

<a id="pdf-ecfb8ec9f7b3-p006-b003"></a>
<!-- pdf-source: page=6; block=3; confidence=0.80 -->

**Figure 2, the cross-over graph $G_C$ (printed p. 24), described.** The figure is a drawing,
with the modular representation of $G_C$ beside it. This description is the maintainer's reading
of the page image.

**(Left) $G_C$.** The figure labels only the four corners: $v_1$ (top left), $v_2$ (top right),
$v_1'$ (bottom right) and $v_2'$ (bottom left). It has 19 nodes and 34 arcs. Name the other 15
nodes as follows (the letters are the maintainer's): $B$, $C$ on the top edge between $v_1$ and
$v_2$; $E$; $F$, $G$, $H$ (a row, $H$ on the right edge); $I$, $J$, $K$ (the middle row); $L$, $M$,
$N$ (a row, $L$ on the left edge); $O$; and $Q$, $R$ on the bottom edge between $v_2'$ and $v_1'$.
The arcs are:

- outer boundary: $v_1B$, $BC$, $Cv_2$, $v_2H$, $Hv_1'$, $v_1'R$, $RQ$, $Qv_2'$, $v_2'L$, $Lv_1$;
- upper part: $v_1E$, $BE$, $EF$, $CG$, $CH$, $FG$, $GH$, $FJ$, $FK$, $GK$;
- middle: $v_1I$, $IJ$, $JK$, $Kv_1'$;
- lower part: $IM$, $IN$, $JN$, $LM$, $MN$, $LQ$, $MQ$, $NO$, $OR$, $Ov_1'$.

The drawing is symmetric under a half-turn, which exchanges $v_1\leftrightarrow v_1'$ and
$v_2\leftrightarrow v_2'$.

**(Right) Modular representation.** A small square with four pendant leads, labelled $v_1$ (top
left), $v_2$ (top right), $v_1'$ (bottom right) and $v_2'$ (bottom left). It stands for a copy of
$G_C$ in Figure 4.

*Maintainer note (not part of the source).* This edge list was checked by machine against every
claim the paper makes about $G_C$:

- the straight-line drawing with the read node positions has no crossing arcs, and the outer face
  meets $v_1,v_2,v_1',v_2'$ in that order (planarity and condition 2a);
- $G_C$ has 36 proper 3-colourings; in all of them $v_1,v_1'$ share a colour and $v_2,v_2'$ share
  a colour (condition 2b); and all nine pairs of colours of $(v_1,v_2)$ occur, so $G_C$ transmits
  the two colours independently;
- $v_2$ and $v_2'$ are joined by a chain of four copies of $G_F$ (Figure 3): the "diamonds"
  $(v_2;C,H;G)$, $(G;F,K;J)$, $(J;I,N;M)$ and $(M;L,Q;v_2')$, each written (end; shared arc; end).
  This is the argument of `pdf-ecfb8ec9f7b3-p002-b002`.

The agreement of this reading with all of these claims is the main evidence for it. The letters
and the arc names are not in the paper.

<a id="pdf-ecfb8ec9f7b3-p007-b001"></a>
<!-- pdf-source: page=7; block=1; confidence=0.85 -->

**Figure 3, the graph $G_F$ (printed p. 25), described.** The figure is a drawing, with the
modular representation of $G_F$ beside it. This description is the maintainer's reading of the
page image.

**(Left) $G_F$.** Four nodes: $u$ at the top, $v$ at the bottom, and two unlabelled middle nodes
joined by a horizontal arc. Both middle nodes are joined to $u$ and to $v$. So $G_F$ is two
triangles sharing an arc (a "diamond", $K_4$ minus the arc $\{u,v\}$), with 5 arcs, and $u$, $v$
are bound.

**(Right) Modular representation.** A diamond outline with a lead to $u$ at the top and a lead to
$v$ at the bottom. It stands for a copy of $G_F$ in Figure 4.

<a id="pdf-ecfb8ec9f7b3-p007-b002"></a>
<!-- pdf-source: page=7; block=2; confidence=0.80 -->

**Figure 4, the construction of $G'$ for $G=K_5$ (printed p. 25), described.** The figure is a
drawing. This description is the maintainer's reading of the page image.

**(Left) $G$.** $K_5$, drawn as a pentagon with its five diagonals.

**(Right) $G'$.** It is drawn with the modular representations of Figures 2 and 3. Every node of
the array carries a number from 1 to 5, the node of $K_5$ to which it is bound.

- **The top row** has five nodes numbered 1, 2, 3, 4, 5, joined by a horizontal path. These are
  the arcs $\{1,2\}$, $\{2,3\}$, $\{3,4\}$ and $\{4,5\}$.
- **Columns.** Below the top row, the numbers are carried down the columns by vertical chains of
  $G_F$ diamonds.
- **Crossovers.** Eight copies of $G_C$ (squares) each exchange the numbers of two adjacent
  columns. They lie on three diagonal staircases.
  - The first staircase moves 1 from the first column to the last. The order becomes 2 1 3 4 5,
    then 2 3 1 4 5, then 2 3 4 1 5, then 2 3 4 5 1.
  - The second staircase moves 2 from the first column to the fourth: 3 2 4 5 1, then 3 4 2 5 1,
    then 3 4 5 2 1.
  - The last crossover exchanges 3 and 4: 4 3 5 2 1.
- **New arcs.** Just before most crossovers, a short horizontal arc joins the two nodes that are
  about to be exchanged. Together with the square below it, this arc is drawn as a trapezoid.
  These arcs are $\{1,3\}$, $\{1,4\}$, $\{1,5\}$, $\{2,4\}$ and $\{2,5\}$. The first crossover's
  arc $\{1,2\}$ is part of the top path.
- **The bottom row** reads 4, 3, 5, 2, 1. The newly adjacent nodes 3 and 5 are joined by the last
  arc, $\{3,5\}$.

So every one of the ten arcs of $K_5$ appears exactly once, between two nodes that are adjacent in
some row. This is the scheme of `pdf-ecfb8ec9f7b3-p005-b001`: the rows of the array are permuted
by the crossovers, bubble-sort fashion.

*Maintainer note (not part of the source).* The staircase reading, the eight crossovers and the
ten arcs were read from the image. The number of $G_F$ diamonds in each column was not counted
exactly, and it does not matter for the construction.
