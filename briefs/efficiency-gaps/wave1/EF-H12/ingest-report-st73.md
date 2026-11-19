# EF-H12 · [St73] ingest, gadget comparison and final citation texts (maintainer, 2026-11-19)

This report records the ingest of Stockmeyer's paper, under Seyoon's ruling to ingest the actual
proof (option B of `ingest-report-gjs74.md`, "For Seyoon to decide", item 1). It compares the
paper's reduction with the course gadget and gives the final citation texts. They replace R1–R6
of `ingest-report-gjs74.md`. Nothing here is committed; the maintainer commits it.

## Summary

- **[St73] proves both results.**
  - Its only theorem (unnumbered, printed p. 22) reads "3-COLORABILITY and PLANAR
    3-COLORABILITY are polynomial complete".
  - Part 1) of the proof is a reduction from SATISFIABILITY WITH AT MOST 3 LITERALS PER CLAUSE
    to 3-COLORABILITY (pp. 22 and 21, with Fig. 1).
  - Part 2) is a reduction from 3-COLORABILITY to PLANAR 3-COLORABILITY by a planar cross-over
    graph (pp. 21, 20 and 23, with Figs. 2–4).
- **Printed pp. 20 and 22 are interchanged in the issue.** The text runs 19 → 22 → 21 → 20 → 23,
  while the running heads are in sequence. So the Theorem is on p. 22, not p. 20.
- **The course gadget is a variant of Stockmeyer's construction, with the same clause gadget.**
  - The six-node clause gadget of `ThreeSATToColoring.lean` is Stockmeyer's $G^*$ (Fig. 1),
    node for node, with the literals attached at the same places.
  - The literal layer is also the same.
  - Two things differ, both in how the "palette" is wired. The course uses a palette *triangle*
    where [St73] uses the single arc $\{t_1,t_2\}$. The course joins the output node to the base
    and to the false node; [St73] joins it to $t_2$ only.
  - So the course graph is Stockmeyer's graph plus one node and some arcs (exact statement
    below). The `Kleinberg–Tardos` guess in `ingest-report-gjs74.md` is superseded: whatever book
    the course took it from, the construction is [St73]'s.
- **[St73] is Karp's form, not Levin's.**
  - [St73] proves polynomial completeness in Karp's sense: an instance map only.
  - EF-H12 proves `LevinNPHard L3COL R3COL`. That adds a polynomial-time witness map and an exact
    output length.
  - [St73]'s construction yields the witness map in substance: a constant-size colouring table
    per clause, which exists by its property ii). But the paper does not write it ("The converse
    is similar", p. 21).
- **The final citation texts cite [St73] for the statement and for the reduction.**
  - [GJS74] is no longer needed in the Lean docstrings. Only a corroborating mention in
    `REPORT.md` is kept.
  - [St73] now has its own `## References` entry, so the second-hand "credited there to [St73]"
    wording of the old R1–R3 is gone. This settles item 2 of the GJS74 report's open questions.

## Source

- **Bibliographic data.** L. Stockmeyer, "Planar 3-Colorability is Polynomial Complete",
  *ACM SIGACT News* 5(3):19–25, July 1973, doi:10.1145/1008293.1008294.
- **The PDF.**
  - Seyoon uploaded it to the scratchpad as `st73-src/st73.pdf`.
  - It has 7 pages and SHA-256 `ecfb8ec9f7b38708e0b8486287cfbcce6369b92feffd8abd8201b062829dd287`.
    The hash was checked before extraction and again by the raw builder, and it matches.
  - The PDF is not copied into the repository.
- **What the PDF confirms.**
  - Page 1 reads "SIGACT News · 19 · July 1973 · PLANAR 3-COLORABILITY IS POLYNOMIAL COMPLETE†
    · Larry Stockmeyer · Massachusetts Institute of Technology · Cambridge, Massachusetts · March
    1973".
  - Every page carries the running head "SIGACT News", the page number and "July 1973". The page
    numbers run 19–25 over the 7 physical pages (physical page *p* is printed page *p* + 18).
  - So the journal, the month and year, the page range, the title and the author are confirmed.
  - The footnote † names Project MAC (ONR contract N00014-70-A-0362-0006) and NSF contract
    GJ00-4327.
- **What the PDF does not confirm.**
  - The PDF does not print the volume and number (5, No. 3) or the DOI. They come from the upload
    citation.
  - The volume, number and pages agree with [GJS74]'s reference list ("SIGACT News 5, No. 3
    (1973), 19-25", anchor `pdf-f17c4a237263-p017-b001`).
  - The PDF metadata has only the scan dates (2004-06-04/10).
  - No correction to the citation is needed.
- **The brief's [Sto73].** The PDF confirms the GJS74 report's side finding.
  - The title is "Planar 3-Colorability is *Polynomial Complete*", not "… is NP-complete" as
    `brief.md` has it.
  - The tag used here is `St73`, as in [GJS74]. `brief.md` was not edited.
- **The PDF is a scan.** Its text layer is OCR of a typescript, with recognition errors such as
  "July 1923", "o~" for the reduction sign, and "[I]" for "[1]".
- **Page order.** The order is forced by the sentences that run across page breaks. Each of these
  pairs is continuous, and no other order is:
  - p. 19 ends with the problem definitions; p. 22 opens with the Theorem.
  - p. 22 ends with the definition of $A$; p. 21 opens with "Now $G$ is 3-colorable iff …".
  - p. 21 ends with "There are four distinct nodes $v_1,v_1',v_2,v_2'$ of $G$ such that"; p. 20
    opens with "2a)".
  - p. 20 ends with "there is some row $i$ and some $j$,"; p. 23 opens with "$1\le j\le n-1$, such
    that".

## Files written

| File | Content |
|---|---|
| `blueprint/src/references/stockmeyer-1973-planar-3-colorability.raw.md` | Raw text of all 7 pages in physical order, with `<!-- pdf-page: N -->` markers. Six header comments: generated-by (with "awaiting Codex source review"), source hash, extractor, scope, the page-numbering and page-order note, and the OCR note. |
| `blueprint/src/references/stockmeyer-1973-planar-3-colorability.md` | Header: hash and validation status (awaiting Codex source review). Then the title and citation paragraph, a page-order paragraph, scope and conventions. Then 20 anchored blocks: 16 transcriptions (the whole text) and 4 described figures. |
| `blueprint/src/references/sources.json` | One new tag only: `St73`, with the full citation and document `stockmeyer-1973-planar-3-colorability`. See the sources.json notes below the table. |
| this report | — |

**`sources.json`.**

- The entry is placed in key order, between `Sho04` and `Vad12`.
- The file was re-read and compared byte for byte immediately before the write. The insertion
  was textual (6 added lines).
- It is still valid JSON. It round-trips through `json.dumps(indent=2, ensure_ascii=False)` byte
  for byte, before and after. All other tags are unchanged.

No other repository file was touched. In particular, `ingest-report-gjs74.md` and the GJS74
reference pair are not edited: this report supersedes their R1–R6. The concurrent Arora–Barak files
are untouched.

## Method and checks

- **Extraction.** `pypdf` 6.17.0 under `python3 -I`, using `extract_text()` in its default plain
  mode, as for GJS74 (the paper is single-column, so the modes differ little). Trailing spaces
  were removed. No control characters occurred (this was asserted).
- **Images.** The pages were rendered with `pypdfium2` under `python3 -I`, at 2× for whole pages.
  Crops at 3–4× were made for: Figures 1–4, the footnote, the reference list, the formula for
  $A$ (p. 22) and the foot of p. 20. **Every transcribed word was checked against the page
  images**, not the OCR layer.
- **Word check.** The prose words (≥ 3 letters) of the 16 transcribed blocks were compared with
  the OCR words of the same page. Maths, labels and notes were removed first. There were 683
  words and 4 misses: "Work" (OCR "tWork", with the dagger fused), "Computations" (OCR
  "Cpmputations"), and "Theory" and "Its" (OCR garbled by the underlining). All four were
  confirmed on the 4× crops. No transcribed word lacks support.
- **Figures.** These checks were run by machine under `python3 -I`, on the maintainer's reading of
  the figures. The scripts are in the scratchpad `st73-ingest/scripts/`.
  - **Fig. 1 ($G^*$).** Properties i) and ii) hold, checked over all 27 colourings of
    $s_1,s_2,s_3$. Stockmeyer's whole reduction of part 1) agrees with satisfiability on 300
    random small 3-CNFs.
  - **Fig. 2 ($G_C$; 19 nodes and 34 arcs, read off the drawing).**
    - The straight-line drawing at the read positions has no crossings.
    - The outer face meets $v_1,v_2,v_1',v_2'$ in that order.
    - $G_C$ has 36 proper 3-colourings. All of them bind $v_1$ to $v_1'$ and $v_2$ to $v_2'$, and
      all nine colour pairs of $(v_1,v_2)$ occur.
    - The reading is symmetric under a half-turn.
    - The chain of four $G_F$ diamonds from $v_2$ to $v_2'$ is present.

    So the reading agrees with every claim the paper makes about $G_C$.
  - **Fig. 3 ($G_F$).** $u$ and $v$ are bound.
- **Parse.** `proofmatch.document.parse_validated_markdown` (repository code, run with
  `python3 -I` and the repository on `sys.path`) parses the `.md`.
  - It finds 20 blocks, each with consistent provenance and the right fingerprint.
  - It assigns these kinds: Theorem → `theorem`; the problem and cross-over definitions →
    `definition`; the proof blocks → `proof`.
- **Not run.** No Lean was run, and no proofmatch matching. So no `\statementsource` or
  `\proofsource` may cite these anchors until an approved run, as with the earlier ingests.
- **Editorial choices** (stated in the `.md` header):
  - **Block order.** The blocks are in **reading order**, not physical-page order. Anchors keep the
    physical page, so they are not monotone in the file. The parser does not require monotone
    order. The raw file keeps physical order.
  - **Symbols.** The reduction sign is written $\propto$. Underlining becomes emphasis.
  - **Misprints** are kept with "[sic]" notes: "here in", "theNational", "purpose the the" in
    the footnote, and "0(n²)" for $O(n^2)$.
  - **Figure node names.** The letters naming the unlabelled nodes of $G_C$ are the maintainer's
    and are marked as such.

## Anchors created

Prefix `pdf-ecfb8ec9f7b3-`. Printed page = PDF page + 18. Rows are in reading order.

| Anchor | PDF p. | Printed p. | Passage | Kind |
|---|---|---|---|---|
| `p001-b001` | 1 | 19 | Title, author, affiliation, date; footnote † | transcription |
| `p001-b002` | 1 | 19 | Introduction: $k$-colourability is polynomial complete [Karp]; shown here for $k=3$ and planar $G$ | transcription |
| `p001-b003` | 1 | 19 | Definitions of 3-COLORABILITY and PLANAR 3-COLORABILITY | transcription |
| **`p004-b001`** | 4 | **22** | **Theorem.** 3-COLORABILITY and PLANAR 3-COLORABILITY are polynomial complete | transcription |
| `p004-b002` | 4 | 22 | Proof of 1): SAT (≤ 3 literals) $\propto$ 3-COL; clause gadget $G^*$, properties i), ii) | transcription |
| `p004-b003` | 4 | 22 | Proof of 1): the graph $G=(N,A)$ ($t_1,t_2$, literals, $r$ copies $G_i^*$) | transcription |
| `p003-b001` | 3 | 21 | Proof of 1): $G$ 3-colourable iff satisfiable; "The converse is similar" | transcription |
| `p003-b002` | 3 | 21 | Remark: $k$-colourability complete for every fixed $k\ge3$ (join with $K_m$) | transcription |
| `p003-b003` | 3 | 21 | Proof of 2): heading; *bound* nodes; cross-over graph, conditions 1), 2) | transcription |
| `p002-b001` | 2 | 20 | Conditions 2a) (common face, order $v_1,v_2,v_1',v_2'$) and 2b) (binding) | transcription |
| `p002-b002` | 2 | 20 | $G_C$ (Fig. 2) is a cross-over graph, via $G_F$ (Fig. 3) | transcription |
| `p002-b003` | 2 | 20 | The planar $G'$: a $p(n)\times n$ array, $p(n)\le O(n^2)$, row permutations $\sigma_i$ | transcription |
| `p005-b001` | 5 | 23 | Each arc $\{u_k,u_\ell\}$ added as $\{v_{ij},v_{i,j+1}\}$ keeping planarity | transcription |
| `p005-b002` | 5 | 23 | Fig. 4 example ($K_5$); merging $G_F$ chains; end of proof of 2) | transcription |
| `p005-b003` | 5 | 23 | Concluding remarks (2-colouring easy [2]; planar $k\ge5$ trivial; planar 4-colouring) | transcription |
| `p006-b001` | 6 | 24 | References [1] Karp, [2] Berge | transcription |
| **`p006-b002`** | 6 | **24** | **Figure 1, clause gadget $G^*$**, with a check of i), ii) | description (0.85) |
| `p006-b003` | 6 | 24 | Figure 2, cross-over graph $G_C$ (edge list) and its modular representation | description (0.80) |
| `p007-b001` | 7 | 25 | Figure 3, $G_F$ (diamond) and its modular representation | description (0.85) |
| `p007-b002` | 7 | 25 | Figure 4, $G'$ for $G=K_5$ (eight crossovers, three staircases) | description (0.80) |

## Locators

| What | Locator | Anchors |
|---|---|---|
| **(a) 3-COLORABILITY of general graphs is polynomial complete** | **[St73, Theorem, p. 22]**; proof: part 1), pp. 22 and 21 (written "pp. 21–22" in docstrings); gadget: Fig. 1, p. 24 | `p004-b001` (statement); `p004-b002`, `p004-b003`, `p003-b001` (proof); `p006-b002` (Fig. 1) |
| **(b) PLANAR 3-COLORABILITY is polynomial complete** | **[St73, Theorem, p. 22]**; proof: part 1) followed by part 2), pp. 21, 20 and 23; Figs. 2–4, pp. 24–25 | `p004-b001`; `p003-b003`, `p002-b001`–`p002-b003`, `p005-b001`, `p005-b002`; `p006-b003`, `p007-b001`, `p007-b002` |
| The problem 3-COLORABILITY ($f:N\to\{1,2,3\}$, adjacent nodes get different colours) | [St73, p. 19] | `p001-b003` |
| The notion used: Karp's polynomial completeness | [St73, p. 19] (citing Karp [1]) | `p001-b002` |
| $k$-colourability is complete for every fixed $k\ge3$ | [St73, p. 21] (remark after part 1)) | `p003-b002` |

Three things to note about (a):

- **It is a proved theorem.** The proof's two directions are not equally explicit:
  - **Soundness** (colouring → satisfying assignment) is written out on p. 21.
  - **Completeness** is "The converse is similar". It rests on property ii) of the gadget, which
    is stated without proof (p. 22).
- **It is Karp's form.** "Polynomial complete as defined by Karp [1]" means membership in NP plus
  a polynomial-time instance map from every NP problem. The paper does not discuss membership in
  NP or witness maps.
- **Its source problem is Karp's SATISFIABILITY WITH AT MOST 3 LITERALS PER CLAUSE.** The paper
  writes every clause with three literals $\sigma_{i1},\sigma_{i2},\sigma_{i3}$ and does not say
  how shorter clauses are handled (presumably by repeating a literal). EF-H12 widens clauses by
  repetition, which fits.

## Gadget comparison: [St73] part 1) vs `ThreeSATToColoring.lean`

**Which copy was read.** The course file is `TCSlib/Complexity/NPReductions/ThreeSATToColoring.lean`
on `records/dw7-phase6`, blob `589f2356…`. It is the same blob as at HEAD of the working branch.
It was read only (`git show`).

**Verdict: a variant of the same construction.** The two constructions have the same clause gadget,
the same literal layer and the same colour semantics. They differ in the palette wiring.

| | [St73] (pp. 22, 21; Fig. 1) | Course file (`EdgeRelation`, lines 132–154) |
|---|---|---|
| Palette | $t_1,t_2$ with the arc $\{t_1,t_2\}$ (no third node) | triangle `Base=0`, `True=1`, `False=2` |
| Literal nodes | $u_i,\bar u_i$; arcs $\{t_1,\sigma\}$ and $\{u_i,\bar u_i\}$ | `pos x`, `neg x`; arcs `Base`–literal and `pos x`–`neg x` |
| Clause gadget | $G^*$: triangle $v_1v_2v_4$, arc $v_4v_5$, triangle $v_5v_6v_3$ | triangle $\{0,1,2\}$, arc $\{2,3\}$, triangle $\{3,4,5\}$ |
| Literal attachments | $\sigma_{i1}\!-\!v_{i1}$, $\sigma_{i2}\!-\!v_{i2}$, $\sigma_{i3}\!-\!v_{i3}$ | `l1`–0, `l2`–1, `l3`–4 |
| Output node | $v_{i6}$, joined to $t_2$ only | node 5, joined to `Base` **and** `False` (lines 150–153) |
| Colour meaning | $t_1\mapsto1$ (base), $t_2\mapsto2$ (false), colour 3 = true | `Base`, `False`, `True` |
| Gadget copies | one per clause index $i=1,\dots,r$ | one per clause *value* (duplicate clauses share one) |

- **The gadgets are identical.** The map $v_1\mapsto0$, $v_2\mapsto1$, $v_4\mapsto2$,
  $v_5\mapsto3$, $v_3\mapsto4$, $v_6\mapsto5$, $s_j\mapsto$ `l`$_j$ is an isomorphism. It carries
  $G^*$ together with its three literal attachments onto the course gadget together with its
  attachments. This was checked by machine.
- **How the graphs relate.** Identify $t_1$ = `Base` and $t_2$ = `False`, and take the list of
  distinct clauses. Then the course graph is exactly Stockmeyer's graph plus three kinds of
  additions:
  - one new node `True`;
  - the arcs `True`–`Base` and `True`–`False`;
  - for each gadget, the arc node 5–`Base`.

  This holds for the part of the course graph on the palette, the literals and the gadgets of
  clauses *in the formula*. The course vertex type also has a gadget for every other clause
  value. Those gadgets have no internal arcs (the `c1 ∈ clauses` test, line 141), so they never
  affect colourability.
- **Consequences.**
  - Every 3-colouring of the course graph restricts to one of Stockmeyer's graph. So
    Stockmeyer's soundness argument (p. 21, $S=\{\sigma\mid f(\sigma)=3\}$ after normalising
    $t_1\mapsto1$, $t_2\mapsto2$) applies verbatim.
  - Conversely, Stockmeyer's completeness colouring with every $v_{i6}$ coloured "true" (which
    his properties i) and ii) allow) extends to the course graph.
  - The course's extra arcs pin node 5 to `True`. Stockmeyer only needs $v_6\ne t_2$.
- **For attribution under EF-H12-R2 (B).** Seyoon ruled that the course file gets a reader-only
  owner PR making `sat3Coloring` public.
  - `sat3Coloring`'s clause part `clauseGadgetColor` (line 163) is exactly the explicit
    completeness colouring that [St73] leaves as "The converse is similar".
  - The gadget it colours is [St73]'s $G^*$. So the published declaration can be attributed as
    "the completeness colouring of [St73]'s reduction (Theorem, part 1), pp. 21–22, Fig. 1),
    made explicit; course material".
  - Whether the owner PR may also add a `[St73]` line to the course file's `## References`
    (lines 27–28 today cite only the course) is item 3 under "For Seyoon to decide".

## Levin form and witness maps

- **What EF-H12 proves.** `LevinNPHard L3COL R3COL` (`ZeroKnowledge/NP.lean:654`), via
  `LevinReduction` (`:134`). Besides a Karp instance map `f`, this requires:
  - a polynomial-time **forward** witness map `w` with `R x y → R' (f x) (w x y)`;
  - an exact output length `|f x| = p(|x|)` with `p ≥ id`.

  No backward map is required. This is strictly stronger than Karp's polynomial completeness,
  which is what [St73] proves.
- **Does [St73]'s construction give the witness map directly?** In substance yes, in text no.
  - **The forward map** sends an assignment to a colouring:
    - $t_1\mapsto1$, $t_2\mapsto2$;
    - each literal to 3 if true and 2 if false;
    - each $G_i^*$ to a colouring with $v_{i6}\mapsto3$.

    The last exists by property i) or ii) and depends only on the three literal colours. So it
    is a fixed table of at most 27 entries, which makes the whole map polynomial time and local.
    [St73] states neither the table nor this direction ("The converse is similar", p. 21).
    EF-H12's `colorWord` (and, after the R2 (B) owner PR, the course's `sat3Coloring`) is that
    table made explicit.
  - **The backward map** (colouring → assignment) is explicit in [St73] (p. 21). Normalise the
    colours so that $t_1\mapsto1$ and $t_2\mapsto2$, then read off $S=\{\sigma\mid f(\sigma)=3\}$.
    EF-H12 does not need it.
  - **Not in [St73] at all:** the length regularity, and the padding by isolated vertices
    (`Padding.lean`). These remain EF-H12's own.
  - **Not used by EF-H12:** part 2) (planarity). Its witness map would also be local: each $G_C$
    and $G_F$ copy is coloured from the colours of its terminals, since all nine pairs occur
    (Fig. 2 check).

## Final citation texts (supersede R1–R6 of `ingest-report-gjs74.md`)

The places C1–C6 are those of the GJS74 report's table. They are in EF-H12's delivery,
`exchange/pass-shelat-ch5-8` at `36d9ac03c329544d33b1f3f9a73e6ce32152dde2`, folder
`inbox/fills/ef-h12-levin-3col/`, re-read for this report. Three changes from the old set:

- **[St73] replaces [GJS74]** as the source of both the statement and the reduction.
- **[GJS74] is dropped from the Lean docstrings.** It adds nothing EF-H12 uses: it gives a
  second-hand statement and a degree-4 planar theorem. It is kept only as a corroborating line in
  `REPORT.md`. If Seyoon wants it kept in Lean too, see decision 1.
- **The gadget citations of C6 become positive attributions to [St73]** (with the course
  variant disclosed), instead of the old "not [St73]'s" disclaimer.

**The [St73] References entry** (used by F1–F6):

```
* [St73] L. Stockmeyer, *Planar 3-Colorability is Polynomial Complete*, ACM SIGACT News 5(3),
  July 1973, pp. 19–25. (Theorem, p. 22; proof of part 1), the reduction from 3SAT, pp. 21–22
  (the text runs from p. 22 to p. 21); clause gadget, Fig. 1, p. 24.)
```

**F1 (C1), the docstring of `levinNPHard_L3COL`** (replaces the first sentence group; the proof
sketch is unchanged):

```
/-- **`3COL` is NP-hard with Levin reductions** [PS10, §4.7, Theorem 124.1, step 2 (the
hypothesis of the "every language in NP" form)]: every language `L` with a witness relation `R`
has a Levin reduction `(f, w)` to `(3COL, R_3COL)` with length polynomial `p ≥ id`,
`LevinNPHard L3COL R3COL`. In Karp form this is the polynomial completeness of 3-COLORABILITY
[St73, Theorem, p. 22]. *Deviation:* [St73] gives an instance map only; this theorem adds a
polynomial-time witness map and an exact output length (padding), reaches 3SAT along the circuit
route [AB09, Lemmas 6.10 and 6.11, p. 111], and ends with [St73]'s reduction from 3SAT
[St73, proof of the Theorem, part 1), pp. 21–22, Fig. 1] in the variant of the course material
(a palette triangle in place of [St73]'s arc `{t₁, t₂}`, and each gadget's output node joined to
the base as well as to the false node). The witness colouring, which [St73] leaves as "the
converse is similar", is explicit here.
```

**F2 (C2), `Hardness.lean` module docstring.**

- In the first paragraph, replace "followed by the 3SAT → 3-colouring gadget of the course
  material" with "followed by the 3SAT → 3-colouring reduction of [St73, proof of the Theorem,
  part 1), pp. 21–22], in the variant formalized in the course material".
- After "…the unconditional forms of [PS10, Theorem 124.1].", add: "In Karp form, the polynomial
  completeness of 3-colourability is [St73, Theorem, p. 22]; this file proves the stronger Levin
  form, with a witness map and exact output lengths."
- Add the [St73] entry to `## References`. Keep [AB09], [PS10] and the course entry.

**F3 (C3), `LevinHardness.lean` facade.**

- In the opening paragraph, replace "and the course 3SAT → 3-colouring reduction" with "and the
  3SAT → 3-colouring reduction of [St73] in the course material's variant".
- Add to `## References`:
  - the [St73] entry;
  - the course entry, which the facade omits today:

    ```
    * CS 294-268 course material (UC Berkeley, Spring 2026, V. Guruswami), the 3SAT →
      3-colouring reduction as formalized in `Complexity/NPReductions/ThreeSATToColoring.lean`.
    ```

**F4 (C4), optional: the `ZeroKnowledge.lean` facade.**

- The bullet becomes: "`LevinHardness` — `3COL` is NP-hard with Levin reductions
  (`levinNPHard_L3COL`; Karp form: [St73, Theorem, p. 22]), making [PS10, Theorem 124.1]
  unconditional."
- Add the [St73] entry to `## References`.

**F5 (C5), `REPORT.md` Attribution.** This is a records-side note if the REPORT is kept verbatim.

- Add a bullet: "[St73] Theorem p. 22 (polynomial completeness of 3-COLORABILITY) and the proof
  of its part 1), pp. 21–22 with Fig. 1 p. 24 (the reduction from 3SAT); anchors
  `pdf-ecfb8ec9f7b3-p004-b001`, `-p004-b002`, `-p004-b003`, `-p003-b001`, `-p006-b002` of
  `stockmeyer-1973-planar-3-colorability`".
- Replace "Garey–Johnson and Stockmeyer are not cited (Q-H12-2: not ingested)." with:

  > The polynomial completeness of 3-colourability and the 3SAT → 3COL reduction are cited as
  > [St73]. The course gadget is [St73]'s clause gadget with a palette triangle and an extra
  > base arc on the output node. [GJS74, §II, p. 52] states the same result and credits it to
  > [St73] (corroboration only; not cited in Lean). [GJ79] is not ingested and is not cited.

**F6 (C6), the gadget files: attribution, recommended (no longer optional).**

- **`Gadget.lean`, module docstring.** After the first paragraph, add:

  ```
  This is the graph of Stockmeyer's reduction from 3SAT [St73, proof of the Theorem, part 1),
  p. 22, Fig. 1 p. 24] in the course material's variant: gadget nodes `0, …, 5` are [St73]'s
  `v₁, v₂, v₄, v₅, v₃, v₆`, with the literals attached at `0, 1, 4` as at `v₁, v₂, v₃`; the
  palette is a triangle (base, true, false) instead of [St73]'s arc `{t₁, t₂}` (base, false), and
  gadget node `5` is joined to the base as well as to the false node, which [St73] does not do.
  ```

  Add the [St73] entry to its `## References`.
- **`ColoringWitness.lean`, module docstring.** Add: "This is the completeness colouring of
  [St73]'s reduction, which the paper leaves as 'the converse is similar' [St73, p. 21], made
  explicit (disclosed re-derivation of the course's `sat3Coloring`)." Add the [St73] entry. Once
  the R2 (B) owner PR publishes `sat3Coloring`, the "re-derivation" wording follows that PR's
  landing.
- **`Soundness.lean`, `ColoringGraph.lean`, `ColoringParse.lean`, `Bridge.lean`.** Keep the
  course attribution. Optionally add "([St73]'s reduction, course variant)" after the first
  mention of the course reduction, with the [St73] entry in `## References`. `Soundness.lean`
  transports the course theorem, whose argument is [St73]'s, p. 21.
- **No declaration should cite [St73] for the Levin form, the padding or the circuit route.**

**Blueprint.** Any `\statementsource{stockmeyer-1973-planar-3-colorability}{pdf-ecfb8ec9f7b3-p004-b001}`
or `\proofsource{…}{pdf-ecfb8ec9f7b3-p004-b002}` must wait for an approved proofmatch run. The
anchors are new and unreviewed.

**The gate after F1–F6** (the landing edit LE-h12-doc, together with F07's other items) checks
five things:

- (a) [St73] is cited for Karp's statement and for the 3SAT → 3COL reduction only;
- (b) the deviation note (Levin vs Karp; the explicit witness colouring; the palette-triangle
  variant) is present in F1;
- (c) no declaration cites [St73] for the circuit route or the padding;
- (d) [GJS74] no longer appears in Lean, unless decision 1 says otherwise;
- (e) the page locator for the Theorem is p. 22, not p. 20.

## For Seyoon to decide

1. **Keep [GJS74] in Lean at all?**
   - **Recommendation: no.** Use [St73] alone, and keep [GJS74] only in `REPORT.md`
     (corroboration).
   - **Alternative:** keep "[GJS74, §II, p. 52] (a restatement, crediting [St73])" as a second
     reference in F2's References. It adds no content EF-H12 uses.
2. **The page-range form.** The proof of part 1) runs from p. 22 to p. 21. F1–F6 write it
   "pp. 21–22", and the References entry says the text runs backwards.
   - Alternative: "pp. 22 and 21" everywhere (more exact, less conventional).
3. **The course file's attribution in the R2 (B) owner PR.** Should the reader-only PR that makes
   `sat3Coloring` public also add the [St73] References line and a one-line variant note to
   `ThreeSATToColoring.lean`?
   - Arguments for: the course gadget *is* [St73]'s. Adding the line closes the course file's
     own policy §2 gap (it cites only the course).
   - Arguments against: it widens a "reader-only" PR into a docstring edit of course material.
   - Proposed lines, if yes:

     ```
     - [St73] L. Stockmeyer, *Planar 3-Colorability is Polynomial Complete*, ACM SIGACT News
       5(3), July 1973, pp. 19–25 (Theorem, part 1), pp. 21–22, Fig. 1): the clause gadget; this
       file uses a palette triangle and joins gadget node 5 to Base as well as False.
     ```
4. **F4 and the optional parts of F6** are optional.
5. **The block order of the `.md`.** It is in reading order, not physical order, because of the
   page interchange. The parser accepts it. If a downstream tool needs monotone anchors, the
   blocks can be reordered with no text change.
6. **Source review.** The new reference pair is marked "awaiting Codex source review". The blocks
   most in need of review:
   - Figure 2 (`p006-b003`, confidence 0.80): an edge list read from a drawing. It is
     machine-consistent with all the paper's claims, but it is still a reading.
   - Figure 4 (`p007-b002`, 0.80).
   - The page-order claim (header).

## Permissions

- No permission was denied.
- Only `python3 -I` was used (pypdf, pypdfium2/PIL, json, and the repository's own
  `proofmatch.document` parser), with read-only git commands. No network, no Lean, no build.
- The work directory was the scratchpad `st73-ingest/`, with `out/`, `img/` and `scripts/`.
  Nothing was removed.
- The PDF was not copied into the repository. Nothing was committed or pushed.
