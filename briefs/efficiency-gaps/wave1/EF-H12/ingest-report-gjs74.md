# EF-H12 · [GJS74] ingest and citation check (maintainer, 2026-11-19)

This report records the ingest of the 3-colouring source under rulings EF-H12-R4 A and Q-H12-2 A,
and the citation check of EF-H12's delivery against it. Nothing here is committed; the maintainer
commits it.

## Summary

- **[GJS74] does not prove that 3-colourability is NP-complete, and it has no reduction from
  3SAT to 3-colouring.** It *states* that GRAPH 3-COLORABILITY is NP-complete, even for planar
  graphs, and credits this to [St73] (Stockmeyer). The statement is in §II on printed p. 52. It
  has no theorem number and no proof.
- **[GJS74]'s only colouring theorem is Theorem 2.1 (p. 53).** It reduces planar
  3-colourability to planar 3-colourability with node degree at most 4.
- **[GJS74] can therefore anchor only the statement** "3COL is NP-complete" (Karp reductions).
  It cannot anchor the 3SAT → 3COL gadget, and it cannot anchor the Levin (witness-map) form.
- **EF-H12's delivery cites no 3-colouring source today.** It has no [GJ79], [Sto73]/[St73] or
  Karp citation. REPORT.md says so explicitly.
- **The proposed edit adds [GJS74, §II, p. 52] in three Lean places** (module docstrings and the
  `levinNPHard_L3COL` docstring) and in REPORT.md. The citation carries a deviation note. The
  gadget citations stay with the course material.
- **The course file `ThreeSATToColoring.lean` cites only the CS 294-268 course material.** Its
  gadget is the textbook OR-gadget reduction (a palette triangle and two chained triangles per
  clause). That gadget is not in [GJS74].

## Source

- **Bibliographic data.** M. R. Garey, D. S. Johnson, L. Stockmeyer, "Some simplified
  NP-complete problems", *Proceedings of the Sixth Annual ACM Symposium on Theory of Computing
  (STOC '74)*, pp. 47–63, 1974, doi:10.1145/800119.803884.
- **The PDF.** It was uploaded by Seyoon to the scratchpad as `col3-src/gjs74.pdf`. It has 17
  pages and SHA-256 `f17c4a237263d340af14431df9a377bed1f5f1c3f9d5a28f7d0d05c1422989bf`. The hash
  was checked before extraction and matches. The PDF is not copied into the repository.
- **What the PDF confirms.**
  - The title page reads "SOME SIMPLIFIED NP-COMPLETE PROBLEMS by M. R. Garey and D. S. Johnson,
    Bell Laboratories, Murray Hill, New Jersey and L. Stockmeyer, Massachusetts Institute of
    Technology, Cambridge, Massachusetts". Stockmeyer's footnote names Project MAC and NSF grant
    GJ-34671.
  - The printed page numbers run 47–63 over the 17 physical pages (physical page *p* is printed
    page *p* + 46). This agrees with "pp. 47–63".
- **What the PDF does not confirm.**
  - There is no running header or footer. The PDF prints no venue, year or DOI. The PDF metadata
    has only creation and modification dates (2000-09-06/07, the scan).
  - So "STOC '74", "1974" and the DOI come from the upload citation. They are unconfirmed but
    not contradicted. The latest work the paper cites is from 1973.
  - The citation is kept as given; no correction is needed.
- **A side finding on the brief's [Sto73].** `brief.md` (Sources; Q-H12-2) titles it "*Planar
  3-colorability is NP-complete*". [GJS74]'s reference list (p. 63, `p017-b001`) gives
  **"Planar 3-Colorability is Polynomial Complete," SIGACT News 5, No. 3 (1973), 19-25**, under
  the tag [St73]. The brief's title for [Sto73] appears to be wrong.
- **The PDF is a scan.** Its text layer is OCR of a typescript and has many recognition errors
  (for example "kBSTRACT", and "~" for the reduction sign α).

## Files written

| File | Content |
|---|---|
| `blueprint/src/references/garey-johnson-stockmeyer-1974-simplified-np-complete.raw.md` | Raw text of all 17 pages, with `<!-- pdf-page: N -->` markers. Five header comments: generated-by (with "awaiting Codex source review"), source hash, extractor, scope (pp. 1–17, printed 47–63), and the page-numbering and OCR note. |
| `blueprint/src/references/garey-johnson-stockmeyer-1974-simplified-np-complete.md` | Header: hash and validation status (awaiting Codex source review). Title and citation paragraph. A scope paragraph with page ranges, saying that the paper does not prove 3COL NP-complete itself. Then 25 anchored blocks. |
| `blueprint/src/references/sources.json` | One new tag only: `GJS74`, with the full citation and document `garey-johnson-stockmeyer-1974-simplified-np-complete`. It is placed in key order (between `FS99` and `GRS25`). The file was re-read and checked unchanged immediately before the write. It is still valid JSON and round-trips byte for byte. |
| this report | — |

No other repository file was touched. The concurrent Arora–Barak ch. 2/6 files are untouched.

## Method and checks

- **Extraction.** `pypdf` 6.17.0 under `python3 -I`, using `extract_text()` in its default plain
  mode.
  - This differs from EF-D4, which used `extraction_mode="layout"`. On this two-column scan, the
    layout mode interleaves the left and right columns line by line. The plain mode reads them
    column by column.
  - Trailing spaces were removed. One DEL control character (p. 14, the Table II header) was
    replaced by U+FFFD. The raw header records all of this.
- **Transcription.** The `.md` blocks were checked against the page images, not the OCR layer.
  The images were rendered with `pypdfium2` under `python3 -I`, at 2× for whole pages and 2.5–6×
  for crops (the Theorem 2.1 statement, the "k > 4" phrase, Figure 1, and the theorem headings
  on pp. 50, 51, 56, 59 and 60).
- **Kinds of block.**
  - The colouring blocks are transcriptions: pp. 52–54 and the appendix entry.
  - The other problems have one summary block each, as asked: MAX CUT family, OLA, Hamiltonian,
    node cover. The introduction and concluding remarks are summaries too.
  - Figure 1 is a described figure, at confidence 0.85. It includes an edge list of `H₃` read
    from the drawing, and a *Maintainer note* that checks (2.1D) for `H₃` from that edge list.
- **Word check.** The prose words of the 17 transcribed blocks (≥ 3 letters; maths, labels and
  notes removed) were compared with the OCR words of the same page. There were 9 misses. Every
  one is an OCR error in the layer and was confirmed on the image: "tape", "literature",
  "degrees", "including", "incident", "being", "disjunction", "each" and "Gav". No transcribed
  word lacks support.
- **Parse.** `proofmatch.document.parse_validated_markdown` (repository code, run with
  `python3 -I` and the repository on `sys.path`) parses the `.md`: 25 blocks, each with
  consistent provenance and the right fingerprint.
- **Not run.** No Lean was run, and no proofmatch matching. So no `\statementsource` or
  `\proofsource` may cite these anchors until an approved run, as with the earlier ingests.
- **Editorial choices** (stated in the `.md` header):
  - α is written `\mathrel{\alpha}`; edges are written with braces; underlining becomes
    emphasis.
  - The two numbered lists of the p. 53 table are joined into one table.
  - "For k > 4" (p. 53) is kept as printed, with a note that `k ≥ 4` is evidently meant.
  - The misprint "Theorem 2.3.2" (p. 59) is noted.

## Anchors created

Prefix `pdf-f17c4a237263-`. Printed page = PDF page + 46.

| Anchor | PDF p. | Printed p. | Passage | Kind |
|---|---|---|---|---|
| `p001-b001` | 1 | 47 | Title page, authors, affiliations, footnote † | transcription |
| `p001-b002` | 1 | 47 | Abstract | transcription |
| `p001-b003` | 1 | 47–48 | Introduction | summary |
| `p002-b001` | 2 | 48 | Karp derived CHROMATIC NUMBER etc. from SAT3; plan of the second half | transcription (two sentences) |
| `p002-b002` | 2 | 48 | Basic definitions: languages, `π`, polynomial reducibility `α`, NP-complete | transcription |
| `p002-b003` | 2 | 48 | Problems as recognition problems; appendix pointer; footnote `(N,A)` | transcription |
| `p002-b004` | 2 | 48–51 | §I MAX CUT family: Theorems 1.1–1.4 | summary |
| `p005-b001` | 5 | 51–52 | §I OPTIMAL LINEAR ARRANGEMENT: Theorem 1.5 | summary |
| `p006-b001` | 6 | 52 | §II opening: CLIQUE trivial; planar MAX CUT polynomial | transcription |
| **`p006-b002`** | 6 | **52** | **§II: GRAPH 3-COLORABILITY is NP-complete even for planar graphs [St73]** | transcription |
| `p007-b001` | 7 | 53 | Continuation; table of results 1–5 with degree bounds | transcription |
| `p007-b002` | 7 | 53 | Degree bounds best possible; Brooks [B41] (max degree 3 easy); corollaries; open problems | transcription |
| **`p007-b003`** | 7 | **53** | **Theorem 2.1** statement | transcription |
| `p007-b004` | 7 | 53 | Proof of Theorem 2.1: node substitutes `H₃`, `H_k` | transcription |
| `p007-b005` | 7 | 53 | Facts (2.1A)–(2.1D) | transcription |
| `p007-b006` | 7 | 53 | Construction of `G'`: embedding, `v₁…v_r`, `G₀…G_r` | transcription |
| `p007-b007` | 7 | 53 | Figure 1 (`H₃`, `H₅`), with a maintainer note checking (2.1D) for `H₃` | description |
| `p008-b001` | 8 | 54 | Proof of Theorem 2.1 concluded ∎ | transcription |
| `p008-b002` | 8 | 54–59 | Hamiltonian results: Theorems 2.2, 2.3 | summary |
| `p013-b001` | 13 | 59–62 | Node cover results: Theorems 2.4, 2.5; planar node cover with degree ≤ 6 | summary |
| `p016-b001` | 16 | 62 | §III Concluding remarks (CHROMATIC NUMBER polynomial on chordal etc.) | summary |
| `p016-b002` | 16 | 62 | Appendix: SAT3 [K72] | transcription |
| **`p016-b003`** | 16 | **62** | **Appendix: GRAPH 3-COLORABILITY [St73] definition** | transcription |
| `p016-b004` | 16 | 62–63 | Appendix: CLIQUE, EXACT COVER, HAMILTONIAN PATH/CIRCUIT, NODE COVER | summary |
| `p017-b001` | 17 | 63 | References B41, C71, Gav72, K72, St73 | transcription |

## Locator of the 3-colourability result

| What | Locator | Anchor |
|---|---|---|
| **GRAPH 3-COLORABILITY is NP-complete (even for planar graphs)**: stated, credited to [St73], no number, no proof here | **[GJS74, §II, p. 52]** | `pdf-f17c4a237263-p006-b002` |
| Definition of GRAPH 3-COLORABILITY (map `f : N → {1,2,3}`, adjacent nodes get different colours) | [GJS74, Appendix, p. 62] | `pdf-f17c4a237263-p016-b003` |
| Planar 3-colourability with node degree ≤ 4 is NP-complete | [GJS74, Theorem 2.1, p. 53] (table, result 1) | `p007-b003` (statement), `p007-b001` (table), `p007-b004`–`p008-b001` (proof) |
| Degree bound 4 is best possible (max degree 3 is polynomial, by Brooks) | [GJS74, §II, p. 53] | `pdf-f17c4a237263-p007-b002` |
| Notion of NP-completeness used (Karp reducibility `α`, one-tape TMs) | [GJS74, §I preamble, p. 48] | `pdf-f17c4a237263-p002-b002` |
| Karp derived CHROMATIC NUMBER (among others) from SAT3 | [GJS74, p. 48] | `pdf-f17c4a237263-p002-b001` |

Use the first row to cite "3COL is NP-complete". Three things to note about it:

- **It is a cited statement, not a proved theorem.** The proof is in [St73], which is not
  ingested.
- **It is the Karp/Cook form.** It concerns polynomial reducibility of languages. It says nothing
  about witness maps.
- **It concerns the decision problem** under [GJS74]'s encoding conventions (encoding details are
  omitted on p. 48).

## Citation check of EF-H12's delivery

**Scope of the check.**

- **What was checked.** The delivery is `exchange/pass-shelat-ch5-8` at
  `36d9ac03c329544d33b1f3f9a73e6ce32152dde2`, folder `inbox/fills/ef-h12-levin-3col/`. Its
  `src/` (14 files) and `REPORT.md` were read with `git show`/`git grep` at that commit. The
  review is `final-r1/review.md`, finding EFH12-F07.
- **The search.** `git grep -i -E "GJ79|Sto73|St73|GJS74|Garey|Stockmeyer|Karp|K72|A1\.1|GT4"`
  over `src/` and `REPORT.md`.
  - Result: **no citation of any 3-colouring source**. The only mention is
    `REPORT.md:260`: "Garey–Johnson and Stockmeyer are not cited (Q-H12-2: not ingested)".
  - F07 records the same ("Garey–Johnson and Stockmeyer are not cited … The final citation gate
    waits for the Q-H12-2 ingestion (R4)").
- **Where the delivery asserts 3COL hardness.** Instead of a source, it gives [PS10, §4.7,
  Theorem 124.1, step 2], [AB09, Lemmas 6.10 and 6.11, p. 111] and "the course 3SAT →
  3-colouring reduction". Below are every such place, and the places that attribute the gadget.

| # | Place (path under `src/TCSlib/Cryptography/` unless noted) | What it says now | Verdict | Replacement |
|---|---|---|---|---|
| C1 | `ZeroKnowledge/LevinHardness/Hardness.lean:198-202`, docstring of `levinNPHard_L3COL` | "`3COL` is NP-hard with Levin reductions [PS10, §4.7, Theorem 124.1, step 2 …]; [AB09, Lemmas 6.10 and 6.11, p. 111] for the circuit route and the course 3SAT → 3-colouring reduction" | No published source for 3COL hardness; the policy §2 deviation is not stated | **R1** below |
| C2 | `ZeroKnowledge/LevinHardness/Hardness.lean:19-38` (module docstring) and `:55-63` (`## References`) | Same attribution; References: [AB09], [PS10], course material | Same | **R2** below |
| C3 | `ZeroKnowledge/LevinHardness.lean:24-30` (facade docstring) and `:47-53` (`## References`) | "…along the circuit route [AB09, …] and the course 3SAT → 3-colouring reduction, which proves `LevinNPHard L3COL R3COL`"; References: [AB09], [PS10] only (the course material is not listed) | Same, and the course entry is missing | **R3** below |
| C4 | `ZeroKnowledge.lean:63-64` (top facade bullet) and `:68-72` (References) | "`LevinHardness` — `3COL` is NP-hard with Levin reductions (`levinNPHard_L3COL`) …"; References: [PS10] | Optional: a facade bullet points to the file | **R4** (optional) |
| C5 | `inbox/fills/ef-h12-levin-3col/REPORT.md:252-260` (Attribution) | "Garey–Johnson and Stockmeyer are not cited (Q-H12-2: not ingested)" | Out of date once GJS74 is filed | **R5** below |
| C6 | `ZeroKnowledge/LevinHardness/`: `Gadget.lean:15-17, 49-55`; `ColoringGraph.lean:20-21, 54-60`; `ColoringParse.lean:17-18, 46-52`; `ColoringWitness.lean:22-26, 45-51`; `Soundness.lean:16-22, 43-49`; `Bridge.lean:19, 52-58` | The gadget, its colouring and its soundness are attributed to "CS 294-268 course material … 3SAT → 3-colouring reduction (`ThreeSATToColoring.lean`)" | **Keep.** [GJS74] contains no 3SAT → 3COL gadget, so citing it here would be a false attribution. The `(§2.3.)` on [AB09] entries is F07's separate wording issue (LE-h12-doc) | none for GJS74; optionally **R6** |

**R1, the docstring of `levinNPHard_L3COL`** (replaces the first sentence group; the proof
sketch is unchanged):

```
/-- **`3COL` is NP-hard with Levin reductions** [PS10, §4.7, Theorem 124.1, step 2 (the
hypothesis of the "every language in NP" form)]: every language `L` with a witness relation `R`
has a Levin reduction `(f, w)` to `(3COL, R_3COL)` with length polynomial `p ≥ id`,
`LevinNPHard L3COL R3COL`. The NP-completeness of graph 3-colourability under Karp reductions is
[GJS74, §II, p. 52], where it is credited to Stockmeyer [St73]. *Deviation:* this theorem
strengthens it to Levin reductions (polynomial-time witness maps both ways are not part of
[GJS74]'s statement) and proves it along the circuit route [AB09, Lemmas 6.10 and 6.11, p. 111]
and the course 3SAT → 3-colouring gadget, not by [St73]'s reduction.
```

**R2, `Hardness.lean` module docstring.**

- After "…the unconditional forms of [PS10, Theorem 124.1].", add: "In Karp form, the
  NP-completeness of graph 3-colourability is [GJS74, §II, p. 52] (credited there to [St73]);
  this file proves the stronger Levin form by its own reduction."
- Add to `## References`:

  ```
  * [GJS74] M. R. Garey, D. S. Johnson, L. Stockmeyer, *Some Simplified NP-Complete Problems*,
    Proceedings of the Sixth Annual ACM Symposium on Theory of Computing (STOC '74), 1974,
    pp. 47–63. (§II, p. 52: GRAPH 3-COLORABILITY is NP-complete, credited to [St73];
    Appendix, p. 62: the problem.)
  ```

**R3, `LevinHardness.lean` facade.**

- Append to the opening paragraph: "(In Karp form, the NP-completeness of 3-colourability is
  [GJS74, §II, p. 52].)"
- Add the [GJS74] entry from R2 to `## References`.
- Also add the course-material entry that the facade omits. That entry is not a GJS74 matter,
  but it is the same attribution gap.

**R4, optional: `ZeroKnowledge.lean` facade.** The bullet becomes: "`LevinHardness` — `3COL` is
NP-hard with Levin reductions (`levinNPHard_L3COL`; NP-completeness of 3-colourability:
[GJS74, §II, p. 52]), making [PS10, Theorem 124.1] unconditional." Add the [GJS74] entry to
`## References`.

**R5, `REPORT.md` Attribution** (a records-side note if the REPORT is kept verbatim):

- Add a bullet: "[GJS74] §II p. 52 (the NP-completeness of GRAPH 3-COLORABILITY, credited to
  [St73]) and Appendix p. 62 (its definition), statement only".
- Replace the sentence "Garey–Johnson and Stockmeyer are not cited (Q-H12-2: not ingested)."
  with: "The NP-completeness of 3-colourability is cited as [GJS74, §II, p. 52] (anchor
  `pdf-f17c4a237263-p006-b002` of `garey-johnson-stockmeyer-1974-simplified-np-complete`).
  [GJS74] gives no 3SAT → 3COL reduction, so the gadget remains attributed to the course
  material. [GJ79] and [St73] are not ingested and are not cited."

**R6, optional (C6): a one-line disclosure** in `Gadget.lean`'s module docstring: "The gadget is
the course's; it is not the reduction of [St73], to which [GJS74, §II, p. 52] credits the
NP-completeness of 3-colourability."

**Blueprint.** Any `\statementsource{garey-johnson-stockmeyer-1974-simplified-np-complete}{pdf-f17c4a237263-p006-b002}`
must wait for an approved proofmatch run. The anchors are new and unreviewed.

**F07.** The R1–R5 wording belongs in the landing edit LE-h12-doc together with F07's other
items. After it, the Codex gate checks: (a) that [GJS74, §II, p. 52] is cited only for the
statement; (b) that no gadget declaration cites [GJS74]; and (c) that the deviation note
(Levin vs Karp; own reduction vs [St73]) is present.

## The course file `TCSlib/Complexity/NPReductions/ThreeSATToColoring.lean`

- **Which copy was read.** The working tree at `1a59b0132` (branch
  `cryptography/pass-shelat-ch2-4`), blob `589f2356…`. The same blob is on
  `records/dw7-phase6`. The file was read only.
- **Its source.** The only citation is lines 27–28, `## References`: "Course material from
  CS 294-268 (UC Berkeley, Spring 2026), V. Guruswami". No published source is cited.
- **Its gadget** (docstring lines 41–57; `EdgeRelation`, lines 132–154):
  - a palette triangle: Base, True, False;
  - one node per literal, joined to Base, with each `pos x`–`neg x` pair joined;
  - six nodes per clause: the triangle {0,1,2}, the edge {2,3} and the triangle {3,4,5}, with
    literals 1, 2, 3 joined to nodes 0, 1, 4;
  - node 5 joined to Base and False, so it must be True.

  This is the standard textbook reduction from 3SAT, made of two chained OR-gadgets per clause.
- **[GJS74] has a different gadget, for a different reduction.**
  - It has **no** SAT3 → 3-colourability reduction at all; it takes the NP-completeness from
    [St73].
  - Its only colouring gadget is the node substitute `H_k` of Theorem 2.1. That is an 8-node
    chain of triangles (`H₃`), glued into `H_k`, and it forces all outlets to one colour. It
    reduces degree within planar 3-colourability (`p007-b004`–`p007-b007`).
  - So the course gadget does **not** match [GJS74]. It is a different, textbook gadget.
- **Which textbook, unverified.** I believe it matches Kleinberg–Tardos, *Algorithm Design*,
  §8.7 (the 3-colouring reduction with a six-node clause gadget whose top node is joined to False
  and Base). This is from memory; that book is not ingested and was not checked. Any
  attribution of the gadget beyond "course material" needs its own ingest.

## For Seyoon to decide

1. **Is [GJS74] enough for Q-H12-2 A?**
   - Q-H12-2 A asked for "one published 3-colouring source ([GJ79, App. A1.1, GT4] or
     [Sto73])". [GJS74] is neither. It is a published, peer-reviewed *statement* of the result
     by one of [St73]'s authors (§II, p. 52), but it has no proof and no 3SAT → 3COL gadget.
   - **(A, recommended)** Accept it for the statement-level citation (R1–R5). Keep the gadget
     attributed to the course material, and disclose the Levin-vs-Karp and gadget deviations.
   - (B) Also ingest [St73] (SIGACT News 5(3):19–25, 1973), which contains the actual proof.
     Then cite [St73] for the proof as well, and keep [GJS74] for the statement and the
     definition.
   - (C) Ingest [GJ79] App. A1.1 [GT4] as originally proposed. That is also a secondary
     statement.
2. **[St73] in docstrings.** R1–R3 name [St73] only as "credited there to [St73]", inside the
   [GJS74] citation, and add no `[St73]` References entry, because it is not ingested.
   - Is this second-hand mention acceptable?
   - Or should it read "credited there to Stockmeyer" without a tag?
3. **Correct the brief's [Sto73] title.** `brief.md` says "Planar 3-colorability is
   NP-complete". [GJS74] p. 63 gives "Planar 3-Colorability is Polynomial Complete". The tag
   also differs ([Sto73] in the brief, [St73] in the paper). `brief.md` was not edited (outside
   the write scope).
4. **Facade R4 and gadget disclosure R6** are optional.
5. **Source review.** The new reference pair is marked "awaiting Codex source review". The
   Figure 1 description (`p007-b007`, confidence 0.85) is the block most in need of review,
   because the paper gives the gadget only as a drawing.

## Permissions

- No permission was denied.
- Only `python3 -I` (pypdf, pypdfium2, json, and the repository's own `proofmatch.document`
  parser) and read-only git commands were used. No network, no Lean, no build.
- The work directory was the scratchpad `gjs74-ingest/` (nothing was removed). The PDF was not
  copied into the repository. Nothing was committed or pushed.
