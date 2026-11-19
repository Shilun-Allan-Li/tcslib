# EF-H12 · [AB09] ch. 2 and ch. 6 ingest and citation check (maintainer, 2026-11-19)

Rulings EF-H12-R4 A and Q-H12-2 A: ingest [AB09] chapters 2 and 6, then re-run EF-H12's citation
check (finding EFH12-F07 included) against the ingested text. This report records that ingest and
the check. The 3-colouring source is covered separately in `ingest-report-gjs74.md`. Nothing here
is committed by the ingester; the maintainer commits it.

## Summary

- **Source.** The ingested text is the authors' **web draft** (footers "Web draft 2007-01-08
  21:59"), not the CUP 2009 edition. The draft's chapter 2 numbering is close to the numbers TCSlib
  cites. Its chapter 6 numbering is **completely different**:
  - the circuit-SAT material TCSlib cites as [AB09, §6.1.2, Def 6.9, Lemmas 6.10/6.11, p. 111] is
    the draft's **§6.7, Definition 6.30, Lemmas 6.31/6.32, printed p. 112**;
  - the draft's own Definition 6.9, Example 6.10 and Theorem 6.11 are about advice.
- **Content.** Every [AB09] citation in EF-H12's Lean docstrings and REPORT has matching content in
  the ingest, **except three**:
  - `CircuitWitness.lean:310` cites Def 6.9 for circuit evaluation (the wire values), which is
    Def 6.1 material;
  - `Relations.lean:23` attributes the TCSlib default-`false` input-reading convention to Def 6.9;
  - the "(§2.3.)" module references on the glue-only files `UnaryArith`, `Gadget` and `Padding`
    have nothing to match, and §2.3 has no 3-colouring content at all.

  This confirms and sharpens F07.
- **Numbers that cannot be confirmed.** This source cannot confirm the CUP numbers themselves
  (Def 6.9, Lemmas 6.10/6.11, Remark 6.7, §6.1.2, p. 111). They agree with the in-repo audited
  anchors and are consistent with the draft's content, but checking them needs a CUP copy.
  - "Remark 6.7" has **no draft counterpart number**. Its content (the polynomial-time/logspace
    circuit emitter) is the draft's Theorem 6.7 and its proof sketch.
- **3-colouring.** EF-H12 cites no 3-colouring source: no [GJ79] and no [Sto73]. The 3SAT → 3COL
  gadget is attributed to the CS 294-268 course material. The draft's chapters 2 and 6 contain no
  3-colouring material.

## Source and method

- **The PDF.** `book.pdf`, downloaded on 2026-11-19 from
  `https://theory.cs.princeton.edu/complexity/book.pdf`:
  - 489 pages;
  - SHA-256 `da0881782a35bde6a0779a2eb1a8d480f39fbddf70bbb92824d1dc5550a033b2` (anchor prefix
    `pdf-da0881782a35`);
  - the hash was checked before extraction and re-checked after the container restart.

  The PDF is not committed and is not under `blueprint/src/references/`. It is a different file
  from the per-chapter PDFs behind the ch07 ingest (`26d95080…`) and the ch13 ingest
  (`52929dbaa962…`), but it comes from the same draft (same footer date).
- **Pages.**
  - Chapter 2, "NP and NP completeness", is PDF pp. 55–80. Chapter 3 begins on p. 81.
  - Chapter 6, "Circuits", is PDF pp. 117–130. Chapter 7 begins on p. 131.
  - Printed draft page = PDF page − 16. For example, PDF 61 is "p2.7 (45)" and PDF 128 is
    "p6.12 (112)".
- **Extraction.** `pypdf` 6.17.0 under `python3 -I`, `extract_text(extraction_mode="layout")`, as
  in EF-D4.
  - Per page, the common left indentation is removed, trailing spaces are stripped and runs of
    blank lines are collapsed.
  - C0 control characters (figure debris in Figure 2.4) are replaced by U+FFFD.
  - Nothing else is edited.
  - Re-running the extraction after the restart reproduces both `.raw.md` files byte for byte.
- **Transcription.** The `.md` blocks follow the ch07/ch13 form:
  - definitions, theorem, lemma and claim statements, Remark 2.11, §2.3.6 item 2 (Levin
    reductions) and all of §6.7 are transcribed close to the draft's wording, in Unicode;
  - other proofs, examples and discussion are condensed;
  - exercises are summarised by number.

  They were checked against page images rendered with `pypdfium2` under `python3 -I` (pp. 56, 59,
  61, 62, 65, 66, 67, 69, 71, 72, 118, 122, 124, 128). That check was used to restore the overbars
  the text layer drops (Example 2.13, Claim 2.14, Lemma 2.15, Theorem 2.16, Lemma 6.32) and to
  read the arrows of Figure 2.4. Draft errors are kept and flagged as *Transcription notes*:
  - Definition 2.21 reads "L̄ ∈ P" (meant: NP);
  - Theorem 2.16's proof says "clique" for independent set;
  - condition 3 of Lemma 2.12's proof writes z_{inputpos(i)};
  - Exercise 11's parsimony definition is garbled;
  - Exercise 6.11 reads "NC¹ = L";
  - Definition 6.28 has an unresolved "Remark ??".
- **Checks.**
  - `proofmatch.document.parse_validated_markdown` parses both `.md` files:
    - ch02: 98 blocks;
    - ch06: 59 blocks;
    - every anchor has consistent provenance;
    - every page in range has at least one block, and block numbers are contiguous per page.
  - Both raw files carry exactly the in-range `<!-- pdf-page -->` markers.
  - A word check compared each verbatim block (confidence ≥ 0.95) with its raw page. Only
    ingester words remain: "footnote", "epigraph", and similar. Mixed blocks were lowered to 0.93.
- **Header.** Each `.md` header states the source URL, the SHA-256, the page range, and that the
  numbering is the draft's and may differ from CUP 2009. Status: `awaiting Codex source review`.
  No proofmatch run was made, so no `\statementsource`/`\proofsource` may cite these anchors yet.

## Files

| File | Size | Content |
|---|---|---|
| `blueprint/src/references/arora-barak-ch02-np-completeness.raw.md` | 79 KB | PDF pp. 55–80 |
| `blueprint/src/references/arora-barak-ch02-np-completeness.md` | 51 KB | 98 anchors |
| `blueprint/src/references/arora-barak-ch06-circuits.raw.md` | 40 KB | PDF pp. 117–130 |
| `blueprint/src/references/arora-barak-ch06-circuits.md` | 32 KB | 59 anchors |
| `blueprint/src/references/sources.json` | | `AB09.documents` gains the two names before ch07; other entries unchanged; valid JSON. `GJS74` (separate ingest) is present |

The sizes are in line with ch07 (51/84 KB). The AB09 `title` still names CUP 2009, as it did for
the ch07/ch13 draft ingests.

### Anchors per page (`pdf-da0881782a35-pNNN-b001` … `bNNN`)

| Chapter | Anchors per page |
|---|---|
| ch02 | p055: 2, p056: 3, p057: 5, p058: 5, p059: 5, p060: 6, p061: 4, p062: 7, p063: 4, p064: 3, p065: 4, p066: 6, p067: 1, p068: 6, p069: 3, p070: 3, p071: 4, p072: 7, p073: 6, p074: 3, p075: 3, p076: 3, p077: 2, p078: 1, p079: 1, p080: 1 (98 in all) |
| ch06 | p117: 3, p118: 4, p119: 6, p120: 7, p121: 3, p122: 4, p123: 6, p124: 2, p125: 5, p126: 5, p127: 4, p128: 6, p129: 3, p130: 1 (59 in all) |

### Key anchors

All anchors below carry the prefix `pdf-da0881782a35-`.

| Anchor | Draft locator (printed p.) | Content |
|---|---|---|
| `p056-b002` | Def 2.1 (p. 40) | NP via verifier M and certificate u ∈ {0,1}^{p(\|x\|)} |
| `p059-b004` | Def 2.7 (p. 43) | Karp reduction ≤p, NP-hard, NP-complete |
| `p060-b002`, `p060-b003` | Thm 2.8 (p. 44) | transitivity of ≤p |
| `p061-b001` | §2.3.1 (p. 45) | Boolean formula, satisfiable, CNF, literals, clauses, kCNF ("at most k literals") |
| `p061-b002` | Thm 2.10 (p. 45) | Cook–Levin; SAT and 3SAT defined |
| `p061-b003` | Remark 2.11 (p. 45) | circuit proof of Cook–Levin is "in Section 6.7" |
| `p062-b002`, `p063-b001` … `p065-b001` | Lemma 2.12 (p. 46), proof §2.3.4 (pp. 47–49) | SAT is NP-hard |
| `p065-b002`, `p065-b003` | Lemma 2.15 (p. 49) | SAT ≤p 3SAT |
| `p065-b004`, `p066-b001`, `p066-b002` | §2.3.6 (pp. 49–50) | **Levin reduction** and parsimonious reduction (item 2) |
| `p071-b003`, `p072-b001` | Thm 2.19 and proof (pp. 55–56) | search to decision through the Levin reduction |
| `p118-b002`, `p118-b003` | Def 6.1 (p. 102) | Boolean circuit (fanin 2/1, size, formula); evaluation of node values |
| `p120-b002`, `p120-b003` | Def 6.5 (p. 104) | logspace-uniform families; SIZE/TYPE/EDGE representation |
| `p120-b005` … `p121-b001` | Thm 6.7, Remark 6.8, proof sketch (pp. 104–105) | P = logspace-uniform poly-size circuits; snapshot (tableau) construction |
| `p121-b002` | Def 6.9 (p. 105) | **DTIME(T(n))/a(n), advice**, not CKT-SAT |
| `p128-b001` | §6.7, Def 6.30 (p. 112) | **CKT-SAT** |
| `p128-b002` | §6.7 (p. 112) | alternative Cook–Levin proof "by combining the following two lemmas" |
| `p128-b003`, `p128-b004` | Lemma 6.31 and proof (p. 112) | **CKT-SAT is NP-hard**: x ↦ C_x with C_x(u) = M(x,u), via the proof of Thm 6.7, in logspace |
| `p128-b005`, `p128-b006` | Lemma 6.32 and proof (p. 112) | **CKT-SAT ≤p 3SAT**: one variable per node, gate clauses, output clause |

## Numbering map (TCSlib-cited CUP number → this draft)

| TCSlib cites | Draft | Anchor(s) | Status |
|---|---|---|---|
| Def 2.1 | Def 2.1 | `p056-b002` | same number |
| Def 2.7 | Def 2.7, printed p. 43 | `p059-b004` | same number |
| Thm 2.8 | Thm 2.8 | `p060-b002` | same number |
| Thm 2.10, p. 45 | Thm 2.10, printed p. 45 | `p061-b002` | same number and page |
| Lemma 2.11, pp. 45–49 (SAT NP-hard) | **Lemma 2.12**, pp. 46–49 | `p062-b002`; proof `p063-b001`–`p065-b001` | draft +1, because it inserts Remark 2.11 |
| Lemma 2.14, p. 49 (SAT ≤p 3SAT) | **Lemma 2.15**, p. 49 | `p065-b002`, `p065-b003` | draft +1 |
| §2.3 / §2.3.6 (Levin remark) | §2.3.6, item 2, printed p. 50 | `p066-b002` | same; gate 03e's "§2.3.6" is **verified for the draft** |
| §2.3.1 | §2.3.1 | `p061-b001` | same number |
| Def 6.1 | Def 6.1 | `p118-b002` | same number |
| §6.1.2 | **§6.7** | `p128-b001`–`p128-b006` | the draft has no §6.1.2 (§6.1 has only §6.1.1, advice) |
| Def 6.9 (CKT-SAT) | **Def 6.30** | `p128-b001` | draft Def 6.9 is advice (`p121-b002`): **number collision** |
| Lemma 6.10 | **Lemma 6.31** | `p128-b003`, `p128-b004` | draft "6.10" is Example 6.10 (advice) |
| Lemma 6.11 | **Lemma 6.32** | `p128-b005`, `p128-b006` | draft "6.11" is Theorem 6.11 (P/poly = advice) |
| Thm 6.6 (in-repo quote "the proof of Theorem 6.6 yields …") | **Thm 6.7** | `p120-b005` | the draft's Lemma 6.31 proof says "Theorem 6.7" |
| Remark 6.7 (poly-time/logspace circuit emitter) | **no counterpart number**; content in Thm 6.7, its proof sketch, Def 6.5, and Lemma 6.31's "in logarithmic space (which in particular implies polynomial time)" | `p120-b002`, `p120-b003`, `p120-b007`, `p121-b001`, `p128-b004` | inferred from in-repo usage ("logspace half of [AB09, Remark 6.7]"); draft Remark 6.8 is "P ⊆ P/poly" |
| p. 111 | **printed p. 112** (PDF p. 128) | `p128-*` | draft p. 111 (PDF 127) is §6.5.2–§6.6 (P-completeness, DC uniformity) |

The CUP-side entries are TCSlib's existing citations, taken from the audited files
`CircuitSatNPHard.lean`, `DAGCircuitSat*.lean`, `SAT.lean`, `CounterProgSim*.lean` and the
EF-H12 brief. This ingest does not verify them.

## Citation check of EF-H12's delivery

**Delivery checked.**
- Branch `exchange/pass-shelat-ch5-8`, folder `inbox/fills/ef-h12-levin-3col/`, at
  `36d9ac03c329544d33b1f3f9a73e6ce32152dde2`.
- Extracted with `git archive` into the ingester's scratch directory.
- Scope: `src/` (14 files) and `REPORT.md`.
- Paths below are relative to `src/TCSlib/Cryptography/ZeroKnowledge/`.

**How it was checked.** Every `AB09` occurrence was grepped, including split lines and the
`## References` parentheticals. There are 26 in-text citations, 13 reference-list parentheticals and
the REPORT line. EF-H12 uses no quotations from [AB09].

### Statement and module-text citations

| # | Where | Cited | Anchor(s) | Content | Draft numbering |
|---|---|---|---|---|---|
| 1 | `LevinHardness/Relations.lean:17-18` | §6.1.2, Lemmas 6.10 and 6.11, p. 111 (the route L → CKT-SAT → 3SAT) | `p128-b002`–`p128-b006` | **match**: the two-lemma route to 3SAT | §6.7, Lemmas 6.31/6.32, p. 112 |
| 2 | `LevinHardness/Relations.lean:52` (`R_CKT`) | Def 6.9 | `p128-b001`; circuit model `p118-b002` | **match**: an n-input circuit with ∃u ∈ {0,1}ⁿ, C(u) = 1. Fan-in two is Def 6.1's. The string form is `DAGCircuit.encode`, not the draft's adjacency matrix (`p120-b003`), an in-repo divergence already recorded in `DAGCircuitSatLang.lean` | Def 6.30 |
| 3 | `LevinHardness/Relations.lean:23` ("certificate convention of `BoolCircuit.CVALPrefix`, [AB09, Def 6.9]") | Def 6.9 | `p128-b001` | **partial**: AB09 has u ∈ {0,1}ⁿ only. Reading u from a list with default `false` is TCSlib's convention and should not carry the AB09 tag | Def 6.30 |
| 4 | `LevinHardness/Relations.lean:65` (`R_3SAT`) | §2.3.1 | `p061-b001`; 3SAT language `p061-b002` | **match**: kCNF = clauses with at most k literals; φ(z) True. The 3SAT language itself is defined in Thm 2.10 (§2.3.2) | same number |
| 5 | `LevinHardness/CircuitWitness.lean:310` ("wire values are the circuit's vertex values") | Def 6.9 | **none at Def 6.9**; the content is `p118-b002`, `p118-b003` | **mismatch**: node-value evaluation is Def 6.1 and the paragraph after it, not CKT-SAT | the draft's Def 6.1 has the same number |
| 6 | `LevinHardness/CircuitWitness.lean:21` (Tseitin map) | Lemma 6.11, p. 111 | `p128-b005`, `p128-b006` | **match**: variable z_i per node; AND, OR and NOT clauses; output clause | Lemma 6.32, p. 112 |
| 7 | `LevinHardness/CircuitWitness.lean:374` (witness map `R_CKT` → `R_3SAT`) | Lemma 6.11, p. 111; [PS10] | `p128-b006` | **match in substance**. The draft states only "φ satisfiable iff C is". Assigning z_i the node values is implicit, and the Levin (witness-map) property is not stated for Lemma 6.32. The witness map is rightly co-cited to [PS10, Theorem 124.1, step 2]. The Levin notion is `p066-b002` | Lemma 6.32 |
| 8 | `LevinHardness/CircuitWitness.lean:398, 413` (converse; equisatisfiability) | Lemma 6.11, p. 111 | `p128-b006` | **match** | Lemma 6.32 |
| 9 | `LevinHardness/Verifier.lean:20, 277`; `LevinHardness.lean:36` (step 1) | Lemma 6.10 | `p128-b003`, `p128-b004` | **match**: x ↦ C_x with C_x(u) = M(x,u), so certificates are satisfying inputs. The certificate as identity witness map follows from C_x(u) = M(x,u) but is not stated as a Levin map in the draft; it is co-cited to [PS10] | Lemma 6.31 |
| 10 | `LevinHardness/Verifier.lean:42` (overlap with `CircuitSatNPHard.lean:93-127`) | Lemma 6.10 | `p128-b003` | **match** | Lemma 6.31 |
| 11 | `LevinHardness/Verifier.lean:184` (`verLang_mem_P`) | Lemma 6.10, "the verifier of L ∈ NP" | `p128-b004`; `p056-b002` | **match**: the polynomial-time M of the proof, which is Def 2.1's verifier | Lemma 6.31; Def 2.1 |
| 12 | `LevinHardness/Verifier.lean:227` (`tabInst`) | Lemma 6.10; Remark 6.7 | `p128-b004`; `p120-b007`, `p121-b001` | **match**: the instance map is the circuit given by Thm 6.7's proof, computable in logspace, hence polynomial time | Lemma 6.31; Thm 6.7 (no Remark 6.7) |
| 13 | `LevinHardness/Verifier.lean:30, 211` (polynomial-time emitter of the configuration tableau) | Remark 6.7 | `p120-b002`, `p120-b003`, `p120-b007`, `p121-b001`, `p128-b004` | **match**: the snapshot/tableau circuit and its uniform computability. The CUP number is unconfirmable here | Thm 6.7 and its proof sketch |
| 14 | `LevinHardness/Hardness.lean:22, 199`; `LevinHardness.lean:27` (the circuit route) | Lemmas 6.10 and 6.11, p. 111 | `p128-b002`–`p128-b006` | **match** for the route L → CKT-SAT → 3SAT. The 3SAT → 3COL leg is correctly attributed to the course material, not to AB09 | §6.7, p. 112 |
| 15 | `LevinHardness.lean:37` | Lemma 6.11 | `p128-b005` | **match** | Lemma 6.32 |
| 16 | `LevinHardness/ColoringGraph.lean:19`; `LevinHardness/ColoringParse.lean:17` ("the Levin reduction 3SAT → 3COL ([AB09, §2.3]; the course reduction …)") | §2.3 | `p066-b002` (and `p072-b001`) | **match for the notion of a Levin reduction only**. The draft's chapters 2 and 6 contain **no 3-colouring material** (no "colo…" anywhere in either raw file). The gadget is the course material's, as the text says | §2.3.6, item 2 |
| 17 | `LevinHardness/Padding.lean:17` ("The Levin reduction to 3COL ([AB09, §2.3]; [PS10 …]) is assembled …") | §2.3 | `p066-b002` | **match for the notion only**. The file is framework glue. The draft's padding (Thm 2.25, Remark 2.26, `p073-b006`, `p074-b001`) is unrelated | §2.3.6 |
| 18 | `LevinHardness/UnaryArith.lean:18` (unary arithmetic rows "of the Levin reduction 3SAT → 3COL ([AB09, §2.3])") | §2.3 | none for the rows themselves | **notion only; the rows have no AB09 content** (F07: "on unary arithmetic rows it is not" acceptable) | — |

### Reference-list parentheticals (`## References`, "[AB09] … (…)")

| File | Parenthetical | Check |
|---|---|---|
| `LevinHardness/Relations.lean:43` | §6.1.2, Definition 6.9, Lemmas 6.10 and 6.11, p. 111 | matched; mapping: §6.7, Def 6.30, Lemmas 6.31/6.32, p. 112 |
| `LevinHardness/CircuitWitness.lean:65` | §6.1.2, Definition 6.9, Lemma 6.11, p. 111 | matched, except Def 6.9 at line 310 (row 5) |
| `LevinHardness/Verifier.lean:71` | §6.1.2, Remark 6.7, Lemma 6.10, p. 111 | matched. Read as a list, not as "Remark 6.7 is in §6.1.2". In-repo files place Remark 6.7 variously in "§6.1" (`TQBFHard.lean:75`) and "§6.1.1" (`CounterProgSim*.lean`); the draft cannot settle which |
| `LevinHardness/Bridge.lean:55` | §6.1.2, Lemma 6.11 | matched (Lemma 6.32) |
| `LevinHardness.lean:50` | §6.1.2, Lemmas 6.10 and 6.11, p. 111 | matched |
| `LevinHardness/Hardness.lean:58` | §2.3; §6.1.2, Lemmas 6.10 and 6.11, p. 111 | matched (§2.3 as the Levin notion) |
| `LevinHardness/ColoringGraph.lean:59`, `LevinHardness/ColoringParse.lean:51`, `LevinHardness/ColoringWitness.lean:50`, `LevinHardness/Soundness.lean:48` | §2.3 | notion only; **no 3-colouring content in AB09 §2.3** |
| `LevinHardness/Gadget.lean:54`, `LevinHardness/Padding.lean:45`, `LevinHardness/UnaryArith.lean:39` | §2.3 | **unmatched**: glue-only files with nothing AB09-specific (F07) |

`REPORT.md:256` lists "[AB09] Def 6.9, Lemmas 6.10/6.11 p. 111, Remark 6.7, §2.3, §2.3.1". All of
these locate matching content, with the mappings above. The reservations are the ones in rows 3, 5
and 18 and the glue-file entries.

### Not cited by EF-H12 (brief anchors, for completeness)

EF-H12's files do not themselves cite [AB09] Def 2.1, Def 2.7, Thm 2.10, Lemma 2.11 or Lemma 2.14.
It reaches NP and Levin hardness through `ZeroKnowledge/NP.lean` (J6), which cites "[AB09, §2.3]"
for Levin reductions. The mappings for those brief anchors are in the numbering map:

- the NP definition is `p056-b002`;
- Karp reductions are `p059-b004`;
- Cook–Levin is `p061-b002`;
- the Levin remark is `p066-b002`.

### Citations that cannot be matched

1. **Content.** Three citations have no matching content:
   - `CircuitWitness.lean:310`, "[AB09, Def 6.9]" for circuit evaluation (the content is at
     Def 6.1, `p118-b002`/`b003`);
   - `Relations.lean:23`, the default-`false` reading convention attributed to Def 6.9 (TCSlib's
     convention);
   - the "(§2.3.)" module references on `Gadget.lean`, `Padding.lean` and `UnaryArith.lean`
     (no AB09 content). `UnaryArith.lean:18`'s in-text "[AB09, §2.3]" is in the same position.
2. **Numbers.** Def 6.9, Lemma 6.10, Lemma 6.11, Remark 6.7, §6.1.2 and p. 111 cannot be
   confirmed as CUP numbers from this source.
   - Each has matching content under the draft's own number, given above, except Remark 6.7,
     which has no draft number.
   - Against the draft, "Def 6.9", "6.10" and "6.11" name **different, unrelated items** (advice).
     A reader checking the citations against this ingest would be misled without the mapping.

### 3-colouring citations

- **No published source.** EF-H12 cites no published 3-colouring source. `REPORT.md:260` says
  "Garey–Johnson and Stockmeyer are not cited (Q-H12-2: not ingested)". Neither [GJ79, App. A1.1,
  GT4] nor [Sto73] appears in `src/`.
- **The gadget.** The 3SAT → 3COL gadget is attributed to the CS 294-268 course material (UC
  Berkeley, Spring 2026, V. Guruswami) through `Complexity/NPReductions/ThreeSATToColoring.lean`.
  These references are at:
  - `Gadget.lean:16, 51`;
  - `ColoringParse.lean:18, 48`;
  - `ColoringGraph.lean:21, 56`;
  - `ColoringWitness.lean:47`;
  - `Soundness.lean:45`;
  - `Bridge.lean:56`;
  - `Hardness.lean:61`.
- **Within AB09.** The draft names [GJ79] only as a general catalogue of NP-complete problems
  (`p066-b004`, `p077-b001`), not for 3-colouring.
- **Out of scope here.** A 3-colouring source is out of this ingest's scope. The separate [GJS74]
  ingest (`ingest-report-gjs74.md`) found that [GJS74] states, but does not prove, NP-completeness
  of 3-colourability.

## For the maintainer to decide

1. **Citation numbering for [AB09] ch. 6.** The recommended course follows the ch07 precedent
   ("the ingested draft numbers it 7.2.1, while TCSlib cites the published §7.2.2"):
   - keep the CUP numbers in docstrings, with the mapping above recorded;
   - when \statementsource / \proofsource are written, cite the `p128-*` anchors.

   The alternative is to add the draft locator in docstrings, e.g. "[AB09, Lemma 6.10] (web draft
   §6.7, Lemma 6.31)". Either way, the CUP numbers stay unverified until someone checks a CUP copy
   (rule 16).
2. **F07 landing edits (LE-h12-doc).** The edits the check supports:
   - (a) `CircuitWitness.lean:310`: Def 6.9 → Def 6.1, since evaluation is Def 6.1 and the
     paragraph after it;
   - (b) `Relations.lean:23`: drop the AB09 tag from the reading convention, or mark it as
     TCSlib's;
   - (c) drop "(§2.3.)" from `Gadget.lean`, `Padding.lean` and `UnaryArith.lean`, and
     `UnaryArith.lean:18`'s tag;
   - (d) optionally narrow "[AB09, §2.3]" on the 3COL files to "[AB09, §2.3.6]", or to the Levin
     remark. §2.3.6 is verified in the draft; the CUP number is unverified, so "§2.3" is the safe
     choice.
3. **In-repo quotations (outside EF-H12; for the owner file `CircuitSatNPHard.lean`).** Two
   quotations do not match the draft's wording:
   - "[AB09, p. 111]: 'The Cook–Levin Theorem follows immediately from the next two lemmas'" —
     the draft (`p128-b002`) reads "… by combining the following two lemmas";
   - "the proof of Theorem 6.6 yields a polynomial-time transformation …" — the draft
     (`p128-b004`) reads "the proof of Theorem 6.7 yields a way to map M, x into the circuit C_x
     in logarithmic space".

   These are presumably CUP wording and cannot be verified with this source.
4. **The `sources.json` AB09 title** still names CUP 2009 while all four AB09 chapter files are
   draft ingests (as for ch07/ch13 before). Leave it, or add a note.

## Permissions

No permission check denied anything. Only `python3 -I` (pypdf, pypdfium2, proofmatch's parser),
`git` reads and read-only commands were used; there was no network access, no Lean and no build.
Nothing was committed or pushed by the ingester. The coordinator committed the partial ingest
before and after the restart (`79633c0d`, `9acebf0b`).
