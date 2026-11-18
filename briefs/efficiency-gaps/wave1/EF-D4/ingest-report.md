# EF-D4 · [PW10] §3.1–§3.2 ingest report (maintainer, 2026-11-18)

Ruling Q-D4-1 (A): ingest [PW10] §3.1–§3.2 before EF-D4 is dispatched. This report records that
ingest and the edits that make the EF-D4 dispatch ready. Nothing here is committed. The maintainer
commits it and then fills `<RECORDS>`.

## Source

C. Peikert, B. Waters, *Lossy Trapdoor Functions and Their Applications*, author version dated
June 4, 2010. The PDF has 44 pages and SHA-256
`74f48b0eff6f4a0afd52ffe2bfddc6bef006c241c458812bfe085ce85059752c`, the same file the existing
reference (pages 33–39) was built from. The hash was rechecked before extraction. The PDF is not
committed and is not under `blueprint/src/references/`.

The PDF has no table of contents. The pages were located from the section headings in its text
layer: §3 and §3.1 begin on p. 14, §3.2 on p. 15, and §3.3 also on p. 15. Printed page numbers
equal the PDF page numbers.

## Pages ingested and anchors added

The ingest covers PDF pages 14–15, from the heading "3 Lossy and All-But-One Trapdoor Functions" to
the end of §3.2, just before the heading "3.3 Basic Relations". §3 has no text between its heading
and §3.1.

| Anchor | Page | Passage |
|---|---|---|
| `pdf-74f48b0eff6f-p014-b001` | 14 | §3.1 parameters: input length `n(λ) = poly(λ)`, lossiness `k(λ) ≤ n(λ)`, residual leakage `r(λ) = n(λ) − k(λ)` |
| `pdf-74f48b0eff6f-p014-b002` | 14 | §3.1 definition of a collection of `(n, k)`-lossy TDFs `(S_inj, S_loss, F_ltdf, F_ltdf⁻¹)`, properties 1–3 |
| `pdf-74f48b0eff6f-p014-b003` | 14 | §3.1 remark: hardness of inversion is not required (forward reference to Lemma 3.3) |
| `pdf-74f48b0eff6f-p014-b004` | 14 | §3.1 almost-always lossy TDFs, first part (the sentence breaks at the page end) |
| `pdf-74f48b0eff6f-p015-b001` | 15 | §3.1 almost-always lossy TDFs, continued |
| `pdf-74f48b0eff6f-p015-b002` | 15 | §3.2 ABO overview (branches, one lossy branch, hidden by the description) |
| `pdf-74f48b0eff6f-p015-b003` | 15 | §3.2 definition of a collection of `(n, k)`-ABO TDFs `(S_abo, G_abo, G_abo⁻¹)` with branch collection `𝓑 = {B_λ}_{λ∈ℕ}`, properties 1–2 |
| `pdf-74f48b0eff6f-p015-b004` | 15 | §3.2 almost-always ABOs |

### Files

- **`blueprint/src/references/peikert-waters-2010-lossy-tdf.raw.md`**
  - Pages 14 and 15 are inserted before page 33, with `<!-- pdf-page: N -->` markers.
  - Four header comments are added: the extension and its status, the extractor, the scope line
    ranges (`p14: 17-48; p15: 1-33`), and the page-numbering note. These follow the DW-7 scoped-raw
    convention, for example `brakerski-vaikuntanathan-2011-fhe.raw.md`.
  - The pages 33–39 text and its original header lines are unchanged.
- **`blueprint/src/references/peikert-waters-2010-lossy-tdf.md`**
  - The `validation-status` header is extended.
  - An "EF-D4 extension (2026-11-18)" paragraph is added, modelled on the Pei16 "DW-7 extension"
    paragraph.
  - Eight anchored blocks are added before `p033-b001`, each with a `pdf-source` comment
    (confidence 0.95, as in the DW-7 extensions).
- **`blueprint/src/references/sources.json`** is unchanged. The tag `PW10` already maps to
  `peikert-waters-2010-lossy-tdf`.

### Method and checks

- **Extraction.** The task's rules allow `python3 -I` only, so `pdftotext` (used for pages 33–39)
  was not run. The raw text for pages 14–15 comes from `pypdf` 6.17.0,
  `extract_text(extraction_mode="layout")`, and the raw header names this extractor. The extraction
  glues math symbols to the neighbouring words and keeps the "ﬁ" ligature, as a raw extraction may.
- **Transcription.** The `.md` blocks are the paper's wording, with mathematics in LaTeX and the
  paper's italics as Markdown emphasis. They were checked against the page images: the Read tool's
  PDF pages, plus 2.6× crops rendered with `pypdfium2` under `python3 -I`.
  - The passages have **no displayed formulas**. All mathematics is inline. Examples:
    `$2^r=2^{n-k}$`, `$\{X_\lambda\}\overset{c}{\approx}\{Y_\lambda\}$`,
    `$(s,t)\leftarrow S_{\mathrm{abo}}(b_i^*)$`.
  - The only editorial changes are these: the line-break hyphen in "in-distinguishable" is removed;
    curly quotes are written as straight quotes, as elsewhere in the file; and bold block labels and
    two *Transcription notes* are added. The extension paragraph says that these are not part of the
    source.
- **Word-level diff.** The prose of the new blocks (math and labels removed) was compared with the
  raw text layer. Every difference is a heading or a math token that the extractor glued onto a word.
  No prose word differs.
- **Parse.** `proofmatch.document.parse_validated_markdown` parses the extended `.md`: 23 blocks,
  each with consistent provenance.

## Review status

The new section is marked exactly as the earlier extensions were: **awaiting Codex source review**.
This appears in the `.md` header
(`validation-status: approved scoped reference for draft PR #250 (pages 33-39); EF-D4 extension
(Sections 3.1-3.2, pages 14-15) awaiting Codex source review`) and in the raw extension header line.
The approval of pages 33–39 is unchanged. No proofmatch matching was run, so no
`\statementsource`/`\proofsource` may cite these anchors until an approved run.

## Edits to the EF-D4 files

**`brief.md`**

- The header Rulings line adds "Q-D4-1 A (the [PW10] §3.1–§3.2 ingest is done; anchors under
  Sources)".
- The targets cite anchors:
  - target 1 cites `[PW10, §3.1, p. 14]` with `p014-b001`/`p014-b002`;
  - target 2 cites `[PW10, §3.2, p. 15]` with `p015-b003`/`p015-b002`.
- **Sources**
  - The text "covers printed pages 33–39 only … §3 is not ingested (see Q-D4-1)" is replaced.
  - In its place is an anchor table of the eight blocks with their pages, and a short note listing
    where the targets specialise [PW10] (below). The §6.2–§6.4 anchors remain for lattice remarks
    only.
- **Optional sanity item.** The ABO-with-one-bit-branch-set-gives-`LossyTDF` item was conditional on
  "the ingested source supports it after Q-D4-1". It is now an explicit **Skip**, because that result
  is [PW10] Lemma 3.1 in §3.3 (pp. 15–16), outside this ingest.
- **Gate preparation** now also asks for the specialisations listed under Sources, each with the
  anchor it departs from.
- **Q-D4-1** is marked "Ruled A; done". The options text is kept for the record.

**`dispatch-prompt.md`**

- The records pin is the `<RECORDS>` placeholder again. Its two occurrences were the substituted
  `54dcb302…` hash. `<RECORDS>` is defined as the commit that files the ingest together with the
  updated brief and prompt.
- The Q-D4-1 B alternative ("Under Q-D4-1 B, add to step 2 …") is removed.
- A **rule-16 line** is added before the prompt: "Local inputs (rule 16): none needed". It explains
  that the worker reads only the records branch and GitHub, that the PDF is not needed, and that
  nothing is prepared or pasted.
- Step 1 names the §3.1–§3.2 blocks (anchors `p014-b001` to `p015-b004`). Step 2's attribution clause
  says to cite [PW10, section 3.1, p. 14] and [PW10, section 3.2, p. 15] by those anchors.
- The footer "Not yet ready to dispatch … Q-D4-1 answered (A needs the §3 ingestion first)" is
  replaced by "Ready to dispatch once `<RECORDS>` is filled", and the footer adds that no local inputs
  are needed.

**Not edited** (outside this task's write scope; the maintainer may want to update them):

- `../README.md` (lines 13, 29–30, 49, 65–66);
- the `PassShelatChapter5-8Plan.md` decision log (rows of 2026-11-18, "Held: EF-D4 (needs the [PW10]
  §3.1–§3.2 ingest)").

These still describe EF-D4 as waiting for the ingest.

## Differences from what the brief assumed

None of these blocks dispatch. They are design points that the worker's REPORT.md and the Codex gate
should see. The brief now lists the first four under Sources.

1. **Exact versus almost-always.**
   - [PW10]'s definitions state correctness, injectivity and lossiness exactly
     (`p014-b002`, `p015-b003`).
   - The lattice constructions need the almost-always relaxation: these properties hold with
     overwhelming probability over the generator's coins (`p014-b004`/`p015-b001`, `p015-b004`).
   - The brief's `Correct`/`Lossy` ("every coin string") are the exact form. That is faithful to the
     main definition, but the §6 instances are almost-always in [PW10].
   - Whether EF-H9's Lean instances can meet the exact form depends on their deterministic bounded
     errors. Earlier audits note that the Lean replaces PW10's Gaussian tail by deterministic
     entrywise bounds. This should be confirmed before EF-H9 relies on it.
2. **Branch collection.** [PW10] allows an arbitrary family of sets `{B_λ}` (`p015-b003`). The brief
   fixes `{0,1}^{b(κ)}`. This is a specialisation and should be disclosed. It suits the §6.4 lattice
   ABO, whose branch set is `{0,1}^w`.
3. **Hidden lossy branch.**
   - In [PW10] the adversary itself outputs `(b₀*, b₁*) ∈ B_λ × B_λ`, and the pair is part of its
     view (`p015-b003`, property 2).
   - The brief's `HiddenBranch` instead takes, for each `NUPPT` `D`, one negligible bound uniform
     over all pairs, and `D` sees only the index. This is the `SingleMessageSecure` shape.
   - For non-uniform distinguishers, the maintainer expects the two to be equivalent: hard-wire the
     worst pair and coins per security parameter. This is a reading, not a checked claim, and the gate
     should confirm it.
4. **`k ≤ n`.** [PW10] requires `k(λ) ≤ n(λ)` (`p014-b001`). The brief's fields leave it implicit. With
   truncated subtraction, `2^{n−k}` becomes `1` when `k > n`, so the worker should state how this is
   handled.
5. **Uniform adversaries.** [PW10] defines security against uniform adversaries (footnote 5, p. 11,
   not ingested). TCSlib's predicates are over `NUPPT`. This is a standard design choice that the
   REPORT should disclose. It cannot be anchored without ingesting p. 11.
6. **The skipped Lemma 3.1 differs from the brief's sketch.**
   - The brief's parenthetical was "(the lossy branch `b* = 1`)".
   - In [PW10] Lemma 3.1 (p. 16, read but not ingested), the LTDF always evaluates the ABO on branch
     0. The injective generator is `S_abo(1)`, which has lossy branch 1, and the lossy generator is
     `S_abo(0)`.
   - The item is now skipped. If it is revived, it needs a §3.3 ingest and this correction.
7. **Matches.**
   - `ModesIndist` matches property 3 (indistinguishability of the first outputs).
   - `LossyTDF.Correct`, inversion on the image only, matches property 1, under which behaviour
     outside the image is unspecified.
   - The lossy-mode generator outputting only `s` matches `S_loss` outputting `(s, ⊥)`.
   - The ABO `Correct` (every `b ≠ b*`) and `Lossy` (branch `b*`, image at most `2^{n−k}`) match
     property 1 of §3.2.
   - [PW10] does not require hardness of inversion (`p014-b003`). The brief does not add it, which is
     consistent.

## Permissions

No permission check denied anything. Only `python3 -I` and read-only commands were used, and no
build. Nothing was committed or pushed.
