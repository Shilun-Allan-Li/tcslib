# Review · external ingest job `dw8-ingests` (DW-8), final r1

**Verdict: ACCEPT WITH EDITS.** The four ingests are faithful. Anchors, hashes, registry and
scope are correct, and the citation report is accurate. Before landing I made two small
mechanical edits, both listed in §3: a layout fix to one display in [BGZ09], and scope
extensions to three `.raw.md` files so that every transcribed sentence has its raw text.
One delivery-hygiene breach is in the patch metadata only (F3). Nothing landed carries it.

| Item | Value |
|---|---|
| Delivery | `exchange/pass-shelat-ch5-8` at `443df15b1619ad01c6d71b3a944d02c040e3995b`, `inbox/ingests/dw8/` |
| Brief | `briefs/pass-shelat-ch5-8/ingests/dw8-issued-r1/brief.md`; identical to the exchange `outbox/ingests/dw8/brief.md`. Its `SHA256SUMS` verifies (`brief.md`, `README.md`). |
| Issue base | `6f08055d5cc533c70c0c91bf7e92aa899466c323` |
| Scratch replay | local branch `review/dw8` (not pushed), sparse worktree limited to `blueprint/src/references/`, removed after the review. Tip: `15b74a6ac6757a0954011b5153c1334577613bce`. |
| Method | `pdftotext -layout` (Poppler 24.02.0, the delivery's version), plus per-page `pdftotext -f N -l N` for [BGZ09], and page images via `pdftoppm` at 110–600 dpi. Python was run as `python3 -I`, with scripts kept outside the extraction folder. No Lean was run and no `.lean` file was changed. |

## 1. Checks

### 1.1 Integrity — pass

- **`SHA256SUMS`:** all 16 entries verify, and the listed path set equals the delivered files
  exactly, apart from `SHA256SUMS` itself.
- **Patches:** `git am --whitespace=error-all` applies `0001`–`0005` cleanly onto the issue base,
  with no whitespace errors. The result equals `src/` byte for byte for all 9 files.
  - The new commit hashes differ from `COMMITS.tsv`, as expected, because the committer and date
    differ.
- **Paths:** the series touches only `blueprint/src/references/`. It adds 8 files and modifies
  `sources.json`.
  - No deletions, renames or binary hunks.
  - No `.pdf` path in any commit.

### 1.2 PDF hashes — pass

| Tag | Uploaded file | Pages | SHA-256 | vs brief |
|---|---|---|---|---|
| [BGZ09] | `barthe-gregoire-zanella-2009-popl.pdf` | 12 | `216f8cd86ce5e077730bcf9d5ed1a90131f0107d23e64f249c7df02690b4678a` | matches |
| [Sho04] | `shoup-2004-332.pdf` | 33 | `fde1f65e83ec85297f58840bf87de15fb68e91ada8aefaf77db3b153cf826820` | matches |
| [Gen09] | `craig-thesis.pdf` | 209 | `9e7f32f1b8543416fc6c2fcbfedd5d2d69150226b9bbd2cccac57840a5db7b66` | recorded |
| [Vad12] | `pseudorandomness-published-Dec12.pdf` | 339 | `bf2ce542208824ebf39ce132aae2d26a3b90bc04d3496a4ec05361f27e62118c` | recorded |

### 1.3 Format and anchors — pass

- **Headers:** they mirror DW-7 (`boneh-boyen-2004-selective-id-ibe.*`, `gentry-sahai-waters-2013-fhe.*`):
  `generated-by` / `source-pdf-sha256` / `extractor` / `scope` / `note` in the raw files, and
  `generated-by` / `source-pdf-sha256` / `validation-status` in the transcriptions.
- **Fingerprints:** both files of each pair carry the full 64-hex SHA-256 of their upload.
- **Anchor format:** all 53 anchors have the form `pdf-<hash>-pNNN-bNNN`.
  - `<hash>` is the first 12 hex digits of the upload's SHA-256. This is
    `proofmatch.document.stable_block_id`, as for DW-7.
  - Each anchor's `pdf-source` provenance matches its page and block.
  - There are no duplicates, block numbers are contiguous per page, and every anchored page has a
    raw page.
- **Parsing:** `proofmatch.document.parse_validated_markdown` and `_raw_payload` parse all four
  pairs (the landed versions). The block counts match the REPORT (15/10/15/13). A DW-7 pair was
  run alongside as a baseline.
- **Raw files are exact:** I wrote an independent rebuilder that regenerates a `.raw.md` from the
  stated `pdftotext` command and scope. It reproduces all four delivered raw files **byte for
  byte**, and every scope range lies on its stated physical page.

### 1.4 Fidelity — pass, with the edits in §3

I compared every transcribed passage with the `pdftotext` text. I checked the cited passages and
all mathematics against page images.

- **[Vad12]:**
  - Checked against the 110-dpi images of pp. 182–183 (printed 179–180): Thm 6.18, the
    proof, and Theorem 6.17 with Footnote 2.
  - The unprimed `H'(X)` in the "if and only if" sentence is printed that way, and the delivery's
    note on it is correct.
  - Defs 3.21/3.22, the 2-universal remark, Def 4.7/Lemma 4.8, Def 6.2/Lemma 6.3, Defs 6.7, 6.9,
    6.13 and 6.16, the Rényi remark and the chapter notes all match.
- **[Gen09]:**
  - `KeyGen_{E^(d)}` (p. 56) and the hybrid display of Thm 4.2.3 (p. 60) were checked at
    150–200 dpi. The overbars restored in the transcription (`sk̄_ij` on the left,
    `sk_ij`/`sk'_ij` inside `Encrypt`) are exactly as printed.
  - The statement `t' ≈ t·ℓ`, `ε' ≥ ε/ℓ(d+1)` matches.
  - The printed slips ("takes as these things", the incomplete final clause of the proof) are
    transcribed as printed and marked.
- **[Sho04]:**
  - §1–§1.1 (pp. 1–3) match word for word. The printed typos are kept and marked.
  - Game 2 (p. 13) matches, apart from the glyph in F5.
  - The editorial "[Context: …]" bracket was checked against pp. 11–12 and is accurate (F8).
- **[BGZ09]:**
  - Figure 5 (p. 8) and §5.2 (p. 9) were checked at 170 dpi. All ten rules, Def. 5, `(=⟦⟧)`,
    `(≤⟦⟧)`, `⊨_φ`/`⊨_{Ψ,Φ}`, Lemma 1 and `O_l`/`O'_l`/`O'_e` match.
  - The `O_e` display misgroups the paper's two-dimensional layout (F1, fixed).
  - The byline note ("Santiago Zanella") is correct.
- **No fabrication.** Every sentence in the four transcriptions is in the PDF on the anchored
  page. Three files had sentences outside their raw scope, though still on the anchored page
  (F2, fixed).

### 1.5 Scope — pass (one gap in the source, reported correctly)

| Tag | Asked | Delivered |
|---|---|---|
| BGZ09 | rule for adversary/oracle calls | **No such rule exists in this paper** (F4). The delivery gives the nearest material: `(=⟦⟧)`, the invariant-carrying `⊨_φ` (§4.2), §3.4 adversaries and §5.2 Lemma 1 over arbitrary contexts. |
| Sho04 | transition types and bridging steps | all three types, Lemma 1, its generalization, and a worked bridging step |
| Gen09 | leveled key chain and its hybrid | §4.1 construction (KeyGen chain, Evaluate/Augment/Reduce), Thm 4.2.1, Thm 4.2.3 with full proof, §4.3, Rem. 4.3.1 |
| Vad12 | Thm 6.18 (LHL) and its definitions | Thm 6.18 with full proof, Defs 3.21/3.22, 2-universal, 4.7/4.8, 6.2/6.3, 6.7, 6.9, 6.13, 6.16, Thm 6.17, attribution |

### 1.6 Registry — pass

- `sources.json` is valid JSON with the same top level (`_comment`, `tags`).
- The diff only adds `BGZ09`, `Gen09`, `Sho04` and `Vad12`, taking the registry from 22 to 26
  tags. No existing row changed.
- Each new row has exactly `{title, documents}`, keys stay sorted, and every document stem
  exists as an `.md`/`.raw.md` pair.
- The file round-trips exactly through
  `json.dumps(indent=2, ensure_ascii=False) + "\n"`, which is `scripts/reference_coverage.py`'s
  writer.
- The schema has no hash field. Keeping the hashes in the file headers, as DW-7 does, is right.

### 1.7 Citation report (REPORT.md) — correct

- **Locations:** every citation location and anchor in REPORT §§3–6 is correct against the PDFs,
  including:
  - the section and page placements (BGZ09 §3.4 and §4 on p. 6, §3.2 on p. 5);
  - the page offsets (Gen09 printed = physical − 10, Vad12 printed = physical − 3);
  - Thm 6.18 on printed p. 179.
- **Unconfirmed side remark (Info):** among the paper's "named rules" the REPORT lists [R-Trans].
  It occurs only as a forward reference ("and [R-Trans] in the next section") and is never
  stated. This does not affect any citation.
- **Search claims:** the REPORT says no adversary/oracle-call rule exists and "invariant" occurs
  once. I confirmed both by full-text search.
- **Gen09 against the plan:** the REPORT's comparison with `briefs/lattice-gsw/phase6/plan-section.md`
  §H3.11 is accurate. The plan's hybrid is top-down and substitutes encryptions of `0`; Gentry's
  is bottom-up and substitutes an unrelated random key.

**[Vad12] check against the three `.lean` citations — the number and statement are right, with
two precision points (F6, F7).**

- `Regev/Experiments.lean:38`, `SIS/Columns.lean:33` and `SIS/Universality.lean:30` each carry
  `* [Vad12] S. Vadhan, *Pseudorandomness*, 2012, Theorem 6.18.`
- In the uploaded published edition, Theorem 6.18 is the Leftover Hash Lemma, in its strong
  (seed-published) form.
- Its hypothesis is "pairwise independent (or even 2-universal)". This covers the
  collision-universal family of `Universality.lean`, whose zero input hashes to zero.

The REPORT says that *if* the Lean error was calibrated to the proof, that is consistent. I
checked, and it was:

- `extractionError := ½·√(q^(n+1)/2^m)`, `strong_leftover_hash`'s `√(q^n/2^cols)/2`, and the
  underlying `TCSlib/InformationTheory/LeftoverHash.lean` bound `½·√(|β|·2^(−k))` are all exactly
  the proof's closing claim, "a strong `(k, ε/2)`-extractor", with `ε² = M/K`.
- They are not the theorem's headline `ε`.
- They are also stated for arbitrary finite seed and output sets, such as `(ℤ_q)^(n+1)`. That
  generality comes from the proof's `D, K, M` and the remark after Def. 6.13, not from the
  statement's literal `{0,1}^m`.

Under `policy.md` §2 ("Deviations"), the docstrings should say this (see §4).

### 1.8 Model identifiers — one breach, outside the landed files (F3)

- **Landed files:** none of the nine landed files contains a model identifier.
- **Patch metadata:**
  - Each of the five patch files carries a `Co-Authored-By` trailer that names a model, and a
    session link, in its commit message.
  - Each patch header also has a worker `From:` name.
  - The brief says "Write no model identifiers."
- **`validation-status` line:** the transcriptions carry DW-7's line verbatim. It names a
  reviewer role used across `blueprint/src/references/`, not a model identifier. No change is
  needed.

## 2. Findings

| # | Severity | Finding | Disposition |
|---|---|---|---|
| F1 | Medium | [BGZ09] p. 9, `O_e` display (`pdf-216f8cd86ce5-p009-b003`, cited as `[BGZ09, §5.2, O_l → O_e]`). The paper sets `L ← (x,y) :: L` on its own indented line after the inner `if x = x' then y ← y' else y ←$ d;`, so the table is updated on both branches. The delivery flattened this into one parenthesized line ending `else y←$d; L←(x,y)::L)`, which reads as updating `L` only on the `else` branch. | **Fixed (E1):** the display now reproduces the printed line breaks and indentation. |
| F2 | Low | Raw scopes stop short of transcribed text on anchored pages. [BGZ09] p6 lines 82–83 (§3.4 "(those that can be read …) … `⊢wf A` can be derived") and p9 lines 128–147 (`O_e`, `O'_l`, `O'_e`). [Vad12] p88 line 3369 ("Supp(π)."), p184 lines 7138–7139 (end of the Rényi remark), p212 lines 8263–8264 (start of the attribution sentence). [Sho04] p11 lines 538–540 (the formula quoted in the glyph note). | **Fixed (E2):** scopes extended and the raw files regenerated with the delivery's own commands. |
| F3 | Medium (hygiene; not landed) | Model-name `Co-Authored-By` trailers in all five patch headers, against the brief. Because the `review/dw8` replay used `git am`, its commits carry them too. | Land by file copy, as done here. Never push or cherry-pick `review/dw8`, and do not apply the series to the records. Ask the job to drop such trailers next time. |
| F4 | Medium (source gap; not a delivery defect) | [BGZ09] (POPL 2009) has no rule for adversary/oracle calls under a relational invariant. Its Fig. 5 is complete, and no adversary rule appears anywhere in the text. The delivery reports this honestly and proposes the right substitutes. | Cite the substitutes in §4 with a deviation note. A named adversary rule would need a new source and a ruling (Q11 follow-up). |
| F5 | Low | [Sho04] p. 13: the random-assignment mark is legible at 600 dpi as a **cent sign `¢`** over the arrow. The delivery writes `\stackrel{?}{\leftarrow}` and calls it unidentified, which is conservative, not fabricated. The boxes marking the changed lines of Game 2 are also not represented. | Recommend in a later pass: replace `?` with `¢` and reword the note. Not changed here. |
| F6 | Low | The Lean leftover-hash error `½·√(M·2^(−k))` is the *proof's* `(k, ε/2)` conclusion over general finite sets, not Thm 6.18's headline `(k, ε)` over bit strings. The theorem number and statement are right. | Docstring-only follow-up (§4); `.lean` files not edited. |
| F7 | Low | `SIS/Universality.lean:103` (`isUniversal_hash`) cites `[…; Vad12, Theorem 6.18]` for collision-universality. The definition of 2-universal is in [Vad12] §3.5, p. 64, after Def. 3.22 (`pdf-bf2ce5422088-p067-b002`). | Docstring-only follow-up (§4). |
| F8 | Info | [Sho04] `p013-b001` opens with an editorial "[Context: …]" bracket in the same style as the paper's own "[This transition is a bridging step.]". Its content was checked against pp. 11–12 and is accurate. | Optionally relabel it as an italic editorial note. |
| F9 | Info | [Vad12] masthead reads "Vol. 7, Nos. 1–3 (2011) 1–336", © 2012. The registry title and transcription say "7(1–3):1–336, 2012". | Acceptable as is (publication year 2012). |
| F10 | Info | `generated-by: maintainer transcription` and the `validation-status` wording are copied from DW-7. The files were written by the external job. | Matches the requested format; no change. |

## 3. Edits applied in the landed copy

All other files land exactly as delivered.

- **E1** — `barthe-gregoire-zanella-2009-certified-proofs.md`: the `O_e` display only. The
  one-line parenthesized form became an `aligned` block with the paper's line breaks:

  ```
  O_e(x) ≝ if x ∉ dom(L) then
               if x = x' then y ← y' else y ←$ d;
               L ← (x, y) :: L
           return L[x]
  ```

- **E2** — scope extensions. The raw files were regenerated from `pdftotext` with the delivery's
  own commands and re-verified to equal the stated line ranges exactly:
  - `barthe-gregoire-zanella-2009-certified-proofs.raw.md`: `p6: 84-118` → `p6: 82-118`;
    `p9: 39-123` → `p9: 39-123; p9: 128-147`;
  - `vadhan-2012-pseudorandomness.raw.md`: `p88: …-3368` → `…-3369`; `p184: …-7137` → `…-7139`;
    `p212: 8265-…` → `8263-…`;
  - `shoup-2004-sequences-of-games.raw.md`: `p11: 541-544` → `p11: 538-544`.

| Landed file (`blueprint/src/references/`) | SHA-256 | Status |
|---|---|---|
| `barthe-gregoire-zanella-2009-certified-proofs.md` | `1ef9a1c40f5474068bcd602368dfc95cae7d092b8cf7221e9a19be7680d5e68d` | E1 |
| `barthe-gregoire-zanella-2009-certified-proofs.raw.md` | `6a1ec2735414832ac04cfc89931d946f7e4dab8511678c9f1f43aace2160f734` | E2 |
| `shoup-2004-sequences-of-games.md` | `3dfc581404fcadc57a5cf62e72040817b9ee278c3bd0cbc43de8bdf0e5bc983f` | as delivered |
| `shoup-2004-sequences-of-games.raw.md` | `9e2635c2529bbc99449e4098984962f1c0f7f67c975ddc1e029fd7eb3ca5921c` | E2 |
| `gentry-2009-fhe-thesis.md` | `078db24941b2d00f6f307747ecff87a15d96878fdaab6a008b6c0de14a781d0d` | as delivered |
| `gentry-2009-fhe-thesis.raw.md` | `c88465ed38124ad78a9c2814c14b06f9fd74c0e8ec96d83f54f77e90f48ce064` | as delivered |
| `vadhan-2012-pseudorandomness.md` | `74faefebc6a67a3be3fa398ff11786fb821d153ae3062cf402ab6034c54a4964` | as delivered |
| `vadhan-2012-pseudorandomness.raw.md` | `146abe38a4ea6de16018a7619ecfd429e44d47a1ce1a3278cbb0699d230e1b7a` | E2 |
| `sources.json` | `2e80ff54cbf15451556c75333826a1be0c48f38b52734bbd9aabfee009defee4` | as delivered (base + 4 rows) |

After the edits, all four pairs still parse with proofmatch. All 53 anchors check, and each raw
file still equals its scope's `pdftotext` lines exactly. Nothing is staged or committed: the
maintainer commits the records.

## 4. Citation strings for later docstrings

The forms follow `policy.md` §2. The anchor is given for the maintainer's checking and is not
part of the string.

**Module `## References` lines**

```
* [BGZ09] G. Barthe, B. Grégoire, S. Zanella Béguelin, *Formal Certification of Code-Based
  Cryptographic Proofs*, POPL 2009.
* [Sho04] V. Shoup, *Sequences of Games: A Tool for Taming Complexity in Security Proofs*,
  Cryptology ePrint Archive 2004/332, revision of 18 January 2006.
* [Gen09] C. Gentry, *A Fully Homomorphic Encryption Scheme*, PhD thesis, Stanford University, 2009.
* [Vad12] S. Vadhan, *Pseudorandomness*, Foundations and Trends in Theoretical Computer Science
  7(1–3), 2012.
```

The existing [Vad12] line, "S. Vadhan, *Pseudorandomness*, 2012, Theorem 6.18.", is correct and
need not change.

**[BGZ09] and [Sho04] — `Games.ProbComp.expect_simulate_rel` / `prob_simulate_rel` (bb1-sim Q11)**

| Use | Citation string | Anchor |
|---|---|---|
| conclusion form: related runs, test functions agreeing along the relation, equal expectations | `[BGZ09, §4.1, lemma (=⟦⟧)]` | `pdf-216f8cd86ce5-p007-b005` |
| the invariant carried as pre- and postcondition | `[BGZ09, §4.2, ⊨_φ]` | `pdf-216f8cd86ce5-p008-b003` |
| pRHL judgment semantics | `[BGZ09, §4.1, Def. 5]` | `pdf-216f8cd86ce5-p007-b002` |
| equivalence inside an arbitrary context, oracle replacement | `[BGZ09, §5.2, Lemma 1]` | `pdf-216f8cd86ce5-p009-b002` (and `p009-b003`/`p010-b001`) |
| adversaries may call oracles only | `[BGZ09, §3.4]` | `pdf-216f8cd86ce5-p006-b001` |
| bridging step: purely conceptual change, `Pr[S_i] = Pr[S_{i+1}]` | `[Sho04, §1.1, bridging steps]` | `pdf-fde1f65e83ec-p003-b002` |
| worked bridging step: random function versus lazily tabulating oracle | `[Sho04, §4.2, Game 2]` | `pdf-fde1f65e83ec-p013-b001` |

Required deviation note (F4): "[BGZ09] states no rule for adversary calls with a relational
invariant. This lemma generalizes its `(=⟦⟧)` and `⊨_φ` (§4.1–§4.2) to oracle simulations whose
states are related by an invariant, in the arbitrary-context style of §5.2." Do **not** write
`[BGZ09, rule …]` for an adversary rule.

**[Gen09] — GSW phase 6b leveled scheme (P6-Q14, P6-Q19)**

| Use | Citation string | Anchor |
|---|---|---|
| the key chain | `[Gen09, §4.1, KeyGen of E^(d)]` | `pdf-9e7f32f1b854-p056-b003` |
| security hybrid and its loss | `[Gen09, Thm 4.2.3]` | `pdf-9e7f32f1b854-p060-b001`, proof `p061-b001` |
| layered circuits, padding with trivial gates | `[Gen09, §4.1, Evaluate]` | `pdf-9e7f32f1b854-p057-b001` |
| correctness of the leveled scheme | `[Gen09, Thm 4.2.1]` | `pdf-9e7f32f1b854-p059-b001` |
| why the chain is acyclic | `[Gen09, §4.3]` | `pdf-9e7f32f1b854-p061-b002` |

Required deviation notes:

- **Index direction.** Gentry encrypts `sk_i` under `pk_{i−1}` and decrypts under `sk_0`. The
  library runs the chain upward. Gentry calls the order a presentational choice (§4.1, p. 46).
- **The hybrid.** The library's hybrid replaces the chain ciphertexts by encryptions of `0`,
  top-down. Gentry's Game `k` replaces them by encryptions of an unrelated random key, bottom-up,
  with loss `ε/ℓ(d+1)`.

**[Vad12] — leftover hash lemma (Regev, SIS)**

| Use | Citation string | Anchor |
|---|---|---|
| the leftover hash lemma, strong form | `[Vad12, Thm 6.18]` | `pdf-bf2ce5422088-p182-b002` |
| the `½·√(M·2^(−k))` error constant | `[Vad12, Thm 6.18 and its proof]` | `pdf-bf2ce5422088-p183-b001` |
| 2-universal (collision-universal) families | `[Vad12, §3.5, 2-universal hash functions]` | `pdf-bf2ce5422088-p067-b002` |
| strong extractor, seed published | `[Vad12, Def 6.16]` | `pdf-bf2ce5422088-p181-b001` |
| min-entropy, `k`-source | `[Vad12, Def 6.7]`, `[Vad12, Def 6.9]` | `p174-b001`, `p176-b001` |
| statistical difference, half the `ℓ₁` distance | `[Vad12, Def 6.2]`, `[Vad12, Lemma 6.3]` | `pdf-bf2ce5422088-p172-b001` |
| collision probability | `[Vad12, Def 4.7]`, `[Vad12, Lemma 4.8]` | `pdf-bf2ce5422088-p088-b001` |

Required deviation note wherever the `½·√(…)` bound is cited (F6): "with error `ε/2`,
`ε = √(M·2^(−k))`, as obtained at the end of the proof (a strong `(k, ε/2)`-extractor), and for
arbitrary finite seed and output sets as in the proof." For F7, change the citation at
`SIS/Universality.lean:103` to `[Vad12, §3.5, 2-universal hash functions]`. Both are
docstring-only follow-ups for a Lean change.

## 5. Housekeeping

- The scratch worktree was removed. The local branch `review/dw8` is kept and was never pushed.
- Extracted delivery, PDFs, text and page images are under
  `/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad/dw8-review/`.
  The scripts are in the sibling `dw8-review-scripts/`.
- No permission was denied.
