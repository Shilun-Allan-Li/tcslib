# Brief · external ingest job `dw8-ingests` (four sources)

Deferred-work item **DW-8** (`briefs/pass-shelat-ch5-8/deferred-work.md`): source ingests that never block other work. Seyoon
dispatches this job to an external Claude worker. The worker is documentation-only: it reads PDFs and writes
Markdown transcriptions and registry rows. It runs no Lean and changes no `.lean` file.

## Where the PDFs are
The PDFs are on the **private** repository `sragavan99/tcslib`, branch `sources/pdfs`, folder `pdfs/`. Attach that
repository to your session; Seyoon owns it. The PDFs must **never** be committed to `Shilun-Allan-Li/tcslib`, which
is public (DW-7 rule).

| Tag | File | Source | SHA-256 (if known) |
|---|---|---|---|
| [BGZ09] | `barthe-gregoire-zanella-2009-popl.pdf` | G. Barthe, B. Grégoire, S. Zanella Béguelin, "Formal certification of code-based cryptographic proofs", POPL 2009 | `216f8cd86ce5e077730bcf9d5ed1a90131f0107d23e64f249c7df02690b4678a` |
| [Sho04] | `shoup-2004-332.pdf` | V. Shoup, "Sequences of games: a tool for taming complexity in security proofs", IACR ePrint 2004/332 | `fde1f65e83ec85297f58840bf87de15fb68e91ada8aefaf77db3b153cf826820` |
| [Gen09] | `gentry-2009-thesis.pdf` | C. Gentry, *A Fully Homomorphic Encryption Scheme*, PhD thesis, Stanford University, 2009 | record it |
| [Vad12] | `vadhan-2012-pseudorandomness.pdf` | S. Vadhan, *Pseudorandomness*, Foundations and Trends in Theoretical Computer Science, 2012 | record it |

Verify the two known hashes and record the other two. If a file is missing, ingest the others and report the gap.

## What to ingest (only the passages used, plus the context needed to read them)
Ingest only what each citation needs:
1. **[BGZ09]:** the relational Hoare logic rule for adversary/oracle calls, and the definitions it depends on. It is cited for
   the new `Games.ProbComp.expect_simulate_rel`: two oracle implementations with states related by an invariant, where each call
   preserves the invariant and gives equal answer laws, so that whole runs agree. Sources:
   `briefs/pairings/fills/bb1-sim/design-r1.md` §2 and §5 (Q11, risk 7) and `briefs/pairings/fills/bb1-sim/rulings.md` (Q11).
2. **[Sho04]:** the game-hopping transition types, in particular "bridging steps" (a change of a game that does not change its
   distribution). It is cited for the same lemma.
3. **[Gen09]:** the leveled-bootstrapping construction, meaning the key chain (one evaluation key per level, each encrypting the
   previous level's secret key) and its security hybrid. It is cited for GSW phase 6b's leveled scheme
   (`briefs/lattice-gsw/phase6/plan-section.md` r3, §H1 gap 1 and §H3.11; `briefs/lattice-gsw/phase6/rulings.md`, P6-Q14 and
   P6-Q19 with the refinement).
4. **[Vad12]:** Theorem 6.18 (the leftover hash lemma) and the definitions it needs. It is already cited, as "[Vad12] S. Vadhan,
   *Pseudorandomness*, 2012, Theorem 6.18", in `TCSlib/Cryptography/Encryption/PublicKey/Regev/Experiments.lean:38`,
   `TCSlib/Cryptography/Hashing/SIS/Columns.lean:33` and `TCSlib/Cryptography/Hashing/SIS/Universality.lean:30`. Check that the
   theorem number and statement match how those files use it, and report any mismatch. Do not edit the `.lean` files.

## Format: mirror the DW-7 ingests exactly
- Study `blueprint/src/references/boneh-boyen-2004-selective-id-ibe.{raw.md,md}`, `gentry-sahai-waters-2013-fhe.{raw.md,md}` and
  `barrington-1989-bounded-width-bp.{raw.md,md}`. The `.raw.md` holds the mechanical text with anchors `pdf-<hash>-pNNN-bNNN`; the
  `.md` is the scoped transcription carrying those anchors.
- Study the registration rows in `blueprint/src/references/sources.json`, and any pipeline tool the DW-7 ingests used (records commit
  `6078f369` and the `briefs/` folders it touched).
- Write these files, using `pdftotext`/`pdfinfo` and Python as `python3 -I`, with scripts kept outside the PDF folder:
  - `blueprint/src/references/barthe-gregoire-zanella-2009-certified-proofs.{raw.md,md}`;
  - `blueprint/src/references/shoup-2004-sequences-of-games.{raw.md,md}`;
  - `blueprint/src/references/gentry-2009-fhe-thesis.{raw.md,md}`;
  - `blueprint/src/references/vadhan-2012-pseudorandomness.{raw.md,md}`;
  - registration rows for all four in `sources.json`, in the existing schema, with the PDF hashes.
- **Never fabricate text.** Transcriptions must match the PDF, and anything illegible is marked as such. Write no model identifiers.

## Base and delivery
- **Base:** the records branch `cryptography/pass-shelat-ch2-4` of `Shilun-Allan-Li/tcslib`, at the issue base named in the
  dispatch prompt. Commit on a local branch `ingest/dw8` (`commit.gpgsign=false`); never push it.
- **Delivery:** deliver only under `inbox/ingests/dw8/` on `exchange/pass-shelat-ch5-8`, with:
  - `REPORT.md`;
  - `patches/` (the `git format-patch` series from the base, with `COMMITS.tsv`);
  - `src/` (the written files);
  - a top-level `SHA256SUMS` listing every delivered file except itself.

  Pull with rebase before pushing. Never force-push, never edit another path, never push a campaign branch, and never push a PDF.

## REPORT.md must give
- For each tag: the files and their SHA-256s, the PDF hash, the pages ingested, and the exact citation locations in the library's
  form (for example `[BGZ09, §n, rule …]`, `[Sho04, §n]`, `[Gen09, Thm/§ …]`, `[Vad12, Thm 6.18]`) with their anchors.
- A short assessment of how directly each passage supports its use.
- For [Vad12], the check against the three existing `.lean` citations.
- The `sources.json` diff.
- Anything missing or illegible.
