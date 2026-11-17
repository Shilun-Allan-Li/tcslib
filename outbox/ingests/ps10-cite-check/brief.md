# Brief · external docs job `ps10-cite-check` (PS10 ch. 5–8 citation check)

Seyoon ruled on 2026-11-17 that the full PS10 ingest (ch. 2–8, through the repository's dataset pipeline) waits for
the ch. 2–4 → `main` integration, as the 2026-11-05 ruling says. This job is **only the citation check**:
- it transcribes nothing;
- it writes no `blueprint/src/references/` file and no `sources.json` row;
- it edits no `.lean` file;
- it runs no Lean.

## Inputs
- `Pass–Shelat.pdf`, at the root of the records branch `cryptography/pass-shelat-ch2-4` at the pinned commit, SHA-256
  `7624556077a7a272ba0b3ddb7cd47b96574fb0b4b4947a25467d1f91bb61bda8`. Book page = PDF page − 12; ch. 5–8 are book
  pp. 133–184 (PDF pp. 145–196).
- `citations-ch5-8.tsv` (this folder): every site in `TCSlib/**.lean` that cites a PS10 ch. 5–8 location. There are 67
  distinct locators at 871 sites, computed at records `ff0c2552`. Recompute it at the pinned commit with
  `git grep -n "PS10" <pin> -- 'TCSlib/**.lean'`, filtered to ch. 5–8 (items 133.x–184.x, §5–8, pp. 133–184, ch. 5–8),
  and report any difference.

## Check each locator
1. **Existence and kind.** Does the numbered item exist on the cited page with the cited kind (Definition, Theorem,
   Lemma, Protocol, Construction, Claim, …)? Labels are printed in lower case, for example "protocol 134.3"; 160.4 is a
   "Construction".
2. **Lettered locators.** The seven lettered locators (157.a, 158.a, 159.a, 160.a, 169.a, 172.a, 179.a) name
   unnumbered passages from the campaign inventory. Confirm that each named passage exists where cited.
3. **Content, for each site.** Does the docstring's description at that site (its prose, the formula line, or the
   deviation note) match what the cited item says? Flag wrong numbers, wrong pages, wrong kinds, and claims the item
   does not make.
4. **Section headings.** §-locators point to real headings (§8.3.3 is a heading on the last line of p. 184).

Use `pdftotext -layout` per page, and page images (`pdftoppm`) where the layout matters. Run Python as `python3 -I`,
with scripts kept outside any extraction folder. Never copy or commit the PDF.

## Delivery
Deliver only under `inbox/ingests/ps10-cite-check/` on `exchange/pass-shelat-ch5-8`, with:
- `REPORT.md`, holding:
  - a per-locator status table (OK / wrong page / wrong kind / missing / content mismatch);
  - the list of mismatching sites (`path:line`, the citation, the problem, a suggested docstring correction);
  - the recomputed citation list's difference from the TSV;
- `SHA256SUMS`.

Commit unsigned. Message `cite-check ps10: final`, with no trailers. Run `git pull --rebase` before pushing; never
force-push; change no other path; never push a campaign branch.
