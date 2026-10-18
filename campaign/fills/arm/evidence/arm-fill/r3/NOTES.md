# NOTES: ARM fill gate, round 3 (evidence, scripts, reproduction)

The evidence behind `audits/arm-extensions-fill-r3-pack.md`. Everything here was produced by the
scripts in `scripts/` from read-only inputs: the repository (git), round 2's committed evidence and
the payback's landing folder. No Lean was run in this round.

## Trees

| Name | What | How it was made |
|---|---|---|
| base | the merged tip `ff4cab18` (Lean equal to `c9cc485b`), on which the payback was built | `git archive <base> TCSlib TCSlib.lean \| tar -x` into `work/base` |
| landed | the base plus the payback's 27 patches | `work/base` copied, then `patch -p1` with each of `payback/patches/*.patch` |
| tip | the campaign tip `3648415c` (`git rev-parse origin/complexity/arora-barak-ch3-4`) | `git archive <tip> TCSlib TCSlib.lean \| tar -x` into `work/tip` |

The provenance log asserts each against git: the base export equals `git show` of every base
`.lean` file; base plus patches equals the landing folder's tree and PR #101's 27 files; the tip
export equals `git show` of the tip; the tip's 27 payback files equal the landed tree. Full hashes
are printed there from `git rev-parse`.

## Inputs (read only)

- Round 2's evidence at the tip: `r2/pairs.tsv` (the round-2 ids), `r2/classify.tsv` and
  `r2/kfam.tsv` (the acknowledged classes, families and groups), `r2/manual.tsv`,
  `r2/ledger2-decls.tsv` (round 2's A4+ declarations), `r2/ledger-r2-tables.md`;
  `r2/inputs/added.txt` (the 73 added files); `screen-population-labels.txt` (round 1's 214-file
  population).
- The screen: `audits/evidence/retrofit/copy-text-screen-v3.py`, copied byte for byte to
  `scripts/copy-text-screen-v3.py` (SHA-256 `f4feac91d3a1ec036f3bbcaafde83e6855a1bf1a62d31dac31a40a40d878f181`).
- The payback's landing folder, bundled under `payback/`: `LANDING-NOTES.md`, `ledger-map.md`,
  `patches/`, `logs/`, `scripts/`, `work/api-delta.json`, `replay-order.txt`, `SHA256SUMS`. Its
  `tree/` is not bundled: its 27 files equal the bundled tip files byte for byte (provenance log),
  so `SHA256SUMS`' `tree/` lines can be checked against those.

## Scripts (`scripts/`)

| Script | Does |
|---|---|
| `screen.zsh` | runs the v3 screen over `pop3.txt` at one tree, `nice -n 10`, recording exit status and elapsed time |
| `imports.py` | the module import graph of a tree (round 1's tool, unchanged) |
| `popcheck.py` | asserts the 218-file population: round 1's 214, plus the two modules in the added files' closure at the base and the two the payback adds |
| `screenfilter.py` | the screen's hit lines with an added-file side, verbatim, for the screen logs |
| `leancore3.py` | the declaration parser shared by the scripts (v3 naming; floor 60 for screen-eligible bodies, none for all bodies) |
| `pairs3.py` | unordered pairs with an added side, mapped to round 2's ids; new ids `L3-*`, `T3-*` |
| `r2compare.py` | the base's pairs against round 2's: ids, hits, bodies; moved lines |
| `classify3.py` | round 2's classes carried, the named round-3 changes, round 2's rule for new internal pairs, `n3lib.tsv` for new library pairs, `landed-overrides.tsv` at the landed tree and the tip |
| `manualtile3.py` | measures the manual rows (`manual3-spec.tsv`) on one tree |
| `ledger3.py` | the accountings C, K, K+; both measures, both units, both character denominators; per-file, fifth lists, declaration table |
| `r2decls.py` | K+ at the base against round 2's A4+ |
| `tipcompare.py` | the tip's pairs, classes and K+ rows against the landed tree's |
| `transitions.py` | every pair base → landed, and the ledger map's dispositions |
| `excerpts.py` | the 25 absent library counterparts and L033's, with the screen's tiles |
| `tables3.py` | `ledger-r3-tables.md` |
| `paybackkinds.py` | the 27 payback files, comment-only or code-changed |
| `homes.py` | R2-5's lower homes on an import graph |
| `leftovers.py` | R2-8: round-1 finding 11's leftovers, base against landed |
| `records3.zsh` | R2-2 and R2-6: where the records are at the tip, and the rows #101 made stale |
| `hashcheck.py` | every hash-like token in the pack and these notes resolves to a git object |
| `stage.zsh` | stages the bundle's files at their repository paths, in bundle order |
| `run_r3.zsh` | the runner: graphs, provenance, screen logs, pairs, classes, manual rows, ledgers, transitions, excerpts, homes, leftovers, records, tables, evidence copies |

## Reproduce

```
zsh scripts/screen.zsh work/base   work/pop3.txt work/screen-base.out     # about 50 minutes each
zsh scripts/screen.zsh work/landed work/pop3.txt work/screen-landed.out
zsh scripts/screen.zsh work/tip    work/pop3.txt work/screen-tip.out
zsh scripts/run_r3.zsh <scratch-root> <repo>
python3 -I -B scripts/hashcheck.py <repo> <pack> NOTES.md      # once the pack is final
```

Run the screens one at a time. The runner refuses to start unless all three screens finished with
exit 0, the payback folder's base is `ff4cab18` or `eb750e63`, and every hash it uses resolves.

## Outputs

Evidence (this folder): `pairs3-{base,landed,tip}.tsv`, `classify3-*.tsv`, `manual3-*.tsv`,
`ledger3-*-decls.tsv`, `transitions.tsv`, `dispositions.tsv`, `n3lib.tsv`, `landed-overrides.tsv`,
`excerpts-n-pairs.md`, `ledger-r3-tables.md`, `pop3.txt`, `patch-stats.txt`. The bundle's file list
(`BUNDLE-FILES.txt`, with sizes) is written by `stage.zsh` beside them; it is the list `verifybundle.py` checks.
Logs (`audits/logs/arm-fill-r3-*.log`): provenance, screen-base, screen-landed, screen-tip, pairs,
classify, ledger, transitions, excerpts, homes, leftovers, records, hashcheck.

## Conventions

- A declaration counts once, whole, if it is the copy side of a counted pair (round 2's rule);
  between two added files every directed hit's reproducing side counts.
- Manual rows count one side (round 2's M1 convention); the M3 rows state their original.
- "Screen-eligible body characters" are bodies of at least 60 whitespace-free characters, the
  screen's floor; "all body characters" have no floor. Manual rows enter numerators only.
- Line numbers are at the tree named in each table; the excerpts are at the base.
