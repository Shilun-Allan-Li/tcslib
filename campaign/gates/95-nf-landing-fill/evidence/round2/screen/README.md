# Gate 95's copy-text screen, re-run with `BufferWords` in the population (finding 5)

Run on 2026-11-05 by a sub-agent of the cloud maintainer session (text only, under the screen lock) and reviewed by the maintainer.

## How the final screen was run (worked out from the bundled evidence)

- **Script:** `campaign/gates/95-nf-landing-fill/evidence/screen/screen-nf-pairs.py.txt`, the v3
  screen (`scripts/copy-text-screen-v3.py`, blob `2a8df2dc`, the same at every commit used here)
  with two comment lines on top and one line added in the pair loop:
  `if 'NDNormalForm' not in fa[0] and 'NDNormalForm' not in fb[0]: continue`. Declarations are
  extracted from every file of the population, so the declaration count covers all of them; only
  pairs with an `NDNormalForm` declaration on one side are tiled and reported. A diff of the
  bundled file (without its first two lines) against v3 shows that line and nothing else.
  - Run here byte for byte as bundled, saved as `copy-text-screen-v3-nf-pairs.py` (SHA-256
    `c56af478…0383a`; `cmp` against the bundled `.py.txt` is clean). The name carries
    `copy-text-screen` so that the screen lock's staleness check (`pgrep -f copy-text-screen`)
    sees it.
- **Population:** `population-landed.txt` = the bundled `population.txt`, 22 files (the brief's
  21 plus `CfgFacts`), in its order. `population.txt` = those 22 plus
  `TCSlib/Complexity/TuringMachine/BufferWords.lean` (23 files). No basename repeats, so the
  labels stay `<basename>::<name>` and `pairdiff.py` compares across both populations.
- **Root:** the repository tree at the commit, exported with
  `git -C /home/user/tcslib archive <commit> -- TCSlib | tar -x -C trees/<commit8>` (a frozen copy,
  never a worktree). The file arguments are the population's paths, relative to that root.
- **Command** (`tools/run-screen.sh.txt`, which takes and releases
  `$TCSLIB_SCRATCH/locks/screen` around each run and records the exit status):
  `nice -n 10 python3 -I copy-text-screen-v3-nf-pairs.py <root> $(cat <population>)`.

## Runs

| Run | Commit | Population | Declarations | Pairs | Characters | Output |
|---|---|---|---|---|---|---|
| reproduction | landed head `e8994dc1` | 22 files | 1,438 | 13 | 5,230 | `screen-landed-nf-pairs.txt` |
| auditor's check | landed head `e8994dc1` | 23 files | 1,444 | 13 | 5,230 | `screen-landed-bw-nf-pairs.txt` |
| **repaired** | repaired head `10c01517` | 23 files | **1,444** | **13** | **5,191** | `screen-repaired-nf-pairs.txt` |

- **Reproduction:** `screen-landed-nf-pairs.txt` is byte-identical to the bundled
  `screen-final-nf-pairs.txt` (`cmp` clean): 1,438 declarations, 13 pairs, 5,230 characters.
- **Auditor's check:** the 23-file population at the landed head gives 1,444 declarations and
  pair lines identical to the 22-file run's (13 pairs, 5,230 characters), as finding 5 reports.
  `BufferWords` adds six declarations and no pair.
- `status.txt`: each run's exit status (all 0), commit and finish time (UTC); `*.time`: wall and
  CPU seconds; `*.err`: empty.

## The repaired head against the landed head

`pairdiff.py screen-repaired-nf-pairs.txt screen-landed-nf-pairs.txt` (`pairdiff-landed.txt`) and
`pairdiff.py screen-repaired-nf-pairs.txt screen-landed-bw-nf-pairs.txt` (`pairdiff-landed-bw.txt`):
**head pairs 13, new 0, gone 0** in both. The pair set is the landed one, by name.

What changed is inside one pair:

- `nf_bClear` reproduces `nf_aReturn`: 1,353/2,357 (57%) → **1,314/2,367 (56%)**. This is the
  whole drop in reproduced text, 5,230 → 5,191 (−39 characters). The 39 characters are exactly
  one landed tile, `,FinTM.bufferTape_nat,FinTM.bufferTape_n`: the hand indexing the two `hw`
  steps shared. The repair replaces it with `FinTM.bufferTape_drop` in `nf_bClear` and
  `FinTM.bufferTape_eq_none_of_not_mem` in `nf_aReturn`. The other tiles are the same text, one
  of them matched at a different place (landed and repaired tiles compared). What is left in
  common is the two leaves' shared skeleton (`phaseHostTM_run` with `nf_retag`, the
  `skipTM_run_ofCfg`/`skipBackTM_run_ofCfg` calls and the `Function.update` bookkeeping;
  `tiles-repaired.txt`). It stays one of the eleven in-file pairs the pack leaves with the cont1
  review's dispositions.
- The other twelve pairs are unchanged to the character, including NF-X1 (`un_setup` against
  `nf_setup`, 57%) and the in-file `nf_entry`/`nf_tag` pair (54%, the pack's idiom).

**Declarations the repair changes** (`decls-landed-bw.tsv` against `decls-repaired.tsv`,
`../tools/decl-list.py`): exactly the four sites of `10c01517`, all screened before and after:
`nf_pack` (v3 body 1,090 → 1,024 characters, finding 3), `nf_aReturn` (2,357 → 2,367),
`nf_bClear` (4,132 → 4,006) and `nf_region` (852 → 848) (finding 1). Every other declaration of
the 23 files is unchanged; `BufferWords.lean` is the same blob (`78eaf8b7`) at both commits.

**`BufferWords` in the population:** its six screened declarations (`bufferTape_append_shift`,
`bufferTape_append_mid`, `bufferTape_drop`, `bufferTape_take`, `bufferTape_eq_none_of_not_mem`,
`bufferTape_unary`; 73 to 321 characters each) account for 1,438 → 1,444. No `NDNormalForm`
declaration is paired with any of them, at either head.

## Reading of the result

The screen enumerates candidates: a pair needs one declaration to reproduce, by greedy tiling in
blocks of at least 25 characters, at least half of another's whitespace-free body (and at least
60 characters); declarations whose body is under 60 characters are not extracted. It is not an
exhaustive search for re-derivations; inline steps are the sweep's business. Finding 1's three
sites were inline steps inside declarations of 852 to 4,132 characters, and no pair against
`BufferWords` showed them, with `BufferWords` in the population or not. With `BufferWords` in
the population, as WORKFLOW §3 requires, the result the pack stated stands at the repaired head:
the same 13 pairs, with one pair's shared text 39 characters shorter.

## Files

- `population-landed.txt` (22, the bundled population), `population.txt` (23, with `BufferWords`)
- `screen-landed-nf-pairs.txt`, `screen-landed-bw-nf-pairs.txt`, `screen-repaired-nf-pairs.txt`
  (each with `.time` and `.err`), `status.txt`
- `pairdiff-landed.txt`, `pairdiff-landed-bw.txt`
- `decls-landed-bw.tsv`, `decls-repaired.tsv`: every declaration v3's extractor sees, with
  `screened`/`short`, v3 body length and hashes (`../tools/decl-list.py`, which runs v3's own
  extraction code and tiles nothing)
- `tiles-repaired.txt`: the shared tiles of the 13 repaired-head pairs (`../tools/pairtiles.py`,
  v3's own `lcs` and tiling order, on the listed pairs only)
