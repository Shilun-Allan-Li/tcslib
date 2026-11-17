# Gate 45 round 2 · the GSW 6a gate (#358, #359) · G45-01..03 fixed by LE-g45 and LE-g45b

Read `pack-r2.md` first.

Files:
- `pack-r2.md`: the round-2 pack (pins, the two edits, evidence summary, what carries over, known slips, questions,
  merge conditions, delivery).
- `findings-r1.md`: round 1's findings, filed verbatim.
- `resolutions-r1.md`: the maintainer's resolution of G45-01..03 (LE-g45 and LE-g45b) and round 1's confirmations.
- `le-g45.md`, `le-g45.diff.txt`, `le-g45-evidence.zip`: LE-g45 (`ad9c4fc7` on `73aedcda`) and its Lean evidence.
- `le-g45b.md`, `le-g45b.diff.txt`, `le-g45b-evidence.zip`: LE-g45b (`d154c883` on `ad9c4fc7`) and its Lean evidence.
  Each zip carries its own `SHA256SUMS`, `PROVENANCE.txt` and `tools/TOOLS.txt`.
- `records-r1-r2.diff.txt`: the records delta between the two pins (below).
- `pr359-description-r2.md`: PR #359's body as read from GitHub at staging (title, not in the file: "GSW 6a statements:
  branching programs, Barrington, NAND form and formula arithmetic (98 targets)").
- `SHA256SUMS`: covers every other file here.

Pins: PR #358 `a616adcac0760ab56b1b0a2a4869f4763843f9ab` (unchanged); PR #359
`d154c8830fc8ffc52671b41992e7dbef61e30959`. Records: round 1 `8c5875fa268a622e4e166da5f7a992715097c2c7`, round 2
`a9d422cc4f76fbe188770405bfd264f5710947ff` ("Records: Gate 45 round 2 pack"). Every file here except this README and
`SHA256SUMS` is byte-identical to its copy in `briefs/lattice-gsw/gates/45-gsw-6a/` at the round-2 records pin, where
`SHA256SUMS-r2` lists the same hashes. The round-1 pack is `outbox/gates/45-gsw-6a-gate/` at exchange
`059331913c8a5380d3ae53e5e9dffa3c7ff6e2b4`.

**The records delta and its self-reference.** `records-r1-r2.diff.txt` is

```
git diff 8c5875fa268a622e4e166da5f7a992715097c2c7 a9d422cc4f76fbe188770405bfd264f5710947ff -- \
  LatticeCryptographyPlan.md briefs/lattice-gsw/gates/45-gsw-6a/ \
  ':(exclude)briefs/lattice-gsw/gates/45-gsw-6a/pack-r2.md' \
  ':(exclude)briefs/lattice-gsw/gates/45-gsw-6a/resolutions-r1.md' \
  ':(exclude)briefs/lattice-gsw/gates/45-gsw-6a/records-r1-r2.diff.txt' \
  ':(exclude)briefs/lattice-gsw/gates/45-gsw-6a/pr359-description-r2.md' \
  ':(exclude)briefs/lattice-gsw/gates/45-gsw-6a/dispatch-r2.md' \
  ':(exclude)briefs/lattice-gsw/gates/45-gsw-6a/SHA256SUMS-r2'
```

The diff file is itself filed at the pin, so it cannot contain its own addition; the round-2 pack files are therefore
excluded, and they are supplied whole in this folder instead (`resolutions-r1.md` was first committed as a
work-in-progress draft at records `9989e28e`; the pin holds the final text). The command reproduces the file byte for
byte at the pin. `dispatch-r2.md` is not in this folder: it holds the dispatch prompt, and a later records commit fills
the pin and this exchange hash into it (the one round-2 records file that postdates the pin; `SHA256SUMS-r2` does not
cover it). The delta also shows the round-1 pack's records copies, which were filed after round 1's pin as round 1's
dispatch stated; zips appear as binary additions.
