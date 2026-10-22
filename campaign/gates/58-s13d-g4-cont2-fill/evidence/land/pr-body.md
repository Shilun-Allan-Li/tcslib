§13d G4, continuation 2 (`Turing.exists_zoneExtendTM`, `Turing.exists_zoneRebalanceTM`,
`Build/ZoneRebalance.lean`): the partial delivery `fill-s13d-g4-cont2.zip` (SHA-256
`d6f9dedb…81dd`). It is 0 of 2: both rows keep their original `sorry` bodies. It lands the first
composed machine of the zone rows, which continuation 3 builds on.

**Commits** (on the campaign branch at `eb08fb16`):
- `4b76f0ff` is the worker's commit `6fe3bf88`, cherry-picked from the verified bundle
  (prerequisite `96d60278`). It touches only `Build/ZoneRebalance.lean`, unchanged from the
  base to the tip.
- `c60ed898` (maintainer), docstrings and blank lines only; the code is identical with comments
  stripped:
  - the extension's status paragraph in public-facing terms, now also saying that the right
    pass's endpoint equation and envelope bound are not yet stated;
  - a proof sketch for `zr_adjustedBack_post` (a 21-line proof);
  - two double blank lines collapsed.

**What it adds:** 34 private `zr_` declarations, and `zr_left_two_walks` restated for the
amended left route:
- the ruler prefix and the adjusted walk;
- the half-zone writes;
- `zr_rightPassContract`, one contract for the whole positive-level right pass, composed from
  public rows by `Contract.seq` and re-wrapped by `Contract.ofSegment`, with its exact
  precondition (`zoneRowPre`), exact time `zoneStart ℓ + 10·2^ℓ + 23` and the bound
  `32·(2^ℓ + 1)`.

There is no new public declaration and no admission: 861 → 1,370 lines, 18 public / 65 private.

**Review** (sub-agent; `campaign/fills/s13d/reviews/g4-cont2/REVIEW.md`; verdict "partial 0/2,
landable"):

| Check | Result |
|---|---|
| Integrity | `SHA256SUMS` 10/10; the bundle (sole prerequisite the base) and the patch agree with the delivered file |
| Ownership and freeze | owned regions only; both statements frozen |
| Elaboration | 0 errors at the base and at the tips, only the two rows' sorry warnings |
| Axiom and admission walks | `sorryAx` only through the two rows' own bodies |
| Rule 10 | 56 other-file definitions sealed; the controls fail inside the seal and pass outside it; every external rewrite argument a published theorem |
| Import probe | 439/439 (the brief's 338 plus 101) |
| v3 screen | 808 → 838 declarations, 439 → 478 pairs; the 39 new pairs all in-file, maximum 81%: no new copy |
| Lint | 0 FAIL; one new WARN, the file's size (not a driver) |
| Environment | addendum v2.3's narrowed cache fetch succeeded on first use: 35 roots, 967 files, no retry |

The maintainer re-elaborated after the docstring commit against `oleans-l132b` (0 errors, the
same 2 warnings) and re-linted (`TuringMachine/Build` 0 FAIL, 31 WARN over 39 files).

**Replay:** `replay-lg4c2.sh`, the downstream closure on the merged tree of every file changed
since #132's merge (13 modules: this PR's `Build/ZoneRebalance` and the campaign's merges of #133,
#134, #136, #138 and #140, with the facade last), into `oleans-lg4c2`, a copy of `oleans-l132b`.
**Pending.**

**Gate:** a fill gate for this partial. **Pending.**

🤖 Generated with [Claude Code](https://claude.com/claude-code)
