# Gate 157 resolutions

## Round 1: HOLD (0 blockers, 1 major, 2 minors, 3 notes; `findings.md`, verbatim)

- **G157-01 (major), repaired.** `dz_kit_exists` (NTimeDiagonalizer) now states the kit's
  bounds as the Lean gives them:
  - the input calls (stage query, `bits(g(|x|))`, prepending `1`) run within `A(g(n) + 1)`
    steps, and the stage query's output length is at most `A(g(|x|) + 1)`;
  - the install calls run within `A(|y| + 1)` steps, with the inner component's output at most
    `A(|y| + 1)`.

  A related entry was vague: `qy_kit_exists` said each call met "its stated linear or
  polynomial time bound"; it now lists every call's bound, including `A(g(n) + 1)` for
  `bits(g(|x|))`. The same overstatement was in a title: `exists_queryTM`'s "The stage query in linear time" is
  now "The stage query within a multiple of `g(n) + 1`". Its body already stated `C(g(n) + 1)`.
  The `DzKit` definition entry already gave `A(g(n) + 1)`.
- **G157-02 (minor), repaired.** `ScId`'s heading is "Scale-loop labels". Its two siblings
  repaired in the same pass got matching headings: `IcId` is "Increment-chain labels" and `CpId`
  is "Copy-loop labels". Their bodies were already correct.
- **G157-03 (minor), corrected.** The pack's explanation was wrong: the validator normalizes
  private names before computing orphans.
  - **Validator:** `scripts/blueprint_validate.py`, blob `ee022d64` (last changed in
    `68b90c92`). It is run from the repository root, with `dep_graph.json` replaced by the
    refreshed graph and then restored.
  - **Classification** (`evidence/ORPHANS-CLASSIFIED.json`), **none in the chapter scope**:
    - **860** label declarations that exist in source, in modules no root import reaches
      (GraphTheory/Core, BooleanAnalysis/RazborovSmolensky, Cryptography/RSA, the Karger
      chapters). They were never compiled, so they have no graph entry; this is the case
      `--allow-orphans` describes.
    - **712** are entries for declarations that earlier campaign refactors removed in chapters
      1–2 areas: TuringMachine 583, CookLevin 64, ClassNP 62, and one each in ClassP,
      GraphTheory/Core and Randomized. They are outside W5's scope and are not touched here.
  - **Log:** `evidence/VALIDATE-r2.txt` is the rerun at the repaired head. The counts are
    unchanged: 0 dangling, 0 duplicates, 0 cycles, 1,572 orphans.
- Notes G157-N1 to N3: no action beyond the above.
