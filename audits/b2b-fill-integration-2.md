# B2b fill, delivery 2 (partial; setup proved, admission narrowed): integration record

Brief: `briefs/ch34-b2b-cont.md` (ancestor `8e9a9b7e`). Delivery:
`infra_local/fill-ch34-b2b-cont.zip`, agent commits `cd351471` and `a4354452` (delivery
`cc43e573`) on base `4aafe9e4`. The agent's report is
`audits/b2b-fill-agent-reports/fill-2-REPORT.md`. The first delivery's record is
`audits/b2b-fill-integration.md`. The two patches were applied at the campaign tip `fc999a8b`;
`Inclusions.lean` is unchanged between base and tip.

## Result

**Partial: neither target is admission-free yet.** This is a continuation under ground rule 9,
with no escalation and no defect in a frozen definition.

- **Proved now:** the complete S1–S5 setup, assembled by `b2b_setup_run`:
  - `b2b_setup_capture`;
  - `b2b_origin_run`, the S2 virtual rewind;
  - `b2b_seed_run`, the S3 copy and S4 overflow;
  - `b2b_rewind_return`.

  The endpoint is exactly the outer loop's `.dec .run` seam, with certificate `0^Q`, counter
  `1^Q`, blank scratch, origin heads and empty output. Also proved: the reusable silent
  capture `b2b_clean_capture`, and **the window-to-cardinality packaging inside
  `b2b_host_contract`**, whose statement is unchanged and whose body is new.
- **Open:** one narrower admitted private helper, `b2b_search_contract`. It covers the search
  from the established setup seam: the shared trial/round contract, the counter loop with
  classical first-arrival durations, the final call and the answer, and the search windows.

There are 10 new private declarations: 8 proved theorems, 1 configuration definition and the
admitted helper. There is no new machine, public declaration or import.

## Verification (maintainer)

- **Integrity.** All 50 `SHA256SUMS` entries are OK. The zip's C file
  (`environment/lean-readlink.c`, an `LD_PRELOAD` shim) is excluded: never compiled or run,
  and nothing references it. `evidence/check_freeze.py` was not run.
- **Integration.** Both patches applied with `git am -3`, keeping the agent's authorship. The
  file matches the delivered snapshot byte for byte.
- **Freeze** (`audits/logs/b2b-fill-2-freeze.log`).
  - No public was added or removed, and no public body changed.
  - The only changed existing declaration is the private `b2b_host_contract`. Its statement is
    unchanged; brief rule 2 permits a body change.
  - 10 privates added.
  - Imports unchanged (7).
  - The only `sorry` among the added lines is `b2b_search_contract`'s.
- **Duplication** (`…-screen-after.txt`, base `b2b-cont-screen-base.txt`). Byte-identical to
  the agent's run: 843 → 854 screened declarations, **634 → 634 pairs**, and every pair line is
  identical. **New copies: none.**
- **Lint** (`…-stylelint.log`): 0 FAIL, 2 WARN over `SpaceComplexity`, both size warnings.
- **Size:** `Inclusions.lean` 815 → 1,538 lines. The brief sets no size cap and requires
  helpers to be private here; file size alone is not a driver (user, 2026-10-11).
- **Replay** (`…-replay.log`). 4 modules at `a4354452` into a tip-consistent snapshot; the user
  ran it. **0 errors.** 5 sorry warnings: `Inclusions` 1 (`b2b_search_contract`) and `TQBF` 4.
- **Axioms and admission walk** (`…-axioms.log`).
  - `DTIME_subset_SPACE` and `P_subset_PSPACE` print the standard triple.
  - Both targets print `sorryAx`, and the walk gives `b2b_search_contract` as their only
    `sorryAx` source.

## Disposition

This partial goes in by PR. The second continuation brief, `briefs/ch34-b2b-cont2.md`, targets
`b2b_search_contract`. The B2b fill gate runs once both targets close.
