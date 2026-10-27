# B5a: the after-screen of the review's proof (maintainer, 2026-10-27)

The review's assembly (`campaign/fills/b5a/reviews/unisim-rewrite/probe/B5aReviewAssembly.lean.txt`,
without its axiom prints) committed on the local branch `local/b5a-landing` at `1a508123`, on the
campaign tip; not pushed (D1 pending). The 57-file population on that frozen worktree
(`wt-b5aland`, no tracked change), against the screen base `../preship-9d0af8cb/screen-base.txt`.

- **The screen:** 2,842 declarations, 3,062 pairs, 983,367 characters; 52 minutes, peak 6.7 GB.
- **Against the base:** 24 new pairs, none gone (`pairdiff-head-vs-base.txt`). **None reaches
  90%.**
  - **`us_start` as the source, 21 pairs** (281 characters: "a composite restarted at a tagged
    state starts at the relabelled blank start", by `Cfg.ext` and the field equations). The two
    highest are 89%: `ExhaustiveReplay`'s `xr_E_initCfg` and `NTimeHierarchy`'s `un_setup`, both
    private, already contain the same identity. Then `exists_selfStartupTMK` (78%), `UniversalK`'s
    `ss_buffer*` (64–72%), `phaseHostTM_run` and `Cfg.mapState_mapState` (64%), the canonizer's
    legs (60%), the startup (56%) and `sl_rewrap` (54%). With `UniversalK`'s private
    `uk_init_mapState` (the review's F8), this is a family of four private variants of one
    identity: a promotion candidate, a public lemma beside `MultiTapeTM.initCfg_with_q₀`.
  - **`us_table_le` as the source, 2 pairs:** `CodeFormat`'s `numStates_decode_le` (63%) and the
    target's body (60%), the `serialize_decode_length_le` bound's shape.
  - **New code as the target, 1 pair:** `us_junction` reproduces `sl_rewrap` at 54%, the accepted
    rewrap idiom.
