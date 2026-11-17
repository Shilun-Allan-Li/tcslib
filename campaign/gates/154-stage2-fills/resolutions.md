# Gate 154 resolutions

## Round 1: HOLD (0 blockers, 1 major, 1 minor, 4 notes; `findings.md`, verbatim)

The dispatched pack and evidence (head `f2d1ead7`) are preserved. Round 2 is a new head and pack.

- **G154-01 (major), repaired.** `dgWindow_step` (SingleTape; changed by Fill B) passed Mathlib's
  definition `SignType.cast` to `simp only` at five sites. It now uses the published
  `SignType.neg_eq_neg_one`, `zero_eq_zero`, `pos_eq_one`, `coe_neg`, `coe_one` and `coe_zero`,
  as CfgRecord's `InWindow.apply_iff` does. Commit `375531b6`.
  - **Every other flag of the Lean-backed sweep was located in the tactic lists and classified.**
    - The simprocs `reduceIte` (Codec/Step), `Int.reduceNeg` and `reduceCtorEq` (CfgRecord) are
      not reads.
    - The other constants occur only inside proof-term arguments of `rw`:
      - `rfl`: `xr_phase_step … rfl rfl` (ExhaustiveReplay), `if_pos rfl` and `if_pos ⟨rfl, …⟩`
        (CodeSimulator), and `ss_live_map … rfl` (UniversalK);
      - `Bool.noConfusion`/`Sum.noConfusion`: `if_neg (fun h => ….noConfusion …)` (CodeSimulator);
      - `Nat.find`: `List.take_append_drop (Nat.find hex) w` (Nondeterministic).
    - `SignType.cast` was the only definition passed as a rewrite rule.
  - **Procedure fixed:** WORKFLOW.md §4 now requires every flag, Core and Mathlib included, to be
    dispositioned this way. "Outside TCSlib" is not a disposition. SingleTape's two older
    `SignType.cast` uses (in `encodeAction`-level proofs at lines 193 and 1217) are in unchanged
    proofs.
- **G154-02 (minor), accounting.** `universalCapture_embed` (UniversalStartup, new in #350) is an
  RN-1 member. It is now counted in `duplication-ledger.md` (RN-1 at closeout stage 2) and carried
  in `CARRIED-REGISTER.md`: citing `Cfg.mapState_eq_of_fields` needs a CfgFacts import into
  chapter 1's UniversalStartup, which is not approved.
- Notes G154-03 to G154-06: no action beyond the two above.
