# Gate 151 · Closeout C1E-1 trims: `ClassNP/ExhaustiveReplay` (PR #344)

**Not yet clear to merge** · PR #344 is a draft. Seyoon dispatches and merges.

- Lean head: `974599a43484632ba38ab4dec4196790a6d0cb46`.
- Base: campaign Lean `c01114e7`; records `80882831`.
- This is the first audit. The PR is independent of #343 (gate 150): the files are disjoint.

## Scope

This is wave R3, family C1E-1: the remaining trims (b), (c) and (d) of `campaign/backlog.md`
§C1E-1, recommended in the R3 row of `campaign/closeout/R3-R6-MEASUREMENT.md`. Both files are
bundled. Seyoon said go ahead on 2026-11-16. Item (a), re-pointing `xr_val` to `counterValue`, stays
declined, as the measurement recommends: the public API offers only `counterValue_eq`/`_bits`, so
the eight `xr_val` lemmas would be re-proved under the public name and nothing would be saved.
Item (d)'s optional part, merging the nine one-bank update lemmas into one, is not done.

The changes, all in `ClassNP/ExhaustiveReplay`:

- **(b) Buffer-tape facts.**
  - `xr_bufferTape_neg` is deleted. Its two other uses, in `xr_passTM_run` and `xr_test_tail`,
    cite the public `FinTM.bufferTape_of_neg`.
  - `xr_bufferTape_ge` is deleted. It was used only by `xr_bufferTape_eq_none_iff`.
  - `xr_bufferTape_eq_none_iff` keeps its statement and 5 uses. It is now proved from the public
    `FinTM.bufferTape_eq` by splitting on `0 ≤ p`.
- **(c) The replay's two exits.**
  - The new private `xr_replay_prelude` states the common start of `xr_replay_finish` and
    `xr_replay_timeout`: the shifted start is live at `N`'s start state, the budget word sits
    unshifted on the counter, and the replay phase runs as the silent embedding of the clock
    host's run. Its proof is the former shared text.
  - Both exits open with `obtain ⟨hq, hct, hE⟩ := xr_replay_prelude C z s w wD h`. Their
    statements and remaining steps are unchanged.
- **(d) Bank inequalities.**
  - The ten lemmas `xr_work_ne_choice`, …, `xr_cap_ne_dep` are deleted. Each was a two-line
    proof comparing `Fin.val`s.
  - A file-local tactic `local macro "xr_bank_ne"` replaces them. It runs
    `apply Fin.ne_of_val_ne`, then `simp only` with the five `xr_*_val` equations, then `omega`.
  - Its 38 use sites read `(by xr_bank_ne)`, mostly as `Function.update_of_ne (by xr_bank_ne)`.
  - `xr_dep_ne_cap`, which comes earlier in the file than the value equations, is unchanged.

There are no statement changes and the module's public API is unchanged. Net: **−38 Lean
lines** (+74/−112).

## Brief for the auditor

1. **Statements.** Confirm that every public declaration and every surviving private statement is
   byte-identical to base. `SOURCE.json` lists one `header_changed`, `xr_work_injective`. This is a
   splitting artifact: the new `local macro` and its docstring sit just above that theorem, and
   the declaration splitter attaches them to its chunk. Its own text is unchanged.
2. **(b).** Check `xr_bufferTape_eq_none_iff`'s new proof, including the boundaries `p = -1`,
   `p = 0` and `p = |v|`, and check that the two `bufferTape_of_neg` citations have the hypotheses
   they need.
3. **(c).** Check that `xr_replay_prelude` states exactly what both exits used (`hq`, `hct`, `hE`)
   and that its proof is the old shared text.
4. **(d).** Check that `xr_bank_ne` closes only true inequalities: it fails, rather than
   mis-proving, when the values coincide. Check that every replaced citation's goal is an
   inequality between two distinct banks. Consider whether a file-local tactic is acceptable
   here in place of named lemmas.
5. **Rule 10.** The changed proofs: seals, controls and both sweeps (counts below).
6. **Copy screen** (population: ExhaustiveReplay): see `evidence/PAIR-DISPOSITIONS.json` and the
   note under Evidence.

## Evidence

- `evidence/REPLAY.json`: the merged-tree replay of ExhaustiveReplay's downstream closure on
  `oleans-cc011`, against records tip `80882831`. 4 modules replayed: 4 passed, 0 failed, 0
  inherited admissions. There are 874 objects in and 874 out.
- **Seals:** all 17 changed proofs pass with every other-file definition they reach made
  irreducible (21 heads).
- **Controls:** 25 definitions' 50 paired controls close natively and fail when sealed.
- **Proof-syntax sweep:** 17 roots, 0 explicit reads.
- **Lean-backed sweep:** 138 identifiers. The flagged constants are `absurd` and `rfl`, both
  proof terms passed as arguments in `xr_copy_host`, `xr_pass_host` and `xr_passTM_run`. They
  occur there at base the same number of times (4, 5 and 10). These proofs changed only in their
  bank-inequality and buffer-tape citations. Neither
  unfolds a definition, and the sealed check of all three passes.
- **Citation homes** (G147-02 procedure, `defsweep/CITATION-HOMES.json`): the newly cited
  `FinTM.bufferTape_of_neg` and `FinTM.bufferTape_eq` live in `TuringMachine/Simulation`, which is
  in the bundle. `Fin.ne_of_val_ne` is Lean core.
- **Lint:** no change. The only style finding is the pre-existing file-size line (now 3,213
  lines), and the campaign lint has 0 FAIL.
- **Copy screen:** 119 → 105 directed pairs, 22 gone and 8 new.
  - **Gone:** all pairs among the ten `_ne_` lemmas; `xr_bufferTape_eq_none_iff`/`xr_bufferTape_ge`;
    and `xr_replay_finish`/`xr_replay_state`. The `xr_replay_finish`/`xr_replay_timeout` pair
    remains, at 404 instead of 992 reproduced characters: the statements differ only in their
    hypotheses and exit.
  - **New:** 8 pairs among the one-bank update lemmas `xr_tapes_upd_*` and `xr_heads_upd_*`. These
    were already siblings, with 59 directed pairs at base. Their distinct `_ne_` citations became
    the uniform `(by xr_bank_ne)`, so more of them cross the 50% line.
  - Merging those nine lemmas is backlog C1E-1(d)'s optional remainder. Judge whether it should
    be required.
- `evidence/DATA-CARRIER.json` and its recovery map: decode each gzip+base64 blob, then check its
  SHA-256 and byte count.

Use the campaign finding table and give a CLEAR or HOLD verdict.
**Deliver your findings as a downloadable file named `gate151-c1e-1-trims-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content in your
reply.
