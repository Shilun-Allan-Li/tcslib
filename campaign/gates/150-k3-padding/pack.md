# Gate 150 · Closeout R4 kind 3: padding through `Build/EmitIterEmbed` (PR #343)

**Not yet clear to merge** · PR #343 is a draft. Seyoon dispatches and merges.

- Lean head: `0b12a1b30ad0fb8b800b67beb806766e6f266b86`.
- Base: campaign Lean `c01114e7` (the #342 merge); records `70adbe56`.
- This is the first audit.
- The head descends from #342's head `a12da4d3` (the merge base). The PR diff against the campaign
  branch is exactly the four owners below.

## Scope

This is wave R4, SG1 kind 3: the padding layer. The rulings are in
`campaign/closeout/REFACTOR-PLAN.md` and the design study is in
`campaign/closeout/r4-design-request/delivery/`; both are bundled.

SAT and Cook–Levin hardness each carried a private copy of the same padding layer. It lets a
module with `m` work tapes run inside a host with `K ≥ m` tapes, keeping the extra tapes blank
and their heads at the origin. The layer has these parts:

- a padded action (`satPadAction`);
- a padded machine (`satPadTM`);
- a padded configuration (`satPadCfg`);
- the apply, run and seam lemmas.

On 2026-11-16 Seyoon ruled that kind 3 cites the public padding layer of `Build/EmitIterEmbed`
(`padAction`, `embedCfg`, `embed_step`, `embedCfg_ofWords`), and that SAT may import it.

That layer, and the forwarding configuration `emitCfg` of `Build/Wrappers` (used by the hosts),
publish no equations that read back their configurations' fields. Without them, the rewritten
host proofs would have to unfold another file's definitions, which rule 10 forbids. The maintainer
prototyped the rewrite and reported the measured cost and benefit. Seyoon then approved doing it
as one PR on 2026-11-16: the field equations and the rewrite together.

### New public API (approved 2026-11-16)

| File | Addition | Form |
|---|---|---|
| `Build/EmitIterEmbed` | `Turing.embedCfg_state`, `_inputPos`, `_workTapes`, `_workTapePos` | `attribute [simps (config := { isSimp := false }) state inputPos workTapes workTapePos] embedCfg` |
| `Build/EmitIterEmbed` | `Turing.embedCfg_output_eq` | theorem, `rfl` (the name `embedCfg_output` is already taken by the record-update lemma) |
| `Build/Wrappers` | `Turing.emitCfg_state`, `_inputPos`, `_workTapes`, `_workTapePos`, `_output` | `attribute [simps (config := { isSimp := false })] emitCfg` |

The pattern is the one in `Build/CounterLoop` (`counterLoopBody`) and `Build/Embed`
(`embedSilentCfg`/`embedEmitCfg`): the equations are generated without the `simp` attribute.
`_workTapes` and `_workTapePos` are stated pointwise. Both module docstrings list the new
equations. Neither file's existing declarations change.

### Owners

- **`ClassNP/SAT`** and **`CookLevin/Hardness`**, symmetric changes:
  - **Deleted:** `satPadAction`, `satPadCfg`, `satPad_apply` and `satPad_seam`, with their
    `clA5` twins.
  - **`satPadTM`**: the transition is `padAction hk (Option.map id)` of the source transition on
    `Fin.castLE hk`-read work symbols.
  - **`satPad_run`** (restated): `(satPadTM M K hk).tm.runFrom (embedCfg hk id c) t =
    embedCfg hk id (M.tm.runFrom c t)`. A live configuration steps through `Turing.embed_step`;
    a halted one stays put (`MultiTapeTM.step_of_halt`).
  - **New private `satPad_words`:** with `0 < k`, `embedCfg_ofWords`' padded assignment of
    `stateWord k w` is `stateWord K w`.
  - **`satHost_seam`** (now takes `hk`) and **`satHost_call`**: they read `emitCfg` and `embedCfg`
    through the new equations and `Cfg.ofWords_*`, and no longer unfold them. At base they unfolded
    both by `rfl` and `simp [emitCfg, …]`, as legacy reads in unchanged proofs.
  - `clA5Host_clean` and the other consumers are unchanged.
- **New import:** SAT imports `Build/EmitIterEmbed`. Hardness already reaches it through SAT.
- **`Build/EmitIterEmbed`** and **`Build/Wrappers`**: the API above.

The public statements of SAT, Hardness, EmitIterEmbed and Wrappers are otherwise unchanged. The
private `header_changed` entries are `satPadTM`, `satPad_run`, `satHost_seam` and their `clA5`
twins. Net: **+6 Lean lines** (+140/−134). The first head measured −2; the seal repair (History)
adds 8.

## Brief for the auditor

1. **API.** Check that the ten field equations state exactly the fields of `embedCfg` and
   `emitCfg`, carry no `simp` attribute, and that `embedCfg_output_eq` is correct and named
   without a clash. Check that the docstrings mention them, with no campaign labels.
2. **Statements.** Confirm that every public statement in the four owners is byte-identical to
   base, apart from the new equations.
3. **Padding.** Check that `satPadTM`'s padded transition is the old `satPadAction` behaviour,
   with tapes beyond `m` stationary and blank, and that `satPad_run`/`satHost_seam`/`satHost_call`
   still give the hosts' consumers what they need.
4. **Deadness.** Check that each deleted declaration was referenced at base only from the deleted
   set or from a restated site.
5. **Rule 10.** The changed proofs: seals, controls and both sweeps (counts below). The restated
   host proofs must read `emitCfg`, `embedCfg` and `Cfg.ofWords` only through published
   equations.
6. **Copy screen** (population: the four owners): see `evidence/PAIR-DISPOSITIONS.json` and the
   note under Evidence.

**History.** At the first head, `79580ea8`, the replay passed (227/227), but the sealed check
failed in `satHost_call` and `clA5Host_call`. Their start seam (`hinit`) identified
`{Cfg.ofWords q₀ (stateWord k arg) with state := some q₀, output := []}` with
`Cfg.ofWords q₀ (stateWord k arg)` by letting `simpa` unfold `Cfg.ofWords`. The base proof did the
same as an unexposed legacy read. The head `0b12a1b3` proves that equation from the published
`Cfg.ofWords_state` and `Cfg.ofWords_output`, rewrites with it, and then runs the same `simpa`
(`patch/head1-to-head2.patch`). Every check below was rerun at `0b12a1b3`. The failing seal lines
and the first head's results are in the carrier (`history/head1-79580ea8/`), and the copy screen
delta is identical.

## Evidence

- `evidence/REPLAY.json`: the merged-tree replay of the four owners' downstream closure on
  `oleans-cc011` (the #342 merge's snapshot), against records tip `70adbe56`.
  - 227 modules replayed: 227 passed, 0 failed.
  - The 28 inherited admissions are pre-existing, outside this PR, and the same 28 that the
    `oleans-c56ab` adoption replay recorded: MaxCutAlgorithm 2, UniqueGames 8, RecordTable 4,
    WordSize 3, Simulation 2 and Classes 9 (`replay/module-results.json`).
  - There are 874 objects in and 874 out.
  - The driver gained one fix: the gate 149 `added_owners` check no longer runs when no owner is
    new (`drivers/driver/driver.py`).
- **Seals:** all 9 changed proofs pass with every other-file definition they reach made irreducible
  (10 heads): 4 in SAT, 4 in Hardness and `embedCfg_output_eq`.
- **Controls:** 17 definitions' 34 paired controls close natively and fail when sealed.
- **Proof-syntax sweep:** 9 roots, 0 explicit reads.
- **Lean-backed sweep:** 122 identifiers. The only flagged constant is `rfl`, a term argument
  inside a rewrite rule: `rw [emit_run … (by intros; rfl) …]` in `satHost_call`/`clA5Host_call`,
  as at base. It closes the host-agreement hypothesis by the same-file `satHostTM`.
- **Citation homes** (G147-02 procedure, `defsweep/CITATION-HOMES.json`): the newly cited
  other-file lemmas live in `Build/Convention` (`Cfg.ofWords_*`), `Build/Loop` (`stateWord_eq`),
  `Configuration` (`Cfg`), `Deterministic` (`MultiTapeTM.step_of_halt`) and `Simulation`
  (`FinTM.bufferTape_nil`). The other citations (`padAction`, `embedCfg`, `embed_step`,
  `embedCfg_ofWords` and the new equations) are in the owners. All are in the bundle.
  - The `#kinds` scope pass for `Build/EmitIterEmbed` reports a namespace-opening error in one of
    its scope blocks. Its one changed declaration, `embedCfg_output_eq`, cites only its own file.
- **Lint:** no new style finding, and 0 campaign FAIL.
  - The campaign lint's informational WARN lines for EmitIterEmbed and Wrappers shrink:
    `embedCfg` and `emitCfg` no longer appear in "structure-valued def(s) without field
    equations" or "public def(s) without a lemma beside them".
  - The normalized delta lists the reworded lines as new and removed.
- **Copy screen** (population: the four owners): 242 → 237 directed pairs, 8 gone and 3 new.
  - The 8 gone are the four padding twins: `satPadAction`, `satPadCfg`, `satPad_apply` and
    `satPad_seam`, against their `clA5` counterparts.
  - New: `satPad_words`/`clA5Pad_words` (both directions). This is a 9-line private twin replacing
    the 12-line `satPad_seam` twin. Both hosts stay private, because kind 6, the dispatcher, is
    carried.
  - New: `EmitIterEmbed.embedCfg` reproducing `Wrappers.captureCfg` at 54%. This is a screen
    artifact: the new `simps` line and its comment, which list the field names, attach to
    `embedCfg`'s text chunk. `embedCfg`'s definition is unchanged.
- `evidence/DATA-CARRIER.json` and its recovery map: decode each gzip+base64 blob, then check its
  SHA-256 and byte count.

Use the campaign finding table and give a CLEAR or HOLD verdict.
**Deliver your findings as a downloadable file named `gate150-k3-padding-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content in your
reply.
