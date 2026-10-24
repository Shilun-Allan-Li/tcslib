"""The review's text fixes to u2s-fill-universal.DRAFT.md, each an asserted unique replacement.
Usage: edit_draft.py <file>  (edits in place)"""
import sys
p = sys.argv[1]
t = open(p, encoding="utf-8").read()
E = []
def rep(old, new, tag):
    global t
    n = t.count(old)
    assert n == 1, (tag, n)
    t = t.replace(old, new)
    E.append(tag)

# F1/F2/F3/F11: the issue condition in the HTML comment
rep("""equations under the names `simps` generates beside them (`StepBlock.forwardLoopCfg_state`, …,
`rulerHostCfg_output`); at issue, replace them by the landed names if they differ, and re-run the
pre-ship against the API's head. Other issue-time items: @ANCESTOR@, ⟨BASE⟩, ⟨IN-FLIGHT⟩,
the megafill banner. -->""",
"""equations under the names `simps` generates beside them (`StepBlock.forwardLoopCfg_state`, …,
`rulerHostCfg_output`); at issue, replace them by the landed names if they differ, and re-run the
pre-ship against the API's head. The generated tape equations are pointwise in the cell
(`… .workTapes i a = … i a`), unlike the route probe's stand-ins: re-run the probe with `funext`
before each tape rewrite (the review's API probe does, against the generated lemmas).
**The same API PR also carries** (review F1, F2): `Turing.MultiTapeTM.spaceUsedByTape_eq_card`
beside the definition in the vendored `Deterministic.lean` (U2-U's space ledger has no other
published card step; replay: `Deterministic`'s closure, 325 modules, as #149's) and
`Turing.pairEncode_drop` in `Build/InputDevice` (the suffix after one header; no extra replay).
Other issue-time items: @ANCESTOR@, ⟨BASE⟩, ⟨IN-FLIGHT⟩ (#156's head moved during review; if it
is in the issue base, its two lemmas become citable: add them to the probe), ⟨its PR⟩, the megafill
banner. -->""", "F1-comment")

# F1/F2: the ancestor list's API item
rep("""  - **the field-equation API (Q-U1, ⟨its PR⟩)**: `StepBlock.forwardLoopCfg_state`, `_inputPos`,
    `_workTapes`, `_workTapePos`, `_output` and `rulerHostCfg_state`, `_inputPos`, `_workTapes`,
    `_workTapePos`, `_output`;""",
"""  - **the field-equation API (Q-U1, ⟨its PR⟩)**: `StepBlock.forwardLoopCfg_state`, `_inputPos`,
    `_workTapes`, `_workTapePos`, `_output` and `rulerHostCfg_state`, `_inputPos`, `_workTapes`,
    `_workTapePos`, `_output` (the tape equations pointwise: `… .workTapes i a = … i a`); with
    them `MultiTapeTM.spaceUsedByTape_eq_card` (`Deterministic`: a tape's space is the card of its
    visited set) and `pairEncode_drop` (`Build/InputDevice`: `(pairEncode u x).drop (2|u| + 2) =
    x`);""", "F1-ancestor")

# F5: phase 2's tape layout, and F2's drop, in the phase-2 intro
rep("""**Phase 2, U2-E** (checkpoints 2.1–2.5), on `z := pairEncode α x`, with `ℓ := 2|α| + 2`, the
header's length (`length_pairEncode`, `universal_pair_length`), and `z.drop ℓ = x`.""",
"""**Phase 2, U2-E** (checkpoints 2.1–2.5), on `z := pairEncode α x`, with `ℓ := 2|α| + 2`, the
header's length (`length_pairEncode`, `universal_pair_length`), and `z.drop ℓ = x`
(`pairEncode_drop`; never a `uk_` copy of it). **U2-E's machine has one more tape than the
startup's `K + (k + 2)`, the ruler, last.** Run the startup there by R1 (`embedEmitTM` on the first
`K + (k + 2)` tapes; it is silent), started from `U`'s initial configuration through
`embedEmitCfg_eq` (or `_mapState_eq`); embed `H` by R1 along `σ` with `σ j.castSucc = ⟨j, _⟩` and
`σ (Fin.last _)` the ruler.""", "F5-F2-phase2")

# F4: seamCompTM's initial state, in step 1.1
rep("""1. **The seam into H2-F** (checkpoint 1.1). `U` is the startup `R`, seamed at its `exit`
   (`seamCompTM`) into the embedded `L` (R1 on the first `k + 2` of `R`'s `K + (k + 2)` tapes: tape
   `j` of `L` is tape `⟨j, _⟩` of `R`).""",
"""1. **The seam into H2-F** (checkpoint 1.1). `U` is the startup `R`, seamed at its `exit`
   (`seamCompTM`) into the embedded `L` (R1 on the first `k + 2` of `R`'s `K + (k + 2)` tapes: tape
   `j` of `L` is tape `⟨j, _⟩` of `R`). No published equation states a seam's (or a phase host's)
   initial state: build `U` as `{ seamCompTM R exit _ _ with q₀ := Sum.inl R.q₀ }`, as the startup
   built its own, and read it through `MultiTapeTM.initCfg_with_q₀` and `runFrom_with_q₀`.""",
"F4-step11")

# F1: the space ledger's card step
rep("""3. **The space ledger** (checkpoint 1.3). `U`'s space to `C · (t + 1)` is its space to its halt
   (a halted run is frozen: `MultiTapeTM.runFrom_of_halt`), the startup's at most `B`, plus the
   embedded `L`'s by tape (`spaceUsed_eq_sum`, `seamCompTM_visitedByTapeHead_ofCfg`,
   `embedEmitTM_visitedByTapeHead` and `_frame`): H2-F's ledger puts each mirrored tape's visits
   inside `M`'s (at most `s` in all) and each auxiliary head within
   `50 (|tableBitsK M.tr| + 1) + C_L` of home.""",
"""3. **The space ledger** (checkpoint 1.3). `U`'s space to `C · (t + 1)` is its space to its halt
   (a halted run is frozen: `MultiTapeTM.runFrom_of_halt`), the startup's at most `B`, plus the
   embedded `L`'s by tape (`spaceUsed_eq_sum`, `seamCompTM_visitedByTapeHead_ofCfg`,
   `embedEmitTM_visitedByTapeHead` and `_frame`): H2-F's ledger puts each mirrored tape's visits
   inside `M`'s (at most `s` in all) and each auxiliary head within
   `50 (|tableBitsK M.tr| + 1) + C_L` of home. Every count goes through the API's
   `MultiTapeTM.spaceUsedByTape_eq_card` (`Finset.card_le_card`, `Finset.card_union_le`;
   `MultiTapeTM.visitedByTapeHead_mono` for `t₀ ≤ t`); the auxiliary tapes also by
   `spaceUsedByTape_le_card_Icc`. The seam's card corollaries
   (`seamCompTM_spaceUsedByTape_le_add`, `_le_max`) are stated over `Cfg.ofWords` seams only, and
   the startup's endpoint is not one.""", "F1-step13")

# F8: the converse's L-level lemma, reused by phase 2
rep("""4. **The converse** (checkpoint 1.4). If `U` halts with `output` at some `t'`, `L` halted by then""",
"""4. **The converse** (checkpoint 1.4; state its `L`-level part, and step 2's run of `L` to the
   encoded first halt, as input-generic `uk_` lemmas: phase 2 cites both at `x`). If `U` halts with
   `output` at some `t'`, `L` halted by then""", "F8-step14")

# F7: the leaf's statement form and reading
rep("""   lemma: exact time `ℓ + O(1)`, the ruler `FinTM.bufferTape (List.replicate ℓ true)` from its
   start, every other tape and head unchanged, silent. **`α = []` is allowed** (`ℓ = 2`). Then""",
"""   lemma: exact time `ℓ + O(1)`, the ruler `FinTM.bufferTape (List.replicate ℓ true)` from its
   start, every other tape and head unchanged, silent. State it for one header read from any
   input position `1 + p` with `z.drop p = pairEncode u v`, writing `2|u| + 2` cells from the ruler
   head over blank cells, so that two runs serve the promotion's second consumer (a two-pairing
   header); U2-E is `p = 0`. Read the cells through `inputSymbolInner` and the suffix
   (`List.getElem_drop`, `pairEncode_eq`), not by index lemmas: `UniversalStartup`'s private
   `universal_pair_get`, `universal_pair_separator` and `universalPrefix_bits` read the same cells.
   Each step writes `true` and moves both heads right: `step_of_tapeAction_write` (the probe lists
   only the non-writing `step_of_tapeAction_move`), `moveInputPos_pos_of_ne_right`.
   **`α = []` is allowed** (`ℓ = 2`). Then""", "F7-leaf")

# F6: gate 60's carry
rep("""- **Gate 60** (H5's landing) and its resolutions' C60-1/C60-2: the ruler host's exits are return
  points; cite `exists_rulerHostTM` as stated.""",
"""- **Gate 60** (H5's landing), its resolution C60-1, carried: the ruler **device**'s exits
  (`exists_rulerDeviceTM`) are return points, not stationary anchors: consume each at its first
  occurrence (a seam or a phase-host redirect), never cite its configuration after the return time,
  and escalate if a stationary exit is needed. In `exists_rulerHostTM` the ruler's space clause is
  an upper bound (`⊆ Finset.Icc (rp - 1) (rp + ℓ)`) and `inj` is a state map, not an injection.
  Cite `exists_rulerHostTM` as stated.""", "F6-gate60")

# F8: rule 4
rep("""   it**. Phase 2 does not depend on phase 1's ledgers or converse, only on its seam (1.1).""",
"""   it**. Phase 2 depends on phase 1's seam (1.1) and on the two `L`-level lemmas of 1.2 and 1.4
   (`L`'s run to the encoded first halt, its divergence when `M` diverges), not on U2-U's ledgers.""",
"F8-rule4")

# F1/F4: rule 10's reading list
rep("""      through its fields and `runFrom`/`cut`/`locate`; the startup through its statement;
      `MultiTapeTM.spaceUsed` through `spaceUsed_eq_sum` (never by its definition).""",
"""      through its fields and `runFrom`/`cut`/`locate`; the startup through its statement;
      `MultiTapeTM.spaceUsed` through `spaceUsed_eq_sum` and `spaceUsedByTape` through
      `spaceUsedByTape_eq_card` (never by their definitions); a machine's initial state through
      the `with q₀` override's two equations; `pairEncode` through `pairEncode_eq`.""", "F1-rule10")

# F9: the seal list
rep("""        every other-file TCSlib definition your proofs mention (start from the pre-ship's 8 and
        extend: at least `Lockstep`'s consumers' definitions you reach, `seamCompTM`,
        `embedEmitTM`, `MultiTapeTM.runFrom`, `MultiTapeTM.spaceUsed`, `rewindTM`), and""",
"""        every other-file TCSlib definition your proofs mention (start from the pre-ship's 8 and
        extend: at least `seamCompTM`, `embedEmitTM`, `embedEmitCfg`, `Cfg.mapState`,
        `MultiTapeTM.runFrom`, `MultiTapeTM.spaceUsed`, `MultiTapeTM.spaceUsedByTape`,
        `MultiTapeTM.visitedByTapeHead`, `FinTM.ComputesInTime`, `pairEncode`, `rewindTM`,
        `Cfg.inputSymbol`), and""", "F9-seal")

# F2/F7: known hazards
rep("""- **Known hazards:** H2-F's and H5's private proofs (`fl_*`, `rd_*`: cite their contracts);""",
"""- **Known hazards:** H2-F's and H5's private proofs (`fl_*`, `rd_*`: cite their contracts); the
  header's cells and its suffix: `UniversalStartup`'s `universal_pair_get`,
  `universal_pair_separator`, `universalPrefix_bits` (the prefix parser reads the same pairs),
  `NDCodeSimulator`'s `ic_input_suffix` and the drop inside `pairEncode_pairEncode_drop` (cite
  `pairEncode_drop`);""", "F7-hazards")

# F10: the input-rewind lesson
rep("""- **Leaves you may write: one, phase 2's header-ruler scan** (below), with a docstring saying no
  public row writes a ruler of the header's length. It is a leaf (a finite-state scan), not a
  host. Any further leaf is an escalation.""",
"""- **Leaves you may write: one, phase 2's header-ruler scan** (below), with a docstring saying no
  public row writes a ruler of the header's length. It is a leaf (a finite-state scan), not a
  host. Any further leaf is an escalation.
- **No input rewind is needed** (the scan ends where the host starts). If your route needs one,
  cite `Turing.inputRewindTM` (`Build/InputRewind`, in your closure); never write one.""", "F10-rewind")

# F13 (note): the checklist's Implementation paragraph
rep("""- [ ] Promotion candidates and escalations (each stated mathematically), or "none".""",
"""- [ ] Promotion candidates and escalations (each stated mathematically), or "none"; for each
      proved target whose construction departs from its frozen sketch (U2-E: the startup first,
      then the scan), a proposed `**Implementation.**` paragraph for the maintainer.""", "F13-checklist")

# F3: pitfall wording
rep("""- **The simps field equations are pointwise** (`Cfg.init_workTapes`, `Cfg.mapState_*`,
  `embedEmitCfg_*`, and the API's): `funext` before `rw`, or the step closes by unfolding and the
  seal rejects it (the route probe needed it at `Cfg.init_workTapes`).""",
"""- **The simps field equations are pointwise** (`Cfg.init_workTapes`, `Cfg.mapState_*`,
  `embedEmitCfg_*`, and the API's tape equations, which take the cell: `… .workTapes i a`):
  `funext` before `rw`, or the step closes by unfolding and the seal rejects it (the route probe
  needed it at `Cfg.init_workTapes`). `rulerHostCfg_inputPos` is a `Fin.mk`: compare by
  `Fin.ext`.
- **A seam's initial state has no equation**: the `with q₀ := Sum.inl R.q₀` override and
  `MultiTapeTM.initCfg_with_q₀`/`runFrom_with_q₀`, as the startup's own `R`.""", "F3-F4-pitfall")

open(p, "w", encoding="utf-8").write(t)
print("applied:", ", ".join(E))
for i, l in enumerate(t.split("\n"), 1):
    if len(l) > 100 and not l.startswith("#"):
        print("OVER 100:", i, len(l))
