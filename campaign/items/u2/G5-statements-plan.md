# G5's statement phase: the plan (maintainer, 2026-11-04)

**What G5 is.** Hennie–Stearns `k → 2` for binary machines, per run and with the converse. It is
the input to Theorem 1.9 at `T log T` and to the `f log f` time hierarchy (book-form Theorem 3.1),
through `Diagonal.lean`'s parameterization (U2 design §1, §3.2, §4.2). The U2 probe
(`probes/U2DiagParam.lean.txt`) drafted the statements, and its axiom prints show that the chain to
the book-strength theorems is proved except for G5 and U2-E. The statement phase lands G5's
interface by PR and statement gate (§13d's process rule). The fill then proves it over G2–G4's
contracts.

## 1. The statements

| Statement | Form | Status in the PR |
|---|---|---|
| `Turing.FinTM.two_work_tapes_run (M : FinTM Bool)` | `∃ M' c, M'.k = 2 ∧ (∀ x o t, M.ComputesInTime x o t → M'.ComputesInTime x o (c · (t + 1)(log₂(t + 1) + 1))) ∧ ∀ x o, (∃ t, M'.ComputesInTime x o t) → ∃ t, M.ComputesInTime x o t` (the probe's, verbatim) | **sorried**, G5's fill |
| `Turing.FinTM.two_work_tapes_binary M f T hM` | the function-level form, `one_work_tape_binary`'s mirror | proved from the above (2 lines, the probe's) |
| `Turing.FinTM.alphabet_reduction_run e M` | the per-run export of `alphabet_reduction`: `∃ c M', M'.k = M.k ∧ (∀ x w t, M.ComputesInTime (x.map e) (w.map e) t → M'.ComputesInTime x w (c · t)) ∧ ∀ x w, (∃ t, M'.ComputesInTime x w t) → ∃ t o, M.ComputesInTime (x.map e) o t ∧ ∀ v, o = v.map e → v = w` | **proved**, from the private `arTM_computes` and `arCfg_run` (20–40 lines, ESTIMATE) |
| `Turing.universal_TlogT (c : EffectiveMachineCode2)` | Theorem 1.9 at `T log T`, per run with the converse (the probe's) | proved from `two_work_tapes_run` and U2-U/E (`universalK 2`) |

**The converse's form (D2).** `arTM`'s output is the source's output under a private total bit
decoder (`arBit`). A completed output of `M'` therefore determines the source's output only up to
that decoder. The public form says: the source halted with some output `o`, and if `o` is an image
`v.map e` then `v = w`. G5's fill meets this, because the Hennie–Stearns machine of a binary `M`
writes only images of bits.

## 2. Gate 22's carried minors

1. **`run_cost_le` at `k = 0`.** The fit probe's rebalance budget cannot absorb a fixed per-step
   cost at `k = 0`. `two_work_tapes_run` is stated for every `M`, `k = 0` included. The fill
   treats `k = 0` separately: pad with two idle tapes, a lockstep embedding, as `one_work_tape`'s
   zero-tape branch does. Recorded in the statement's docstring and in the fill's brief.
2. **`trackStep_fit`'s interface.** It omits `Fintype S` and the endpoint equalities for
   `inputPos`, `output` and the scratch head. The fill builds the stronger interface from G4's
   endpoint theorems, and the fill's brief pins it.

## 3. Homes (D1)

- **`two_work_tapes_run` and `two_work_tapes_binary`:** a new `TuringMachine/Robustness/TwoTapes.lean`,
  beside `SingleTape.lean` (`one_work_tape_binary`). It imports `AlphabetReduction` and G2–G4's
  `Build/Zone*` contracts.
- **`alphabet_reduction_run`:** in `Robustness/AlphabetReduction.lean`, beside `alphabet_reduction`.
  It is ours, and additive.
- **`universal_TlogT`** (U2 design Q12): either in `TwoTapes` or in a small sibling, say
  `TuringMachine/UniversalTlogT.lean`. The sibling is recommended: the `Robustness` layer does not
  import `UniversalK`, and only the assembly needs both.

## 4. The work

1. A PR with the four statements (≈ 120–200 lines) and the docstrings' sketches. Its statement gate
   (gate 92) covers:
   - freeze;
   - elaboration;
   - axiom prints: `sorryAx` only through `two_work_tapes_run` and U2-E;
   - the converse's adequacy for `universal_TlogT`;
   - lint, screen and the name search.
2. G5's fill brief, after the gate: Hennie–Stearns over G2–G4, the two minors pinned, `k = 0`
   separate. ESTIMATE: 1.0–2.0k lines, Codex first (the soft rule).
3. After the fill: Diagonal Part 1's `f log f` layer, U2 design §6 item 7, one PR and gate, under
   the 2026-10-14 authorization.

## 5. Status (2026-11-04)

**Drafted on `lean/g5-statements`** at `6bd12e68` (local, on the campaign at `e66b714e`, Lean `711f5444`):
- `alphabet_reduction_run`, proved (about 25 lines, from `arCfg_init`, `arCfg_run`, `arTM_computes`
  and `arBit_embed`; the converse uses the halted run's stationarity);
- **added to the plan: `Turing.exists_code2TM`** in `Codes2Tape`, the two-tape counterpart of
  `exists_codeTM`, which `universal_TlogT` needs and the probe had proposed there. It is proved
  through `FinTM.computesInTime_iff` and `relabelState_runFrom_init` rather than the probe's
  unfolding of `ComputesInTime`;
- `TwoTapes.lean`: `two_work_tapes_run` (sorried) and `two_work_tapes_binary`;
- `UniversalTlogT.lean`: `universal_TlogT`, via `universalK 2 c.toK`. `universalK` is now
  admission-free, so `sorryAx` reaches `universal_TlogT` only through `two_work_tapes_run`;
- the facade imports both new modules.

**Checks (`$S/g5ps/`):**
- **chain:** 39 modules from a clone of `oleans-leqc3`, all exit 0; `TwoTapes`' one `sorry`;
- **axioms:** `alphabet_reduction_run` and `exists_code2TM` standard; `two_work_tapes_*` and
  `universal_TlogT` add `sorryAx`; `universalK` is standard;
- **rule 10 sealed:** 3 copies, 13 definitions, 0 diagnostics; controls 26/26 unsealed, 0/26
  sealed;
- **lint:** `style_lint` 0 findings on the new files, and the base's on the edited ones; campaign
  lint 0 FAIL / 71 WARN at base and head;
- **names:** none on 514 refs.

**Cost:** `AlphabetReduction` sits below `Encoding` (through `SingleTape`), so its downstream is
325 of 922 modules, against 5 for `Codes2Tape`. The PR's replay is that closure. Moving the theorem
elsewhere is not possible: it needs the file's private run lemmas.

**Next:** the screen; the PR and gate 92's pack; the replay, after #181 merges, from `oleans-lsm5`.

## 6. The fill's pre-ship, started (2026-11-05, overnight)

- **The zone layer is complete.** `Build/Zone`, `Build/ZoneTape` and `Build/ZoneRebalance` have no
  `sorry`; the rows `exists_zoneRebalanceTM` and `exists_zoneExtendTM` are proved.
- **The consumer fit still holds on the landed rows.** Gate 22's fit section
  (`s13d/g24/landing/parts/fit.tail`: `trackStep_fit`, `amortized_le`, `run_cost_le`), on top of
  the landed `ZoneRebalance`, `ZoneTape` and `Contract/Seam`, elaborates with 0 diagnostics
  against `oleans-lcf3`, the campaign after #190 (`probes/G5FitLanded.lean.txt`, `.out`). The
  statement-phase probe as a whole no longer elaborates, because it restates the layer that has
  since landed.

**Decision G5-F1 (the user's, before the brief):**
- **API first** (as for NF's host and the deepening). The maintainer publishes the consumer side
  by PR and gate, beside the rows (`Build/ZoneRebalance` or a small `Build/ZoneStep`):
  - `trackStep_fit`, strengthened per gate 22's minor 2 (`Fintype S`, and the endpoint
    equalities for `inputPos`, `output` and the scratch head);
  - `amortized_le`;
  - `run_cost_le` with a fixed per-step overhead (minor 1).

  The fill then writes the controller, the invariant and the count bound.
- **Or all in the fill:** it proves these as privates of `Robustness/TwoTapes`, citing the rows.

The recommendation is API first. It fixes the interface under rule 10 before the fill starts,
and the three are statements another consumer (a later `k → 1` or `k → 2` variant) would reuse.
Size: about 300–400 lines (ESTIMATE), and the replay is `ZoneRebalance`'s downstream.

## 7. Decision G5-F1 ruled: API first (the user, 2026-11-05)

The consumer side is published by PR `lean/zone-step-api` and gate 97
(`campaign/gates/97-zone-step-api/`):
- **`Build/ZoneStep` (new):**
  - `exists_zoneTrackStepTM`, one track's step. It meets gate 22's minor 2 (`Fintype S`, and the
    endpoint's scratch head, input head and output), has one constant for every direction and
    track, and has live exits (`none ∉ X`) for the phase host;
  - `sum_two_pow_le_of_count`, the layer cake, through Mathlib's geometric sums;
  - `sum_cost_le_of_count`, with the fixed overhead `B` of minor 1, sound at `k = 0`;
  - `zoneTrackStepData`.
- **`Build/ZoneRebalance`:**
  - `zoneRowPre_iff`, `zoneRebalanceIndex_eq` and `zoneRebalanceIndex_le`;
  - the data maps' and endpoints' fields (`simps`).
- **`Build/Contract/Basic`:** `Contract.zero`, the zero-time contract.
  - The screen paired the step's private stop contract with `ZoneRebalance`'s private anchor
    (99%), so both now use `Contract.zero` (homes first).

G5's fill then writes the controller, its invariant and the count bound, citing these. Its brief
follows the merge.

## 8. The fill brief's decisions (the user, 2026-11-05)

The brief's first draft (`campaign/fills/u2s/drafts/u2s-fill-g5.DRAFT.md`, drafted by a sub-agent of
the cloud maintainer session and reviewed by the maintainer) raised three questions, ruled:
- **The iteration: API first.** The controller chains one segment per simulated step, from a
  different control state each time (`zoneRowPre` fixes both tapes, so the simulated state is in
  the finite control). `Round.iterate_seq` iterates rounds back to one anchor only, and no lemma
  composed a sequence of segments with varying endpoints. A maintainer PR and gate add
  `Turing.Segment.iterate_seq` to `Build/Contract/Basic` (a sequence of segments composes into one
  segment over the summed time), with `Round.iterate_seq` re-proved from it, before the brief
  issues.
- **`k = 0`: separate, via R1.** As §2 and the frozen sketch say: the zero-tape case goes through
  R1's published `embedEmitTM` (with its `q₀` override), not a copy of `SingleTape`'s private
  idle-tape family; the zone route assumes `0 < k`.
- **The agent: Claude** (the user's choice, over the soft rule's Codex-first).

The controller itself stays the fill's (decision G5-F1).
