# §13d G2–G4 statement gate: resolutions (round 1; gate CLOSED)

**Gate:** G2's mapped sweeps, the restructure (plain rows as the mapped rows at the identity map,
and the shared `sweepContract`), G3's zoned-tape carrier, G4's pure rebalance layer, and G4's
rebalance and extension rows (`audits/s13d-g24-statements-pack.md`; bundle SHA-256
`3154dc39b1c5493e9c0b4d97ba272d5bbdc1d4375afaa71e4343276a0e2dca1f`, 106 sections, dispatch folder
22).

**Round 1** (`audits/s13d-g24-statements-findings.md`, verbatim): **PASS, 0 blockers, 0 majors, 5
minors. The gate closes.**
- **The six sorried statements:** each is true and nonvacuous. The G4 rows are adequate for G5.
- **The restructure:** no public statement or admitted-axiom regression. The auditor
  independently matched all 92 public Catalog axiom sets.
- **Duplication:** both duplication families the user chose to remove are gone. The 24 new
  sibling pairs are accepted, with no debt acknowledgment needed.
- **The source:** fidelity to [AB09] §1.7 is checked.

## Findings

| # | Severity | Finding | Resolution |
|---|---|---|---|
| 1 | minor | The fit probe's `run_cost_le` step budget cannot absorb a fixed per-step controller cost at `k = 0` | **Carried to G5's statement phase.** The lemma covers the rebalance phase only. G5 either treats zero-work-tape machines separately, or carries a fixed overhead (`B + A·Σ(2^idx+1) + k`, with `B·T` in the conclusion); `0 < k` is never assumed silently. The design note's §5(e) is annotated at landing |
| 2 | minor | `trackStep_fit` omits `Fintype S` and the endpoint equalities for `inputPos`, `output` and the scratch-head position | **Carried to G5's statement phase.** The probe's advertised role is restricted to chaining the zoned representation and bounding time. G5 constructs and exposes the stronger interface from the G4 contracts, which retain those facts. The probe is evidence and does not land |
| 3 | minor | `copyMapTM`/`transferMapTM`'s prose omits the `src ≠ dst` side condition; `sweepPost` says "both heads" | **Fixed at landing:** the behavioral descriptions are qualified by `src ≠ dst`, and the text says "all work heads". No theorem or table changes |
| 4 | minor | `exists_zoneRebalanceTM` and `exists_zoneExtendTM` use the label `**Proof sketch** (fill plan…)` | **Fixed at landing:** `**Proof sketch.**`, with the fill-plan text kept after it |
| 5 | minor | The pack's duplication accounting: `zonedTape_left_word`'s body is 724 characters (the overlap is 285), and the table overlaps changed slightly (369/344/478) | **Corrected here:** the body size and the reproduced text are distinct measures, and the table pairs are the same sibling family with slightly changed counts. The totals and dispositions stand |

## Rulings on questions 1–9 (adopted)

All nine as the pack proposed:
1. G2's home is `Build/Catalog.lean`.
2. `short`, then extend and retry.
3. Pure Zone keeps exactly two Mathlib imports.
4. Inner packing.
5. Existential G4 rows now, named machines at fill.
6. The slot/index family stays until the Zone split.
7. One trace family at the G2 fill. The plain framed rows derive from the proved mapped rows, and
   proved plain theorems are never retargeted to admitted mapped results meanwhile.
8. The time-implied scratch envelope.
9. All three Zone documentation fixes.

## Obligations carried

1. **Order:** MIG-1 stage S lands first. This gate's landing PR then rebases on S, regenerates the
   landed files, and re-runs the landed-Catalog check, the Catalog chain, the freeze and the
   complete public axiom inventory at the actual tip (including S's new public declarations).
   Then the downstream replay.
2. **G2's fill only after S.** Then the cascade-home lemma and the G4 witnesses, the fill gate, and
   G5's own statement gate.
3. **Hosts first for G4's fill:** before its fill brief, identify the public host for the two-tape
   layout (scratch and ruler layout), or gate a missing reusable host. A tape-adding counter loop
   cannot stand in for a two-tape witness.
4. **F-D** (MIG-1) must not unfold the copy or transfer tables by name.
