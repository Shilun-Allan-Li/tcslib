# Gate 154 round 2 · Closeout stage 2: fills A, B and C (PR #350)

**Not yet clear to merge** · PR #350 is a draft. Seyoon dispatches and merges.

- Lean head: `375531b6055178ec846435b7670be5d0e2a526fe` (branch `closeout/stage2`).
- Base: campaign Lean `5c153802` (the #349 merge), as in round 1.
- Round 1 audited `f2d1ead707d9ba12779dd0b377daba708bac8915` and returned HOLD: one major
  (G154-01) and one minor (G154-02), plus four notes (`findings.md`, verbatim). This round checks
  their resolutions (`resolutions.md`) on a fresh replay and fresh checks of the repaired head.
  `pack.md` and `evidence/` are round 1's, unchanged. This round's evidence is in `r2-evidence/`.

## What changed since round 1

- **Lean: one commit, `375531b6`, one file.** In SingleTape's `dgWindow_step`, the five
  `simp only [..., SignType.cast]` calls now use Mathlib's published sign equations:
  `SignType.neg_eq_neg_one`, `zero_eq_zero`, `pos_eq_one`, `coe_neg`, `coe_one` and `coe_zero`.
  CfgRecord's `InWindow.apply_iff` uses the same equations. The change is +10/−5, and its patch is
  `patch/round1-to-head.patch` in the carrier. Statements, names, imports and the API are
  unchanged since round 1.
- **Records:**
  - `duplication-ledger.md` (RN-1 at closeout stage 2) counts `universalCapture_embed` as an RN-1
    member, and `CARRIED-REGISTER.md` carries it. The copy screen's disposition of that pair is now
    `carried-duplicate` (G154-02).
  - `campaign/maintainer/WORKFLOW.md` §4 now requires every flag of the Lean-backed sweep to be
    dispositioned, Core and Mathlib included.

Net change against campaign Lean: **−172 Lean lines** (+346/−518) across the same 17 files. By file:
UniversalK −138, CodeSimulator −46, Codec/Step −24, ExhaustiveReplay −13, ExpBFS/Radius −13,
Constructible −12, Oracle −10, NDNormalForm −8, Sweep −3, TQBF 0, Build/Loop 0, SingleTape +4,
CfgRecord +10, CfgFacts +14, UniversalStartup +17, Nondeterministic +25, Seam +25.

## Brief for the auditor

1. **G154-01.** Check that `dgWindow_step` passes no Core or Mathlib definition to `simp`, `rw`
   or `unfold`, and that the six equations are published lemmas at the pinned Mathlib revision.
2. **Every sweep flag** (below and `r2-evidence/DEFSWEEP-SUMMARY-r2.json`). Check each
   disposition against the tactic text.
3. **G154-02.** Check the RN-1 entries in the ledger and the carried register, and the
   `carried-duplicate` disposition in `r2-evidence/PAIR-DISPOSITIONS-r2.json`.
4. **Evidence.** Check the replay, seals, controls and copy screen on the new head. Round 1's
   notes G154-03 to G154-06 covered statements and behavior. Only SingleTape's one proof changed
   since round 1.

## Evidence (`r2-evidence/`)

- `REPLAY-r2.json`: a fresh merged-tree replay of the 17 owners' downstream closure on
  `oleans-c5c153`, with **353 of 353 modules passed** and 0 failed. There are 28 inherited
  admissions (pre-existing), and 874 objects in and 874 out.
- **Seals:** all 33 changed or added proofs pass with every other-file definition they reach made
  irreducible: 17 owners and 86 ordinary boundary heads.
- **Controls:** two disjoint parts of 43 heads and 86 paired identities each, both passing, for a
  **total of 86 sealed definitions and 172 paired identities**. Each identity passes natively and
  fails sealed.
- **Proof-syntax sweep:** 33 roots and 1 read candidate, as in round 1. The candidate is
  `unfold step` in `OracleTM.workTapes_step_eq_of_ne`. It resolves to `MultiTapeTM.step` and
  reaches Oracle's own `OracleTM.step` (same file), and the sealed check passes.
- **Lean-backed sweep, all flags dispositioned.** It collects 534 identifiers (SingleTape's
  identifiers go from 28 to 33). `SignType.cast` is no longer flagged, and no file flags a
  definition used as a rewrite rule.

  | File | Flag | Where it occurs | Disposition |
  |---|---|---|---|
  | Codec/Step | `reduceIte` | `simp` set | simproc, not a definition |
  | CfgRecord | `Int.reduceNeg`, `reduceCtorEq` | `simp` set | simprocs |
  | ExhaustiveReplay | `rfl` | `xr_phase_step … rfl rfl` inside a `rw` argument | proof term |
  | UniversalK | `rfl` | `ss_live_map … rfl` inside a `rw` argument | proof term |
  | CodeSimulator | `rfl` | `if_pos rfl`, `if_pos ⟨rfl, …⟩` | proof term |
  | CodeSimulator | `Bool.noConfusion`, `Sum.noConfusion` | `if_neg (fun h => ….noConfusion …)` | proof term |
  | CodeSimulator | `Turing.embedEmitTM` | machine argument, e.g. `seamReleaseTM_runFrom_pos (embedEmitTM ι₃ P) …`, in `canonStageFrontSpec` and `exists_canonGrammarStage`, on lines unchanged from base | term argument, not a rewrite rule |
  | Nondeterministic | `Nat.find` | `List.take_append_drop (Nat.find hex) w` | term argument |

  SingleTape's two older `SignType.cast` uses (lines 193 and 1217) are in proofs this PR does not
  change.
- **Citation homes:** `CITATION-HOMES-r2.json` lists the same eight bundled files as round 1.
  Their scope-pass results (`Cite_*` exits) are unchanged from round 1.
- **Copy screen:** 376 → 366 directed pairs, 12 new and 22 gone, the same pair list as round 1.
  The only disposition change is `universalCapture_embed` → `Cfg.mapState_eq_of_fields`, now
  `carried-duplicate` (RN-1).
- **Carrier:** `DATA-CARRIER-r2.json` and its recovery map, with 1,339 logical files. They
  include `patch/campaign-to-head.patch`, `patch/round1-to-head.patch`, and the logs of the
  seals, controls, sweeps and screen. To check it, decode each gzip+base64 blob, then check its
  SHA-256 and byte count.

Use the campaign finding table and give a CLEAR or HOLD verdict.
**Deliver your findings as a downloadable file named `gate154-stage2-fills-r2-findings.md`**
(the findings table and the verdict line, no other wrapping), and also paste its content in your
reply.
