# External audit pack — B3a fill gate: logarithmic and linear space constructibility (2 targets)

Campaign: Arora-Barak chapters 3-4 (`AroraBarakChapters3-4Plan.md` §4e, cluster B3).
`SpaceComplexity/Constructible.lean` states [AB09, §4.1, p. 79]'s space constructibility,
`SpaceConstructible S`: some machine computes `S(|x|)` in `O(S(|x|))` space, with the
domination and no-premature-halt conditions of its docstring. Its statements were gated at
**P4.1**, which closed at round 1 (`audits/ch4-p41-findings.md`, resolutions
`audits/ch4-p41-resolutions.md`); P4.1's minors 1–2 bind the fill. **This gate covers B3a, the
two constructibility statements**:

| File | Target | Statement |
|---|---|---|
| `SpaceComplexity/Constructible.lean` | `Complexity.spaceConstructible_logSpace` | `SpaceConstructible logSpace` |
| `SpaceComplexity/Constructible.lean` | `Complexity.spaceConstructible_linear` | `SpaceConstructible fun n => n + 1` |

The rest of cluster B3 (`savitch`, `PSPACE_eq_NPSPACE`, `spaceConstructible_poly`) is not
filled. Savitch is to be written as a program of the §15 language (design §16, decision 3).

One delivery, integrated by `git am -3` with Codex authorship:

| Delivery | Brief | Agent commit (base) | Integrated | Result |
|---|---|---|---|---|
| B3a | `briefs/ch34-b3a.md` | `fe512dd4` (`ebc58d67`) | `595f5237`, PR #66 (fills-6) | **2/2** |

`Constructible.lean` is unchanged from P4.1's close (`4f29ef98`) to the agent's base, and no
maintainer commit touches it afterwards.

**Every proof is kernel-checked**; the replay and axiom evidence is below. Both targets print
exactly `[propext, Classical.choice, Quot.sound]`. Fill gates close on zero blockers and zero
majors (`workflow.md` §4), and the duplication rule (`audits/TEMPLATE.md`, failure mode 5) is in
force. The standards are attached.

**Bundle:** `audits/ch34-b3a-fill-bundle.md`: this pack, the standards, the statement-gate records, the briefs, the
reports, the integration records, the owned files with their bases, the patches, the freeze,
replay, axiom, screen and lint logs, and every screen-population file, so that the screen can
be rerun.

## What changed (verify)

| Class | Declarations |
|---|---|
| **Target bodies, `sorry` → proof** | both targets |
| **Other publics** | `SpaceConstructible` byte-identical |
| **Privates added** | 15, listed with their roles in the report |
| **Imports** | four sanctioned additions (brief rule 6): `Build/InputLength`, `Build/VirtualInput`, `Build/Seam`, and the optional `SpaceComplexity/Machines/Bin` (Mathlib-only). All are acyclic: no module in their closures imports a `SpaceComplexity` module |
| **Docstrings** | a flagged fill appendix on each target; status labels "proved" |
| **Size** | 95 → 538 lines |

## Brief for the auditor

1. **Freeze.** Re-establish it from the attached base (at `ebc58d67`), the head and the patch
   (`audits/evidence/ch34-b3a-fill-gate/`): both statements and `SpaceConstructible` unchanged;
   only the two bodies, their appendices and the imports changed.
2. **`spaceConstructible_linear`, the brief's main realization** (P4.1 minor 2: an uncorrected
   length counter emits `bits n`): the length counter runs on the virtual input `true :: x`, by
   composing Catalog's prepend and length-counter witnesses with `bufferedCompTM_computesInTime`;
   the space is the linear time bound through `spaceUsed_le_mul_succ`. Check the domination
   `logSpace n ≤ n + 1` (`1 ≤ 1` at `n = 0`; otherwise `Nat.log 2 n ≤ n`), the constants
   `t + 1 ≤ (a + 2b + 4)(n + 1)`, and the multiplier `M.k·(a + 2b + 4) + 1`.
3. **`spaceConstructible_logSpace`, the brief's main realization** (P4.1 minor 1: `Nat.bits 0 =
   []`, so the bits-length identity holds only for `n > 0`):
   - **count:** R8.5c (`exists_inputLengthTM`) on the native input at position `1`, with its
     framing and first-exit cut;
   - **overwrite:** cell `0` with `true` by the four-step public writer, which makes the word's
     length `logSpace n` for every `n`, so `n = 0` needs no branch;
   - **emit:** the Z1 forwarding host (`vhostEmitTM`) of Catalog's length counter on that word,
     with the handover proved equal to `vhostCfg (initCfg y) true 1 []`;
   - two nested seams dispatch exactly at each phase's first exit;
   - **space:** the native bank within R8.5c's radius interval, the writer's two cells, Z1's bank
     and buffer allowance with both clamp boundaries, and the relocation's unused tapes; the
     bound `A·(logSpace n + 1) ≤ 2A·logSpace n` uses `logSpace n ≥ 1`.

   Confirm the realization is sound and matches the brief's sanctioned route and its appendix.
4. **Duplication** (failure mode 5).
   - The delivery's screens (`audits/logs/ch34-b3a-1-screen-{before,after}.txt`, its 24-file
     population): 1,228 / 1,520 → 1,243 / 1,520, **no new pair**.
   - The fills-6 chapter-3/4 union screen (66 files at the integration head) has no new pair
     involving B3a's declarations.
   - **The maintainer's review found two near-restatements the text screen cannot see:**
     - `b3a_seam_space` re-derives the public Seam space lemma (`seamCompTM_spaceUsedByTape_le_add`
       and its relatives) in reworded text. B3a disclosed it as a promotion candidate, not as a
       copy;
     - `b3a_cfg` is close to the public `Cfg.ofWords` (`Build/Convention.lean`).

     Both are recorded as backlog F6-1(b). **Rule** whether either is debt under failure mode 5
     (undisclosed duplication of proved material), and whether it must be factored before the
     gate closes or can wait for the dedup window.
5. **Downstream.** S1b's `NL_subset_P` and `polyTimeReducible_of_mem_NL` now rest only on
   `NSPACE_subset_exp_dtime`. Confirm from the attached walks.
6. **Documentation.** Check the two appendices and every new private's docstring and sketch
   against the delivered proofs.
7. Report anything else the fill or its records misstate, in the standard table.

## Repository-side attestations (verify or challenge)

* **Delivery integrity.** The delivery's `SHA256SUMS` was all OK (27 entries; attached). Its
  environment shim and agent scripts were never compiled or run, and nothing references them.
  These are maintainer attestations.
* **Freeze:** `audits/logs/ch34-b3a-1-freeze.log`.
* **Replay** (user-run, fresh `.oleans` into the snapshot; `audits/logs/fills-6-replay.log`):
  41 modules, **0 errors**; `Constructible` has no sorry warning.
* **Axioms** (`audits/logs/ch34-b3a-fill-gate-axioms.log`; probe
  `audits/evidence/ch34-b3a-fill-gate/AxB3aGate.lean.txt`, against the replay tree): every public
  of `Constructible`, `ConfigGraph` and `Hierarchy`, 23 in all. Both targets have empty walks;
  the two S1b corollaries rest on `NSPACE_subset_exp_dtime` only; the four `Hierarchy` rows rest
  on themselves. No non-standard axiom; the private censuses (Constructible 47, ConfigGraph 57)
  find no `sorryAx`.
* **Lint** (`audits/logs/fills-6-stylelint.log`): 0 FAIL over `SpaceComplexity`.

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `audits/TEMPLATE.md`. Findings go verbatim into
`audits/ch34-b3a-fill-findings.md`. The gate closes when it has zero blockers and zero majors.

## Erratum (gate round 1, minors 1 and 2; `audits/ch34-b3a-fill-resolutions.md`)

- **Screens.** The bundle carries the delivery's 24-file population, from which its screens can be
  rerun. It does not carry the other 42 files of the fills-6 union screen's 66-file population,
  among them `Build/Convention.lean`. That screen's result rests on the historical log
  (`audits/logs/fills-6-ch34-screen-combined.txt`).
- **Delivery integrity.** The bundle attached five of the delivery manifest's 27 payloads. The
  delivery's sanity and pre-ship sources and logs, its sweep logs, its bundle check and its axiom
  log are now in `audits/evidence/ch34-b3a-fill-gate/delivery/`, each matching its manifest
  hash. The other manifest entries are attested by the maintainer, not attached.
