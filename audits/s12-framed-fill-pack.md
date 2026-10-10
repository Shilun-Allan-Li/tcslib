# External audit pack — §12.6 framed catalog contracts, fill gate

Campaign: Arora-Barak chapters 3-4 (`AroraBarakChapters3-4Plan.md` §4b). The
§12.6 statement gate closed in one round with no findings
(`audits/s12-framed-findings.md`, `audits/s12-framed-resolutions.md`, both
attached). This round audits the **fill**. One batch (brief
`briefs/s12-framed-fill.md`, report attached verbatim) proved all five framed
contracts in `TCSlib/Complexity/TuringMachine/Build/Catalog.lean`, and
re-derived the canonical rows from them as the statement gate asked. Fill
gates close on zero blockers and zero majors (`workflow.md` §4). The
duplication rule (`audits/TEMPLATE.md`, failure mode 5, as amended) is in
force.

The fill is the attached single-commit patch `audits/evidence/s12-framed-fill.patch`,
Codex-authored and integrated by `git am -3` as `0aea2108`, at recorded base
`0658eb8c`. The campaign tip `e44b5656` leaves `Catalog.lean` unchanged.
**Every proof is kernel-checked**; the maintainer's replay evidence is
below. The audit object is therefore the **surface**:

- the private declarations the fill generalized, added or removed;
- the fidelity of the proofs to the statement gate's binding route;
- the 14 sanctioned public proof-body changes, and the sanctioned reordering;
- the duplication rule.

## What changed (verify)

| Change | Declarations |
|---|---|
| **Framed contracts proved** | `transferTM_run_ofCfg`, `copyTM_run_ofCfg`, `clearTM_run_ofCfg`, `incrementTM_run_succ_ofCfg`, `incrementTM_run_overflow_ofCfg` |
| **Canonical run rows re-derived** (sanctioned proof-body swaps) | `transferTM_run`, `copyTM_run`, `clearTM_run`, `incrementTM_run_succ`, `incrementTM_run_overflow`, each now citing its framed contract at `Cfg.ofWords` |
| **Space rows adapted** (sanctioned; the brief allowed either disposition) | `transferTM_spaceUsedByTape`, `copyTM_spaceUsedByTape`, `clearTM_spaceUsedByTape`, `incrementTM_spaceUsedByTape`, now specializing the generalized traces |
| **Private traces generalized in place** (14) | `catalogClearF`, `catalogClearR`, `catalog_clear_trace`; `catalogCopyF`, `catalogCopyR`, `catalog_copy_forward`, `catalog_copy_trace`; `catalogTransferR`, `catalog_transfer_trace`; `catalogIncF`, `catalogIncR`, `catalog_increment_trace`; `catalog_write_take`, `catalog_write_middle` |
| **Private removed / added** | removed `catalog_erase_take`; added `catalogTape`, the word-interval overlay over an arbitrary tape. Net 384 → 384 |
| **Reordering** (sanctioned, flagged) | The framed section moved above the canonical run and space rows |
| **Unchanged by rule** | `catalogCfg`, `catalogTrace`, `catalog_trace_run` (generic), every `compareTM` declaration, all imports, and the other 30 public declarations in full |

## Brief for the auditor

1. **The central rule: one generalized trace per routine.** Blind-restate
   each of the 14 generalized privates and `catalogTape` from its body.
   - Each trace must hold for an **arbitrary** framed configuration, as the
     statement gate required.
   - No canonical-only trace may survive beside its framed generalization.
     That would be a parallel copy, and it is what the brief forbade.
   - Copy and transfer share `catalogCopyF`/`catalog_copy_forward`, and both
     increment verdicts share `catalog_increment_trace`. Confirm the sharing
     is real and not a near-copy under another name.
2. **Route fidelity.** Compare the proofs with the binding route in the
   attached statement-gate findings ("Transition-based justification" and
   "Every-time trajectory and frame"):
   - forward offset `t`;
   - the turn, then the return at offset `2m − t`;
   - entry at `2m + 2`, with `m = n`, or `m = p` for a successful increment;
   - `Action.apply` writing at the old head and then moving;
   - inactive tapes receiving `(none, 0)`.

   Check particularly that the successful increment never visits the cell
   beyond the first `false`, so the trajectory bound is `[pos − 1, pos + p]`.
3. **The canonical specializations.** For each of the five run rows, verify
   that the new proof is a genuine specialization of its framed contract at
   `d := Cfg.ofWords …`, with the statement unchanged. The specialization
   table is in the statement-gate findings:
   - the time slack `2n + 2 ≤ 3n + 3`, or `2p + 2 ≤ 2n + 2`;
   - the finish configuration extensionally equal to the canonical
     `Cfg.ofWords` finish;
   - the canonical blank-destination premise `hdst` killing the
     destination's old suffix;
   - width preservation for `incFixed`.
4. **The space rows.** Verify the four adapted proofs: their statements are
   unchanged, they rest on the generalized traces rather than a new copy, and
   the integer-interval cardinality argument still holds at every time,
   including after the exit, as the report claims.
5. **Freeze and reordering.** Re-establish from the attached patch:
   - all 44 public statements are byte-identical;
   - the 30 public declarations outside the sanctioned 14 are unchanged in
     full;
   - the reordering moved statements without editing them;
   - only `Catalog.lean` changed, and its imports did not.

   Two independent checks agree, the agent's and the maintainer's (both
   attached).
6. **Duplication (failure mode 5).** The brief's binding measure was the
   generated census, under which no file's member count may increase. The
   maintainer also ran the text-level screen introduced after RB4. Both are
   below; verify that the fill created **no new copy** and did not inline
   one. The pre-existing in-file sibling repetition among
   `transferTM`/`copyTM`/`clearTM`/`compareTM`/`incrementTM` is
   acknowledged debt (12.2c item 5, a common scanner) and out of scope,
   provided the fill did not grow it. **The text screen shows new pairs in
   exactly that family** (attestation below): the five new framed proofs are
   parallel tactic scripts over parallel traces, and the canonical rows,
   re-derived the same way, resemble one another more than before. Rule on
   it under the amended failure mode 5. Is this growth inside the
   acknowledged sibling family, so a minor or a note with the factoring left
   to 12.2c item 5? Or does it change that family's scope, so a major? And
   could the fill reasonably have shared one framed sweep argument across
   transfer, copy and clear within its single-file ownership?
7. **Docstrings.** Report any docstring whose *content* the fill made false.
   One staleness is declared and pre-existing: the status tags
   "(spec, fill pending …)" on 37 Catalog docstrings, the five framed ones
   among them, and the "Status: statement skeleton" module headers of
   `Build/{Embed,Seam,Catalog}.lean`, stale since the §12 fill epochs closed.
   They are queued as a maintainer doc-only refresh once RB5 lands, since
   `Embed.lean` is RB5's. Confirm that this staleness is the only kind, for
   example that each framed docstring's "This specializes to …" sentence now
   describes exactly how the canonical row is proved.
8. Report anything else the fill misstates, in the standard table on the
   standard severity scale.

## Repository-side attestations (verify or challenge)

* **Delivery integrity.** `SHA256SUMS` all OK. The zip ships no C or shim
  source, and the patch references none; the report notes the agent's
  environment used a pre-existing executable-path shim. None of the agent's
  scripts was run by the maintainer.
* **Freeze** (`audits/logs/s12-framed-fill-freeze.log`, the maintainer's
  independent declaration-level check). 44 public declarations before and
  after, none added or removed. No statement or docstring changed. Exactly
  the 14 sanctioned bodies changed. Private declarations 384 → 384, with the
  removal, addition and 14 in-place changes above. This agrees with the
  agent's `audits/evidence/s12-framed-fill/agent-surface-freeze.log`. The
  delivered `Catalog.lean` is byte-identical to the integrated file.
* **Replay** (`audits/logs/s12-framed-fill-integration-sweep.log`, fresh
  `.olean`s): `Build/Catalog` exits 0 with **0 errors and 0 sorry
  warnings**. `Build/Zone` keeps its 2 baseline admissions (the ZF-A3 shift
  machines) and `Codes2Tape` its 1 (the uniform code), unchanged. The
  `TuringMachine` facade is clean.
* **Axioms** (`audits/logs/s12-framed-fill-axioms.log`, from the
  maintainer's probe `audits/logs/s12-framed-fill-axioms.lean.txt`): all 44
  public Catalog declarations printed. 37 are within
  `[propext, Classical.choice, Quot.sound]`, and 7 definitions depend on no
  axioms. `sorryAx` appears nowhere.
* **Lint** (`audits/logs/s12-framed-fill-stylelint.log`): 0 FAIL. The 4
  warnings are the pre-existing file-size ones.
* **Census** (`audits/logs/s12-framed-fill-census-after.log`, the
  maintainer's run of the unmodified generator): pass 4 reproduces the
  agent's after-run exactly, with every file unchanged: Catalog 318/428,
  Primitives 173, Loop 98, Wrappers 19, Composition 6, TimeConstructible 20.
* **Text-level screen** (`audits/evidence/s12-framed-fill/copytext-{before,after}.txt`,
  `audits/evidence/retrofit/copy-text-screen.py` over `Catalog.lean` at base
  and after; pair diff `copytext-diff.txt`). This screen was supplementary,
  not binding. The total copied text fell slightly, from 276 pairs and
  98,775 characters to 272 pairs and 98,445. **But the pair set changed:**
  - **16 pairs are new** (5,520 matched characters), all among the sibling
    rows. The five framed proofs, which replaced `sorry` bodies, reproduce
    one another: transfer → copy 97%, copy → transfer 84%, increment
    success → overflow 90% and the reverse 74%, clear ↔ copy/transfer
    65–78%. The re-derived canonical rows also reproduce one another more,
    for example `clearTM_run` → `copyTM_run` rising from 54% to 83%.
  - **20 pairs are gone** (7,265 characters). These are mainly the old
    canonical traces' mutual copies: compare/clear/copy/increment traces,
    and `catalogCopyR` ↔ `catalogTransferR`.
  - **21 shares changed.**

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide as in `audits/TEMPLATE.md`. Findings go verbatim into
`audits/s12-framed-fill-findings.md`. The gate closes on zero blockers and
zero majors; this completes §12.6 end to end (statements, gate, fill, fill
gate). ZF-A3 consumes these contracts next.
