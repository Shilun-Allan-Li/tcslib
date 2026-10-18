# Chapter-1/2 retrofit — Batch RB4: the acknowledged dedup debt (`Build/Loop.lean` + `Build/Primitives.lean` + `CookLevin/Hardness.lean`)

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`** — this exact branch,
  NOT `main`.
- Create your working branch off it (suggested name `fill/retrofit-rb4`),
  record the base commit hash in `REPORT.md` (the brief was issued at
  `8f13d74ecba8e73a3642d605f462774092d7ef8a`), and never rebase.
- **Delivery is by zip, not PR or push**: `retrofit-rb4.zip` with the
  standard contents. Integration note (no action for you): the maintainer
  integrates retrofit deliveries on a side branch and opens a PR for the
  user's manual merge.

## What this is

A **retrofit batch discharging human-acknowledged duplication debt**
(`audits/duplication-ledger.md`, acknowledgment table; the user's RB4
decision of 2026-10-09): **zero `sorry` and zero `error:` before and
after every commit**; a partial delivery means fewer tasks completed,
never an admission. The two debt families, verified byte-identical by the
retrofit-R1 round-2/round-3 audits
(`audits/retrofit-r1-r2-findings.md`, the family map and H3 list):

1. **The three-file relocation family** — `emCallAction`/`emCallCfg`/
   `emCall_apply`/`emCall_relocate_run` (Loop 3520-3595) ≡
   `emitterP2Action`/`emitterP2Cfg`/`emitterP2_apply`/
   `emitterP2_relocate_run` (Primitives 4699-4774) ≡
   `clSlotAction`/`clSlotCfg`/`clSlot_apply`/`clSlot_run`
   (Hardness 1803-1878): identical after consistent identifier
   substitution, 73 declaration/docstring lines per file.
2. **The Loop-internal H3 family** — 13 `emLoopHost_*` phase lemmas
   byte-identical to their `loopHost_*` originals after renaming
   (suffixes: `fuel_capture`, `input_rewind`, `fuel_rewind`, `fuel_copy`,
   `fuel_return`, `fuel_setup`, `prepare`, `release`, `borrow_step`,
   `borrow_run`, `borrow_rewind`, `borrow`, `reject`), plus the `_init`
   near-copy (one extra simp entry) and the 36-line near-copy
   `emLoopHost_anchor_return`.

**The proved infrastructure that unlocks this batch** (all
kernel-checked; cite, never copy):

- **Z5**: `Turing.MultiTapeTM.AgreeOn`, `step_eq_of_agreeOn`,
  `runFrom_eq_of_agreeOn` (`Simulation.lean`) — guarded run transfer
  between machines with agreeing tables.
- **The Z1-rider selected-tape exports**:
  `embedSilentCfg_selected_tape`/`_pos`,
  `embedEmitCfg_selected_tape`/`_pos` (`Build/Embed.lean`), plus the
  public `embedEmitTM_runFrom`/frame/visited contracts (R1).
- The binding composition plan (the A-S1 statement-gate audit's Z5
  customer-strength analysis, `audits/vhost-infra-findings.md`, adopted at
  its close): **transport first, then agree** —

> Z5 must be applied **after** tape relocation and state transport produce
> the reference machine on the host carrier; the compared machines then
> use the same starting host configuration. [...] For the concrete
> injective constructor/pair state embeddings, one can extend the renamed
> source table to the host state type, use the existing unguarded
> state/block transport and R1 relocation to identify its run, then use
> Z5 on the image of the good source states.

## Tasks

**Task 1 — collapse H3 (`Build/Loop.lean`).** `emLoopHost` agrees with
`loopHost` on every non-body state (the forwarding host's table delegates
there — the Loop inventory's verified fact). Replace the 13 verbatim
`emLoopHost_*` phase lemmas (and, if it falls out, the `_init` near-copy
and `emLoopHost_anchor_return`) with Z5 transfers of the corresponding
`loopHost_*` lemmas: one agreement fact (`AgreeOn` on the non-body state
set), then per-lemma `runFrom_eq_of_agreeOn`/`step_eq_of_agreeOn`
citations with the strict-prefix guards supplied by the originals' own
no-anchor/liveness hypotheses. Expected ≈ −500 lines. The originals and
all consumers' statements stay byte-identical; only the 13+ proof bodies
of the copies' consumers change to cite the transferred facts (or the
copies' statements survive as one-line corollaries — your choice,
disclosed; **net private count must drop by at least 13**).

**Task 2 — replace the relocation family (all three files).** Replace the
four-declaration family per file with the public route: the R1
embeddings' contracts plus the selected-tape exports for the frame
identities, and Z5 (per the composition plan above) for the guarded
agreeing-host lockstep that `emCall_relocate_run`/`emitterP2_relocate_run`/
`clSlot_run` currently provide. Call-site counts (round-2/round-3 audit
data): Hardness has 13 `clSlot_run` sites with state guards of the shape
`q ≠ exit` / component-nonempty / `True` — all read-uniform, so `AgreeOn`
suffices after transport. If a residual per-file glue lemma is genuinely
needed (e.g. the state-extension of the renamed table), it must be **one
public shared lemma requested for `Simulation.lean`** via "Requested
shared lemmas" with a `private` local copy in ONE file only — never three
copies again (that is the exact debt being discharged; three new copies
would be rejected at integration).

**Priority on exhaustion**: Task 1 complete, then Task 2 file by file
(Hardness last — its 13 call sites are the bulk).

## Ground rules (binding)

1. **Ownership**: exactly the three named files.
2. **Public-surface freeze**: every public declaration of all three files
   byte-identical (signatures, statements, docstrings, proof bodies) —
   this batch touches privates only.
3. **Duplication governance**: the REPORT's ledger line must show the
   **net member reduction** against `audits/duplication-ledger.md` (the
   13 H3 copies and the 12 relocation members are the targets); zero new
   copies; one disclosed local copy at most, per Task 2's rule.
4. **Escalation** on any site where the public route genuinely cannot
   reproduce a needed fact: restore, record, continue — never weaken a
   surviving statement.
5. **No import changes** except, if needed, `Build.Seam`/`Build.Embed`
   into files not yet importing them — each flagged.

## Environment and verification

Standard setup (65-module bootstrap + Build files; never `lake build`).
Iterate per edit. Final, in order: `Build/Loop`, `Build/Primitives`,
`Build/Catalog`, `CookLevin/Hardness`, the `TuringMachine` facade, the
`CookLevin` facade — **zero errors and zero sorry warnings in all six**
(the tree's other sorries are the concurrent A-S2 fill surfaces and
baseline admissions; list what you observe). Axiom prints for all public
declarations of the three files (8 + 18 + 5): byte-identical to baseline,
no `sorryAx`. Lint both directories — 0 FAIL.

## REPORT.md checklist

- [ ] Task 1 and Task 2 per-file status; net line/private deltas per file;
      the ledger-member reduction stated against the current ledger rows
      (Loop 104, Primitives 150, Hardness 4).
- [ ] Every new `private` or requested shared lemma listed; the one
      permitted local copy (if any) disclosed.
- [ ] Final sweep tail (six checks) + 31 axiom prints + both lint lines.
- [ ] Diff touches only the three owned files.

## Known pitfalls at this pin (hard-won)

- Z5 is **same-carrier**: never feed `runFrom_eq_of_agreeOn` two machines
  of different tape counts or state types — transport first (the quoted
  composition plan); the unguarded transports are `leftCfg_run`/
  `rightCfg_run` (`Simulation.lean`) and the R1 contracts.
- The agreement set for H3 is a **state-shape** set (non-body
  constructors); `AgreeOn` needs table equality for ALL reads at those
  states — the Loop inventory verified the delegation is literal, so
  `fun _ _ => rfl`-grade facts should discharge it.
- The strict-prefix guard of `runFrom_eq_of_agreeOn` is `∀ u < t`: the
  originals' phase lemmas carry exactly such guards; thread them, do not
  re-prove liveness.
- `Function.update_of_ne`; `dsimp only` after `cases` on control; avoid
  bare `simp` with folded forms; deleting a declaration takes its
  docstring with it.
- Hardness's five publics live in namespace `Complexity`; Loop/Primitives
  in `Turing.FinTM` — print axioms with the names as declared.
