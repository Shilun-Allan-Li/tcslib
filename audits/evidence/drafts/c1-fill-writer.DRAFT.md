# Ch3–4 fill campaign — C1, wave 1, W: the bounded choice writer (`Turing.ndWriterTM_run_block`, `Build/NDHost.lean`)

> **DRAFT (maintainer, 2026-10-17). Not issued.** Measured at #120's head `95a3b6a0` (the tip once
> #118, #119 and #120 merge). It issues with wave 1 after #119 and #120 merge (C1's fill plan; user,
> 2026-10-17). ⟨…⟩ are filled then.

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`**, this exact branch, NOT `main`.
- Before you start, confirm that `git merge-base --is-ancestor @ANCESTOR@ HEAD` succeeds. If it
  fails, **stop**. That commit contains:
  - **your target as a gated statement** (the C1 host-contracts gate,
    `audits/c1-hosts-statements-findings.md`, PASS 0/0/11; resolutions
    `audits/c1-hosts-statements-resolutions.md`), and the guess-then-run assembly built on it
    (the C1-A assembly gate, `audits/c1-assembly-statements-r2-findings.md`);
  - C1's design (`audits/evidence/c1/C1-design.md`; the writer is §3.4) and C1's fill plan
    (`audits/evidence/c1/C1-fill-plan.md`; you are wave 1's W);
  - **the API PRs** (the user's "Everything" rule, 2026-10-16: every definition your route reads
    has a published lemma): the specification API (PR #112), the core API (PR #116), the
    brief-inventory API (PR #118, whose round 3 gives `Action.apply`'s fields) and **the ND
    inventory API (PR #119, which gives `NDTM.stepWith_of_some` for this brief)**;
  - the fill-agent environment addendum `briefs/fill-environment-addendum.md`, and the
    declaration-keyed copy-text screen v3 `audits/evidence/retrofit/copy-text-screen-v3.py`;
  - **this round's inputs** (`audits/evidence/c1-fill-writer/`): the import probe and the screen
    population. Also the order list `briefs/orders/c1-fill-writer.txt`, the base sorry set, the
    screen base and the pre-ship log (`audits/logs/c1-fill-writer-*`).
- If Lean cannot start, follow `briefs/fill-environment-addendum.md` exactly.
- **Branch at exactly that commit, not at the campaign tip:**

  ```sh
  git checkout -b fill/c1-writer @ANCESTOR@
  git rev-parse HEAD        # must print @ANCESTOR@
  ```

  Record that hash as your base in `REPORT.md`. Never rebase, merge or cherry-pick.
- **Delivery is by zip, not PR or push** (`workflow.md` §4): `fill-c1-writer.zip`. It contains:
  - `REPORT.md` and the full modified source;
  - a `git format-patch` series against your base, and a git bundle whose only prerequisite is
    your base;
  - the bootstrap and final sweep logs and the axiom log;
  - both screen outputs, and `SHA256SUMS`.

## Base, line numbers and what lands around you

- **Your base's Lean content is the campaign tip after #120** (⟨BASE-LEAN⟩). The inputs commit
  adds no Lean change. Lines in this brief are those of that tree. `Build/NDHost.lean` has 1,098
  lines there. Every probe and measurement below was run there, against the olean snapshot of
  #120's replay (`oleans-lndnf`).
- **In flight, merging after your base and invisible to it:** wave 1's other four briefs (WC in
  `Build/InputWindow`, E in `ClassNP/ExhaustiveReplay`, R in `NDCodeSimulator`, UN in
  `Diagonalization/NTimeHierarchy`); the six #118 briefs (U2-S, F5, F3's continuation, the
  canonizer's continuation 6, G4's continuation, MIG-12); C1-E's statements (#121,
  `Diagonalization/NTimeDiagonalizer`). Cite nothing they add.

## Parallel batches this round

None in `Build/NDHost.lean`. Your consumers are already written: the guess-then-run assembly's seven
theorems in this file (`guessRunTM_runWith_handoff` and the rest) are proved modulo your target, and
through them the universal NDTM (UN) and the diagonalizer (C1-E).

## What this is

**C1's choice writer, bounded flavor:** the guess of [AB09, §2.1.2] as a device (C1's design §3.4).
One target, frozen:
1. **`Turing.ndWriterTM_run_block`** (line 200): from `run ()` over a nonblank block of `m` cells
   of tape `j` followed by a blank, every choice word of length `m + 1` writes its first `m` bits
   over the block, leaves the head after it and reaches `done`, every other field unchanged; and no
   shorter word reaches `done`.

**The published lemmas your route reads** (ground rule 10):
- the ND run algebra: `NDTM.runWith_nil`, `runWith_cons`, `runWith_append`;
- **the ND step** (the ND inventory API, #119): `NDTM.stepWith_of_some` (a live step applies
  `tm.tr b q …`) and `stepWith_of_halt`;
- **the applied action** (#118, round 3): `Action.apply_state`, `_inputPos`, `_workTapePos`,
  `_output`, and `Action.apply_workTapes`;
- the scanned symbols: `Cfg.workTapeSymbols_eq`; the buffer: `FinTM.bufferTape` and its lemmas;
  `Function.update` (Mathlib).

**Read first:**
- the target's docstring, whose proof sketch is binding where this brief does not refine it;
- `ndWriterTM` (line 177) and the module docstring's "Design";
- the assembly's use of your target (`guessRunTM_runWith_handoff`, line 443, at line 505): what it
  needs from both clauses.

**Pre-ship check** (maintainer, at the base, against `oleans-lndnf`;
`audits/logs/c1-fill-writer-preship.log`):
- **No import is added.** Your file elaborates at the base with exactly your target's sorry warning.
- **The import probe** (`C1WriterImportProbe.lean.txt`, 20 `#check`s): every public
  declaration this brief cites resolves from your file's import context. 0 errors, 0 warnings.
  Re-run it after your delivery.

## Owned regions and targets (modify these and nothing else)

| # | File:line | Target |
|---|---|---|
| 1 | `Build/NDHost.lean:200` | `Turing.ndWriterTM_run_block` |

Your regions:
- **(a) one home**, for your `private` declarations: the blank line **187**, between `ndWriterTM`
  and the target's docstring. `private` only, and no `section`, `open` or `variable` that leaks
  past one.
- **(b) the body**, the `sorry` on line **216**.
- **(c) a flagged "Fill appendix (C1-W)" paragraph at the end of the target's docstring**, before
  its closing ` -/` (line 199). The closer ends a text line; put it on its own line after your
  paragraph.

Frozen: the module header and docstring, `NDWriterState`, `ndWriterTM`, the phase host, the whole
guess-then-run assembly, the target's statement, and every other file. The maintainer updates the
module's status text at integration.

### Route (binding; `policy.md` §1, `workflow.md` §2)

- **The writer is a leaf, and it is yours:** `ndWriterTM` is defined in your file, so you may
  unfold it. Read its steps through `NDTM.stepWith_of_some` and its actions through `Action.apply`'s
  fields. Never unfold `NDTM.stepWith`, `NDTM.runWith` or `Action.apply` (rule 10).
- **One induction over the block.** For `u ≤ m`, after a prefix of length `u` of a choice word the
  configuration is the block-update with `w.take u` over the first `u` cells, the head at
  `c.workTapePos j + u`, state `run ()`, every other field `c`'s. At `u < m` the head reads cell `u`
  of the block, which is still the original nonblank cell (`hblock`), so the writer writes `w[u]`
  and moves right. At `u = m` it reads the blank (`hend`) and moves to `done` without moving.
- **The second clause** is the same invariant: before the `(m + 1)`-th step the state is `run ()`.
  A shorter word ends there.
- **Promotion candidate** (list it in `REPORT.md`; a note only): a generic "write a word over a
  nonblank block" invariant, if one emerges. The controller-stopped flavor (the normal form's
  display guess) will want it.

## Gate guidance (binding)

- **The C1 host-contracts gate** fixed the statement (`audits/c1-hosts-statements-findings.md`,
  note NF3: "trivial control, nonblank block, blank endpoint, exact time, and the frame are
  adequate; `m = 0` works"). Its minor M1 corrected the prose: under a general controller the choice
  also selects the successor, so only the trivial controller is branch-independent.
- **The instances the gate checked (its tests table) must stay true of your proof:**
  - `m = 0`: at a blank head cell the writer enters live `done` after one bit, writes nothing, and
    stays at the original head; no zero-length word reaches `done`;
  - `m = 2`: all eight words of length three reach `done` at time 3 with their first two bits
    written, and all four words of length two remain in running control;
  - without the nonblank-block hypothesis, a blank inside the block stops the writer early, so
    `hblock` is necessary; the values of the nonblank cells are irrelevant, as they are
    overwritten.

## Cited infrastructure (public and proved at the issue commit; all in `C1WriterImportProbe.lean.txt`)

The probe's names: the target and `ndWriterTM`; the ND run algebra and step (`NDTM.runWith_nil`,
`_cons`, `_append`, `stepWith_of_some`, `stepWith_of_halt`); the applied action
(`Action.apply_state`, `_inputPos`, `_workTapePos`, `_output`, `Action.apply_workTapes`);
`Cfg.workTapeSymbols_eq`; `FinTM.bufferTape` and its lemmas.

**Proved modulo, exactly:** none.

## Ground rules (binding)

1. **File ownership, by region.** Only regions (a)–(c) of `Build/NDHost.lean`. List every new
   declaration with its role.
2. **Statement freeze** over the target and every landed declaration: no renames, re-signatures,
   restatements or attribution edits.
3. **No new public declaration.**
4. **Escalation** on anything unprovable as stated: stop on that item, record the obstruction, and
   report.
5. **No touching other sorries.** Cite proved material; never re-prove it.
6. **Imports.** None added.
7. **One proof per shared argument.** Never re-prove the phase host's or the assembly's lemmas.
8. **Size.** No cap; file size alone is not a driver. Report the final line count and the public
   and private declaration counts (base: 1,098 lines).
9. **Continuation budget.** A partial zip states the open declarations (each with a literal "Proof
   sketch") and the target's axiom walk. A partial is fine; an unreported gap is not.
10. **The pinned base, and no unfolding (user, 2026-10-16).**
    - Cite only declarations public at your base, and your file's own privates.
    - **Never unfold a definition of another file.** Read every definition through its published
      lemmas: the specification API (#112), the core API (#116), the brief-inventory API (#118) and
      the ND inventory API (#119), and the landed lemmas the probe lists.
    - **The machine model's primitives** (`NDTM.stepWith`, `NDTM.runWith`, `MultiTapeTM.step`,
      `Action.apply`) are read through their lemmas: the run algebra, `NDTM.stepWith_of_some` and
      `_of_halt`, and `Action.apply`'s fields.
    - Your own file's definitions (`ndWriterTM`, `NDWriterState`) may be unfolded.
    - If a fact you need about another file's definition has no published lemma, **stop on that
      item and escalate** (ground rule 4), naming the lemma you need. Never prove it by unfolding.
    - List every declaration you cite outside your file. If you cite more than the probe's list,
      add them to a copy of the probe and run it.
11. **MIG-1 compatibility.**
    - Cite none of the six R3 canonical rows.
    - Cite no private declaration of another file.
    - Keep your new privates under the `wr_` prefix.

## Duplication governance (binding)

Run the text-level screen **before and after**, **one run at a time, under `nice -n 10`**
(`audits/TEMPLATE.md` failure mode 5; `policy.md`, **Duplication**).
- **The population** is 7 files (`audits/evidence/c1-fill-writer/screen-population.txt`): your file;
  the ND model `Nondeterministic`; `ChoiceReplay`; `Build/Seam`, `Build/Embed`; and
  `Build/Primitives` and `Build/Catalog`, where the write-and-move leaf proofs live.
- **The screen** is `audits/evidence/retrofit/copy-text-screen-v3.py`, on the repository paths.
- **The base** is `audits/logs/c1-fill-writer-screen-base.txt`: **780 declarations, 1,018 pairs,
  380,649 characters** (MEASURED; most pairs are the catalog's known `f2_` copies, MIG-1's).

```sh
P=audits/evidence/c1-fill-writer
nice -n 10 python3 -I audits/evidence/retrofit/copy-text-screen-v3.py . \
  $(grep -v '^#' $P/screen-population.txt) > /tmp/screen-before.txt
# after your changes, again, only when the first run has finished
nice -n 10 python3 -I audits/evidence/retrofit/copy-text-screen-v3.py . \
  $(grep -v '^#' $P/screen-population.txt) > /tmp/screen-after.txt
```

- **No new cross-file pair** with an owned-file declaration on one side. Nothing is pre-disclosed.
- **Known hazards:** the catalog's one-tape write rows and their run lemmas. Follow their pattern,
  never transcribe it. A pair at 90% or more is a copy.
- List every new in-file pair with a one-line justification. Quote both outputs in `REPORT.md`,
  which carries **"new copies: none"** (or lists each pair).

## Environment and verification

- Lean 4 v4.25.0, mathlib pinned; `lake exe cache get`; **never `lake build`**. Use
  `scripts/lean_check_tree.sh` for every check.
- **Bootstrap once** from `briefs/orders/c1-fill-writer.txt` (**80 modules**: the upstream closure
  of your owned file and of every module downstream of it, without the root `TCSlib`).

  ```sh
  ( while read -r m; do bash scripts/lean_check_tree.sh "$m" || exit 1; done \
      < briefs/orders/c1-fill-writer.txt )
  ```

  **The base sorry-warning set has 35 entries in 15 modules** (`audits/logs/c1-fill-writer-base-sorries.txt`).
  Yours is `Build/NDHost`'s one. Record the base list by name first, and report any difference.
- **Final checks:**
  1. `Build/NDHost`: zero errors, no sorry warning (for a partial, exactly the open declarations'),
     and no other warning in anything you added.
  2. Every other module of the order list: zero errors, and sorry warnings exactly the base's minus
     yours.
  3. Re-run `C1WriterImportProbe.lean.txt`: 0 errors.
- **Axiom prints** for the target, the seven assembly theorems that cite it, and every new private:
  within `[propext, Classical.choice, Quot.sound]`, no `sorryAx` for a complete delivery.
- **Lint:** `python3 -I scripts/campaign_style_lint.py TCSlib/Complexity/TuringMachine/Build`,
  0 FAIL (base: 0 FAIL, 31 WARN over 37 files). No new line over 100 characters.

## REPORT.md checklist

- [ ] The target proved, or the obstruction; the base hash and the ancestor check.
- [ ] Nothing outside regions (a)–(c).
- [ ] Every new declaration with its role; the appendix.
- [ ] Promotion candidates and escalations, or "none".
- [ ] Rule 10: the declarations cited outside your file, and the probe re-run. Rule 11: a grep of
      your diff for the six R3 rows and for other files' private names.
- [ ] Duplication: both v3 screens, every new pair justified, "new copies: none".
- [ ] File size; the final sweep tail; the axiom prints (including the assembly's seven theorems,
      now without `sorryAx`); the lint line.

## Known pitfalls at this pin (hard-won)

- **`ndWriterTM`'s blank test is `(w j).isNone` on the scanned symbol**, so it reads the cell under
  the head of tape `j`: `Cfg.workTapeSymbols_eq` turns that into `c.workTapes j (c.workTapePos j)`.
- **The written symbol is `some (some b)`**: the action writes `some b` (a nonblank cell). The
  block-update in the statement is `FinTM.bufferTape (w.take m)` at the offset.
- **`runWith` consumes the word left to right** (`runWith_cons`); split a word of length `m + 1` as
  `w.take m ++ [w[m]]` with `runWith_append` if the induction runs on prefixes.
- `omega` with products as atoms (`ring` first). The linter needs a literal "Proof sketch" before
  every `sorry` (partial only).
