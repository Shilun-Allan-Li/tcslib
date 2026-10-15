# §13 fill campaign — Tranche A-S1, single batch: the virtual-input layer and the agreement transfer (`Build/VirtualInput.lean` + `Simulation.lean`)

## Repository and branch — read this before anything else

- Clone: `https://github.com/Shilun-Allan-Li/tcslib`
- Check out branch **`complexity/arora-barak-ch3-4`** — this exact branch,
  NOT `main`. Every file this brief cites exists only on it.
- Create your working branch off it (suggested name `fill/vhost-f1`),
  record the base commit hash you branched from in `REPORT.md` (the brief
  was issued at `756657d0b45f41f2a5e93f976f3189ce99080772`), and never
  rebase onto anything else.
- **Delivery is by zip, not PR or push** (`workflow.md` §4):
  `vhost-f1.zip` with `REPORT.md`, both full modified source files, a
  `git format-patch` series against your recorded base, a git bundle, the
  final sweep log, the axiom-print log, and `SHA256SUMS`.

## Context

You are filling the **11 audited-true statements** of the §13 tranche
A-S1 (the virtual-input layer): 9 in
`TCSlib/Complexity/TuringMachine/Build/VirtualInput.lean` and 2 in
`TCSlib/Complexity/TuringMachine/Simulation.lean`. The statement gate
closed in one round (`audits/vhost-infra-{findings,resolutions}.md` —
read both). **The auditor supplied a complete per-statement mathematical
argument for every target; those arguments are quoted verbatim below and
are the binding proof routes.** The in-repo fill template is the proved
`Turing.FinTM.bufferedSecondCfg_step`/`bufferedSecondCfg_run`
(`Simulation.lean` — the same arbitrary-source-configuration, valid-tag,
existential-arrival-tag, all-horizon shape; your Z1 proofs adapt them with
the inactive first block removed and an output prefix carried along).

Retrofit batches RB1/RB3 run concurrently on `Build/Loop.lean` and
`CookLevin/Hardness.lean` — **you never touch those files**.

## Owned files (modify these and nothing else)

`Build/VirtualInput.lean` — all 9 sorried theorems, suggested order:
1. `vhostEmitTM_step` 2. `vhostEmitTM_runFrom` (the core pair)
3. `vhostEmitTM_visitedByTapeHead_bank`
4. `vhostEmitTM_visitedByTapeHead_buffer` 5. `vhostCfg_buffer_head_mem`
6. `vhostEmitTM_spaceUsed_le` 7. `vhostEmitTM_emitting_halt`
8. `vhostSilentTM_runFrom` 9. `vhostSilentTM_spaceUsed_le` (the two
silent contracts are **two-layer citations** — `embedSilentTM_runFrom`
and the R1 silent space clauses over your targets 2 and 6; perform no
third simulation induction).

`Simulation.lean` — the 2 sorried theorems:
10. `MultiTapeTM.step_eq_of_agreeOn` 11. `MultiTapeTM.runFrom_eq_of_agreeOn`.

## Optional permanent lemmas (audit-adopted; deliver any subset, each flagged)

Public additions sanctioned by the gate close (resolutions, "Adopted"):
(a) `VirtualTag (1 : Fin (y.length + 2)) true` and `q₀`-independence of
`runFrom` (replacing `q₀` with the table fixed changes no run);
(b) injectivity of `fun c => vhostCfg c b p pre` at fixed `b, p, pre` —
do **not** assert joint `(c, b)` injectivity (halted transports forget the
tag); (c) native-head constancy for **arbitrary** host configurations
(`((vhostEmitTM M).runFrom d t).inputPos = d.inputPos`), stated as an
input-position fact, never as a work-tape index; (d) named empty-word
left/right clamp corollaries and a silent emitting-halt projection. List
each delivered one in `REPORT.md` under "Optional exports".

## Environment and verification

- Toolchain pinned by `lean-toolchain` (Lean 4 v4.25.0), mathlib pinned.
  Setup once: `lake exe cache get`. **Never run `lake build`.**
- Bootstrap once:
  `while read -r m; do bash scripts/lean_check_tree.sh "$m" || break; done < scripts/ab_ch1_module_order.txt`
  (65 modules; the known baseline admissions are out of scope:
  `CounterProgRun`'s S9 and the chapter-3/4 statement surfaces), then
  check `Build/Embed`, `Build/Seam`, `Build/Catalog`, and
  `Build/VirtualInput` in that order.
- Iterate per edit on the file you changed. Final, in order:
  `Simulation`, `Build/Embed`, `Build/VirtualInput`, `Build/Catalog`,
  then `TCSlib/Complexity/TuringMachine` (the facade) — zero `error:`
  lines and **zero `sorry` warnings in all five**, fresh `.olean`s.
- **Axiom prints**: `#print axioms` for all 11 filled theorems on the
  final fresh tree; each footprint **at most**
  `[propext, Classical.choice, Quot.sound]` — proper subsets fine — and
  no `sorryAx`: this batch has no sanctioned admitted dependency.
- Style lint (one directory per invocation):
  `python3 scripts/campaign_style_lint.py TCSlib/Complexity/TuringMachine/Build`
  and `python3 scripts/campaign_style_lint.py TCSlib/Complexity/TuringMachine`
  — 0 FAIL (Simulation's 1,005-line WARN is justified in the plan's
  decision log; cite that justification in `REPORT.md`, do not split the
  file).

## Ground rules (binding)

1. **File ownership.** Only the two owned files, and only the 11 targets'
   proofs, `private` helpers, and the flagged optional exports. Shared
   wishes go under "Requested shared lemmas" in `REPORT.md` with a
   `private` local copy. List every new declaration — the epoch audit
   blind-restates them.
2. **Statement freeze.** No renames, re-signatures, restatements, or
   attribution edits anywhere. Docstring sketch appendices allowed,
   flagged.
3. **Duplication governance** (`policy.md`, **Duplication**): zero new
   copies of existing proved material; `REPORT.md` carries the ledger line
   ("new copies: none" expected). In particular, adapt — do not copy —
   the `bufferedSecondCfg` proofs: cite `bufferTape_inputSymbol`,
   `virtualMove_correct`, and the `runFrom` lemmas rather than restating
   them.
4. **Escalation** on anything unprovable as stated: stop, record the
   obstruction, deliver what exists.
5. Docstrings stay; precise imports; keep `set_option` headers.
6. **Continuation budget**: 11 targets over one core. On exhaustion,
   deliver a partial zip whose `REPORT.md` states what is proved, which
   `private` helpers remain `sorry` (allowed **only** in a partial
   delivery, each listed), and the frontier.

## Inherited audit contract (verbatim; binding on the fill)

From `audits/vhost-infra-findings.md`, "The eleven sorried statements,
literally" — the route for each target, in the brief's numbering:

> 1. **`step_eq_of_agreeOn`.** If `c.state = none`, both steps equal `c`.
> Otherwise write `c.state = some q`; `hq` gives `q ∈ Q`, so `h` equates
> the two actions at `c.inputSymbol` and `c.workTapeSymbols`, and applying
> equal actions to the same configuration gives the stated equality.
>
> 2. **`runFrom_eq_of_agreeOn`.** Induct on the number of steps up to the
> requested horizon, with equality at zero because both runs start at `c`.
> At time `u < t`, substitute the already-equal configurations and apply
> the preceding step lemma using `hq u`; if that configuration is halted,
> equality is automatic. No assumption about the control at time `t` is
> needed, and no equality of the two `q₀` fields is needed.
>
> 3. **`vhostEmitTM_step`.** In the halted case take the original tag,
> because source and host configurations are both fixed. In the live case
> the buffer read is the source input read by `bufferTape_inputSymbol`,
> and the bank reads are identical by the transport's fields; choose
> `b' := virtualNextTag b (virtualMove b c.inputSymbol a.inputTape)`,
> where `a` is the source action. `virtualMove_correct` supplies both the
> exact buffer-head equation and validity of `b'`; all other configuration
> fields follow from the action definition and append associativity,
> including when `a.state = none`.
>
> 4. **`vhostEmitTM_runFrom`.** At time zero, use witness `b` and the
> supplied tag hypothesis. For the successor step, apply the step contract
> to the transported source configuration and its valid arrival tag, then
> substitute the source and host iteration identities. This works after a
> halt as well as before it and introduces no nonemptiness or liveness
> premise.
>
> 5. **`vhostEmitTM_visitedByTapeHead_bank`.** Apply the run contract
> separately at every `u ≤ t` and project `workTapePos (vhostBank i)`.
> The resulting head equals `(M.runFrom c u).workTapePos i`, independently
> of the existential arrival tag, so the two images of
> `Finset.range (t+1)` are equal. Thus the statement is equality, not
> merely containment.
>
> 6. **`vhostEmitTM_visitedByTapeHead_buffer`.** The corresponding
> buffer-head projection at each time `u ≤ t` is exactly
> `((M.runFrom c u).inputPos.val : ℤ) - 1`. Substitution into the defining
> finite image gives exactly the stated right-hand side, with both time
> zero and time `t` included.
>
> 7. **`vhostCfg_buffer_head_mem`.** The run identity gives the head as
> the integer source input position minus one. Since that position belongs
> to `Fin (y.length+2)`, its value lies between zero and `y.length+1`, so
> the transported head lies between `-1` and `y.length`, inclusively.
>
> 8. **`vhostEmitTM_spaceUsed_le`.** Split the sum of work-tape
> visited-set cardinalities into tape zero and the bank indexed by
> `Fin m`. The bank equalities give exactly `M.spaceUsed c t`, while the
> buffer equality and interval lemma bound its cardinality by
> `y.length+2`. This yields the printed coefficient one, at the same
> horizon, without any output-length term.
>
> 9. **`vhostEmitTM_emitting_halt`.** The hypotheses say that the action
> applied from the live source configuration has successor `none` and
> emission `some bit`. The host applies that same emission while mapping
> the successor to `none`, so its new output is
> `(pre ++ c.output) ++ [bit]`. Transporting the source step gives
> `pre ++ (c.output ++ [bit])`; append associativity makes these equal to
> the displayed contract, so the final bit is neither dropped nor
> duplicated.
>
> 10. **`vhostSilentTM_runFrom`.** Apply `embedSilentTM_runFrom` with
> source `vhostEmitTM M`, the specified embedding, capture tape, and
> transported starting configuration; the required capture-disjointness
> follows from the layout arithmetic [the unselected set is exactly the
> capture tape]. Substitute `vhostEmitTM_runFrom` and its valid arrival
> tag. The result is precisely `vhostSilentCfg` of the source endpoint,
> with capture prefix `capPre` and physical output `out₀` unchanged; no
> third simulation induction is needed.
>
> 11. **`vhostSilentTM_spaceUsed_le`.** Split the silent host into the
> selected forwarding host and its sole capture tape.
> `embedSilentTM_visitedByTapeHead` gives the selected contribution
> exactly, and `embedSilentTM_spaceUsedByTape_cap` bounds capture by
> source output growth plus one. That quantity is at most the final
> capture-word length plus one, so the forwarding bound gives exactly the
> stated inequality.

Also binding (the audit's layout arithmetic, verify it inside your proofs
of 10-11): for the silent layout,
`j ∈ range (Fin.castAddEmb 1) ↔ j.val < 1 + m`, and the complement is
exactly `vhostCap m` — capture is disjoint from the selected range and
there is no third, ambient case, including `m = 0`.

## Out-of-scope sorries you will see (leave untouched)

`CounterProgRun`'s `sim_run_of_regs_le` (S9, baseline); the chapter-3/4
statement surfaces (`NDCodes`, `Formulas/QBF*`, `Diagonalization/*`,
`ClassOracle/*`, `SpaceComplexity/*`, `ClassPSPACE/*`,
`TuringMachine/Oracle*`, `NondeterministicSpace`). Everything in
`Build/Loop.lean` and `CookLevin/Hardness.lean` (concurrent retrofit
batches own them).

## REPORT.md checklist

- [ ] 11/11 filled (or the partial frontier per ground rule 6).
- [ ] Base commit hash; every new `private` declaration listed; optional
      exports listed (or "none").
- [ ] Duplication ledger: "new copies: none".
- [ ] Final sweep log tail (the five checks, 0 errors / 0 sorries) +
      11 axiom prints (at most the standard triple; no `sorryAx`).
- [ ] Diff touches only the two owned files.

## Known pitfalls at this pin (hard-won)

- `Fin.addCases` on `Fin (1 + m)`: after `cases`/`refine Fin.addCases`,
  `simp [vhostCfg]` exposes the two blocks; the repo's
  `bufferedFirstCfg_init`/`bufferedSecondCfg_step` proofs show the exact
  `Fin.addCases ?_ ?_ i <;> intro j <;> simp [...]` idiom.
- `Option.map` on the control: `c.state.map (fun q => (q, b))` — after
  `cases hq : c.state`, `dsimp only` before rewriting; a halted transport
  has state `none` with no tag to track.
- `virtualMove_correct` consumes `c.inputSymbol`; rewrite the buffer read
  to it via `bufferTape_inputSymbol` **before** introducing the source
  action, as `bufferedSecondCfg_step` does (its `hv` step).
- `Function.update_of_ne` (not `update_noteq`); avoid bare `simp` with
  folded forms; `omega` needs beta-reduced, non-`Fin`-projection goals.
- Visited sets are `Finset.image` over `Finset.range (t + 1)`:
  trajectory equalities give image equalities pointwise
  (`Finset.image_congr`-style); for target 8 use the `Fin.sum_univ_succ`/
  `Fin.addCases` split of `spaceUsed`'s sum, not interval arithmetic.
- For targets 10-11, the R1 lemma names are `embedSilentTM_runFrom`,
  `embedSilentTM_visitedByTapeHead`, `embedSilentTM_spaceUsedByTape_cap`
  (`Build/Embed.lean`); instantiate `hcap` disjointness from the layout
  arithmetic, with `Fin.castAddEmb`'s value-preservation (`Fin.ext`,
  `omega`) closing the range computation.
- The `∃ b'` witnesses chain: never case on the existential tag of a
  previous time except through the lemma's own statement.
