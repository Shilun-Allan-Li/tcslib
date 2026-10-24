# C1, the replay canonizer: the pre-ship at the campaign tip `77f1eb4f` (drafting agent, 2026-10-24)

Tree: `77f1eb4fb74deb7a1ac7bae7bc4e98d5d0f9a532` (the campaign tip when megafill C's drafting
started; TCSlib as after #155). Olean tree: a fresh bootstrap of the union of megafill C's three
new order lists (119 modules) on this host, by `scripts/lean_check_tree.sh` one module at a time,
under addendum v2.5 Part 1; the shared environment logs are in
`campaign/fills/megafill/drafts/megafill-C-env-77f1eb4f/logs/`. Every probe below ran through
`scripts/lean_check_tree.sh` as a copy under the clone's ignored `.lake/probes/`, one Lean process
at a time; each `.out` file is that run's output with its time, peak memory and exit status.

| Check | Result | File |
|---|---|---|
| Owned file | `NDCodeSimulator` (2,325 lines; 3 public, 22 private; the target's docstring 80–95, statement 96–98, `sorry` 99): exactly the target's sorry warning (line 96). Its bootstrap check: 101 s, 2,787,220 KiB | `elab-NDCodeSimulator.out` |
| Order list | 119 modules (the upstream closure of the owned file and of every module downstream of it, without the root `TCSlib`); 41 Mathlib roots | `order.txt`, `roots.txt` |
| Base sorries | 31 declarations in 15 modules; the bootstrap's sorry warnings agree module by module | `base-sorries.txt` |
| Import probe | a standalone import of the owned module: **102 checks of 102 names**, 0 errors, 0 warnings; `codePrim_machine`, `computesFunInTime_comp`, `ComputesInTime.mono` and the bridge on the standard three axioms (`codeSkipActionK_append` on two) | `C1RCImportProbe.*` |
| Route probe | sealed over 14 TCSlib definitions (none `@[simp]`): the composition step with `g` abstract (`c1rc_compose`), the choice field, the record widening, the read order, both tables' layouts and the widening's `Primrec` proof. 0 diagnostics; seven axiom prints, all within the standard three | `C1RCRouteProbe.*` |
| Seal controls | 15 goals (one per sealed definition, `FinTM.ComputesFunInTime` twice): unsealed, all close; sealed, all 15 fail, each at its own goal (lines 92–157) | `C1RCSealControl.*` |
| Definitions probe | the brief's recommended `rc_widen`, `rc_round`, `rc_table`, `rc_g` elaborate. **Evaluation, not proof**: on two concrete coded machines `rc_g` reproduces the replay serialization exactly (732 → 1,407 bits, one state; 1,545 → 2,949 bits, two states with a choice-dependent table). `decide` and `decide +kernel` do not reduce here (well-founded recursion in the serializations) | `C1RCDefsProbe.*` |
| Screen base | the 16-file population: **541 declarations, 173 pairs, 86,076 characters**; no pair has a declaration of the owned file on either side; 12.6 minutes under `nice -n 10` | `screen-base.*`, `screen-population.txt` |
| Lint | `TuringMachine`: 0 FAIL, 68 WARN over 83 files; `NDCodeSimulator`'s is its size | `lint-turingmachine.txt` |

**The copy-hazard search** (the drafting brief's §5). The tree and both open PR heads at drafting
(`lean/phasehost-last`, #156; `complexity/arora-barak-ch7`, #135) were searched for private copies
of what the route proves: a running-maximum monotonization of a time bound, a `workReadsK`
read-order lemma, a replay-table or record-widening identity, and `codePrim_machine`/composition
pipelines. None exists; the compiler and composition idiom recurs in `UHaltMachine`,
`NotTimeConstructible`, `PolyTime` and `CodeSimulator`, which the population covers.

**The lists' tool.** `devtools/seyoon/fillinputs.py` (blob `04164b21`) at the tree, unchanged.

**At issue**, re-run this pre-ship at the issue commit and stage: the probes and the population
into `campaign/fills/c1/inputs/c1-fill-replaycanon/`, `order.txt` as
`campaign/fills/c1/orders/c1-fill-replaycanon.txt`, `base-sorries.txt` and `screen-base.txt` as
`campaign/fills/c1/logs/c1-fill-replaycanon-{base-sorries,screen-base}.txt`, and this table as the
pre-ship log.
