External audit of PR #116, core specification API, round 2 — 2026-10-16.

The bundle's SHA-256 is **559c64bbaba7a045404872a24704b2708710833867416573a6fb998e1827592b**, exactly as commissioned. It contains **89 unique sections**. I read `audits/core-api-r2-pack.md`, `audits/TEMPLATE.md`, `policy.md`, and `workflow.md` in that order, followed by the prior findings, resolutions, repair evidence, and relevant source.

**Both majors and all three minors from round 1 are closed.** No new findings were identified; the findings table is intentionally empty. The checks and definition restatements supporting that result follow.

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

This is a source-and-evidence audit of the supplied packet. Lean is not installed in this environment, so I did not independently elaborate the sources. I independently checked patch reconstruction, preserved code, consumer identities, axiom-log coverage, duplication screens, lint changes, replay accounting, and static admission counts for the included source files. Elaboration results below are the supplied execution evidence.

1. **Finding 1: closed under the no-unfolding rule.**

   `MultiTapeTM.runFrom_with_q₀` (`Finite.lean:232`) says that replacing a machine's initial-state field preserves its run from every explicitly supplied configuration, for every natural-number duration. It quantifies over arbitrary tape counts, alphabets, and state types; no finiteness, positivity, liveness, or halting assumption is added. This follows from the underlying definitions: `step` uses the transition table, and `runFrom` iterates `step`; neither uses the initial-state field.

   `MultiTapeTM.initCfg_with_q₀` (`Finite.lean:239`) says that initialization of that replacement machine is exactly `Cfg.init` at the replacement state. Its statement matches `initCfg`'s definition.

   Consequently, a consumer obtains the following equality by first rewriting with `initCfg_with_q₀`, then with `runFrom_with_q₀`:

   ```lean
   ({ tm with q₀ := q }).runFrom
       (({ tm with q₀ := q }).initCfg x) t
     = tm.runFrom (Cfg.init q x) t
   ```

   Substituting `tm := Complexity.LogProg.cleanTM M q₁` and the replacement state `.init q` gives exactly the starting configuration of `cleanTM_run`. The consumer can transfer its halting, output, blank-tape, restored-head, and intermediate head-envelope conclusions through this equality. It never needs the value of `(cleanTM M q₁).q₀` or the body of `cleanTM`.

   The same equality applies to a host composite restarted at its chosen entry state. It transfers every time-indexed configuration, hence the first-exit and silence clauses. Visited-set facts transfer through the already-published `mem_visitedByTapeHead_iff`; U2-S can also obtain its space bound directly from `spaceUsed_le_mul_succ`. Resetting the existentially chosen machine's initial state changes no frozen target statement.

   Both copies of the U2-S draft contain the repaired construction and cite the restart pair. `CleanRestartProbe.lean.txt` uses identical local stand-ins for the pair, then only the published `cleanTM_run` to establish its consumer result; its supplied log reports exit 0. Separately, `FiniteAx.lean.txt` is byte-identical to the repaired `Finite.lean` up to its appended check/axiom commands. Thus the probe establishes the proposed route, while the other evidence checks the final declarations. Neither repair patch touches Hydroxyi's files.

2. **Finding 2: closed under the no-unfolding rule.**

   The relevant definitions, restated from their bodies, are:

   | Definition | Mathematical meaning |
   |---|---|
   | `FinTM.ComputesInTime` | There exists a space witness for the initialized run at the specified time; the run is halted with exactly the specified output. Absorbing halting makes this a time upper bound. |
   | `FinTM.ComputesFunInTime` | Every input is computed within the time bound evaluated at that input's length. |
   | `FinTM.ComputesFunInTimeVia` | For every source-alphabet input, the machine computes its embedded output on its embedded input, with the bound evaluated at the source input's length. |
   | `FinTM.Computes` | Every input has some finite computation time; that time may depend on the input. |

   These meanings agree with the docstrings. The three new equivalences reproduce their definitions exactly, including the quantifier order, both `List.map` applications, and the length argument. In particular, `computes_iff` retains `∀ input, ∃ t`.

   For introduction, apply `(computesFunInTime_iff M f T).mpr`, introduce the input, and apply `computesInTime_iff` in the introduction direction to the halting/output facts. For elimination, apply `(computesFunInTime_iff M f T).mp` to the hypothesis, specialize to the desired input, and apply `computesInTime_iff` in the elimination direction. This supplies both directions needed by U2-S without reducing either imported predicate. Taking a maximum of the cleaned machine's witness times over binary strings of each fixed length is compatible with this interface and the draft's existing route.

3. **Findings 3–5: closed.**

   | Earlier finding | Independent check |
   |---|---|
   | 3: stale consumers | `StepBlockForward.lean` is the 555-line source with Git blob prefix `60e29249`, a proved `exists_forwardLoopTM`, and an actual proof citation of `visitedByTapeHead_add_subset` at line 525. `ZoneRebalance.lean` is the 571-line source with blob prefix `9deb85fb` and 18 private declarations. These match the reviewed post-merge consumers. The replay includes both, with admission counts 0 and 2 respectively. |
   | 4: missing axiom print | `serializeK_eq` is now printed with `[propext, Quot.sound]`. Comparing the patches with `axioms.log` accounts for all 46 explicit round-1 additions/relocations and all five round-2 additions: 51 distinct names, 52 print lines because `zoneCapacity_eq` is repeated. Every print uses only the standard axiom set; none contains `sorryAx`. |
   | 5: vendoring inventories | `Configuration` lists its generated fields and reading equations; `Deterministic` lists its equations, the visited-set relocation, and the earlier `timed_input_bound`. Both distinguish additions from preserved upstream content. `Finite` no longer calls the modified vendored files unmodified or byte-comparable. These headers accurately describe the repair and included API additions; I did not independently compare the upstream repository. |

4. **No behavior or frozen-statement change from the repair.**

   Both repair patches have the SHA-256 values recorded in the review. I reversed the optional patch, then the required patch, successfully. The reconstructed round-1 Git blob prefixes are `52aa83c` (`Finite`), `b609dc9` (`Deterministic`), and `2a0820d` (`Configuration`); the repaired prefixes are `c923402`, `5b3f881`, and `b40d0ea`, respectively. All match the patch indices.

   After stripping comments and removing exactly the five new theorem declarations, the repaired code equals the reconstructed base code, ignoring whitespace. The repair therefore changes no existing definition, theorem statement, proof, import, or attribute. It introduces no admission or new `simp` registration. This comparison concerns the repair patches; the separately identified campaign merges also bring in the already-recorded consumer proofs.

5. **Evidence: consistent, with the following verification boundary.**

   | Evidence | Result |
   |---|---|
   | Supplied elaboration logs | Exit 0 throughout. `Finite`: 2 warnings before and after; `Configuration`: 3; `Deterministic`: 0. The consumer probe has no diagnostic. |
   | Copy-text screen, independently rerun | Both outputs reproduce the supplied files byte for byte: 50 screened declarations, 10 pairs, 728 reproduced characters, before and after. The five short new proofs are below the screen's body-length threshold; direct inspection finds no copied proof family. |
   | Lint check 8 | The supplied warning sets change only by removing `Finite`'s three uncovered predicate names: 71 to 70 warnings, no new warning, zero failures. Independently running the check-8 logic on the affected sources confirms that change. |
   | Replay log | Exactly 320 distinct module rows, in the supplied order, all with exit 0 and errors 0; admission counts sum to 94. Both repaired consumers are present. |
   | Static admission comparison | All 19 included Lean source files agree with their replay rows, totaling 12 admitted declarations. The supplied whole-tree summary reports 320 modules, zero mismatches, total 94. |

   The other 301 module sources and #112's per-module replay log are not included. The whole-tree static comparison and the unchanged counts on 85 shared modules therefore remain maintainer execution attestations, rather than independently reproduced results of this audit. This does not contradict the supplied evidence or leave a demonstrated defect in the repair.

6. **Records: consistent.**

   The round-2 pack and resolutions identify the correct five additions, repaired draft, merged consumers, appended axiom prints, and stacked replay head `93c4c630`. Their required merge order remains #112 before #116. The older `NOTES.md` and round-1 pack describe historical checkpoints and should remain historical. The U2-S document is explicitly an undispatched draft with placeholders; this audit closes the core API gate, not the eventual U2-S fill or its dispatch checks.

Adversarial checks:

- **Zero tapes and empty input:** the restart pair imposes neither a positive tape count nor a nonempty input; the configuration identities still hold. `cleanTM_run` likewise includes the zero-tape case.
- **Zero duration and already-halted configurations:** the run-preservation theorem retains the entire supplied configuration at time zero, and preserves the absorbing halted run at every duration. It imposes no hidden live-state hypothesis.
- **A zero time bound:** specializing `computesFunInTime_iff` to the empty input would require a zero-step computation when the bound at zero vanishes, which `not_computesInTime_zero` excludes. The characterization does not admit a vacuous zero-time computer.
- **A nonsurjective symbol embedding:** `computesFunInTimeVia_iff` still quantifies only over mapped source inputs; it does not silently require correctness on every target-alphabet string.

PASS — 0 blockers, 0 majors, 0 minors, 0 notes.
