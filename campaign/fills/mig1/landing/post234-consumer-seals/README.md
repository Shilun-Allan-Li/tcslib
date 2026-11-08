# MIG post-234 consumer seals — frozen proposal

The hypothetical combined proposal passes all fourteen complete-header/body Rule 10 seals and all required native probes. The evaluated pushed source pin is `f631647190998272127fcd37b7a5d1e61fac4f3f`; no Lean source, Git state, compiled context, cache, or canonical campaign record was changed by this agent. **Not yet clear to merge: #233.**

`0001-public-reader-body-repairs.patch` changes six proof bodies in four files, preserving every original header. `0002-private-header-carrier-transports.patch` adds explicit public `branchTM_k`/`branchTM_State` transports to exactly two private headers (`timed_start`, `condTM_start`) after the body patch. Root must obtain the user's approval of those literal private-header changes before adopting the second patch. `combined-proposal.patch` is their exact composition. No new public API, import, machine definition, sorry, or axiom is proposed.

Both complete old/proposed forall theorem types are kernel-equal by `rfl` in the transparent prior context. The equality scaffolds report only `propext`, `Classical.choice`, `Quot.sound`; two unused `hD` binder warnings occur only in each equality scaffold. They preserve the exact endpoint and hypotheses. The combined full-header seals keep `branchTM` opaque and pass; there is no type-shape guard exclusion.

| Owner | Targets | Native seconds | Full seal seconds | Changed warnings |
|---|---:|---:|---:|---:|
| Catalog | 2 | Root Native2 (unchanged source) | 19.76 | 0 |
| Loop | 3 | 14.26 | 14.72 | 0 |
| Primitives | 6 | 17.08 | 17.98 | 0 |
| Wrappers | 1 | 3.00 | 3.41 | 0 |
| Composition | 1 | 2.25 | 2.66 | 0 |
| Simulation | 1 | Root Native2 (unchanged source) | 3.30 | 0 |


The changed regions have zero errors, zero declaration-sorry warnings, and zero linter warnings in both final native and sealed forms. Full-file legacy warnings are recorded unfiltered in `FINAL-CHECKS.json` and raw logs. All 14 selected roots and 17 generated descendants (31 objects total) have only the standard axiom set. This is bounded selected-region evidence; root separately owns the complete MIG scope census and final gate.

The six repairs are `emCall_eval_first`, `emCall_right_endpoint`, `lenStart`, `splitEmbed_cut`, `timed_start`, and `condTM_start`. They replace explicit or implicit foreign definition reads with existing public initial/field/step/run equations. `splitEmbed_cut` uses `Cfg.inputSymbol_of_zero`, `Cfg.inputSymbol_of_end`, and `Turing.inputSymbolInner`; it adds no import of the out-of-scope `Cfg.inputSymbol_congr`. `Option.map` is a non-TCSlib definition and is explicitly classified separately. Same-home definitions/local lets remain permitted. The parent’s f631 implicit-`x` fix in `fwdMap_launch` is retained byte for byte.

Controls cover 116 owner-context guard occurrences and 36 distinct ordinary TCSlib definitions. Each has two exact paired identities (232 total): native identities are kernel-added checked declarations; the same goals fail with the matching `rfl` diagnostic under the exact guard list. The strict data checker verifies ordered identity multiplicity, kernel names, source equality except the guard line, exit/error counts, and every input/raw hash. It rejects all nine synthetic corruptions. Every original guard remains effective. `incFixed` and `pairDecode` use documented constructor point/function identities after generic whole-definition unsealed calibration failed; no unsafe transparency/reducibility workaround was used. Abbreviations/projections are disclosed compiled-kernel exclusions, with no claim that irreducible controls work on them.

Each seal compiles a full source file, with guards scoped around only the changed declaration spans. Removing every prefix/suffix plus the metadata appendix recovers the full proposed source exactly. The small `SealScope` probe proves default-simp removal and local irreducibility restore after the section. All explicit `simp`, `simpa`, `rw`, `dsimp`, `unfold`, and related forms were rechecked; no ordinary foreign TCSlib definition occurs as an unfolding argument. Fresh final selected metadata follows own ordinary definitions and foreign theorem statement types, stops at imported theorem proof values, and finds every reached ordinary foreign definition covered by the effective guards. No theorem proof value was rendered.

The sole imported context was root-confirmed PASS12 `S/oleans-mig-post234-native2`, a complete MAC5 clone. All 895 TCSlib `.olean` path/size/SHA rows match before versus after every own probe. Invalid native1 was never used. All runs use the mandated `leanelab.sh`, plain mode without compiled output, local cap 3/machine cap 5, and one own Lean at a time. `source_head` in the run records is the imported/baseline pin; each hypothetical probe’s actual contents are separately bound by its input SHA.

`SOURCE-BINDINGS.json` captures every TCSlib source via `git show f631…:path`, never records-worktree Lean bytes. Complete before/body-only/combined source captures and all fourteen unfiltered proof blocks are included. Forward and reverse independent hunk application validates all three patch files. All other bytes, imports, machine definitions, and fourteen docstrings remain exact.

`RUN-INDEX.json` identifies every current check/control and retained earlier attempt. `evidence/runs/<label>.out` is the complete raw output; `-driver.out` files are terminal-display excerpts and are not the raw authority. Executed Lean inputs are retained as `.lean.txt` with matching hashes. Unrun generated probes remain data and are not claimed as checks. The initial e3 static proposal, failed preparation assertions, generic recursive calibrations, unsupported `local -simp` syntax test, original whole-header failures, branch-shape-open failed diagnostics, and later repaired attempts are all retained and explicitly superseded. The branch-shape-open diagnostic inherited stale 21/18 count labels while actually omitting one guard; it is not used in any pass count.

Own Python helpers are archived as data with their complete stdlib import inventory; all ran with `python3 -I`. The managed wrapper is included byte-exact. `env.sh` is hashed without copying environment contents. `graph.py` was not used by this task. The archived scripts are review data and were not executed from the packet.

Root owns user approval of the two private-header literals, actual scoped source adoption and push, fresh complete owner/AX/seal/replay evidence, gate118, readiness, ledger, and publication. These hypothetical successes do not mark those steps complete.
