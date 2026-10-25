# Megafill D's triage evidence (drafting base `fe666d60`), 2026-10-25

No candidate was ready, so this folder holds the triage's evidence and the dossiers of the two
nearest candidates, not pre-ships of drafted briefs. Every Lean run went through
`../megafill-D-env-fe666d60/tools/run_probe.sh` (a copy of the record under the clone's ignored
`.lake/probes/`, checked by `scripts/lean_check_tree.sh`), one at a time, against the bootstrap of
`../megafill-D-env-fe666d60/`. Each `.out` begins with the record's SHA-256 and ends with its `MEM`
line and exit status.

| Run | Record | Result |
|---|---|---|
| A1's statements | `a1/A1ApiProbe.lean.txt` | 7 lemmas (`a1_` names) by `Iff.rfl`/`rfl`/a 4-line induction: 0 errors, 0 warnings; axioms within `[propext, Classical.choice, Quot.sound]` |
| `spaceConstructible_poly`: the overlay | `scp/SavitchOverlay.lean.txt` (one import added) | exactly its two sorry warnings (overlay lines 82, 115) |
| `spaceConstructible_poly`: import probe | `scp/SCPImportProbe.lean.txt` | 21 checks of 21 names: 0 errors, 0 warnings |
| `spaceConstructible_poly`: route probe | `scp/SCPRouteProbe.lean.txt` | **the target proved** as `scp_route`, sealed over 12 TCSlib definitions, with A1 as local stand-ins: 0 errors, 0 warnings; axioms `[propext, Classical.choice, Quot.sound]` |
| `spaceConstructible_poly`: seal controls | `scp/SCPSealControl.lean.txt` | 12 controls: none fails unsealed; each fails sealed (12 errors, lines 52–70), the `SpaceConstructible`, `ComputesInSpace`, `logSpace` and `transduce` ones being the blocker |
| `spaceConstructible_poly`: duplication probe | `scp/SCPDupProbe.lean.txt` | `exact?` finds nothing for the tail transducer, the copying-state lemma or the length bound; it finds `MultiTapeTM.spaceUsed_le_mul_succ` for the space-from-time step, which the route cites |
| E-Q: the overlay | `eq/NTimeDiagonalizerOverlay.lean.txt` (eight imports added) | exactly its two sorry warnings (overlay lines 278, 343) |
| E-Q: import probe | `eq/EQImportProbe.lean.txt` | 81 checks of 81 names: 0 errors, 0 warnings (a first run on four imports found 14 names outside that closure; the overlay was widened, `eq/EQImportProbe.out` is the final run) |
| E-Q: route probe | `eq/EQRouteProbe.lean.txt` | 6 lemmas (the witness through A1's stand-in, the timeout deduction, the stop rule, the stage, the passed rung's operands, the ledger), sealed over 5 definitions: 0 errors, 0 warnings; axioms within the standard three |
| E-Q: seal controls | `eq/EQSealControl.lean.txt` | 6 controls: none fails unsealed; each fails sealed; control 1, the eliminating `obtain` on `TimeConstructible`, fails with "`rcases` failed: `hf : TimeConstructible f` is not an inductive datatype": the blocker |
| E-Q: duplication probe | `eq/EQDupProbe.lean.txt` | `exact?` finds nothing for any of the five statements |
| E-D: import probe | `ed/EDImportProbe.lean.txt` | 20 checks of 20 names: 0 errors, 0 warnings |

Also here: each dossier's order list, Mathlib roots and base sorry set from `fillinputs-overlay.py`
(megafill C's overlay variant of `devtools/seyoon/fillinputs.py`, copied unchanged) on its overlay
(`scp/`: 183 modules, 54 roots, 27 sorried declarations in 10 modules; `eq/`: 81 modules, 34 roots,
23 in 12), the owned subtrees' lint lines (`scp/lint-spacecomplexity.txt`: 0 FAIL, 82 WARN over 107
files; `eq/lint-diagonalization.txt`: 0 FAIL, 2 WARN over 5 files), and `evidence/`: the triage
greps, the open-PR searches and the scan of MIG-1's moved proofs.
