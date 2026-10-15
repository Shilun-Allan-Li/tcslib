# §13d G1 gate — resolutions (CLOSED, round 1)

## Round 1 (2026-10-10): 0 blockers, 0 majors, 2 minors, 9 notes

Findings verbatim in `audits/s13d-g1-findings.md`. Pack:
`audits/s13d-g1-pack.md`, bundle `audits/s13d-g1-bundle.md`. The auditor
reconstructed all four base files from the patch and reproduced every
after-file forward from the sanctioned substitutions, byte for byte (finding 3).

| Finding | Disposition |
|---|---|
| 1 (minor): four docstrings keep binary wording ("emitted bit", "original source bit", "that bit", "changed bit") on generalized declarations | **Swept on the PR branch** (`s13d/g1`), comment-only: "symbol" for `bufferTape_append`, `embedSilent_apply` and `catalog_copy_forward`; "cell" for `catalog_write_middle`. The remaining "bit" wording in Catalog sits in its Bool-specific Part 2, where it is correct |
| 2 (minor): Seam's module documentation and `seamCompTM`'s docstring were framed around `Cfg.ofWords` seams | **Swept on the PR branch**, comment-only: arbitrary-alphabet, arbitrary-configuration composition is described first, with the canonical `Cfg.ofWords` seams as the `Bool` specialization |
| 3–6, 8–10 (notes) | Substitution fidelity, the input binders, definition bodies, the 30 instances, the retained `Bool` declarations, duplication and the logs all confirmed. No action |
| 7 (note): no hidden `Bool` dependence; the `Fin 7` pre-ship check covers the machine's type, not the whole contract family | Carried to the §12.8/§13d statement phases, whose probes instantiate the contracts at rich alphabets (the §12.8a probe already does, against the G1 tree) |
| 11 (note): archive integrity and execution claims are attestations | Pack practice adopted (see `audits/s12-counter-resolutions.md`, F2) |

**Gate CLOSED.** The doc sweep is comment-stripped identical in all four
files, and the four modules re-check at 0 errors in the side-branch tree. PR #15 is
ready for the user's merge. After the merge the maintainer replays the merged
campaign tip, and §13d continues with the G2–G4 statement phase (G2 centered
on `scanTM`, decision O3).
