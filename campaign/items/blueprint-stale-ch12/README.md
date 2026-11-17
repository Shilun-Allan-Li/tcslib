# Stale chapters 1–2 blueprint entries (Seyoon, 2026-11-17: delete in a later small PR)

Gate 157 (W5) found 712 blueprint entries for declarations that earlier campaign refactors removed,
outside the chapters 3–4 scope (`campaign/gates/157-w5-blueprint/evidence/ORPHANS-CLASSIFIED.json`).
This change deletes them.

- **Deleted:** 712 entries (`DELETED.json`, entry by chapter): TuringMachine 583, CookLevin 64,
  ClassNP 62, and one each in ClassP, GraphTheory/Core and Randomized. Their names were dropped
  from other entries' `\uses` lists (257 references).
- **Checked against Lean:** `StaleCheck` imports all 898 modules of snapshot `oleans-c179c8`
  (campaign Lean `179c8c9c`) and looks up each of the 712 names, with or without a private
  prefix. **0 of 712 exist** (`StaleCheck.out.txt`: `TOTAL|712|0`).
- **Validation** (`VALIDATE.txt`, `scripts/blueprint_validate.py` against the refreshed graph):
  - 0 dangling `\uses`, 0 duplicate bindings, 0 `\uses` cycles;
  - coverage unchanged at 18,010;
  - orphans down from 1,572 to 860. The remaining 860 belong to declarations in modules that no
    root import reaches, so they are never compiled.
- No Lean change.
