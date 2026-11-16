# GSW phase-5 statements: evidence

Branches (local, not pushed), from `523d80d2d4dd8e4ed6799358831e5b3806c6187b`:
- `stmt/dagcircuit-readers` `94eae71b779c4ca0f76c138d699f4d737dbd6cee`: `DAGCircuit.lean` +94 lines (Q2): readers
  `DAGGate.depth_eq`, `DAGCircuit.{depths_eq, depthAt_eq, depth_eq}`; `DAGGate.getD_lt_depth` and `runWith_rel`, both
  **proved**.
- `stmt/gsw` `48d796a8a68cd50897047f01825a8132dd19e8d8` on top of it: `8ce56b0d0b5175e6001e1b18a6777f07194e944d`
  (modules and facades) and the exports commit (`Hashing/SIS.lean`, `TCSlib.lean`).

Evidence: `$SP/dl-review/stmt-gsw.zip`, SHA-256 `4b144e17683c3675088a620796bd21e9963d8a43a489145208efda9c5c1f85d3`
(`PROVENANCE.txt`, `SHA256SUMS`, `unchecked-fixes.md`, `questions-statement-changes.md` inside; not committed).
Method as for the pairing statements (`../../pairings/statement-phase/EVIDENCE.md`): one Lean process at a time on
`$SP/dl-oleans-2` only, `scripts/lean_check_tree.sh`, no `lake build`, `python3 -I`.

| Step | Result |
|---|---|
| Files | `AdvancedEncryption/Homomorphic/GSW/{Gadget 204, Noise 235, Scheme 215, Eval 207, Security 217, Symmetric 111}`, `Hashing/SIS/Columns` 89; facades `AdvancedEncryption` 25 (imports only `Homomorphic`), `AdvancedEncryption/Homomorphic` 22, `Homomorphic/GSW` 35; widths at most 100 |
| Build | 33 closure modules rebuilt (21 stale base); final sweep 12/12 rc 0, 0 errors; only the 35 target `sorry`s (Gadget 5, Noise 12, Scheme 6, Eval 4, Columns 2, Security 4, Symmetric 2) |
| Axioms | 285 declarations + 56 auxiliary constants (GSW and Columns 124 + 8); `sorryAx` in exactly the 35 targets; all else standard |
| `UNCHECKED` | 23 markers, all verified as drafted and removed; 4 other fixes (2 statement texts, meaning unchanged: QS1 `Matrix.of` in `hashColumns_eq_mul`; QS2 `GSW.mul` in `Encrypts.mul_bit`/`mul_le`; 2 sketch citations); the facade's missing `-/` |
| Rule 10 | whole-file seals A/B, strict and coe, `-DmaxErrors=0`, 12 files: 48/48 pass; controls: 5/5 sealed negatives fail once each, unsealed and positive pass |
| Lint | `style_lint.py` 0 findings (12 files); `campaign_style_lint.py --check8b` 0 FAIL / 0 WARN (AdvancedEncryption, Hashing); DAGCircuit's check-8 WARN loses `depths` |
| Root `TCSlib` | 278 modules rebuilt (DAGCircuit and Hashing.SIS downstream, GSW): 278/278 rc 0 |
| Tree | snapshot `457ba704d26757307f14131aa534929ffd70d30a732b0c744b104ca3fc96a15f` before and after (byte-identical) |

Open: GSW13 ingestion (Q14) is not in these branches. The records branch advanced to `a32ad0df` during the job
(#318, #319, #323): all three branches merge cleanly; the only closure overlap is #323's `isFaninTwo_iff` in
`DAGCircuit.lean`, a disjoint hunk.

**Filed (Gate 41, 2026-11-16).** The archive is now in the records at `evidence/stmt-gsw.zip` (SHA-256
`4b144e17683c3675088a620796bd21e9963d8a43a489145208efda9c5c1f85d3`), byte-identical, with its inner manifest
`evidence/SHA256SUMS` (545 files, all verified) and `evidence/PROVENANCE.txt`.
