# Gate 95, round 2: the seal and the controls on the repaired blob (finding 2)

The repaired head is `10c015177fde0f9f2b020c010cf44f0f3b3dd37f`; `NDNormalForm.lean` there is blob
`ad4202caae768181dfb38f0dec71fd293543c165`. Every file was elaborated on 2026-11-05 with
`devtools/seyoon/leanelab.sh` against the snapshot `oleans-cloud0` (the campaign at `dfed8b1f`'s
Lean tree), which holds the seven imports' closure; none of the files imports `NDNormalForm`.

- **Candidates** (`NFCandAudit.lean.txt`, the blob plus the review's own filter as a command;
  `NFCandAudit.out`): 366 raw; without compiler auxiliaries (`_sizeOf_*`, `._flat_ctor`,
  `._sunfold`, `._unsafe_rec`), **277** (`cand-lean-filtered.txt`), identical to the textual list
  the generator used (`seal-candidates-textual.txt`). Against round 1's 257: 20 new, 0 dropped
  (`seal-set-delta.txt`): 19 from `Build/Contract/Basic` (`Turing.Segment`, `HeadBox`, …) and
  `Turing.FinTM.stateEquivFin`.
- **Sealed copies:** `NFSeal.lean.txt` (round 1's placement, before the continuation's section) and
  `NFSealWhole.lean.txt` (the seal over the whole file, so also over `nf_pack`'s edited `hinit`):
  **0 diagnostics** each (`NFSeal.out`, `NFSealWhole.out`, empty).
- **Generic controls** (`NFSealCtl_*`): unsealed `CONTROLS 277: rfl closes 267, eqn closes 276`;
  sealed `rfl closes 5, eqn closes 5`.
- **Source controls** (`NFSrcCtl_*`: round 1's 41 plus `Turing.Segment` and `Turing.HeadBox`,
  `src-controls-new.lean.part.txt`): unsealed 0 errors (all 43 close); sealed 43 errors (all 43
  fail).
- **Summary** (`summary.txt`): 272 of 277 discriminated by the generic controls; the five that
  close sealed are derived instances (`instFintype…Phase` ×4, `instInhabitedCfg`), discriminated
  by source controls, as in round 1. So all 277 are discriminated.
- Generator: `mkseal_nf.py.txt` (the gate's `mkseal.py`, re-anchored for the repaired blob), with
  the textual index tool `tcsdefs.py.txt`.
