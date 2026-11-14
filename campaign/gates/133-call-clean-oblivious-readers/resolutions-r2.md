# Gate 133 round 2 resolutions for #300

Round 1 audited `829648df28ddfe34af4a7f92a0c0227ba41cec0c` and returned **HOLD** with one major,
G133-01, one minor, G133-02, and notes G133-03 to G133-09 (`findings.md`, SHA-256
`4d7a3a5a467272cde4501991c00c558386056e0f20fc22e220714634d1f8ea4c`). The current PR head is
`4ddce70c45e0a397fbc4d9a25ac925da80e05cda`, against campaign Lean `b313afe522991f2114390952f26ffe7de825bace` (after #301, which touches
none of this PR's files). It changes one declaration after `829648df`.

| Finding | Resolution |
| --- | --- |
| G133-01 · `dataTM_ready` reads the new transport | **Repaired** in `4ddce70c` as proposed. Both passages now read `obliviousScheduleCfg` through its reader: `rw [hrun0, obliviousScheduleCfg_eq_id, id_eq] at hinv` replaces the `rw [hrun0] at hinv; change prepInvariant … base … at hinv`, and `rw [hrun0, obliviousScheduleCfg_eq_id, id_eq]` replaces `rw [hrun0]; rfl`. A focused seal (`focused/` in the carrier: head exit 0 with no errors; round 1 body exit 1 at its `change`) keeps `obliviousScheduleCfg` and every other head of the whole-proof seal irreducible except the two legacy header transports, `obliviousSchedule` and `decorateTM`, through which the unchanged header of `dataTM_ready` elaborates. The head body passes it; the round 1 body, run as a control under the same seal, fails at its `change`. |
| G133-02 · the base comparison counted a guard-only failure | **Corrected.** The base side no longer seals declarations that exist only at head (`scripts/grouped-cmp.py` drops `SOURCE-base.json`'s `added` names from each base seal; the base runtime has no `obliviousScheduleCfg`). The re-run comparison (`seals-cmp-base/`: 10 of 12 owners pass at head, 7 at base, no new failing root) has no guard error. `clockStageCfg_captures` passes at both commits, so the proof improvements are six: `call_run`, `regPos_box`, `cleanTM_run`, `obliviousSchedule_ready`, `obliviousSchedule_halts` and `setupCfg_finish`. The pack and the PR description are corrected. |

## Notes G133-03 to G133-09

Each is accepted within its stated scope. This round's evidence replaces their replay, seal,
control, screen and metadata inputs. The qualification of G133-06 stands: `setupCfg_initializes`
and the header of `dataTM_ready` still reach the unchanged cross-type statements (ObliviousSetup's
private steps; `prepInvariant_run` and `dataTM`'s tape count and state type), as at base.

## Round 2 result (2026-11-14)

Codex returned **CLEAR (0 blockers, 0 majors, 0 minors, 9 notes)**, recorded verbatim as
`findings-r2.md` (SHA-256 `c307470aa51e5db4908745c7dc7c8ba206487ff2a7efb3fd8a411d4a3388a102`). It finds G133-01 and G133-02 resolved; G133-06 keeps the two
disclosed legacy seal roots (`dataTM_ready`'s header, `setupCfg_initializes`'s private steps)
within scope. The other notes need no action. **Gate 133 is closed.**
