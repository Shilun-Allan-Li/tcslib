Two targeted non-simp owner equations suffice to repair the complete held `Turing.ClockHost.startup` proof. This is a viable private hypothesis awaiting Seyoon's public-API decision. No source branch or canonical record was changed.

The proposed readers stay in the already imported `TCSlib/Complexity/TuringMachine/Build/NDClockHost.lean`. `bootCfg_of_halt` exposes only a halted yardstick configuration's rewind assembly. `runCfg_initCfg` exposes only the attempt assembly of `A`'s initial configuration, at an arbitrary yardstick position. No blanket `hostCfg` field API is added. The existing `yard` is a reducible abbreviation and needs no extra API. Both new reader proofs use only standard `propext`/`Quot.sound`, have no admission and are non-simp.

```lean
/-- A halted yardstick configuration is the rewind configuration with its output on the
extra tape and with the attempt bank blank. -/
theorem bootCfg_of_halt (c : Cfg S.k Bool S.State x) (hc : c.state = none) :
    bootCfg (A := A) c =
      hostCfg (some .rew) c.inputPos c.workTapes c.workTapePos (fun _ _ => none)
        (fun _ => 0) (bufferTape c.output) c.output.length [] := by
  simp only [bootCfg, hc, Option.map_none, Option.getD_none]

/-- The attempt configuration of the initial machine has the initial control and input
position, a blank attempt bank, and no captured output, at the given yardstick position. -/
theorem runCfg_initCfg (j : ℤ) (sT : Fin S.k → ℤ → Option Bool) (sP : Fin S.k → ℤ) :
    runCfg m (A.tm.initCfg x) j sT sP =
      hostCfg (some (.run (some A.tm.q₀) none)) 1 sT sP (fun _ _ => none)
        (fun _ => 0) (yard m) j [] := by
  have hw : (A.tm.initCfg x).workTapes = (fun _ _ => none) := by
    funext i z
    rw [NDTM.initCfg_eq, Cfg.init_workTapes]
  have hp : (A.tm.initCfg x).workTapePos = (fun _ => 0) := by
    funext i
    rw [NDTM.initCfg_eq, Cfg.init_workTapePos]
  rw [runCfg, hw, hp]
  simp only [NDTM.initCfg_eq, Cfg.init_state, Cfg.init_inputPos, Cfg.init_output, capOf]
```

The original complete producer and consumer files are byte-exact at both MAC8 `9b5dcf46408db681bcbc721930ef2203fa6bc47d` and FH13 `f3c8c050ef98375bc237c72bde74f83d33833374`. All original definitions, machines, imports, declaration headers, attributes and other declarations remain literal. The complete startup doc/header is unchanged. The candidate reads `hS` through existing `computesInTime_iff`, obtains its strict first-halt cut and endpoint from existing `exists_first_halt`, transports state/output with that endpoint, then cites `initCfg_eq_bootCfg`, `boot_run`, the proposed halted-boot equation, `rewind_run`, `moveInputPos_inLeft` and the proposed initialized-run equation. The old selector and final foreign-definitional `rfl` are removed. No mathematical fill or gate129/core proposal is used.

| Actual check | Result | Evidence |
|---|---|---|
| Complete producer and consumer native | Both PASS, exit0/errors0/admissions0 | `runs/ndclock-owner-native1/`, `runs/startup-owner-native1/` |
| Complete two reader declarations sealed | PASS,1 and3 fresh ordinary foreign heads; live witnesses | `runs/proposed-readers-sealed2/`, `NDReadersSealed.lean.txt` |
| Complete startup declaration sealed | PASS,12 fresh ordinary foreign heads; live witness | `runs/startup-full-target-sealed2/`, `StartupSealed.lean.txt` |
| Guard effectiveness |26 fresh kernel-checked positive identities;26 matching intended sealed failures, no unexpected error | `CONTROLS-CHECKS.json`, both full raw logs |
| Exact selected metadata | Startup full type/universes exact BASE; standard3 AX unchanged; both new APIs absent BASE/non-simp/standard2 AX;2 HEAD raw runs byte-exact | `SELECTED-CHECKS.json`, `SELECTED-TYPES.md`, all3 raw runs |
| Explicit argument review |16 nonlocal simp/rw arguments are theorems; the3 definition arguments are owned by the new readers' own source | `EXPLICIT-ARGUMENT-CHECKS.json`, complete source rows |
| Imports and physical context | Existing9-file TCSlib closure acyclic and BASE/f3 byte-exact; no import additions; full MAC8 clone | `IMPORT-GRAPH.json`, `IMPORT-ROUTES.json`, complete3-phase source captures |
| Objects | Original895 unchanged; private895 changes only the2 freshly compiled owner outputs | `OBJECT-CHECKS.json`, all full maps and3 independent MAC8 anchors |

The consumer's12 guarded definitions are `FinTM.ComputesInTime`, `NDTM.runWith`, `ClockHost.hostTM`, `NDTM.initCfg`, `ClockHost.runCfg`, `MultiTapeTM.runFrom`, `MultiTapeTM.initCfg`, `ClockHost.bootCfg`, `ClockHost.hostCfg`, `FinTM.bufferTape`, `moveInputPos` and `ClockHost.inLeft`. The new readers additionally bring `Cfg.init` into the13-head union. Active definition simp-unfold rows are removed in each exact scope. Controls bind the union in the complete compiled consumer context; each proof uses its recorded1/3/12-head set. No foreign TCSlib/Core/Mathlib definition is passed explicitly to simp/rw/unfold; owned `bootCfg`/`runCfg`/`capOf` reads in their owner are permitted. No unsafe opacity override is used.

The bounded metadata closure includes each selected full type/value, reached constant types and recursive own definition-helper values. It stops at other theorem proof-values and foreign definition values. Earlier phase proofs and preceding `ClockReady`/reset proofs remain unsealed context; this packet does not clear their implementations or claim unrestricted theorem-value closure. The imported phase contracts themselves were already published. Existing initialization equations close the new owner reader without a further API gap.

The pre-proposal search retains all current1003 source candidates plus all5408 raw matches across captured428 available refs/298 distinct commit heads, reducing to52 inspected path/line/source rows. The existing boot/rewind/attempt contracts and current explicit reads occur, but no equivalent halted-boot or initial-run assembly reader was located. This is enumeration plus source inspection, with no remote fetch or whole-library semantic absence claim.

All12 own Lean helper invocations completed sequentially through the approved wrappers, local3/machine5 shared locks, nice10/j4. No native or sealed candidate failed. Two final guard runs explicitly match the already executed controls’ `smartUnfolding=false` and `maxRecDepth=4096` settings; earlier passing guard contexts remain preserved under their original run names and `preparation/seal-context-v1/`. One initial Python source-writer attempt failed to parse before executing because of nested source-string delimiters; its error and disposition are preserved in `preparation/`. The negative-control run intentionally exits1 with exactly26 expected errors. No screen or downstream replay ran.

`API-only.patch` and `consumer-only.patch` are independent exact patches against the f3 whole-source captures; source/body/doc freezes and hashes are in `SOURCE-FREEZE.json`. Root can bring the exact2 APIs for Seyoon's decision, then decide source PR/gate/current-tree integration if approved. This packet does not close122 or acknowledge/retire any other held debt. The private project and whole compiled clone remain outside this evidence packet; all source captures, helpers, actual commands/logs, source/object maps, toolchain/package pins and anchors needed to review the executed claim are inside. Actual helper paths require rebasing for a different temporary layout; no external distribution of the physical snapshot is claimed.
