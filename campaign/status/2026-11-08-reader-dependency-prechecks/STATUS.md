# Prerequisite and consumer placement, before any source merges

The eight recorded PR pairs produce clean prospective Git merge trees, including the
InputLength and Seam reader branches sharing Simulation, and gate130 and #242 sharing
ConfigCount. This is a source-only check at the exact captured heads, before the final
Seam documentation follow-up, not an integrated merged-tree replay or merge approval.

The five existing consumer patch files (InputLength, Fresh/Prepared, MARMTime, Startup,
and the paired SingleTape repairs) dry-run cleanly both on the current consumer PR source
and with #245's proof-only Hardness cleanup. No patch was applied. Their separate
hypothetical native/opacity evidence stays at its actual source/objects. After the
provider gates close and Seyoon merges the relevant PRs, bind actual source, apply
only the approved mechanical scope, then do the complete required replay, guard,
freeze, copy and follow-up gate work.

- #241/gate121: gate129 supplies InputLength readers and gate131 supplies the Seam
  right transition for the prepared Fresh/Prepared repairs. Already approved
  Hardness CfgFacts import and the current mechanical repairs remain separate.
- #242/gate122: gate130 supplies the readers for MARMTime, startup and the two
  SingleTape repairs; the shared gate121 proof changes also need proper integration.
  Call.call_run, Clean.cleanTM_run and clockStageCfg_captures remain separate open
  governance fronts. None is cleared by reader approval, placement or prior selected13 PASS.
