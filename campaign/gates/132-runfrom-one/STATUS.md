**Not yet clear to merge: #296.** Gate 132 round 2 (Codex): **HOLD**, one minor (findings-r2.md).
- G132-01, G132-02 and G132-03 are resolved.
- G132-04: `Bidirectional.foldCfg_run`'s `zero` case is a one-step run (duration `0 + 1`) that still
  closes with `runFrom_succ_eq_step, runFrom_zero`; its disposition as outside RO-1 was wrong.
No new soundness defect or failing seal root was found. The repair and a round 3 pack are in progress.
