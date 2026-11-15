# Lead authorization for targeted proof debugging

Request:

NormalizedStep check01 is genuinely active (Lean11822→bash11814→time11813→wrapper11806), CPU100%, RSS3,871,008 bytes at2:51. Headroom recheck6.011GiB, no E-RES. Sparse one-second sample (13.95MB) identifies Simpa.evalSimpa + whnf; the module has exactly one simpa, simpa only [hfixed] using hmapped for hproduct. Concrete fix: prove an explicitly typed equality between the TWO REAL sampler functions using funext r; exact congrArg (fun msgs => pre ++ (msgs ++ fillers)) (hfixed r), then rw [hrealSampler] at hmapped and use it directly. This avoids trying to match the real fixed-point rewrite against arbitrary simulated output. Request targeted own-process SIGINT for11822 after source/sample preservation, then apply this single-block rewrite. No timeout or other job touch.

Lead response (verbatim):

Authorized targeted proof-debugging interruption: preserve source/sample/proc/headroom record, verify exact11822 child chain, SIGINT ONLY that own Lean, let wrapper flush/release, then apply the explicit sampler-function equality you diagnosed and recheck. Record third diagnosed unification interruption across this unit transparently (c ErrSoundness, a StatisticalRecursion, a NormalizedStep); no E-RES/timeout. Use explicit typed function equalities before transport throughout remaining proofs to avoid repeating broad simpa/implicit higher-order unification.

Authorization is the lead’s under Seyoon’s best-judgment exception; no separate direct user reply is claimed. The lead identifies this as the third diagnosed proof-unification interruption across the unit.
