# Read-only review of the normalized statistical step

Requested by the lead after repeated deep definitional-equality elaboration in seq-zk-a.
No foreign file was edited or copied. No Lean process, checker, or probe was run.

Inspected versions of seq-zk-a/SequentialZK/NormalizedStep.lean:
- SHA256 `a5e3d33ae6ae57da4457315844a5a09f04b670fcc9e177f9c7d71a550cc1d0c5`.
- Latest SHA256 `3b66ca0084824138c5334b18e641e24d588d15f9d9eed716c262ca71e7adb406`.

## Mathematical and type review

No mathematical flaw or circular premise was found. ExecCoins is the product of the
prover's and verifier's coin types; both are function types into Bool, so they are nonempty,
including a zero-bit verifier. The supplied hcoins implies its actual string is empty.
The published real-view and transcript equations therefore expose exactly the input to
normalizePhaseMsgs_of_encode. The prover bound and hcount have the right quantifier/order
for exec_snd_bounded and the canonical-normalization fixed point. The same padding and
prefix are used on both sides, and no simulator shape or efficiency premise is required.

Public probability readers checked in the pinned local source:
- Sampling.lean:133 statClose_iff exposes test-probability differences with explicit seed
  types and common output type.
- Sampling.lean:138 StatClose.abs_uprob_sub_le is exactly this test reader.
- Sampling.lean:174 StatClose.map pulls tests back by post-processing.
- Sampling.lean:202 StatClose.comp_pushesUniform requires a map NEW-seeds → OLD-seeds;
  Prod.fst has the opposite direction for removing an unused coin factor. Direct test
  marginalization avoids building the required inverse singleton-coin embedding.
- Foundations/Probability.lean:175 uprob_fst removes a nonempty unused second factor.
- OneWayFunctions/Basic.lean:50 uprob_congr transports pointwise-equivalent events.

## Elaboration recommendations sent to seq-zk-a and the lead

The first version still mapped and rewrote an entire StatClose at lines77–98. Recommend
eliminating hmapped/hrealSampler/hproduct: apply the target statClose_iff, introduce a
single test T, and apply the ORIGINAL raw comparison to the composed normalization/
prefix/padding test. Rewrite only the first scalar probability using explicitly typed
uprob_congr from the pointwise normalization fixed point, then uprob_fst with explicit β.

The latest version implements this route and has consistent scalar predicate domains.
Remaining locations to identify with immediate markers:
- Line96: dot-reader inference of the raw sampler functions from a transparent StatClose.
  A fully explicit `(statClose_iff rawReal rawSim δ).1 hclose composedTest` removes those
  higher-order implicit sampler metavariables.
- Line105: rewriting inside an arbitrary test predicate T. The direct proof
  `Iff.of_eq (congrArg (fun msgs : List (List Bool) => T (pre ++ (msgs ++ pad))) (hfixed r))`
  avoids rewrite-motive search.
These are plausible hotspots, not diagnosed failures. No current running process was
sampled, interrupted, or otherwise changed by this read-only review.

## Immediate flushed marker proposal

Read the exact declarations in Lean4.25 source: Lean/CoreM.lean:356 provides the IO→CoreM
lift, TacticM is ReaderT/StateRefT over TermElabM and MetaM, Init/System/IO.lean defines
IO.getStderr and Stream.putStrLn/flush. The proposed tactic is:

```lean
run_tac do
  liftM (m := IO) (n := Lean.Elab.Tactic.TacticM) <| do
    let err ← IO.getStderr
    err.putStrLn "NormalizedStep.fixed.begin"
    err.flush
```

This writes/flushed bytes directly, unlike Lean trace messages retained until declaration
completion. It is a source-API-checked proposal, not a separately compiled probe. seq-zk-a
retains exclusive source/Lean ownership and will test its own edits.
