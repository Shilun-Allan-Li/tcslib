# Execution notes

- The first sandboxed Owner-home-v1 invocation remained in the managed wrapper with no
  completed Lean output/receipt. A free slot was observed and process inspection was denied
  by the sandbox. That waiting invocation was interrupted (exit130/KeyboardInterrupt).
  Inaccessible scratch-lock writes are the inferred cause; this is not a failed proof
  elaboration or a successful run.
- The same approved command was retried with sandbox access to the managed lock directory.
  All completed invocations use the ordinary leanelab.sh slot acquisition, local budget3,
  one sequential Lean, no outer/nested lock, full read-only oleans-mac3, and no olean output.
- Owner-home-v1 and Consumers-v1 passed on their first completed elaborations. The owner
  prefix emits two existing unused-simp warnings at its unchanged line178.
- The first positive controls used a complete-step match at specialized State=Unit. Its two
  complete-equation rfl examples failed before any seal. That source/output is retained.
  Inspect-step records the compiled definition. Version2 abstracts State in those two
  examples; all eight controls then pass unsealed and fail exactly once each sealed.
  The successful positive controls emit one unused-State-binder warning in the abstracted
  example. These are probe warnings, not library edits.
- Controls-sealed.lean.txt is the unexecuted superseded version1 negative archive;
  Controls-sealed-v2.lean.txt is the executed final negative control. Proposed-contract is
  a source fragment, exercised inside the owner/consumer probes rather than run alone.
- Checker duplicate/missing/zero-exit tests are offline mutations of diagnostic data.
  They are not additional Lean executions. No mathematical or source conclusion rests on
  an unrun archive.
