# Deterministic oracle-run draft: overlap and reuse

Base inspected: 5ed465f62e4ae0f93ded1a1ba49e807591b589eb.
Mathlib source inspected read-only: 029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e.
Lean core source inspected read-only: v4.25.0.

No Lean, lake, Git mutation, or source-PDF reading occurred in this subtask.
The draft is /private/tmp/io-phfe-preflight/drafts/Run.lean; it has one intended
M0 admission in simulate_buildComp_detImpl_eq_pure. The four case readers and
detImpl_apply have complete syntactic proofs, not yet elaborated.

## New declarations and nearest relatives

- detImpl and detImpl_apply: the stateful deterministic answer implementation.
  Nearest relative: Games.QueryImpl.ofComp and ofComp_apply,
  TCSlib/Cryptography/Games/Simulate.lean:125-134; these wrap STATELESS answers
  and preserve the state. detImpl accepts an answer-and-next-state function.
  Also compare the lambda implementation in
  TCSlib/Cryptography/Games/Efficiency/Handler.lean:401.
- runDet and its four case readers: bounded interpretation of next moves with
  stateful deterministic answers. Mirrors the already-public buildComp,
  TCSlib/Cryptography/Games/Machines.lean:112-119, and its four case readers
  :128-151. The construction is necessary because the bounded computation is
  otherwise an OracleComp, not a value/state pair.
- simulate_buildComp_detImpl_eq_pure: identifies simulation with that value.
  Reuses buildComp's readers, simulate_pure, simulate_query, and pure_bind.
  Nearest relative: OracleComp.evalFn and simulate_ofComp_pure,
  TCSlib/Cryptography/Games/Bridges/QueryTree.lean:64-92, interpret STATELESS
  answers only and leave the state unchanged. Another relative is hRaw_spec,
  TCSlib/Cryptography/Games/Efficiency/Handler.lean:389-408, an existential
  simulation equation tied to fixed-width bitCodec machine handlers and their
  raw machine loop. Neither existing result supplies this generic stateful
  value interpreter. No proof text was copied.

## Searches and deferred work

searches.log records searches by names and conclusion shapes in TCSlib,
audits, Lean core, and pinned Mathlib. No equivalent stateful bounded value
interpreter was found. The pre-draft broad search also found unrelated
circuit runWith evaluators; those have no oracle/state-handler contract.

exact?/apply? probes are DEFERRED to the lead: the subagent is explicitly
forbidden to run Lean, and elaboration is conditional on host preflight.
The lead must complete those probes before promoting this draft as checked
source. No new math source citation is claimed or needed: all declarations
are technical glue.

## Shape choices

- Namespace is TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption,
  as required by the dispatch.
- detImpl is generic in the target oracle specification; it makes no calls.
- runDet's explicit parameters are next, timeout, h, q, hist, s, matching the
  proposed reduction shape.
- No explicit theorem of efficiency, query-tree conversion, machine, sampler,
  or extra helper declaration has been added.
