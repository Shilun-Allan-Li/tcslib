# Counted-loop host registration proposal

The exact one-row H16 diff registers the existing counted-loop FP contracts
and their clean-call envelope. It applies to the same registry blob on
draft #250, the central LWE/SIS target, and the current Pass–Shelat base.
[Proposed diff](proposed-for-loop-registration.patch) · [Pins and fingerprints](proposal.json)

`forLoop_bound_of_ctx` bounds intermediate **word lengths**. To obtain a
**machine head bound**, apply H14's `clean_install` to the already-proved
`polyTimeComputable_forLoop` contract. The clean module installs the same
loop result and first halts within its polynomial budget. `Clean.envelope`
bounds each work head by that budget throughout the run. The specialization
uses the existing public APIs and applies to every raw argument word.
[Checked specialization](evidence/HeadEnvelope.lean) · [Axiom prints](evidence/head-envelope.log)

The local probe passed with Lean 4.25.0, the manifest pins and this
worktree's own Gate 13 prerequisites. All six printed declarations use
only standard axioms. The shared-file diff consists of one registry row.
The seven efficiency fills can use the existing FP calculus, with the two
SIS CRH proofs downstream of the collision-output postprocessor.

The shared registry requires maintainer coordination under the campaign
scope and host policy. Gate 14 reviews the proposed registration before
the counted-loop consumer proofs are integrated. This proposal is recorded
as data on draft #250.
