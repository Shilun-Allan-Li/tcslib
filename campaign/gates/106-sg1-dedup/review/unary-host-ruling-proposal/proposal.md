# Proposed ruling: existing unary-clock clean-call host retention

**Awaiting Seyoon. Not yet clear to merge: #215.** No acknowledgment is inferred.
Source `d0c4a292e781b55617e05b33fdd423bb059fd735`; full exact Hardness source is supplied as inert data.
Independent review: ../round3-accounting-review/README.md and accounting.json.

The existing clRepeatTM is generic in an arbitrary FinTM and entry/exit. It uses C.k+1
work tapes, Fin3⊕C.State, a protected unary clock and a fresh begin phase forcing the
positive first source step even when entry=exit. Its seams/call/round/complete/output
contracts run arbitrary clean calls; clA5Iter_native packages data-dependent N(x) iteration
with a bound only on the actual orbit. These are generic host/control facts, independent
of the machine-to-formula consumer. Fourteen named members are listed in proposal.json:
twelve host/clock/output/budget declarations and two class-level iteration/shrinking wrappers.
They are disjoint from the earlier retained named union; do not count them as accepted.

No literal covering user acknowledgment was found. The existing six adapter/dispatcher
kinds and registry H6's private-kit promotion schedule do not waive this host. Public Loop,
PolyTimeBlockLoop and BinaryArith/Iterate have relevant operational/iteration interfaces;
no exact completed replacement for this actual-orbit/data-dependent-count contract has
been proved by the bounded review. This is not a claim that every member duplicates an
already published theorem or that a new public API is unavoidable. The on-image class
wrapper is a separate unresolved comparison, excluded from this proposal.

**Proposed decision:** retain existing implementations of this unary-clock clean-call
repetition kind anywhere in TCSlib, including matching frame/call/run/clock/output/budget
proofs and actual-orbit polynomial wrappers. Owner: maintainer(Codex). Window: next12.2c
consolidation after activeMIG1 and before further SAT/Hardness fills, alongside the already
accepted consolidation. Design/gate a shared host contract (including resource/head-envelope
clauses) and replace the private implementations there. This is a retention/debt exception,
not permission for new public APIs/imports, a newly built private host or a changed route.

[policy.md](../../../../../policy.md)'s Hosts come first rule requires shared host contracts,
and START-HERE§2 reserves debt acknowledgments for Seyoon. If retention is declined, hold
this SG1 leaf while a shared-host extraction/assembly is designed and gated. The independent
follow-up API audit, MIG proposal and F6 fill can continue.
