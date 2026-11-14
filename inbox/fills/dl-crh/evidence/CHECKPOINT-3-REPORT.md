# dl-crh — reduction checkpoint (route checkpoint 2)

**Status: compression, collision shape, an explicit polynomial-time reduction,
and collision-to-discrete-log success are proved. The final collision-resistance
probability bound remains in progress; `dlHash_crh` is still admitted on that
component. This is not a completed fill.**

This is delivery checkpoint 3. It follows the initial reader escalation and the
compression checkpoint. The issue base remains
`eff2dcd0a63f0c371118a17c67b9a5dfc046f4e9`; the proof branch `fill/dl-crh` remains
local. The full two-commit format-patch series and exact source snapshot are
included. The original target header is byte-identical to the issue base.

The new `dlHash_reduction_success` theorem connects the checked concrete machine
with the collision game: for a valid well-formed key, domain guards and equality
of padded hash values imply that the machine's answer decodes to the exact
challenge exponent. It uses the proved exact output length to remove padding,
then the checked unit-group extraction and arbitrary-output postprocessor
contract. Wrong-domain inputs are guarded; equal selectors cannot collide;
equal exponents and exponent zero are covered by the same modular arithmetic.

The reduction uses the finder's coins and advice and has a checked polynomial-
time construction. The new success theorem's axiom probe prints only `propext`,
`Classical.choice`, and `Quot.sound` (raw log under `evidence/logs/helper-2/`).
All eight current source files match successful recorded module checks.

The two provider reader additions are the exact scoped user exception;
Rule 10 remains intact. The shared host has the user-authorized cap of three
Lean processes, and this worker checks one module at a time in its own olean
tree. `evidence/authorization.md` retains the exact authorizations.

The compression checkpoint report is retained as
`evidence/CHECKPOINT-2-REPORT.md`, with its resource/cache/bootstrap/axiom details.
The promotion and overlap ledger is `evidence/PROMOTION.md`. The previous
escalation ZIP is retained verbatim. All development logs, sources, request-
preparation tools and source snapshots generated so far are included. The
independent exact-base source tree and runner have been prepared but no base
bootstrap or seal result is claimed in this checkpoint.

Remaining work: reindex the honest key distribution through the split coins,
apply the proved rejection-sampler bound, compare ideal collision success with
DL success, and use DL hardness plus negligibility. The final full 176-module
sweep, admission delta, all-stored-constant axiom census, whole-file base/final
A/B seals, paired controls, explicit-unfold scan and final lint comparison are
pending. No pending check is represented as a pass.

Both evidence and whole-payload manifests are checked against exact delivered
path sets and SHA-256 hashes. The ZIP bytes match this payload and have dl-crh/
at their root. Only inbox/fills/dl-crh/ is used for exchange delivery.
