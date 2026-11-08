# Dyadic scalar arithmetic statement gate

Own worktree: `tcslib-lwe-sis-dyadic-arithmetic`.
Draft branch: `cryptography/lwe-sis-dyadic-arithmetic`.
Central PR target: `cryptography/lwe-sis-constructions`.
Remote-verified base: `2c37f3f486822a52f4a9e337c6b742e995ebb118`.
Audited stack baseline: `8627edde9892607a699cf997c8dd5a8a2a700e26`.
Frozen Lean/root: `dbacd91218c19f0df106d316ce4ff0e22b869e66`.

The new `Encoding/DyadicArithmetic` module states modular addition, multiplication
and subtraction on nested MSB pairs, using the proved representation adapters and
existing public arithmetic machines. It has 18 declarations: three definitions,
three complete `rfl` readers and twelve admitted obligations with sketches.
No nontrivial proof fill starts before the statement gate passes.

Fresh verification covers 94 modules, 302 owned constants and sixteen backing
contracts. All 284 prior constants are unchanged; exactly twelve new constants
use `sorryAx`. Style is 0 FAIL / 2 unchanged WARN over twenty files. The bit-list
model passes 630,831 operation comparisons; it is not Lean execution or a proof.
See REPORT.md, evidence/summary.json and the raw logs for scope and limits.

The only existing-file overlap is an Encoding facade import/contents entry, in
a separate export commit. All 100 other frozen paths, shared owner APIs, root
exports and pins remain unchanged. No additional Mathlib root/download is needed.
Own development cache reuse and a newly empty final object tree are distinguished
in cache-setup.json; no other chat's packages or objects are used or modified.

Review pack: `audits/lwe-sis-dyadic-arithmetic-statements-pack.md`.
Prepared inputs belong under
`lwe-sis-constructions/outbox/gates/06-dyadic-arithmetic-r1/` on the orphan exchange.
The user freshly selects Codex or Claude and dispatches the audit. The publication
helper updates only this draft branch/PR and this exchange namespace, after
rebasing the private publisher. No new remote PR or dispatch is claimed until
client publication succeeds. Six earlier scoped gates pass; source-policy and
relevant landing checks remain open.

**Not yet clear to merge — the new statement gate and proof fill, source-policy
work, relevant landing checks and user approval remain.**
