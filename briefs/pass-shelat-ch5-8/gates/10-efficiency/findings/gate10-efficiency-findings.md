# Pass–shelat Gate 10 — efficiency proof audit

**Verdict: CLEAR.** No new findings: **0 blockers, 0 majors, 0 minors, 0 notes**. This closes the requested proof gate under the recorded approval for inherited provider proofs. Dispatch and merge remain with the user.

| Pin | Audited value |
|---|---|
| Draft PR | [#285](https://github.com/Shilun-Allan-Li/tcslib/pull/285) |
| Lean head | `747cc18ddb53979919d107fefed450191eb31743` |
| PR base | `e226b470e25cb08a9fe8b10f9f5dd54fc55c1808` |
| Campaign records | `5bcf11aaf08963ab33ce608ea7509e7403e4351a` |
| Exchange | `f5054f40b2df67c04f47354f5cfeccde704e3440` |

## Findings

| # | Severity | File and declaration | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|
| — | — | Four targets and six helper modules | No new defect found within the dispatched scope. | Review and verification below. | None. |

## Integrity and scope

- Read the pinned README, pack, complete bundle, issued brief, design, worker report, maintainer review and verification dispositions. Treated their conclusions as claims to check.
- **12/12 `SHA256SUMS` entries pass.** The bundle is **309,244 bytes**, SHA-256 `2cc346339bb5e77685d5995ab07b6b90336894059d13ca7a06e33a01c0dd0fa4`.
- All **13 ordered `BUNDLE-FILES.txt` sections** match the Git blobs at their indexed revisions. All **143 archived Lean sources** match the pinned head's Git blobs; their internal SHA-256 manifest also passes, and the archive contains every TCSlib import in that closure.
- Independently generated the base-to-head diff. It matches `pr.diff.txt` exactly with the recorded nine-character object abbreviations: **seven files, 3,432 additions, 60 deletions**.
- All four target headers match both the issued brief and PR base exactly. The other **30 primary source declarations** retain their code. The supplied stored-declaration census reports **84 older declarations** with unchanged types and metadata, and precisely the four intended proof-body differences.
- Verified the original **60-file worker archive**, its **59-entry payload manifest**, and the intake's per-file hashes. Relative to that delivery, the final sources add exactly **eleven reader lemmas**: three in `Strings`, eight in `Interactive`; no worker source lines are deleted.

## Proof review

**Plain handler — PASS.** `Efficiency.lean:321`; `Handler.hRaw_spec:389`; `Strings.exists_splitMachine:548`.

The initial state is arbitrary in the parameter and is correctly stored beside the adversary's advice. Pair encoding has length twice the first component plus two plus the second, giving the stated advice bound `2 · A.adv + 2 + H.stateLen`. The seed/coin equivalence appends the two tapes and transports their length; it preserves every individual tape, rather than merely its distribution.

The loop performs at most the query budget plus one activation. Its invariant bounds the encoded history, fixed-length state and unary counter before applying the existing GGM loop's evaluation theorem. Returns are accepted at budget zero; a pending query then times out without invoking the handler. Canonical decoding checks re-encoding, so malformed words and zero-width payloads are distinguished correctly. The proof separately handles failed pair decoding and wrong-width components, preserving `PolyHandler.answer`'s **componentwise** default. No restriction on the actual input or coin tapes is introduced.

**Input-free companion — PASS.** `Efficiency.lean:642`.

The preprocessing map discards the input through the total second projection; postprocessing is the identity. The coin polynomial is unchanged. Equality of next-move functions holds for every history, so the result covers every codec, oracle specification, output type, budget and actual input in the frozen statement.

**Interactive handler — PASS.** `Efficiency.lean:581`; `Interactive.iRounds:383`; `InteractiveSpec.fin_phase:462`, `call_phase:548`, `adv_phase:677`, `iRaw_spec:770`.

The two budgets count different operations. The outer-query bound is

\[
q(n)\,\mathrm{perCall}(n)+\mathrm{finCall}(n).
\]

Counting adversary, call and finalization activations gives

\[
\begin{aligned}
&(q(n)+1)+q(n)(\mathrm{perCall}(n)+1)+(\mathrm{finCall}(n)+1)\\
&\qquad=q(n)(\mathrm{perCall}(n)+2)+\mathrm{finCall}(n)+2.
\end{aligned}
\]

Initialization occurs in `iStart` and requires no extra activation. The three phase inductions maintain the remaining activation allowance and the length bounds, including the unreplayed outer-log suffix bounded by the raw input length.

The replay invariant quantifies over every extension of the consumed prefix. Each query continuation quantifies over **every answer**; `iAsk` copies the supplied entry and never validates it against a deterministic oracle or previous answers. Consequently repeated queries may receive inconsistent replies without breaking the proof. Pending queries at zero budget are handled before consuming an outer entry. Returns, malformed moves and wrong total result widths follow the frozen **joint** default for answer/state. The cost bound is proved before `buildComp_of_replaysFrom` reconstructs the tree, so there is no circular budget argument.

**Oracle-model bridge — PASS.** `Efficiency.lean:684`; `OracleBridge.bridgePost_spec:224`, `eval_buildTree_bridge:288`.

History translation preserves order and inserts the sole oracle's empty unary index. Move correspondence covers every output word: valid queries, both verdicts, malformed words and wrong-width payloads. The re-encoding test remains valid when the query width is zero. Induction on the budget handles timeout and return at zero separately and preserves the supplied coins; the equality holds for every deterministic oracle function.

## Interfaces and verification evidence

- Reviewed the eleven new readers: `canonFun_def`, `sumPoly_zero`, `selLen_of_ge`, and the eight raw-state projection equations. They cover the previously missing inputs and add no global attributes. Imports remain precise; the helper namespace, proof sketches and file sizes meet the issued scope. The implementation uses the existing public GGM loop. Disclosed generic generalizations and shared-helper promotion requests are consistent with the authorized design.
- Reconstructed all **seven seal sources** by removing their recorded insertions: the remaining bytes equal the audited sources exactly. Their request sets cover all **159 sealable owner/foreign-definition pairs** in the elaborated-term inventory. Name components, owners and instance metadata agree; logs record installation and end-of-file verification without errors. Exclusions are abbreviations plus the existing `PolyExpr.eval` ruling.
- The **six controls** pass unsealed and fail sealed at exactly the six recorded lines. Re-ran the supplied scanner's pure parsing functions against the final source: the complete **1,031-item inventory** matches exactly. Reviewed its name classifications and all **five** `List.cons_ne_nil` argument uses; no forbidden foreign definition head was found.
- The axiom census covers **448 stored declarations**, including generated declarations, using only `propext`, `Classical.choice` and `Quot.sound`. The supplied style log records **0 failures and 0 warnings**.
- The supplied native evidence records ten checks, with `Strings` retained separately and nine successful result rows. Those nine rows' log hashes match the archived bytes. Independently confirmed that the **1,146 retained imported-source files** have identical Git blobs at the native baseline and audited head, and that baseline `Efficiency` equals the PR-base file.

**Verification boundary.** This audit independently checked Git provenance, hashes, source arguments, probe coverage and evidence consistency. It did **not** rerun Lean: Lean/Lake are unavailable in this executor. Kernel-elaboration results above are the supplied maintainer evidence. The failed telemetry wrapper, empty ladder attempt and failed initial classification probe are correctly excluded from successful checks. The approved **72 historical diagnostic/declaration pairs** remain deferred cleanup; this verdict does not clear those inherited findings.

**Notation:** `n` is the security parameter; `q(n)` is the adversary's query budget; `perCall(n)` and `finCall(n)` are the handler-call and finalization outer-query budgets. All are the existing quantities in the audited source.
