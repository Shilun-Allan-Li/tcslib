# Gate 06A/D minor corrections, prepared at the audit pin

This is an **unapplied proposal**, not a source advance or a new native run. The active Gate06
PR/audit source stays `3f6db40e1688c4a0bb922c9575dd3bd2157a650b` while 06B/C findings are pending. Patch SHA-256:
`3c5c98acb21f7e252105a1f64be04fea760d2388b60d1fd22dfa954b25c5987a`.

All six modified files have exactly identical bytes outside nested Lean block/line comments,
with string escapes respected. `git apply --check` succeeds against the frozen source.
Every declaration, hypothesis, body, attribute and admission is unchanged. The patch corrects
A-01/A-02 and G06D-01–04. The generator and per-file hashes accompany it. This comparison
does not call the modified files elaborated or the combined S2/Gate06 tree verified.

The derandomization sketch uses an integer-root schedule and a syntactic polynomial envelope;
its `1/12` distinguishing threshold gives an explicit `7/12` majority margin. BPPBridge's
statement is preserved: prose distinguishes coin-independent behavior from the zero-coins
witness chosen by its proof. Lamport counts jointly favorable pairs in an honest-execution
coupling, handles zero-query runs, and implements the averaging choice through bounded advice.

Apply reviewed corrections during final PR source reconciliation, then refresh source-matched
affected checks/pins. A/D close as statement gates at their issued pin; the pending comment
edits do not constitute substantive proof fills or clearance of PR #232.

Two independent internal intake reviews find no additional blockers/majors/minors. A reviews
the final proposal; D reviews the retained initial proposal, whose four D sections are
byte-identical in the final version. The A-02 implementation refinement explicitly names
T1 on extended input `⟨y,i(n)⟩` followed by `NUPPT.exists_withAdvice`. Initial proposal and
all review identities are preserved; no historical file is relabelled as reviewing later bytes.
