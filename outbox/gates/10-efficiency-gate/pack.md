# Gate 10 · shared reduction-machine efficiency

Round 1. Auditor Codex. Draft [PR #285](https://github.com/Shilun-Allan-Li/tcslib/pull/285)
at 747cc18ddb53979919d107fefed450191eb31743, targeting cryptography/pass-shelat-ch2-4 on base e226b470e25cb08a9fe8b10f9f5dd54fc55c1808.

This proof audit covers the four formerly admitted statements in
Games/Efficiency and their six helper modules. The theorem statements passed
Gate 04. The source is [PS10], R. Pass and a. shelat, A Course in Cryptography,
third edition, January 2010, §2.1 and the reduction-machine uses of the later
security proofs. The attached design explains the exact machine contracts.

## Plain handler and input-free companion

Check that exists_handlerMachine constructs a non-uniform polynomial-time
machine for the simulated handler, with arbitrary initial state carried in
polynomial-length advice and the exact seed/adversary coin bijection.
Review the actual activation loop and its length bound. Test the reasoning
at zero query budget, malformed moves, wrong-width payloads and zero-width
payloads. The componentwise default of PolyHandler.answer is part of the
frozen statement. Confirm that the argument covers every adversary and
handler coin tape.

For exists_toCompOn_of_toComp, check the preserved coin polynomial and the
run equation after the input is discarded. The conclusion is quantified over
every codec, oracle specification, output type, budget and actual input.

## Interactive handler

Independently derive the query bound q·perCall + finCall and activation
allowance q·(perCall+2) + finCall + 2. Review the replay invariant and its
adversary, call and finalization phases. Check every outer answer, including
answers inconsistent with earlier replies. The raw machine must preserve the
answer supplied by the outer tree. Check pending queries at budget zero,
all terminal paths, and the combined answer/state default. Confirm that the
cost bound is established before reconstructing the tree from replay.

## Oracle-model bridge

For exists_toOracleAdversary_of_bitCodec, verify the history translation,
the preserved order and coins, and equality on every machine output word.
Review the timeout, false/true verdicts, malformed payloads, and the case
where the single oracle's domain has width zero. Check that the equality
covers all budgets and deterministic oracle functions.

## Proof and interface review

Inspect the seven source files and exact diff, the issued brief, design,
worker report and maintainer verification. Check the four frozen headers,
all older declarations, the eleven added total reader lemmas, and the
published-reader discipline. Check precise imports, proof sketches and
global attributes. Examine the use of the existing GGM state-loop host and
the shared-helper requests. The disclosed wrappers and generic
generalizations were reviewed as applications of public proofs.

Seyoon approved reuse of the issue-time public provider proofs while their
inherited seal findings stay in deferred cleanup. That approval covers the
72 historical diagnostic/declaration pairs in the issued dependency record.
The new proof source is subject to the ordinary seal checks.

The verification archive includes raw native logs, the all-stored declaration
comparison, the 448-declaration axiom census, seven whole-file seals, six
controls, and the explicit-use inventory. Review the evidence against its
stated coverage and the recorded attempt dispositions.

## Findings delivery

Return gate10-efficiency-findings.md as a Markdown file in this chat.
For multiple evidence files, return a ZIP containing the Markdown and the
evidence. The user dispatches and merges.

| # | Severity | File and declaration | Claim | Evidence | Proposed fix |
|---|---|---|---|---|---|

Use blocker for a false or unusable statement or substantive scope violation,
major for a missing premise, forbidden new proof read, incomplete machine
argument or unverifiable necessary evidence, minor for documentation or API
defects, and note for further observations. Report the exact audited head and
counts by severity. The gate closes at zero blockers and zero majors.
