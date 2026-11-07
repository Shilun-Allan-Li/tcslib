# Gate 115: padding-space fill, PR #228

Audit [PR #228](https://github.com/Shilun-Allan-Li/tcslib/pull/228),
`lean/epad-padding-fill`, against the campaign. Exact Lean and records commits are in the bundle
header and `evidence/current/landing/refs.json`. The user selected Codex, dispatches this gate and
merges the PR. This gate does not authorize the later Hierarchy consumer change.

## Trusted surface and proof architecture

The public statements were accepted in gate 110. This PR fills `Complexity.mem_SPACE_padLang`
without changing any public statement or adding/removing a public declaration. The full changed
file is `TCSlib/Complexity/SpaceComplexity/Padding.lean`; its public source declarations remain
`padLang`, `mem_padLang_iff` and `mem_SPACE_padLang`. The source census adds 49 private declarations,
using the permitted prefixes, with surviving order unchanged. Compiler-generated constants are
reported separately and unfiltered in the fresh module census.

For `L ∈ SPACE S`, the theorem puts the language of `pairEncode x 1^{C(|x|+1)^d}` for `x ∈ L`
in `SPACE T` when `m+1 ≤ T m` and `S n ≤ T (2n+2+C(n+1)^d)`. It assumes neither monotonicity nor
computability of `S` or `T`. The file cites [AB09, Exercise 3.2]; gate 110's pack/findings/resolution
are supplied as context for the accepted statement. Challenge the literal statement if the fill
exposes a problem in it.

The implementation has three parts. A concrete ARM validator recognizes correctly padded words.
Two logarithmic-space bank languages answer canonical binary-index queries about their first
component. The run phase uses the published `LogProg.OIS.compile_decides` host on that virtual
input. The final catalog conditional rejects invalid padding and otherwise runs the simulated
decider. On malformed input the virtual input is empty, and the constant `S 0` is absorbed using
the linear lower bound on `T`.

## Delivery and landing review

The final delivery was received from `arora-barak-ch3-4/inbox/fill-epad/` on the exchange branch.
All 118 payload checksums passed. The maintainer read the complete delivered source before
elaboration and applied its four patches with their original authorship. The receipt, original
source, verbatim REPORT, original checksum list, internal review and separate landing review are
under `campaign/fills/epad/reviews/epad-fill/` and are bundled.

Mechanical landing repairs remove the private duplicate `epad_two_pow_bits`, cite the reachable
`LogProg.two_pow_bits_le` and `Turing.length_bits_le_self`, and use canonical
`LogProg.bitsVal_lt_two_pow` (the explicit Codec copy is removed by #222). The redundant Codec.Word
import is removed; an out-of-range read now uses already available Core list equations. Two
identity-update blocks cite `Function.update_eq_self`. Four missing proof sketches and stale
provenance/implementation prose are corrected. These repairs require no new public API, statement,
import or debt acknowledgment.

The original REPORT's claim of exactly three non-private constants is inaccurate: its own log
has the three public declarations plus three generated proof auxiliaries. The REPORT is preserved
verbatim and the discrepancy is disclosed, rather than editing the delivery. Use the fresh
all-constant walk for the landing's exact count and names.

## Brief for the auditor

Apply `campaign/standards/TEMPLATE.md`, `policy.md`, `workflow.md` and the duplication ledger.
Machine-checked tactic correctness is outside the gate; trusted meanings, boundary conditions,
semantic duplication, API reuse, rule 10 and cumulative debt remain in scope.

1. Restate each new definition in mathematical English before reading its docstring. Check the
   validator, virtual input and bank meanings against actual pair layout. The padded length is
   `2n+2+C(n+1)^d`; both delimiters and the doubled first component must be charged.
2. Try at least three adversarial cases, including empty input/component, `C = 0`, `d = 0`,
   malformed pair/unary pad, a zero/noncanonical index, and an index at the virtual input's end.
   Check the malformed-input run at `S 0`, absence of monotonicity assumptions and absorption of
   constants. Challenge the supplied executed boundary probes.
3. Check initialization, all bank tapes, index decoding and simulator bookkeeping in the space
   ledger. The no-case must reject malformed padding even when the original language accepts `[]`.
4. Search all new private proofs and inline `have`/`obtain` steps for existing library routines.
   The internal review compared the ones scan with Codec.Engine's `scan_loop`: that row expects
   two oracle reads and two pointer advances and a finite-state fold, rather than this one-read,
   count-and-early-failure leaf. Published ARM rows supply move/copy/fixed-scale/halve; the private
   multiply/power helpers assemble arithmetic leaves. Challenge this classification, especially
   if a public contract directly instantiates one of them. No new private host is being approved.
5. Verify the foreign-definition inventory against the actual compiled declarations and the
   proof source. The sealed copy uses 36 foreign definitions and removes reachable default-simp
   definition unfoldings. Every seal has two reflexivity controls, the first defining equation
   and that equation abstracted over its parameters, which must close unsealed and fail sealed.
   Inspect every explicit simp/rw/unfold argument too; irreducibility alone does not catch those.
6. The exclusions are explicit in `seal/exemptions.md`: reducible abbreviations, FinTM projections,
   a generated Ins eliminator and a matcher appearing in a published statement. Abbreviations are
   allowed by the standards; the matcher is disclosed as a limitation, not silently counted as an
   effective seal. Challenge any additional bypass or missing seal/simp entry.
7. Verify the public source freeze, every non-private compiler constant, all-declaration axioms,
   source citations, candidate searches and cumulative screen accounting. No acknowledgment is
   inferred from the delivery's REPORT or the maintainer's classification.

## Evidence

`evidence/current/README.md` states the executed outcomes and limits. It points to the independent
merged-tree replay (module and facade), source freeze, lint, actual module census/axioms, citation
and foreign-definition walks, full sealed source, positive/negative controls, boundary probes,
and base/head copy-text screen with its complete population. The bundled population includes
Codec.Engine and ARMKit as well as every other cited library source. Candidate enumeration also
covers all open campaign PRs, prepared landings and available delivery refs.

Failed initial probe attempts are preserved and explained. A preflight or seal is not represented
as the merged-tree replay; the replay is chained independently from the complete Mac campaign
snapshot. Delivery-agent execution claims remain attributed to that agent until reproduced.

## Findings

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Include a verdict line with blocker/major/minor/note counts. An empty table needs the definition
restatements, adversarial cases and reuse/seal analysis that justify it. The gate closes at zero
blockers and zero majors, with minors dispositioned.

**Deliver your findings as a downloadable file named `epad-fill-findings.md`** (the findings table
and the verdict line, no other wrapping), and also paste its content in your reply.
