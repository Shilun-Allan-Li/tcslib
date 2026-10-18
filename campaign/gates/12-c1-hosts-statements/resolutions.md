# C1 host-contracts statement gate: resolutions

**Gate:** `audits/c1-hosts-statements-pack.md`; bundle `audits/c1-hosts-statements-bundle.md`, SHA-256
`8d4ba59b410fab2ddc93e80b81abe76e9c73d76bc3eb294c73456de78aceb65b`, 72 sections.
**Findings:** `audits/c1-hosts-statements-findings.md`, verbatim.
**Verdict: PASS, CLOSED in round 1 (2026-10-14): 0 blockers, 0 majors, 11 minors, 13 notes.** No
false host contract; the decided route (guess first, `BF := E(UN)`, replay codes, the shared
step clock, the window copy) and the six homes are approved. Each minor is fixed as below (none
is waived); the Lean fixes travel with C1's landing PR, which follows #86 because the slice
lemma's proof replaces #86's `sorry`.

| # | Finding (short) | Resolution |
|---|---|---|
| M1 | Part C's prose says the two choices differ only in the written symbol; under a general controller they also change control | **At landing:** restrict the claim to the trivial-controller, never-stop instance of `ndWriterTM_run_block`; describe general control as choice-dependent; drop the implied finiteness of `Q`. |
| M2 | `exists_inputWindowCopyTM`'s sketch ledger does not give the coefficient `2·|w|` | **At landing:** separate exhaustion (`counterOverhead_le` once, `4d + 2|w| + 2`) from early input end (`counterOverhead_le_of_le`), as the auditor gives. |
| M3 | `exists_replayCanonizer`'s sketch appends the choice-tape field after the whole record | **At landing:** decode and re-emit each record, inserting the third work-tape field after the first two and before output and successor. |
| M4 | The pack's example of a halted initial configuration at `t' = 0` is impossible | Recorded. The example is a machine halting on its first transition, `t' = 1`. The objection to the old prefix clause stands (pack text, historical). |
| M5 | C1-design §3.4 claims every materialized input of D has length `O(n)` | Recorded: the bound is `O(n + |α_j| + |bits (g n)|)`, with an `O(g n + 1)` allowance; §3.4's estimate is superseded by the gated prefix clause. The `O(n)` locator obligation stays. |
| M6 | E is said to retire `ClassNP/Nondeterminism.lean`'s private `choiceCore` | Recorded: E searches choices and `choiceCore` verifies a supplied word, so E is not a replacement. A possible retirement goes through the shared choice replay machine with the clock, input and output-capture wrappers. |
| M7 | `exists_codeNDTM_accepts_linear`'s sketch cites `MultiTapeTM.relabelState` | **At landing:** cite `Turing.NDTM.relabelState`, in the comment-only patch. |
| M8 | Three new modules (`Build/InputWindow`, `NDCodeSimulator`, `ClassNP/ExhaustiveReplay`) omit `## Main definitions` | **At landing:** add the heading with "No new definitions" where so. |
| M9 | The cited-name screen is a filtered screen, and some glue declarations carry no AB09 tag | Recorded: the screen is described as filtered, with its filter; glue declarations use policy's technical-glue exemption. |
| M10 | The plan's historical §12.7 entry still calls `clockTM` quadratic, and item 12 routes its re-derivation through the round host | **Fixed in the records now** (plan §12.7 entry annotated; item 12 names the shared step clock). |
| M11 | The patched `ntime_hierarchy` sketch says every phase is cut by D's countdown, though the `g`-witness run precedes it | **At landing:** every phase is either bounded within its reserved share or run under the step-clock cap. |

**Rulings on the open questions:**
- keep `ClassNP/ExhaustiveReplay.lean`;
- state and gate the guess-then-run assembly lemma in `Build/NDHost` during C1-A, before UN's
  brief (it must establish `R`'s clean-bank, head and output precondition and handle live
  verdicts and emission capture);
- the citation fix goes with this landing (M7);
- keep the repaired prefix clause;
- register and complete the H1 hosted-clock harvest (arbitrary represented live start with the
  stream installed, the early-escape time bound, live exits) before `R`'s consumer brief.

**Notes:** `runall.sh` is a log generator that does not fail closed (N2). The H1/H2 public
interfaces remain future obligations (N3).
