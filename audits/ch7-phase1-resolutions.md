# ch7-phase1 — audit resolutions (gate closed)

**Gate: CLOSED on round 1.** The external statement audit
(`audits/ch7-phase1-findings.md`), performed by an LLM from a different vendor in a
fresh context over the 13-module surface at `76fe2f46`, reported **zero blockers, zero
majors, one minor, one note** — the closing condition (`workflow.md` §3). The minor was
swept in the closing commit and re-verified; the note was adopted as a docstring
clarification. One adversarial round; 27 original statements + the three new support
modules audited.

## Round 1 summary

The auditor blind-restated every definition (old and new) before reading docstrings and
compared against the [AB09] 2007 Chapter-7 draft. It confirmed, in its own derivations:

* **CH7-Q1 (priority).** The ℚ-exact-counting Chernoff development does **not** weaken
  any class conclusion: `randProb`/`blockCount`/`randProb_tail_le` give the exact
  binomial mass and a `2(1−4ε²)^{⌊K/2⌋}` tail; `bpp_error_reduction` reaches
  `2^{−((n+1)^d+1)}` for every natural `d` (stronger than the book's `2^{−n^d}`); Adleman
  and Sipser–Gács inherit the ℚ estimates. Checked non-vacuous at `n=c=d=0`.
* **CH7-Q2.** The abort-form `ZPP` identity matches `RP ∩ coRP` in that model; the
  expected-time equivalence is the standard (unformalized) bridge — see finding 2.
* **CH7-Q3.** The sign-corrected Thm 7.41 is the correct inequality direction;
  statement-only is acceptable (book omits the proof).
* **CH7-Q4.** `polyTimeModel` faithfully renders Def 7.4; the named closures are the
  book's tacit machine operations.
* **CH7-Q5/6/7 (new surface).** `pairWiring`/`pairEncodeInput` realize
  `pairEncode (ofFn v) r` exactly (doubled first component, constant separator + `r`),
  with no coordinate loss at `n=0`/`r=[]`; `PrefixByLength.take/drop` share defining
  expressions with `Randomized.takePrefixByLen/dropPrefixByLen` and agree on malformed
  pairs (`→ []`); `shiftInput`/`run_shiftInput`/`Goes.prepend_input` state the
  input-shift semantics with no offset error.

Caveat recorded by the auditor: the bundle carried no Git history, `.olean`s, or
imported upstream definitions, so the freeze, axiom-print, and fresh-elaboration
attestations in the pack **remain maintainer repository claims**, not independently
repeated checks. (The maintainer ran them: the 13-module `lean_check_tree` sweep is
green with exactly four `sorry`s; the comment-stripped freeze check shows `PolyTimeModel`
unchanged; the closed leaves print `[propext, Classical.choice, Quot.sound]` with
`adleman_polyTime` carrying `sorryAx` via the open `closedUnderMajority`.) The auditor
also notes — correctly, and consistent with the pack — that the three still-open
closures mean the polynomial-time machine corollaries are not yet `sorryAx`-free.

## Finding dispositions

| # | Severity | Disposition |
|---|---|---|
| 1 | minor | **Swept (comment-only).** `polyTimeModel_closedUnderShiftOr`'s sketch now states that `shiftOrVerifier` uses `List.zipWith xor v block`, which is poly-time on arbitrary lengths and truncates to the shorter of `\|v\|` and the block length, and that the exact-length witnesses quantified in `InSigma2` recover the book's equal-length XOR. No statement changed; re-elaborated green. |
| 2 | note | **Adopted (comment-only).** `inZPP_iff_inRP_and_inCoRP`'s docstring now explicitly distinguishes the proved Las-Vegas/abort-form identity (`InZPP`) from the book's expected-polynomial-time formulation ([AB09, Def 7.7]), pointing at the unformalized truncate-and-repeat bridge and plan question CH7-Q2. The deviation was already disclosed in the module docstring and plan; no statement changed. |

No blocker or major was raised, so no re-audit round is required. The statements in
`ErrorReduction.lean` independently confirmed to carry the analytic Hoeffding bounds and
the corrected Cor 7.11 (the auditor exhibited the book's Cor 7.11 counterexample and
verified the module avoids it).

## Outcome

**Phase-1 statement-audit gate closed.** The Chapter-7 statement surface — including the
three new support modules — is audited true at `76fe2f46` (plus these two comment-only
sweeps). Fill may resume on the three remaining machine closures
(`closedUnderMajority`/`closedUnderAny`/`closedUnderShiftOr`); Theorem 7.41 remains the
intentional statement-only stub. Those fills are verified at the fill/closure gate
(`workflow.md` §4–5), not here.
