# Gate 02 (Pass–shelat ch. 5–8, S2a), round 2: external API audit pack

**What is audited:** PR [Shilun-Allan-Li/tcslib#185](https://github.com/Shilun-Allan-Li/tcslib/pull/185)
into `cryptography/pass-shelat-ch2-4`, at its head `586510c1416afa21881b9a42b5a8d0578c9bd749`.
- **Round 1** audited `597eef43ccd3c8bfafe0c0c16a2444b12adc1644` and found **1 blocker, 3 majors,
  6 minors and 2 notes** (`gate02-s2a-findings.md`, in the bundle, verbatim).
- **The repairs:** two commits on #185's branch, after `597eef43`:
  - `14e5988633b949811f774a15583d4967397bf292`, the round 1 repairs;
  - `586510c1416afa21881b9a42b5a8d0578c9bd749`, completing finding 8's citation repair.

  Their full diff is `evidence-r2/repair.diff.txt`. Each finding's resolution is in
  `resolutions-r1.md`.
- **The deliverable:** **`gate02-s2a-r2-findings.md`**.

The bundle holds this pack, then every file named below under a `## ===== <path> =====` header.
**The source is attached separately:** [PS10] R. Pass, a. shelat, *A Course in Cryptography*,
3rd ed., January 2010 (PDF). Book page = PDF page − 12; item numbers carry the book page.

## Brief for the auditor

Round 2 does two things.
1. **It verifies the round 1 resolutions.** For each of the 12 findings and the review's 3 extra
   items (M1, M2, M4), say whether the resolution is adequate:
   - **fixed** — the defect is gone, and the fix introduces no new one;
   - **recorded** — the finding is accepted as a declared deviation or as scheduled work, and the
     record is accurate;
   - **not resolved** — say why.
2. **It audits the changed surface afresh,** as round 1 audited the whole: definitions,
   statements, docstrings and proof sketches. The proofs are machine-checked; do not review tactic
   scripts. Most of `Protocols.lean` is new (the execution was redesigned after finding 1), and
   the identical-until-bad lemmas of `Hopping.lean` have a new hypothesis (finding 3).

For **every new or changed definition**, restate it in your own mathematical English before
reading its docstring, and report any daylight. For **every new or changed theorem**, say in
1–3 sentences whether its statement is what the docstring claims. Attempt at least **three
adversarial instantiations** of the new execution, and at least two of the new hypothesis of
`identical_until_bad`. Look for regressions: anything round 1 accepted that the repairs broke. Do
not give a blanket approval.

## Scope

| Item | Where |
|---|---|
| Under audit (new or changed declarations; the rest for regressions) | `TCSlib/Cryptography/Games/{OracleComp,Probability,Simulate,Advantage,Hopping,Protocols}.lean`, `TCSlib/Cryptography/Games.lean` |
| Round 1 record | `gate02-s2a-findings.md` (round 1's findings), `resolutions-r1.md`, `pack-errata.md` (E1–E3), `pack.md` (round 1's pack and questions) |
| Design documents (context; they state the intent) | `briefs/pass-shelat-ch5-8/design/S2-game-framework.md`, `briefs/pass-shelat-ch5-8/design/CITATION-VCVio.md` |
| Campaign inventory (pack erratum E1) | `briefs/pass-shelat-ch5-8/inventory-ch5-8.md`; the rows of the source items asked about are Def-134.2, Def-136.2, Def-140.1, Def-155.1, Def-168.1, Thm-168.2, Def-172.6 and Thm-175.1 |
| Context, not under audit | `TCSlib/InformationTheory/FinDist.lean` (on `main`); the ch. 2–4 layer: `Foundations/Probability.lean` (now imported by `Games/Advantage.lean`, pack erratum E2), `Foundations/Experiments.lean`, `Pseudorandom/Functions/OracleAdversary.lean`, and `ZeroKnowledge/Interaction.lean` (its foundation decision D8, which the new execution follows) |
| Source | [PS10] §4.4 (book pp. 114–116); ch. 5–7 definitions (book pp. 133–175) |
| Standards | `policy.md` |
| Out of scope | tactic proofs; the S2b layer (bridges to the ch. 2–4 layer, the machine model), not in this PR |

## Attestations (maintainer execution claims; evidence under `evidence-r2/` in the bundle)

1. **Elaboration.** `scripts/lean_check_tree.sh`, one module at a time into a fresh olean tree,
   over the 9 modules of the closure (`InformationTheory/FinDist`,
   `Cryptography/Foundations/Probability`, the six modules, the facade): 9/9 pass, 0 errors,
   0 warnings, 0 `sorry` (`replay-head.log`, `replay-order.txt`).
2. **Axioms.** `#print axioms` for all 75 theorems: only `propext`, `Classical.choice` and
   `Quot.sound` (`axioms.log`).
3. **Lint.** `scripts/style_lint.py` and `scripts/campaign_style_lint.py`: 0 findings on the 7
   files; no line over 100 characters (`style-lint.log`).
4. **Imports.** `Mathlib.Data.Nat.Notation`, `TCSlib.InformationTheory.FinDist`,
   `TCSlib.Cryptography.Foundations.Probability` (finding 10's reuse; it imports only Mathlib),
   and the framework's own modules.
5. **Names** (`name-screen.log`). No new clash. The new public names are listed in the log;
   `Party.finish` is removed.
6. **Generalizations of existing code,** unchanged from round 1, attestation 6, with one addition:
   the hybrid argument now reuses the concrete layer's lemmas (finding 10).

## Changes since round 1 (declared; verify them)

- **Execution (findings 1, 2 and 5; ruling 2026-11-05).**
  - `ExecOutcome`: both outputs (`done`), the message budget ran out (`outOfFuel`), or a party sent
    after its counterpart returned (`sentAfterEnd`).
  - When the active party returns, the waiting party's pending send is answered `none`. It may then
    draw coins and must return without sending (`Party.close`, `Party.endWith`). This is D8's
    reading of [PS10, §4.4], with one declared difference: a party may return early.
  - `fuel` is the message budget, and a return costs no fuel.
  - **Views:** `Party.execT` records, for each party, the messages delivered to it and its coins
    (`Party.Obs`). `execT_outcome` proves that its outcome is `exec`'s. Inputs and auxiliary
    inputs are the parties' Lean parameters.
- **Identical until bad (finding 3).**
  - `prob_eq_until_bad` and `identical_until_bad` take a semantic hypothesis: from a good state,
    the two implementations give the same law to good successors (equal expectations of every
    function that vanishes on bad states). Stickiness is still required.
  - `hagree_of_eq` derives this hypothesis from equality on good states.
  - `identical_until_bad_init` starts from a sampled initial state that is good with probability 1.
  - A deviation note against [BR06].
- **Hybrid argument (finding 10, ruled):** `advantage_hybrid` and the new
  `exists_advantage_hybrid_gap` are one-line instances of the concrete layer's
  `abs_sub_le_sum_hybrids` and `exists_hybrid_gap`.
- **Docstrings and citations** (findings 6–9, M1, M2): see `resolutions-r1.md`. The [Sho04] and
  [BR06] section and lemma numbers are dropped, since the revisions could not be inspected from the
  maintainer's session.
- **Recorded, no code change:** finding 4 (Thm 175.1 with strict or truncated simulators, ruled),
  finding 11 (non-dyadic sampling and fair bits) and finding 12 (bridges and efficiency, S2b).

## Specific questions

1. **Resolutions.** Is each round 1 finding fixed or accurately recorded (see the brief)?
2. **The execution.**
   - Does `Party.exec` implement the alternating execution of [PS10, §4.4] under D8's reading,
     with early returns as the only difference? Compare it with `TCSlib.Cryptography.exec` and
     `Protocol` in `ZeroKnowledge/Interaction.lean`.
   - Can a party's misbehaviour (sending after the end, running past the budget) be hidden by
     the outcome?
   - Is the fuel accounting right at the boundaries: `fuel = 0`, an immediate return, and the
     last allowed message?
3. **Views.** Is a party's view in [PS10, §4.4] (its input, auxiliary input, coins and received
   messages) recoverable from `Party.Obs` and the party's parameters? Is the order of received
   messages and coins right, including the coins drawn by `close`? Is `execT_outcome` the right
   consistency statement, or is a sanity theorem missing (for example, about the length of the
   received lists)?
4. **The new hypothesis of identical until bad.**
   - Is it implied by the round 1 syntactic hypothesis (`hagree_of_eq`)?
   - Is it met by the bad-event hops it is meant for: the repeated-nonce hop in Thm 168.2, and
     CCA2's decryption oracle answering the challenge?
   - Is the conclusion still the standard one?
   - Does `identical_until_bad_init` cover a sampled key?
5. **Hybrid reuse.** Do `advantage_hybrid` and `exists_advantage_hybrid_gap` state what their
   docstrings claim, and is [PS10, Lemma 71.6] the right tag?
6. **Expressiveness, re-checked.** With the new execution and views, can Def 155.1 (both views,
   jointly with the other party's output) and the sequential composition of Thm 175.1 (under the
   ruled deviation) be expressed? Report any that cannot as findings.

## Findings format (auditor fills)

Two tables.

**Table 1, resolutions:**

| Round 1 # | Verdict (fixed / recorded / not resolved) | Evidence |
|---|---|---|

**Table 2, new findings:**

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | blocker / major / minor / note | | | | |

Severity guide:
- **blocker:** a downstream phase would build on a wrong definition or statement;
- **major:** fixable but materially misleading as it stands, or debt that needs explicit human
  acknowledgment;
- **minor:** an edge case, or a naming or attribution defect;
- **note:** an observation; no change required.

A round 1 finding judged "not resolved" counts at its round 1 severity. The gate closes at
**0 blockers and 0 majors**.
