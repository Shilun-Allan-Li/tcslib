# External audit pack — Chapter 2 fill campaign, Epoch 1

Audits the integrated epoch-1 state on `complexity/arora-barak-ch1`: nine
agent commits (`07cf205a` … `b5ff4c75`) on base `7494522e`, plus the
maintainer integration commit carrying this pack. **First fill epoch of the
Chapter-2 campaign** (`workflow.md` §4; partition:
`AroraBarakChapter2Plan.md` §4): four parallel batches filled **27 of the 59
audited-true admissions** — the polynomial-time calculus (1A, 8), the
nondeterministic run calculus (1B, 6), complementation and the easy
inclusions (1C, 6), and the formula mathematics (1D, 7). The statement
layer was audited across the four closed phase gates; **this round audits
proofs and their new private helpers**, not statements. Gate closes on zero
blockers/majors. Record findings in `audits/ch2-epoch1-findings.md`.

## Maintainer-side integration attestations (verify or challenge)

1. **Checksums and provenance.** All four archives' `SHA256SUMS` verified
   in full (26/26, 26/26, 22/22, 18/18). Every batch pinned base
   `7494522e`; patch replay reproduced each delivered tree per the agents'
   own logs, and `git am -3` applied all nine commits cleanly here,
   authorship preserved (author: Codex).
2. **Statement freeze, independently audited.** Across the entire
   integration diff (`7494522e..b5ff4c75`), the deleted lines are **exactly
   the 27 `sorry` lines plus one docstring closing line** — the disclosed,
   rule-2-sanctioned sketch appendix on `mem_P_of_polyTimeReducible`
   (append-only; the hunk is reproduced in the integration record). No
   other pre-existing line changed.
3. **Declaration drift: none public.** Ordered public declaration lists
   per owned file are identical to base; zero removals; additions are
   exactly the **19 private helpers** the reports declare (1A: 1 —
   `comp_time_bound`; 1D: 18, itemized with contracts in its report;
   1B/1C: none). The appendix-cited `succ_pow_le` pre-exists
   (`ClassP/ModelInvariance.lean`, phase 1).
4. **Elaboration.** Full fresh-olean 53-module sweep at the integrated
   tree (`scripts/ab_ch1_module_order.txt`, Lean 4.25.0 / mathlib
   `029db123ddaa`): zero `error:` lines, exactly **32 admission warnings**
   (59 − 27). Log: `audits/logs/ch2-e1-sweep-53mod.log`.
5. **Axiom prints.** All 27 filled targets at the integrated tree
   (`audits/logs/ch2-e1-axioms.log`): **zero `sorryAx`** — the two
   brief-sanctioned `sorryAx` carriers of batch 1A are clean after
   integration, since 1C's `P_subset_NP` fill closes their one admitted
   dependency. Footprints: 16 targets `[propext, Classical.choice,
   Quot.sound]`, 10 targets `[propext, Quot.sound]`, and
   `Std.Sat.CNF.evalDNF_dual` axiom-free.
6. **Policy.** Style lint: 0 FAIL / 0 WARN on `ClassNP/` and `Formulas/`;
   `TuringMachine/` keeps its six pre-existing Chapter-1 size WARNs,
   unchanged. All docstrings and attributions intact.

## Maintainer dispositions taken this epoch (review requested)

* **D1 — axiom-footprint subsets accepted.** The briefs said to expect
  "exactly" the standard triple; batches 1B (five targets) and 1D (six)
  escalated honestly that their proofs use *proper subsets* of it. Subsets
  are accepted a fortiori — the brief wording was the defect, and the E2
  briefs will read "at most the standard triple; `sorryAx` never, except
  where sanctioned".
* **D2 — branch-name deviation noted, cosmetic.** Batches B/C/D worked
  under the campaign branch's own name rather than the brief's
  `fill/ch2-e1-X`; integration is by patch series, so nothing turns on it.
* **D3 — shared-lemma request deferred.** 1D requests promoting its
  generic `foldr_max_le_of_forall` to a shared list utility; the private
  copies compile standalone, so promotion is deferred to a later serial
  merge and tracked in `backlog.md` §2.

## What is under audit

Per batch: the proofs of the 27 targets and the 19 private helpers, against
the audited statements (frozen; re-verified above) and the audited sketches
(the in-file routes plus each brief's amplifications — the briefs are in
`briefs/ch2-epoch1-batch{A,B,C,D}.md`, committed at the base). Priorities:

1. **1A's `comp_time_bound`** — the one place the composition exponent
   arithmetic (`max c (c·c')`, phase-1 finding 7) lives; blind-rederive the
   inequality, including zero coefficients and degrees.
2. **1D's parser round trip** — the fuel-≥ strengthenings
   (`parseClause_serializeClause`, `parseClauses_serialize`) and the
   additive consumed-prefix accounting in the `numVars` bounds; check the
   fuel-adequacy side conditions actually discharge at the instantiation.
3. **1B's truncation direction** in `NTIME.mono` — the backward
   acceptance transfer is the one place the sketch's prefix argument could
   have been weakened; confirm the proved form preserves
   output-exactly-`[true]`.
4. **1C's `compl_mem_P`** — timed composition only (finding 4); confirm
   no untimed route slipped in, and that the budget absorption matches the
   explicit-polynomial discipline.
5. **Helper hygiene** — the 19 privates: contracts match their docstrings;
   nothing deserves public status without flagging; no helper restates an
   audited statement in disguise.
6. The four agent reports (attached verbatim) — challenge any attestation
   of theirs that the maintainer layer above did not independently cover.

Severity scheme as always: blocker / major / minor / note; findings to
`audits/ch2-epoch1-findings.md`; this pack is immutable once sent.
