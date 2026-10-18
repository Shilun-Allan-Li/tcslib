# External audit pack — the machine-routine layer (§12), statement gate

Campaign: shared machine-construction infrastructure (`machine-library-design.md`
§12), the third `Build/` increment after the spec layer (`audits/ch1-infra-*`) and
the emitter increment (`audits/emitter-infra-*`). Statement-phase gate per
`workflow.md` §3: definitions plus sorried statements only; the gate closes on a
round with zero blockers and zero majors.

Audited at commit `7fbac9bd` (branch `complexity/arora-barak-ch3-4`). Under audit:
exactly three new files — `TCSlib/Complexity/TuringMachine/Build/Embed.lean` (R1),
`Build/Seam.lean` (R2), `Build/Catalog.lean` (R3). Every pre-existing `Build/`
file is **byte-identical** to its audited state (frozen decision 12.2a;
checkable in the attachments — `Primitives.lean`, `Wrappers.lean`, `Loop.lean`,
`Convention.lean` are attached verbatim as read-only context).

## Brief for the auditor

You are auditing the **trusted surface**: definitions, sorried statement shapes,
and docstrings, against the design document (`machine-library-design.md`,
especially §§2-5, §11, §12 with its four frozen decisions 12.1-12.4) and the
existing audited `Build/` surface. This layer's consumers are the chapter-1/2
retrofit, the Hennie-Stearns `k`→2 conversion, the two-work-tape universal
machine, and the chapters-3/4 space campaign — so **quantifier shapes and
hypothesis strength are where this design can be wrong**, exactly as in the two
prior infrastructure rounds. Failure modes, in priority order:

1. **Unusable shape** — a contract too weak for its named consumers (check each
   statement against the §12 consumer table), or hypotheses no consumer can
   discharge.
2. **Trivialization** — a statement satisfiable degenerately (empty words,
   `k = 0`, `T = 0`, `ι` surjective, `src = dst` where not excluded).
3. **False as stated** — especially the exact constants and the space clauses;
   re-derive each head-movement count independently.
4. **Restatement drift** — every Part-2 space row claims to restate its audited
   time contract *verbatim* plus a space clause on the same witness; diff each
   against the original in the attached home files.

For every definition: restate it blind, then compare. For every sorried
statement: argue true-as-stated in 2-5 sentences or exhibit the problem. Attempt
at least **6 adversarial instantiations**. Propose missing sanity statements.
No blanket approvals.

## Repository-side attestations (verify or challenge)

* Fresh elaboration (`audits/logs/routine-infra-sweep.log`, revision recorded at
  start): all three modules, 0 `error:` lines, fresh `.olean`s, exactly **47**
  `declaration uses 'sorry'` warnings (Embed 9, Seam 6, Catalog 32).
* Style lint (`audits/logs/ch34-skeletons-stylelint.log`): 0 FAIL; the
  `TuringMachine` tree's 8 size WARNs are the pre-existing recorded exceptions,
  none in a file under audit.
* `sorry` tokens: 47, all in the three new files; no `axiom`.
* Statement-freeze baseline: commit `7fbac9bd` itself (snapshots regenerate via
  `scripts/decl_snapshot.py --git-rev 7fbac9bd`).
* Drafting provenance: the skeleton was drafted by a maintainer-directed agent
  and then reviewed line by line by the maintainer, who traced each routine's
  phase semantics and spot-checked the restated time clauses of
  `computesFunInTime_id`/`_prepend`/`_cond` and `exists_loopTM` verbatim against
  the originals. The review record is the plan's decision-log row of 2026-10-08.

## Known deviations and judgment calls (declared — verify each, flag others)

1. **R1 transformer shape** (`Embed.lean`): closed, state-preserving transformers
   (`S → S`; source halt = host halt), **not** the host-parametric
   `hagree`/`emb`/`ret` shape of `Turing.capture_run`/`emit_run`. Lockstep is
   therefore an unguarded equality at every `t`; live-return dispatch is
   delegated to R2. The retrofit's `emitterBank*` privates are literally
   `hagree`-shaped — the declared position is that `embed∘seam` covers them; if
   you find a consumer it cannot cover, that is a shape finding.
2. **R1 silent flavor**: capture rendered as `bufferTape (pre ++ c.output)` with
   head one past (mirrors `captureCfg`); `hcap : cap ∉ Set.range ι` on every
   silent contract (declared possibly-superfluous for the lockstep equality
   itself, kept for the capture semantics); the cap-tape space bound uses
   ℕ-subtraction `(…).output.length - c.output.length + 1`.
3. **R2 dispatch constant is exactly `1`** (`T₁ + 1 + T₂`), dispatch-on-anchor
   (not on halt), matching the live-anchor ABI; `T₁ = 0` is covered by the
   dispatch step alone; phase-two mid-run halts are excluded by `h₂`'s live
   anchor.
4. **R2 space headline is per-tape visited-set containment** (frozen decision
   12.1 — the sharp form); equality is believed to hold but containment is
   stated; "disjointly owned" is rendered as "one phase's visited set on tape
   `i` is `{0}`" in the max corollary.
5. **R3 promotions**: five machines defined fresh (grep confirmed no public
   `copyTM`/`compareTM`/`incrementTM`/`clearTM`/`transferTM` existed — the
   audited catalog is private machines + existential contracts). Space bounds
   are `|w| + 2` (the `-1` overshoot cell is intrinsic: a binary-alphabet head
   detects the origin by overshooting onto the left blank). Transfer/copy are
   stated at the design's `3|w| + 3` though the two-pass builds achieve
   `2|w| + 2` — deliberate slack, bounds not exact. `compareTM`'s verdict lives
   in the exit anchor (`FlagPhase.done v`, two live anchors, the cut excludes
   both); `incrementTM`'s overflow leaves the wrapped all-`false` word (the
   enumerator convention).
6. **Part-2 row shape**: `∃ M c, time-contract ∧ ∀ x t, spaceUsed ≤ bound` —
   one witness for both clauses, space quantified over **all** `t` (equivalent
   to at-halt by post-halt constancy); total `spaceUsed` for the existential
   rows, per-tape for the named machines and W1/W2.
7. **Scope**: P1-P15 as realized, W1-W3, L. The E3′ stream rows **P16-P18 ride
   with the emitter-lazy scope** (decision 12.3's clarification of 2026-10-08,
   recorded in the design doc; their only consumers are the emitters). Confirm
   or contest this reading of the original "P1-P18" wording.
8. **Named bound choices**: `lengthBits` space `c·(Nat.size n + 1)` (the sharp
   log clause chapter 4 consumes); `polyBits` space `c·(C·(n+1)^e + 1)`
   (witness-honest linear-in-value, **not** logarithmic — declared deviation);
   `pairLenCheck` `c·((n+1)^e + n + 1)`; `splitSolve` space one degree below
   time; `pairMapSnd` takes `Sg` + `Monotone Sg`; `cond` concludes
   `sD + max(s₁,s₂) + c` (additive constant); the loop row's space hypotheses
   are bounded only within the round budget (`t ≤ T |x|`) and the conclusion
   `c·(S n + T n + 1)` does **not** scale with `R` — the design's headline
   space property.
9. **L row** annotates the decision form `exists_loopTM` only; the `Cfg` and
   `find` siblings are documented to inherit the host at fill time.
10. **[Bon26] citations** (policy.md §2, *Design adaptation*) are carried in all
    three module docstrings and at adapted declarations; verify presence and
    accuracy, not taste.

## Specific questions (prioritized)

1. Is the **R1 closed-transformer shape sufficient for the three named
   consumer families** (retrofit bank/relocation privates; Hennie-Stearns zones;
   the two-tape universal)? Exhibit a concrete consumer step that cannot be
   expressed as `seamCompTM`-glued `embed{Silent,Emit}TM` runs if you believe
   one exists.
2. Re-derive the **R2 composition**: is `T₁ + 1 + T₂` exact under the stated
   first-return cut, including `T₁ = 0`, `entry = q₂` with `T₂ > 0`, and `M₂`
   halting strictly inside its window? Is `seamCompTM_firstReturn` strong
   enough for iterated chaining (three or more phases)?
3. Check every **exact constant and space interval** in Part 1 by independent
   head-movement counts (sweep/turn/rewind/enter), including: does `compareTM`
   really achieve `2·min + 2` on *equal-prefix unequal-length* inputs, and is
   the `[-1, min + 1]`-trajectory claim consistent with the stated `min + 2`
   visited bound in all mismatch positions?
4. Diff every Part-2 **time clause against the audited original** in the
   attached home files (restatement-drift hunt), and judge each **space bound's
   witness-honesty** (can the existing audited witness family meet it, or does
   the row silently demand a new machine? `polyBits` and `stripLast` deserve
   particular suspicion).
5. Does the **loop space row** interact soundly with the audited loop
   hypotheses — in particular, can `hroundSpace`'s round-budget-limited bound
   (`t ≤ T |x|`) really control the host's whole-run space when rounds restart
   at seams, and should the fuel word's length come from
   `Nat.bits (R n)` rather than `T n`?
6. **S-statement proposals**: name any missing boundary sanity statements
   (e.g. `transferTM` at `w src = []`; `compareTM` at `fst = snd`, which the
   statements do not exclude — is the verdict `decide (w fst = w fst) = true`
   delivered by the machine, or does the lockstep double-move break?).

## Findings format

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|

Severity guide: **blocker** = a consumer phase would build on a wrong statement;
**major** = materially misleading but fixable; **minor** = edge case or
naming/attribution defect; **note** = observation. Findings go verbatim into
`audits/routine-infra-findings.md`; gate closes on zero blockers and majors.
