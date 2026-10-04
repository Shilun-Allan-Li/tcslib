# Review criteria — Mathlib design principles

Both the formalizer and the critic work against this list. The critic rejects on
any **Blocking** item; **Advisory** items are raised but do not by themselves
hold up a unit.

## Blocking

0. **`policy.md` outranks this file.** Where the repo's `policy.md` and this
   rubric disagree, policy wins and this rubric is amended. In particular its
   §2 (a `## References` section per file, `[AB09, location]` tags on every
   source-derived declaration) and §3 (a `**Proof sketch.**` paragraph for any
   proof over ~20 tactic lines) *mandate* prose that item 7 below would have
   counted against. References, source tags, proof sketches and the
   `## Divergences` block item 2 requires are therefore **exempt from item 7's
   volume limits** — they are required content, not bloat.
   Item 7 still applies with full force to everything else.

1. **It compiles.** `lake build <module>` exits 0 with no errors. No new `sorry`,
   and no `sorry` smuggled in behind a `Prop`-valued stub.
   *For this task, running `lake build` is required and explicitly overrides the
   "never run lake build" instruction in `.claude/CLAUDE.md` — that rule applies
   to the sorry-ladder proof workflow, not here.*
2. **The statement is faithful to Arora–Barak.** Read the actual page in the PDF.
   Any divergence from AB's wording must be deliberate, class-preserving, and
   recorded in the module docstring — the way `PPoly.lean` records its fan-in,
   basis, size-measure and layering divergences.
3. **No vacuous or degenerate definitions.** Check the edge cases: `n = 0`,
   empty lists, the empty circuit. `FeedForward.size` is `Nat.card`-based and
   silently returns `0` on infinite types, so any new definition touching size
   must carry the finiteness hypothesis. A definition that is trivially
   satisfiable is a bug, not a simplification.
4. **Reuse what exists.** Do not redefine `Language`, `Clause`, `CNFFormula`,
   `Circuit`, `FeedForward`, or anything else already in Mathlib or in TCSlib.
   Search before defining. Existing assets: `ACP.FeedForward` and its gate sets,
   `ACP.CircuitFamily`, `Language.InSIZE`/`InPPoly`, `BoolCircuit.Circuit`,
   `Literal`/`Term`/`DNF`/`CNF`, `NPReductions.SATTo3SAT`.
5. **Naming follows Mathlib.** `UpperCamelCase` for types and `Prop`s
   (`IsRegular`, `InPPoly`), `lowerCamelCase` for data-producing defs
   (`circuitDegreeBound`), `snake_case` for theorems, named after what they say
   (`toCircuit_size_le`, `mem_language_iff`, `inPPoly_iff`). Class membership
   reads `Language.InX`, mirroring `Language.IsRegular`.
6. **Every declaration has a docstring**, and every module opens with a
   `/-! # Title ... ## Main definitions ... -/` block naming the AB result it
   formalizes by number.
7. **Keep comments lean.** The module docstring stays **under ~40 lines**, and a
   file must never have more comment than code. Declaration docstrings are one
   or two lines; say what the thing *is*, and stop. Record a design decision
   once, in the module block — never restate it in the declaration docstring
   beneath it. Reject on duplicated prose, on essay-style justification, and on
   any docstring that argues a point instead of stating a fact. `PPoly.lean` was
   trimmed from 113 docstring lines to 38 for exactly this reason; do not
   recreate the bloat.

   Note the exemption in item 0: a file's `## References`, its `[AB09, …]` tags,
   its proof sketches and its `## Divergences` block do not count against the
   ~40-line module docstring cap or the comment-under-code ratio. `## Divergences`
   is exempt for the same reason: Blocking item 2 *requires* it, so counting it as
   bloat would set two Blocking rules against each other.

   **Measure with this command, not by estimate.** Three units in a row reported
   counts that did not reproduce. A blank line inside a `/-! ... -/` block counts
   as comment — the stricter of the two conventions, which is the point of the
   rule:

   ```
   awk '
     /^[[:space:]]*$/ && !inb { blank++; next }
     inb { comment++; if (/-\//) inb=0; next }
     /^[[:space:]]*\/-/ { comment++; if (!/-\//) inb=1; next }
     /^[[:space:]]*--/ { comment++; next }
     { code++ }
     END { printf "total=%d code=%d comment=%d blank=%d\n", NR, code, comment, blank }
   ' <file>
   ```

   Quote this command's output in your report. A figure produced any other way
   is not a measurement.

## Advisory

7. **Prefer `∀`-bounds to asymptotics.** Stay `ℕ`-native. Do not introduce
   `Asymptotics.IsBigO` or `ℕ → ℝ` coercions to state a bound that a pointwise
   inequality expresses — the surrounding library (`toCircuit_size_le`,
   `MODq_notin_AC0p_quantitative`) is exact and coercion-free, and the reasoning
   is recorded in `PPoly.lean`'s docstring.
8. **`@[simp]` only for genuinely canonical rewrites**, in the normalizing
   direction.
9. **Don't over-generalize.** Generalize a definition when a second use exists
   or is imminent, not on speculation.
10. **Proofs should be readable.** Prefer structured `have`/`calc` to a long
    `simp_all` chain. Per the repo's own guideline, a `have` becomes a named
    lemma only when it is substantial and reusable; one-liners stay inline.
11. **Match surrounding style.** Copyright header, `set_option` choices, and
    import granularity as in the neighbouring `CircuitComplexity/*.lean` files.

## File ownership under parallel tracks

Units with no dependency between them run concurrently. Every agent owns exactly
one `.lean` file and edits only that.

**Orchestrator-owned, never written by an agent:** `ch6/PLAN.md`,
`ch6/CRITIQUE_LOG.md`, `TCSlib/Complexity/CircuitComplexity.lean` (the aggregator
import list), and any `.lean` file belonging to another track. Agents report what
needs registering or flipping; the orchestrator applies it.

This is not bureaucracy — two agents appending to the same log lose each other's
writes, and two agents editing the aggregator's import list clobber each other.

**A name inside a docstring is not checked by the compiler.** A mechanical
rename can turn a `## Main definitions` entry into a dangling name and leave the
build green — this happened: a `Circuit.Circuit. → Circuit.` de-duplication guard
also matched inside `BoolCircuit.Circuit.`, mangling one call site (caught by
`lake build`) and **two** docstring references (caught by nothing). The unit's own
post-rename grep found one of the two, because it was run over the files the
rename *targeted* rather than over every file the script *wrote to* — and the
guard did not care which name followed the prefix.

So: after any mechanical edit, extract every backticked identifier from every
comment in every file the script wrote to, and resolve each against the live
environment. Not against the list of names you meant to change. The build will
not do this for you, and three of this loop's Blocking findings have lived in the
part of a file the compiler never reads.

**A check that has never failed is not yet evidence.** When you build a sweep to
close a defect class, run a **positive control**: inject a defect into a scratch
copy and confirm the sweep reports it. (The clean run over real files is the
*negative* control, and a classification of benign unresolved entries already is
one.)

**The injected defect must differ in shape from the one that prompted the
check.** Re-injecting the original establishes that the plumbing fires and
nothing about reach. This was tested: an identifier sweep built after a
`Circuit.Circuit. → Circuit.` rename caught its own defect, and its author
proposed the `BoolCircuit.` prefix as the signal distinguishing a real break from
benign unresolved names. A critic injected three breaks of *other* shapes — a
bare `Circuit.` typo, a `Language.` typo, and a name-fragment typo. The sweep
caught 3 of 3; **the prefix discriminator caught 0 of 3.** The prefix was an
artefact of that one substitution pattern. What did the work was the **closed
taxonomy**: module path, file name, declared fragment, prose, binder — and
nothing else admitted.

**Reconstruct every "deliberate name fragment".** That bucket is the one place
where "unresolved and benign" is a judgement rather than a fact: `_size_lt` sits
in the list indistinguishably from `_size_le`, and a typo there is invisible to
the sweep alone. Resolve each fragment against a real declaration by line.

**Line length is measured in characters, not bytes.** `awk`'s `length` counts
bytes and overstates any line carrying `ᵏ`, `∧`, `ⁱ` or similar. Measure in
Python, or expect false positives on exactly the prose lines this rubric is most
likely to make you rewrite.

**Summaries cite, they do not re-derive.** `ch6/PLAN.md` and
`ch6/NOT_FORMALIZED.md` describe work that lives in the Lean files. Twice now a
ledger row has re-derived a docstring's arithmetic and got it wrong — once
collapsing two of AB's conventions into one that exists nowhere, once quoting an
excess against the wrong baseline — while the docstring it summarised was right
both times. A ledger row states *what* is formalized and *what is not*, and points
at the module docstring for the numbers. If a summary needs an equation to make
its point, that is a sign the point belongs in the file, not the ledger.

**The axiom sweep: use the module-index filter, and do not exclude internals.**
Walk `env.constants` filtered by `env.getModuleIdxFor? nm == env.getModuleIdx? <module>`,
calling `Lean.collectAxioms` on each, from a scratch file that *imports* the
module. Two traps, both hit in this loop: `env.constants.map₂` only works from
inside the file being checked, so a sweep written that way leaves nothing
re-runnable for a critic; and an `!nm.isInternal` guard drops `private`
declarations, since those are mangled to `_private.…`.

Keep the second in proportion. `collectAxioms` is **transitive**, so a `sorryAx`
in a private lemma reachable from any public declaration was already caught by a
public-only sweep; the guard hides only a private reachable from nothing public,
i.e. dead code. It is a narrow gap worth closing, not a hole that made earlier
sweeps worthless. And an unguarded count is not a declaration count — of 610
constants across three files, 326 were internal (equation lemmas, `match_*`,
recursors) and 284 were not.

**Scratch files are shared too, and this has already bitten.** One track's
`#print axioms` scratch file was overwritten mid-run by another track's, so the
output it read back was a *different unit's*. Give every scratch file a name
carrying your unit number (`u9_axioms.lean`, not `axioms.lean`), and re-run rather
than trust a result whose input file you did not just write. A verification that
silently measured someone else's code is worse than no verification.

Cross-track drift is the orchestrator's problem, not any single critic's: a
per-file critic cannot see that two tracks defined the same helper lemma twice or
diverged on naming. A cross-cutting pass runs once all tracks land.

## Critic output format

Write to `ch6/CRITIQUE_LOG.md`, appending a section per round:

```
## <unit id> — round <k> — <VERDICT: PASS | REVISE>
- [Blocking|Advisory] <file>:<line> — <what is wrong> → <what to do instead>
```

`PASS` requires zero Blocking items. On `PASS`, flip the unit to `DONE` in
`ch6/PLAN.md`. Cite file and line for every finding; do not report vague unease.
If a previous round's finding was addressed, say so and drop it.
