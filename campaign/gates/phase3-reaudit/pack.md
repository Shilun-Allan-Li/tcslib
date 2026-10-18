# External audit pack — Phase 3, round 2 (re-audit of the blocker repairs)

Round 1 (`audits/phase3-findings.md`, attached) found **two blockers** on the phase-3
statements — the algebraic `MachineCode` admits noncomputable-meaning schemes
(Argument A), and the input-first layout falsifies every stated time bound
(Argument B) — plus three majors and two minors. The fill round and supporting
lemmas were audited clean (findings 9-13). All findings were accepted and resolved
at commit `afe5c3ea`, entirely at the statement/definition level. This round audits
the repairs. Phase 3's gate closes when this round returns no blockers or majors.
Record findings in `audits/phase3-reaudit-findings.md`.

## Resolution changelog (round-1 finding → change made)

| # | Finding | Resolution |
|---|---|---|
| 1 | blocker — algebraic scheme admits noncomputable meanings | New `EffectiveMachineCode extends MachineCode`: an in-model `canonizer : FinTM Bool` computing `fun α => (decode α).serialize` within some `canonizerTime`, where `CodeTM.serialize` is a **new, concrete, scheme-independent** serialization (state count, initial state, full table, fixed enumeration). All three universal statements now require `EffectiveMachineCode`. The docstrings record why targeting the scheme's *own* `encode` would not exclude Argument A's pathology. |
| 2 | blocker — input-first layout falsifies the bounds | Layout is now **code first**: `pairEncode α x` (doubled code, verbatim input), with the deviation from [AB09]'s `⟨x, α⟩` documented on `pairEncode` and in the module docstring; startup is α-dependent and absorbed into `C`; the timed machine uses `pairEncode (pairEncode (Nat.bits t) α) x`. |
| 3 | major — no all-string evaluator, no divergence preservation | `universal` is restated as the evaluator: `∀ α, ∃ C, ∀ x`, forward bound `C · (t + 1)` for `c.decode α` (covering padded and fallback representations), **plus the converse**: any output `U` completes is an output of the denoted machine, so divergence is preserved. |
| 4 | major — quadratic theorem is a total-function corollary | Labeled as such in name-adjacent prose and docstring; the machine-level partial statement is `universal` itself. The scheme parameter is retained (it selects `U`); the sketch now routes `α := c.encode` of the normal form through `MachineCode.decode_encode`. |
| 5 | major — serialization omitted the initial state | `CodeTM.serialize` records `q₀` (unary, self-delimiting) between the state count and the table; the `exists_effectiveMachineCode` sketch parses it. |
| 6 | minor — deadline case unspecified | Documented: halting checked after every simulated transition including the `t`-th (deadline-inclusive success); `t = 0` reports timeout via `not_computesInTime_zero`. |
| 7 | minor — pack namespace erratum | Acknowledged: the lemma is `Complexity.succ_pow_le`. |
| 8 | note — pairing parser lemma requested | `pairEncode_injective` added (sorry'd, Argument D's aligned-pair sketch). |
| 9-13 | notes | No changes required; finding 13's request for baseline diffs/build evidence is noted for future packs (this pack again ships attestations, not raw logs). |

`exists_machineCode` was **removed**, subsumed by `exists_effectiveMachineCode`
(the only removal; everything else is additive or in-place restatement).

## Brief for the auditor

Ground rules as always (trusted surface; no blanket approval). Priority order:

1. **Re-run round 1's two counterexamples against the repaired statements.** Does
   Argument A's permuted scheme fail to instantiate `EffectiveMachineCode` — i.e.
   does computing `serialize ∘ decode` for it really decide the undecidable set?
   Is there a *new* pathology that satisfies the canonizer contract while still
   defeating universal simulation (e.g. schemes exploiting `canonizerTime` being
   arbitrary, or the serialization being non-injective)? Does Argument B's
   identical-prefix construction fail against the code-first layout, including for
   `timed_universal`'s nested pairing?
2. **Blind-restate the changed/new declarations**: `CodeTM.serialize` (and its
   private field formats), `EffectiveMachineCode`, `exists_effectiveMachineCode`,
   `pairEncode_injective`, and the three universal statements.
3. **Check the converse direction of `universal`** for adequacy and truth: is
   "`∃ t, U.ComputesInTime … output t → ∃ t, M.ComputesInTime x output t`" the
   right divergence-preservation statement, and is it consistent with the forward
   direction (e.g. can `U` legitimately produce *no* output at all when `M`
   diverges — is that expressible/required)?
4. **Phase-4 readiness**: with `EffectiveMachineCode` + the evaluator + the timed
   machine, is the interface now sufficient for [AB09]'s `UC` diagonalization and
   the `HALT → UC` reduction (PDF pp. 48-49), or is anything still missing (e.g.
   effectivity of `encode`, which is deliberately *not* required — check whether
   the diagonalization needs to *compute* `α ↦ encode (something depending on α)`)?

## Specific questions

1. Is `serialize` injective as defined (two-bit codes, unary states, fixed record
   order)? Non-injectivity would weaken the canonizer contract's power to exclude
   pathologies — check `numStates` mismatches, the unary/table boundary, and
   whether `Nat.bits` (no leading `false`s, `Nat.bits 0 = []`) creates collisions
   in the doubled-bit region.
2. Does the `canonizer_computes` field's *totality* (it is a `ComputesFunInTime`,
   so the canonizer halts on **every** string) create any unintended strength or
   weakness?
3. In `universal`, `C` now depends on `α`. [AB09] has the constant depend on the
   machine; a padded code `α ++ 1^m` denotes the same machine but may get a larger
   `C`. Acceptable rendering, or should `C` factor through `c.decode α`?
4. `universal_quadratic`: with the code-first layout, verify the corollary's bound
   no longer needs a startup term (the counterexample machines of Argument B never
   read `x`).
5. Adversarial: a scheme whose `decode` is constant (everything denotes one fixed
   machine) — it satisfies `MachineCode`? (No: `decode_encode_pad` forces
   injectivity of `encode`… verify.) A scheme with `canonizerTime = fun _ => 0`?
   `pairEncode (Nat.bits 0) α` in the timed statement (`t = 0` gives an empty
   clock region)?

## Scope

| Item | Where |
|---|---|
| Files under audit | `TCSlib/Complexity/TuringMachine/{Encoding,Universal}.lean` (attached with all other sources for context) |
| Source text | Arora & Barak 2009, §1.4-§1.4.1, Theorem 1.9 (PDF pp. 45-47); §1.5-§1.5.1 (PDF pp. 48-49) for the phase-4 readiness check |
| Context | round-1 findings (attached), `AroraBarakChapter1Plan.md`, `policy.md` |
| Out of scope | tactic scripts; the fill round and supporting lemmas (audited clean in round 1) beyond spot-checks |

## Findings format (auditor fills)

| # | Severity | File · declaration | Claim | Evidence / counterexample | Proposed fix |
|---|---|---|---|---|---|
| 1 | blocker / major / minor / note | | | | |

Severity guide: **blocker** = a downstream phase would build on a wrong statement;
**major** = fixable but materially misleading; **minor** = edge case or
naming/attribution defect; **note** = observation, no change required.
