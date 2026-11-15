# seq-zk-c soundness work log

Issue base: `107f1e8c218733eac12d6b9bee6fece441271317`.

Read policy.md and issued brief and both addenda. No Lean or Lake process started.

Initial searches:
- `rg -n "exists_proverCoins|uprob.*prod|uprob.*equiv|uprob.*fst|uprob.*snd|sound.*rep|Sound.*rep|seqRep" TCSlib/Cryptography TCSlib/InformationTheory`

## Searches before execution-prefix declarations

- Searched TCSlib for `exec.*(IsPrefix|take)|IsPrefix.*exec|take.*exec`: no matching general
  interactive-execution reader. An unrelated WordRAM execution was excluded.
- Searched Lean 4.25.0 `Init/Data/List`: reused `List.prefix_append_of_prefix`,
  `List.prefix_rfl`, `List.prefix_iff_eq_take` instead of re-proving prefix algebra.
- Searched the lead Mathlib clone at HEAD `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`
  using `git grep` because cache checkout was in progress:
  `exec.*(IsPrefix|take)|IsPrefix.*exec|take.*exec` under Mathlib/Data/List and
  Mathlib/Computability. No applicable interactive-execution theorem found.
- `prefix_iff_eq_take|IsPrefix.*take|prefix_append` under Mathlib/Data/List found
  `Mathlib/Data/List/Infix.lean:41` (prefix monotonicity of take), not needed because the core
  characterization gives the exact recovery equations directly.

## Overlap and reuse

- `Composability.exec_prefix` is a new iteration consequence of the published `exec_succ`
  reader at `TCSlib/Cryptography/ZeroKnowledge/Interaction.lean:266`; it does not restate an
  existing execution-prefix result. It directly reuses core List prefix transitivity through
  `List.prefix_append_of_prefix` (`Init/Data/List/Sublist.lean:706`).
- `exec_fst_take` and `exec_snd_take` specialize core `List.prefix_iff_eq_take`
  (`Init/Data/List/Sublist.lean:1315`) to the two execution histories. They publish the
  execution-specific interface requested by the lead; proof is direct reuse.
- Promotion request: the three generic execution-prefix readers belong beside `exec_succ`
  in `ZeroKnowledge/Interaction.lean` at a future shared-file window. This fill keeps them in
  its permitted helper module without editing that frozen file.

## Draft status

Wrote Soundness.lean's three complete declaration bodies. No Lean process has run: waiting
for the lead's package/bootstrap authorization. These declarations remain unverified drafts.

## Adaptive soundness helper

Added the complete but uncompiled draft `uprob_adaptive_all_le`. Search first:
- TCSlib `uprob_and_le_mul|uprob_adaptive_escape`: found and directly reused
  `OneWay.uprob_and_le_mul` at `OneWayFunctions/Basic.lean:90`.
- Mathlib pinned source `prob.*(prefix|adapt)|adaptive.*prob|prob.*pi` under
  `Mathlib/Probability/ProbabilityMassFunction` and `Mathlib/Probability/Kernel`:
  no applicable finite uniform adaptive-rate theorem.
- Mathlib `snocEquiv` search: reused `Fin.snocEquiv` at
  `Mathlib/Data/Fin/Tuple/Basic.lean:701`, rather than duplicating the private equivalence.

Overlap disclosure:
- `uprob_adaptive_all_le` generalizes `ThreeColoring/Protocol.lean:307`
  `uprob_adaptive_escape`, from challenges in `Fin m` with escape rate `1-1/m` to an
  arbitrary finite type and arbitrary nonnegative rate. The existing theorem cannot supply
  the exact frozen bound `s^Q` for a general error function `s`.
- Its local prefix equalities re-derive the cast arithmetic of private
  `challengesBefore_snoc_castSucc` (`ThreeColoring/Protocol.lean:275`) and private
  `challengesBefore_snoc_last` (`:286`) for a general finite type and explicit restriction.
  Those lemmas are private and specialized to `Fin m`; no private lemma was copied or
  referenced. The proof uses core `Fin.ext` and published `Fin.snoc_castSucc`.
- No new host or definition is introduced. Promotion request: the generic adaptive bound
  belongs in `Foundations/Probability.lean` or `HardcoreBit/Basic.lean` at a shared-file window.

Direct Mathlib imports `Mathlib.Data.Fin.Tuple.Basic` and `Mathlib.Tactic.Ring` are both already in supplied roots.txt.

## Compilation attempts

- Attempt 01: slot wait from 09:10:07 UTC; checker finished 09:11:14 UTC, exit 1. Syntax error: `prefix` is reserved, renamed binder to `pre`. Removed unused `if_false` simp argument. Max RSS 2,129,903,616 bytes. Raw log check-01.log retained.

- Attempt 02: exit 1, two dependent-function inference errors in local `Fin.snoc` prefix equalities. Added explicit codomain ascriptions `Fin (q + 1) → α`. Max RSS 2,143,354,880 bytes. Raw log check-02.log retained.

- Attempt 03: exit 1, simplifier did not match the dependent prefix functions. Introduced explicitly typed intermediate phase propositions before rewriting the prefix equalities. Max RSS 2,143,535,104 bytes. Raw log check-03.log retained.

- Attempt 04: exit 0, no errors or warnings. The helper emitted a fresh olean. Max RSS 2,152,775,680 bytes. Raw log check-04.log retained.

## Checked delivery status

All four new theorem declarations compile without admissions. The final source has 163 lines, maximum width 94, SHA-256 `71f0a20ff0b94ff6e064238cf6c4c105ceb68f856419e2ec37d61f695f29e653`.

The lead supplied APFS clones of the first 209 baseline modules into this worktree’s own `.lake/seq-zk-c-oleans`. `.lake/packages` links read-only to the lead package tree. No Lake command was run by this sub-agent. Every Lean invocation held a slot through the shared wrapper, with `LEAN_SLOT_TAG=seq-zk-c`; slot records are included. Host cap: at most three Lean processes across all jobs.

Exact invocation for all four attempts:

```sh
LEAN_SLOT_TAG=seq-zk-c TCSLIB_OLEANS=/Users/seyoonr/.codex/worktrees/seq-zk-c/tcslib-exchange/.lake/seq-zk-c-oleans /private/tmp/seq-zk-lean-slot.sh /usr/bin/time -l bash scripts/lean_check_tree.sh TCSlib/Cryptography/Composability/SequentialZK/Soundness
```

The lead must run the final merged-branch sweep, axioms, seals, and lint as required by the brief.
