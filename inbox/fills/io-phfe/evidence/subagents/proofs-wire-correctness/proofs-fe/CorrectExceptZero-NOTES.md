# First low-level FE proof draft

Live source read at parent's stated HEAD
7d42a6ef6a20d379c524c11db87a1b0c0e4c25df; no Git command was run to independently check it.
No live source edit, Lean/lake/build, new helper or interface statement change.

Target: FEScheme.Raw.Correct.correctExcept_zero in Defs/Correctness.lean:149.
Draft: CorrectExceptZero.lean, same proposition with `_draft` suffix to avoid a name clash.
To integrate, import TCSlib.Cryptography.Games.Hopping in the original module and replace
only the original theorem body with the draft term. No tactic block was authored.

Reasoning: read perfect correctness through correct_iff. AllOutputs.mono turns each
correct-decryption identity into the negation of its inequality. The shared
prob_eq_zero_of_allOutputs gives probability exactly zero for the failure event;
Eq.le supplies the required bound, then correctExcept_iff assembles the proposition.

Searches actually run (read-only rg/sed/cat):

- rg `correctExcept_zero|Correct\.correctExcept|AllOutputs.*prob|prob.*AllOutputs|
  allOutputs.*prob|prob_eq_one|prob.*eq_one` throughout live TCSlib/Cryptography.
- rg `prob_eq_zero_of_allOutputs` throughout live TCSlib.
- rg `theorem.*AllOutputs|theorem allOutputs|def AllOutputs` in Games/OracleComp.lean
  and Games/Probability.lean (Games/Oracle.lean was absent; no guess was substituted).
- Read Games/Hopping.lean:90-128 and Games/OracleComp.lean:308-326.
- Read the nearest existing use in PrivateKey/OracleFromPRF/Collision.lean:294-328.
- Read the entire live Defs/Correctness.lean and Run.lean, plus current
  SemiAdaptive/FromTwoStage law/advantage statements to choose the smallest target.

Reused dependencies:

- Defs/Correctness.lean:126 `correct_iff`, :139 `correctExcept_iff`.
- Games/OracleComp.lean:316 `OracleComp.AllOutputs.mono` (argument order verified).
- Games/Hopping.lean:116 `ProbComp.prob_eq_zero_of_allOutputs`.
- Core/Mathlib `Eq.le` converts equality to the order bound.

No exact?/apply? probe was run, because this agent is forbidden to run Lean/build checks.
Status: DRAFT_UNELABORATED. Parent must check inference of the failure-event predicate.
No apparent false/unprovable claim was found for this implication.
