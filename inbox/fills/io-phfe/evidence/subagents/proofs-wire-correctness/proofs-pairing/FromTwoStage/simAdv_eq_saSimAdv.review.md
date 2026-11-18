# simAdv_eq_saSimAdv proof candidate

The exact frozen theorem header and entire docstring are unchanged. The body
has one tactic block, one simp-only step, no admissions and no helper. No Lean,
lake, Git, live edit or checker was run. Native validation remains pending.
Its substantive dependency expect_simGame_eq_saGame is queued for root native
checking; this candidate is not claimed independently standard-axiom-only.

S.simAdv_eq and S.saSimAdv_eq read the two stated advantages through the common
Games.advantage interface. advantage_eq exposes their absolute acceptance gaps,
accept_eq exposes the probability of output true, and ProbComp.prob_eq_expect
uses the same real-valued indicator test fun b => if b = true then 1 else 0.
The existing exact expectation law then rewrites each committed experiment to
the corresponding derived semi-adaptive experiment, for true and false alike.
Both absolute-difference expressions become identical.

Every simp entry is a published reader/law, not a definition body. No algorithm,
machine, sampler, game equality, security assumption or auxiliary arithmetic
fact is introduced. The advantage orientation is unchanged and the result has
no loss or extra hypothesis. No mathematical obstruction found.
