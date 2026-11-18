# Concrete DLIN ladder: isolated hMatrixAccept

Status: scratch proof-only candidate, inspection only; native verification/timing pending.
No Lean/lake/build/Git/live edits, process operation or extra agent was run. Exactly one
block, four-space body, no holes/sorry, ≤100 columns. Local/frozen targets unchanged.
This fills ONLY hMatrixAccept; hTupleAccept remains admitted and untouched.

Exact target: accept(G.dlinMatrixGame D false κ)=E_(publicParamsGen G κ) P.
Context is exactly the local H/P/Q/loss in the four-obligation ladder.

## Staged one-side normalization

1. Read the actual matrix game and matrix sample through their public equations, accept_eq,
   outer prob_bind and expect_bind. Compare only the functions under publicParamsGen using
   congrArg/funext, fixing pp. Read the ab bind, reduce local P only, then fix ab likewise.
2. The small expect_bind/pure + closed-false-branch simp only normalizes the remaining rs/u
   sample spine. No prob_bind/prob_eq_expect/H rule is in this simp list; the D-coins leaf
   stays an opaque application of prob to its actual computation.
3. Local word/obs merely name the existing encoded input and existing leaf probability.
   The false matrix response no longer mentions rs. The only expect_const application
   explicitly supplies BOTH the unused rs sample and the exact remaining E_u obs value.
   No unrestricted constant-integrand search is made against the distinguisher computation.
4. Fix u under its common expectation. Local verdict names the same D.distinguisherL
   application without evaluating/unfolding D or its machine. Read ONLY the RHS probability
   with fully instantiated prob_eq_expect(sample D.Coins)(verdict= true), then read the
   LHS sampled-verdict bind with prob_bind. Compare its two integrands under D.Coins.
   prob_pure at the abstract verdict r is exactly the final indicator equality.

## Rule10: no ProbComp.prob definitional reading

The change steps only FOLD local word/obs/verdict and local H. At every such step the foreign
ProbComp.prob head and its complete actual arguments already match structurally on the
respective side; no differing probabilistic computations are identified by reduction.
The semantic conversion from prob(bind pure verdict) to prob(sample)(verdict=true) is made
EXCLUSIVELY by the three published readers prob_bind, prob_eq_expect and prob_pure. ProbComp.
prob itself, sample, game functions, encodings and distinguisher definitions are NEVER passed
to dsimp/simp/rw/unfold as definitions. The only dsimp name is local P. No foreign generated
-equation reader is used. This addresses the explicit seal requirement rather than relying
on the unsealed definitional implementation of prob.

## Dependencies / unchanged semantics

Uses existing proved game/sample/accept/probability readers only; it is independent of the
new diagonal bound, hPoint/hLoss and all codec/correctness assumptions. Both actual group
and machine coins retain their original ordering/law. No sampler, machine, generic helper,
scalar witness, DLOG, inverse encoding, or public algorithm/efficiency contract is introduced.
The input word is identical to local H; no alternative wire layout is constructed.

## Actual static inspection this invocation

Read exact current dlinMatrixSample_eq and dlinMatrixGame_eq in Pairing/Linear.lean; actual
line numbers have shifted as root integrated earlier codec proofs. Read Games/Advantage
accept_eq, Probability.expect_bind/pure and prob_eq_expect/prob_bind/prob_pure. Re-read the
ladder H/P definitions and compared every concrete challenge argument. Searched existing
closed-false-branch probability proofs; BonehBoyenSecurity uses Bool.false_eq_true/if_false
with the same public probability readers. No new helper API was needed.

The saved block deliberately does not use the earlier BOTH-side simpa list, does not mix
general prob_eq_expect with bind normalization before the leaf, and never recursively
simplifies expect_const. Native focus: exact one-bind rewrite selection and local input/test
alias matching after fixing pp/ab/u; not a new mathematical distribution obligation.
