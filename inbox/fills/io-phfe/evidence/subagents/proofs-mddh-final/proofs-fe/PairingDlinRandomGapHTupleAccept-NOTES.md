# Concrete DLIN ladder: isolated hTupleAccept

Status: scratch proof-only candidate, inspection only; native verification/timing pending.
No Lean/lake/build/Git/live edit/process operation/extra agent was run. One tactic block,
four-space body, no remaining holes/sorry, ≤100 columns. Exact local/frozen targets unchanged.
This fills ONLY hTupleAccept. Other ladder blocks and all live source files are untouched.

Exact target: accept(G.dlinGame D false κ)=E_(publicParamsGen G κ) Q.
H/Q are exactly the local definitions in the four-obligation ladder.

## Staged canonical-game readers

Read only accept_eq, dlinGame_eq, dlinSample_eq and outer probability/expectation binds.
Use congrArg/funext successively to fix pp, ab, rs and t in their EXISTING order. All canonical
random-branch scalar draws are used; there is no expect_const step and no unused-rs claim.
Read the sample's final pure return, reduce only its closed false branch. Reduce local H,
then read the literal three-vector entries with published Matrix vector equations. This
identifies the exact canonical response exponents ab0*rs0, ab1*rs1 and t in local H.

Only at that single leaf are word/verdict named as local opaque expressions. They retain the
actual dlinEnc/dlinChallenge and D.distinguisherL applications without unfolding or evaluating
them. Fully instantiated prob_eq_expect reads the RHS probability on machine coins; prob_bind
reads the LHS sampled-verdict continuation. Fix r under the common machine-coin expectation.
ProbComp.prob_pure at the abstract verdict r gives exactly the remaining indicator equality.

## Rule10 semantic separation

No ProbComp.prob definition is passed to dsimp/simp/rw/unfold. The two dsimp names are local
Q and local H. H expansion exposes its unchanged prob APPLICATION, without reading the
foreign probability implementation. The change step only folds local word/verdict; each
side's probability head and full actual computation/predicate already match its existing
side structurally. DIFFERENT probabilistic computations are related only by the explicit
published prob_eq_expect/prob_bind/prob_pure readers, never definitional prob reduction.
No foreign generated defining-equation reader is used.

This avoids BOTH-side game expansion, recursive prob/expect normalization or unrestricted
expect_const. At no stage is D's computation, a group encoding or source-group logarithm
evaluated/inverted. No new sampler, machine, generic helper, efficiency witness, wire layout,
scalar witness or public algorithm is introduced.

## Actual source/API inspection this invocation

Read current Pairing/Linear.lean:225-259 for exact canonical sample/game readers and checked
all raw argument positions against local H/Q. Re-read the saved hMatrixAccept's final leaf
reader sequence. Read Data/Fin/VecNotation.lean around head_cons (190), tail_cons (194),
cons_val_one (234) and cons_val_two (237); cons_val_zero (122) was inspected previously.
These are published equation lemmas, not definitions. The exact probability reader signatures
were freshly read in the immediately preceding hMatrixAccept invocation and are reused.
No new API/helper/probe or native command is required here.

Dependencies are existing proved public readers only. The diagonal inequality, hPoint/hLoss,
rank and all correctness/codec/length admissions are unused. Native focus is exact binder
selection and finite-vector entry normalization after fixing all scalar draws, followed by
the abstract observer leaf; no new distribution theorem remains to prove in this block.
