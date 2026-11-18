# Shared hReductionTransport candidate

Scratch-only proof candidate for the existing ∀κ j real local statement. No Lean, lake,
build, Git, live edit, new public helper, machine or sampler was used. Root must native-check
it. This candidate has one tactic block and no admissions; no successful proof claim is made.

## Argument

The actual-game read is isolated as hRead, which normalizes probabilities only through
published probability/readers and applies the already checked hPreScalar. The fixed-order
advice matrix coordinates become precisely the pointwise public-order ring equivalence.

A proof-local matrix equivalence is the double arrow equivalence on the ring equivalence.
Its product on L,S,U is a single equivalence from Tape κ to the pp-dependent target product.
Fubini moves the fixed finite Tape sample through public-parameter generation BEFORE this
pointwise equivalence is used. Thus we never replace the dependent pp draw by a uniform
sigma sample or compute the external schedule in an algorithm.

The published uniform sample-equivalence law changes just that independent advice law.
The pair law factors its three exact matrices. Independent-sample commutation moves L past
S,U,ab,rs,t to the existing plantedCore order. The original t draw stays present for BOTH
real bits, including the real branch where its value is unused. D.Coins stays inside obs.
All unused entries of S,U and all L entries stay drawn; there is no conditional sampler,
counting reproof, exponent extraction or extra slack.

## Static searches / reuse

Read live SelfReduction:250-289 and453-590, including mddhPre_eq and the exact shared
hReductionTransport context. Read Parameters:140-175 for the exact order-equality reader.

Queries during this invocation:

- `rg -n 'def prodCongr|theorem prodCongr_apply|def arrowCongr|arrowCongr_apply|prodCongr_apply'`
  over Mathlib Logic/Equiv, Logic/Function, Algebra/Group/Equiv.
- Read Mathlib Logic/Equiv/Defs:440-476 (arrowCongr) and Logic/Equiv/Prod:60-90 (prodCongr).
  Their pointwise action is exactly postcomposition by the scalar equivalence, with
  unchanged finite coordinate indices. We use the existing equivalence constructors,
  not a hand-written inverse or bijection proof. Core/Mathlib reductions occur only via
  the permitted final rfl, not by putting those definitions in a rewrite/unfold list.
- Read Games/Bridges/Experiments:76-90 and Games/Probability:300-332 for product sampling,
  uniform equivalence, independent-sample commutation, and Fubini.
- Read Probability:200-222 and searched its exact expect_bind/expect_pure/prob_bind/prob_pure
  names; prob_eq_expect:208 is the explicit indicator reader. The foreign definition
  ProbComp.prob is never unfolded or assumed definitionally equal to its indicator mean.
- `rg -n 'expect_sample_pair|expect_expect_sample|expect_sample_comm|ringEquivCongr'` over
  MatrixDH/{ColumnLaws,FiniteLinear,SelfReduction}. Nearest local verified parallels:
  FiniteLinear:76 and ColumnLaws:298 factor uniform products with Bridge.expect_sample_pair;
  ColumnLaws:184 exchanges sample order with expect_sample_comm.

Published dependencies: hPreScalar; G.dlinSample_eq; G.mddhPre_eq; accept_eq;
ProbComp.{prob_bind,prob_pure,prob_eq_expect,expect_bind,expect_pure,expect_expect_sample,
expect_sample_equiv,expect_sample_comm}; Bridge.expect_sample_pair;
order_eq_of_publicParams; ZMod.ringEquivCongr; Equiv.arrowCongr/prodCongr.
Only proof-local definitions occur in dsimp/simp lists.

## Native-check boundaries

hRead is the first isolated normalization step, suitable for a sorry ladder if the native
simplifier needs tighter congruence scopes. The final all_goals rfl permits only core/Mathlib
equivalence/projection reductions after every TCSlib algorithm has been read explicitly.
No verified old proof body or theorem statement is changed by this fragment.

The product-factorization simp is deliberately restricted to the published pair law plus
bind/pure expectation readers. It acts on the proof-local Target product and its nested
S×U product; ordinary matrix/function draws are left intact. The subsequent commutations
are one at a time, always under explicit congrArg expectation and funext, avoiding a broad
commutative simplifier that might reorder unrelated draws.

65 lines; maximum 91 columns. Replacing the one-line hole in the821-line live
file should leave roughly 885 lines before hHybridResample is filled.
