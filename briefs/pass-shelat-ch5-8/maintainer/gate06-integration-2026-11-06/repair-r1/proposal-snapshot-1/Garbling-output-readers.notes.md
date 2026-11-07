# Garbling: output-bound transport and public circuit-output reader

**UNAPPLIED; native elaboration and sealing pending.** Frozen Gate06 head:
`e9d64158461bfe24ddc88ab885bc4017899b4c16`. No library edit, Lean/cache, Git command,
or app was used. The original library bytes remain unchanged.

Valid V3 ordinal27 probe443 maps to frozen `Garbling.lean:393`, the existing term proof of
`garbledOutput_eq`. `Cc.output_lt` supplies a bound by `n + Cc.gates.length`, whereas
`garbledValues_getD` requires a bound by opaque `Cc.size`. The previous proposal supplies
the missing public `DAGCircuit.size_eq`; this term uses its symmetry to transport that
same bound. No bound hypothesis, output choice or algorithm is changed.

Source inspection also identifies a dependency hidden by that first type error:
`garbledValues_getD` concludes with `(Cc.values x).getD Cc.output false`, while the exact
public header uses opaque `Cc.eval x`. `BoolCircuit.DAGCircuit.eval` is among the 40 names
sealed by this valid probe. There is no generic circuit eval reader in the frozen owner;
`DAGGate.eval_eq` concerns a different declaration. Root authorized routine owner-local
term readers necessary for the repair.

The separate `DAGCircuit-eval-reader.patch` adds beside `def eval` only the formula-docstring
and owner-local term theorem:

`theorem eval_eq (x : Fin n → Bool) : C.eval x = (C.values x).getD C.output false := rfl`

There is no `@[simp]`, new helper definition, premise, admission or algorithm change.
The consumer `Garbling-output-readers.patch` changes only the existing theorem's term proof:
use public `garbledOutput_eq_getD`, apply `garbledValues_getD` with the transported bound,
and finish with `congrArg` of the symmetric public circuit evaluation equation. The proof
is valid for every input covered by the unchanged theorem, without assuming a distinct
well-formedness condition or a new security property. It introduces no tactic block.

Both patches are against the frozen source. In-memory application verified that the new
owner patch commutes with `DAGCircuit-size-reader.patch`, and the new consumer patch commutes
with `Garbling-values-size-transport.patch`. Thus all four proposals compose without a
source edit here. Public headers and original definitions, algorithms and admissions are
unchanged. The existing probabilistic correctness admission remains.

Together the two Garbling proposals address both original observed diagnostics (source366
and393) and explicitly handle the additional evaluation dependency exposed at source393.
This is a source-level assessment, not a claim of native elaboration or a passing seal.
The completed original probe verifies all 40 names at INSTALL and EOF; root retains serial
checking after proposal application.

| Artifact | SHA-256 |
|---|---|
| Frozen `Garbling.lean` | `2ecb46029b8a66f043f2b71c0c5d25ab5094bd36091ccc375c0aa06033d5c076` |
| Output-only proposed `Garbling.lean` | `488611bedf35aeecb47c30cac66e323fe690881ce0c2334c994a427fe6367bdd` |
| Combined proposed `Garbling.lean` | `6ec1492d55a8c2bd10bf234746172eb728ced9937775cc5b48fb9a0cbfd01f6d` |
| Frozen `DAGCircuit.lean` | `ce83c43824fc2d37dd753aa53cf62d52787227e7a63f51bc50c5f6d1db00aef8` |
| Eval-only proposed `DAGCircuit.lean` | `1b69f4495925109c089c5567194f21cb319ff2ce07663770d30045e2d6477a55` |
| Combined proposed `DAGCircuit.lean` | `6440c3350f0c2c1128134df8d71a8baaa410190ad2726f0188bb17ee62ab9fa3` |
| New owner-reader patch | `199619c44f8f6fc9d1c1e208d7e46a220f922f0a6d75141d0962935c9cc7288d` |
| New consumer patch | `e81b24063f507873f342fd2e463cbfbf3808a3d12997b5f95b2286c7e2ccb122` |
| Previous size-reader patch | `7dffc286e01fc08c85b1680f9223597c712d705a3d534dfb2aa030585dc95eae` |
| Previous value-bound patch | `1bb941b1646f496f8c72499eb9d104675c3d86af63b25f0b3139d22172f722dc` |
| Completed V3 probe log | `4d0f98d9800652edcb41098df08ad960f10c0871193dc11d20659f17d2ace20b` |
| V3 seal manifest | `e0f7721d5a8b366fee1e247576741d152e9900423344bd200916fb38c93583af` |

Log: `/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-pass-shelat-ch2-4/briefs/pass-shelat-ch5-8/maintainer/gate06-integration-2026-11-06/evidence-rule10-r2/runs-v3/G06Seal_027_TCSlib_Cryptography_SecureComputation_Garbling_HarnessV3.log`.
