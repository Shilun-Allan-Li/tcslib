# Algebra support overlap V2 — UNRUN

Fresh goal-only templates: G4_eval_eq, eval'_correct, Params.G4_seed_allOutputs,
jls_hasComplexity. Original goal formulas, hypotheses and core/support/bit/degree
premises are unchanged. One marker, zero tactic blocks, no owned import or theorem
constant, no Type* and no unused BigOperators opening per template. Original-byte
SHA bindings and exact diffs are beside every goal. Materializer copied unchanged
and not invoked; root will run fresh exact?/apply? separately for each goal.

Universe correction matches actual sources. Public OracleSpec in OracleComp.lean:74
uses iota : Type with dom/rng in Type, and OracleComp:84 accepts result alpha : Type.
The actual construction has Fin coordinates, ZMod coefficients, Fin-indexed output,
finite products/functions/draws and SdCoreOut/Seed in Type0 (Raw.Idx:Defs:102;
Samplers:226,292-304). The original Type* probe binders introduced rigid universe
parameters beyond the monouniverse oracle API. All4 goals now use Type0 for those
actual fields, including D in the first map-support goal; the final complexity goal
only required correcting its iota binder (its Idx was already Nat -> Type).
This removes excess probe generalization, without strengthening actual construction
assumptions or changing an implementation statement.

The proposed G4_seed_allOutputs helper remains represented by its same logical core:
separate support field-value/Boolean-value premises imply evaluation equality after
the seed projection. No new nontriviality premise is added. eval'_correct retains its
existing Nontrivial/DecidableEq coefficients. The complexity goal retains the same
supplied polynomial family, degree bounds and exact seed-support equality.

Original G4_eval_eq's universe error was reported by root's pre-search guard; it is
not a negative mathematical overlap result. No run count or failure is asserted for
the other3 old templates, whose identical universe problem was found statically.
All original artifacts remain unchanged. V2 results/compilation are pending root.

Imports are byte-identical to old headers; only the unnecessary scope opening is
removed. The existing static import audit is explicitly inherited and byte-bound;
it has no Obfuscation module in any of these4 closures. The sole TCSlib dependency
is the existing Games.OracleComp public API, not any construction module. No new
import, helper, algorithm or axiom is introduced by the probe correction.

No Lean, materializer, source edit, Git, cache or agent spawn occurred. Static checks
are syntax-text/signature checks only, not elaboration or proof validation.
