# Floor / real-power reuse for rounded noise widths

Snapshot HEAD: `bb3455c5015031a9b03a4013fbe8d372fc09791d`. Read-only source inspection of current
`StructuredSeed/Stretch.lean` and the relevant `Params.lean` equations; no Lean,
Lake, cache, build, exact?/apply?, or source mutation was performed. Snippets are
**unelaborated candidates only**. No downstream or self sorried StructuredSeed
statement is used as a search fact or as a premise of either candidate.

## Outcome and import choice

There is no mathematical obstruction to the requested comparisons. A public lemma
already proves a stronger floor comparison:

`Nat.div_two_lt_floor (hx : 1 <= x) : x / 2 < (Nat.floor x : Real)`.

Do not rederive this generic result from `sub_one_lt_floor` or a new cardinal/floor
argument. To get the requested non-strict bound once `2 <= x`, apply its `.le`
after `1 <= 2 <= x`. Its threshold is actually only one.

The selected precise root is **`Mathlib.Algebra.Order.Floor.Semifield`**. Add that
import only if the lead's computed import closure lacks it. `Params.lean` directly
imports `Mathlib.Algebra.Order.Floor.Ring` and `Pow.Real`; `Stretch.lean` directly
imports `Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics`. The pointwise route
needs no `SpecificAsymptotics` or `SpecificLimits` import. There is no TCSlib module
named `Cryptography/Foundations/PowAsymptotics`; the existing shared power root is
the Mathlib file actually imported by Stretch. The shared Subexponential API is
not needed for these M2 bounds.

## Public API table

All Mathlib paths below are under `.lake/packages/mathlib/Mathlib/`.

| Existing public fact | Exact file:line | Use |
| --- | --- | --- |
| `Nat.div_two_lt_floor` | `Algebra/Order/Floor/Semifield.lean:92` | Selected stronger lower bound `x/2 < floor x` for `1<=x`. |
| `Nat.floor_le` | `Algebra/Order/Floor/Semiring.lean:43` | Selected upper bound `(floor x : Real) <= x` for `0<=x`. |
| `Nat.one_le_floor_iff` | same file `:102` | Selected to remove `max 1 (floor x)` once `1<=x`. |
| `Nat.lt_floor_add_one` | same file `:61` | Existing generic additive floor estimate, useful separately for reading `E0`; no reproof. |
| `Nat.sub_one_lt_floor` | same file `:365` | Existing additive comparison, searched but not needed because the factor-two lemma is exact. |
| `Real.one_le_rpow` | `Analysis/SpecialFunctions/Pow/Real.lean:662` | `1<=base` and nonnegative exponent imply `1<=base^exponent`; no asymptotic threshold needed beyond kappa>=1. |
| `Real.rpow_nonneg` | same file `:151` | Power nonnegativity when needed by floor bounds. |
| `Real.rpow_natCast_mul` | same file `:495` | `x^(n*z)=(x^n)^z` for `0<=x`; use its reverse direction to identify `(ell kappa)^a` with `kappa^(E*a)`. |
| `Real.rpow_mul` | same file `:399` | More general existing identity; natural-cast specialization above matches the schedule more directly. |
| `Rat.cast_nonneg` / `Rat.cast_pos` | `Data/Rat/Cast/Order.lean:48` / `:52` | Transfer rational delta's sign to Real. |
| `Nat.one_le_cast` | `Data/Nat/Cast/Order/Basic.lean:83` | Transfer kappa>=1 to the real base. |
| `Filter.eventually_ge_atTop` | `Order/Filter/AtTopBot/Defs.lean:62` | Eventual kappa>=1 suffices for the candidate width comparison. |
| `tendsto_rpow_atTop` | `Analysis/SpecialFunctions/Pow/Asymptotics.lean:32` | Existing positive-exponent growth theorem, if the full stretch proof needs a power eventually >=2 or a larger constant. |
| `tendsto_natCast_atTop_atTop` | `Order/Filter/AtTopBot/Archimedean.lean:35` | Compose with real-power growth to obtain the same fact along natural parameters. |
| `Filter.Tendsto.eventually_ge_atTop` | `Order/Filter/AtTopBot/Tendsto.lean:36` | Extract the eventual >=2 inequality from a Tendsto-to-atTop fact. |

## Existing generic asymptotic alternative, checked before a new proof

`Asymptotics.isEquivalent_nat_floor` already states natural floor is asymptotic to
the identity on a normed ordered field (`Analysis/Asymptotics/SpecificAsymptotics.lean:166`).
Its proof uses existing `tendsto_nat_floor_div_atTop`
(`Analysis/SpecificLimits/Basic.lean:739`). Existing
`Asymptotics.IsEquivalent.comp_tendsto`
(`Analysis/Asymptotics/AsymptoticEquivalent.lean:436`) transports it along growing
powers. Thus a generic floor asymptotic theorem must not be recreated.

This alternative is unnecessary here: the exact pointwise factor-two comparison
is stronger for the required estimates and avoids extra asymptotic roots.
Text searches also found `Nat.sub_one_lt_floor` used in
`TCSlib/ErrorCorrectingCodes/Entropy.lean:313`; no duplicate sPRG-width theorem was
used as a fact. Some initial named-path queries hit absent files; the actual paths
listed above were subsequently located and read. No successful exact?/apply?
query, build, or elaboration result is claimed.

## Owner equations and explicit path

Only proved owner readers are needed:

- `Params.noiseWidth_eq`, `Params.lean:93`;
- `Params.w_eq`, `Params.lean:107`;
- `Params.ell_eq` (Lean name `ℓ_eq`), `Params.lean:72`.

For any `L>=1`, put `a=(P.delta:Real)/2` and `x=(L:Real)^a`. Delta positivity implies
`a>=0`, so `Real.one_le_rpow` gives `1<=x`. Consequently
`1<=Nat.floor x`, `max 1 (Nat.floor x)=Nat.floor x`, and the selected public lemmas
give `x/2 < noiseWidth L <= x`. The first snippet states the weaker non-strict
lower bound requested by the lead.

For every `kappa>=1`, substitute `L=kappa^E` and use `Nat.cast_pow` plus
`Real.rpow_natCast_mul` to get

`kappa^(E*(delta/2))/2 <= (P.w kappa : Real) <= kappa^(E*(delta/2))`.

`E*(delta/2)` is exactly `E*delta/2` by the existing `mul_div_assoc` identity.
The second snippet makes this an eventual statement using only eventual kappa>=1.
It requires neither a new generic floor lemma nor the sorried positivity/bounds
lemmas of Params or Encoding. E's nonnegativity suffices for this comparison;
E>=1 and delta>0 additionally give a strictly positive growth exponent when needed.

If an explicit eventual `2 <= (L:Real)^a` is wanted for generic `a>0`, use the
composition of `tendsto_rpow_atTop ha` and `tendsto_natCast_atTop_atTop`, then
`.eventually_ge_atTop 2`. Under that event the already-public floor comparison
applies directly. This route is independent of StructuredSeed theorems.

Boundary caveat: the upper comparison is **not** valid at kappa=0. Here delta>0 and
E>=1 make the real-power expression zero, while the max convention makes w(0)=1.
This is why the pointwise statement starts at one, and why the final result is
phrased eventually. No new hypothesis is needed in the full stretch theorem.

## Candidate signatures and checks still pending

`floor/01-noiseWidth_comparison.proof` expects context
`P : Params`, `L : Nat`, `hL : 1 <= L`, and goal
`(L:Real)^((P.delta:Real)/2)/2 <= (P.noiseWidth L:Real) and
 (P.noiseWidth L:Real) <= (L:Real)^((P.delta:Real)/2)`.

`floor/02-w_eventually_comparable.proof` expects context `P : Params` and goal
`forall-eventually kappa : Nat in Filter.atTop,
 (kappa:Real)^((P.E:Real)*((P.delta:Real)/2))/2 <= (P.w kappa:Real) and
 (P.w kappa:Real) <= (kappa:Real)^((P.E:Real)*((P.delta:Real)/2))`.
Use the actual Unicode field `P.δ` and reader `P.ℓ_eq` as in the snippets.

Only owner equation readers and public cast/power/max theorems are passed to `rw`;
no Core/Mathlib definition is unfolded. Each candidate has one outer tactic block,
no nested tactic-block opener, no new generic helper, no classical choice, and no
self/downstream sorried premise. Coercion inference, availability through the exact
import closure, and rewriting under both conjunction sides require the lead's
Lean test. These files are proof notes, not validated proof delivery.

- `floor/01-noiseWidth_comparison.proof`: 9 lines, max width 75, 1 outer tactic-block opener; SHA256 `587e20850af609fec8a7b2ea5950386ecccd8c3ddfedbf07fca0a95bd93f9a61`.
- `floor/02-w_eventually_comparable.proof`: 13 lines, max width 75, 1 outer tactic-block opener; SHA256 `533e86bdd9f3f2b5d0fab6ad9d9b9365bbca7846962feafc132a2f635cf844b4`.
