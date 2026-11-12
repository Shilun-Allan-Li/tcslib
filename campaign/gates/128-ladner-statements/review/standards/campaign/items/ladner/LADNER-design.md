# Ladner statement phase: decisions and host obligations

This records the already approved statement phase. It introduces no new mathematical proof, public host, theorem header, name, import or route decision. Mathematical holes remain for separately dispatched fills. The intended new home is `TCSlib/Complexity/Diagonalization/Ladner.lean`, namespace `Complexity`, with the planned `Diagonalization.lean` import/Contents wiring. PLAN Track3(c) requires this design note before the source file.

## Approved formal surface

PLAN§(f) records Seyoon's LD1–7 rulings. The planned chapter home/layout and necessary own-definition readings are included in that approved architecture, as recorded in the revised authorization correction; a separate LD10 permission is not required for that existing plan.

| Item | Recorded choice |
|---|---|
| LD1 | `ladnerMachine i := (expCode.decode (Nat.bits i)).toFinTM`, using the existing uniformly timed enumeration. Infinite padded indices remain a fill obligation. |
| LD2 | Test bounded acceptance: `M_i.ComputesInTime x [true] (i * x.length ^ i) ↔ x ∈ padSAT h`, over `x.length ≤ Nat.log 2 n`. Do not replace this with a total Boolean-output deadline at zero length. |
| LD3 | Literal pad: satisfiable `ψ`, then a false separator, then `ψ.length ^ h ψ.length` true bits. The split is at the final false separator. |
| LD4 | Floor logarithms `Nat.log 2 n` and `Nat.log 2 (Nat.log 2 n)`. |
| LD5 | Classical strong recursion, least qualifying index below the double-log cap, fallback to the cap. Skeleton-time readings are proved. |
| LD6 | The general diverging-`h` theorem has the approved `NPHard (padSAT h)` premise. NPHard is a weaker premise than NPComplete, so this is a stronger theorem; disclose the strengthening. |
| LD7 | Both the explicit `SAT_H_intermediate` witness and the existential `ladner` packaging theorem. |

The prototype uses the planned imports `ClassNP.Reductions`, `ClassNP.PClosure`, `CookLevin.Hardness`, `Diagonalization.EXPCOM` and `Mathlib.Data.Nat.Log`. No additional memo-driver import is part of the statement proposal.

The exact revised prototype is `campaign/items/dedup/overnight-2026-11-08/review/ladner-v2/Ladner-v2.lean.txt`, SHA256 `56c999de7f9a86a9d67cf4de3e567381fc448d2f798435602a99d79783bb3a6a`, on BASE/MAC8 `9b5dcf46408db681bcbc721930ef2203fa6bc47d`. It has 17 declarations: four definitions, six own-definition readings, six mathematical targets and the existential packaging theorem. The three substantive routine readings `padSAT_congr`, `ladnerH_eq`, `ladnerH_le` are proved; `mem_padSAT_iff`, `ladnerMachine_eq` and `SAT_H_eq` are definitional readings.

The six direct mathematical holes are exactly:

1. `ladnerH_polyTime`;
2. `SAT_H_mem_NP`;
3. `ladnerH_bounded_of_mem_P`;
4. `ladnerH_unbounded_of_not_mem_P`;
5. `SAT_mem_P_of_padSAT_NPHard`;
6. `SAT_H_intermediate`.

`ladner` only packages `SAT_H_intermediate`; its dependence on sorryAx does not constitute an independent proof of Ladner's theorem. The final proposal check exited0 with six declaration-sorry warnings. The selected17 AX inventory has sorryAx only in those six targets and the dependent packaging theorem; the owner readings use only standard axioms. Existing four-head/eight-pair seals are bounded proposal evidence, not a complete future gate.

## Source fidelity and declared deviations

Use `campaign/items/ladner/2026-11-08-source-check.md`. The accessible author-linked book is a January2007 draft, where the theorem is numbered3.4, and the older Duke chapter has different numbering. The2009 contents/assignment support the campaign's Theorem3.3 location, but exact2009 Exercise3.6 part(a)/(b) wording remains unverified. Follow the approved citation fallback: [AB09, Theorem3.3 and its proof]; do not claim the exercise parts were independently checked.

The natural-language deviations must state the approved acceptance equivalence/zero-deadline convention, uniform enumeration, and stronger NPHard premise. Also preserve the existing SAT convention: its total CNF decoder falls back to the empty satisfiable formula, so malformed words are in SAT. That convention is not altered here. It does not make the empty word belong to padSAT: the separator contributes a symbol, regardless of whether the SAT prefix itself is empty.

## LD9 remains a quantitative fill-route obligation

The current source has no dependency on the separately pending `SAT_exists_linear_verifier` proposal. That missing reader blocks a concrete short-SAT fill route, not the approved statement headers or their preparation. A statement-only PR can therefore proceed with the six admitted targets and explicit host limits. This note does not declare a full gate or fill ready.

The existing successful conditional probes, under the same MAC8 source, are:

| Probe | Actual result | What is still a premise |
|---|---|---|
| `Conditional-bounded-simulator.lean.txt`, attempt07 | exit0, errors0, sorries0 | A preparation machine for `pairEncode (pairEncode (Nat.bits (deadline z)) (code z)) (input z)`, its setup clock, a polynomial bound on the simulator's numeric deadline cost, and a final polynomial envelope. |
| `Conditional-linear-SAT-search.lean.txt`, attempt08 | exit0, errors0, sorries0 | A P verifier language `V` and the exact `x.length+1` certificate equivalence for SAT. |
| `Conditional-memo-driver.lean.txt`, attempt10 | exit0, errors0, six unchanged main holes | Concrete FP step/init/readout functions, a polynomial iteration count, a uniform polynomial state-length invariant and exact final readout correctness. This scratch probe imports existing `BinaryArith.Iterate`; that extra import is not applied to the statement prototype. |

For fixed simulator degree `d`, the needed Ladner-specific numerical leaf includes

```text
∃ A e, ∀ n i (x : List Bool),
  i < Nat.log 2 (Nat.log 2 n) → x.length ≤ Nat.log 2 n →
  d * ((Nat.bits i).length + x.length + i * x.length ^ i + 1) ^ d
    ≤ A * (n + 1) ^ e.
```

The simulator's bound is polynomial in the value of the deadline, not in its bit length. Binary clock encoding alone does not discharge this leaf or the preparation-machine contract.

The conditional short-SAT probe assumes exactly

```text
∃ V : Language Bool, V ∈ P ∧
  ∀ x : List Bool, x ∈ SAT ↔
    ∃ u : List Bool, u.length = x.length + 1 ∧ x ++ u ∈ V.
```

It derives an explicit search clock of the form

```text
b * 2^(m+1) * (a * (m+(m+1)+1)^d + (m+(m+1)+1)^2).
```

Public `SAT_mem_NP` loses the fixed certificate constants; a generic bound `2^(C*(log n+1)^c)` with `c>1` does not establish polynomial time in `n`. Existing private SAT verifier facts supply the intended sharp shape in the owner file, but they are not a public consumer interface. The proposed reader remains a separate pending decision; do not implement it, unfold private/foreign definitions, or infer approval from this note. An alternative sharp route is not claimed complete.

For memo iteration, the successful transfer is conditional on

```text
∀ z i, i ≤ a*(z.length+1)^k →
  (step^[i] (init z)).length ≤ B*(z.length+1)^b
```

and on the output equaling `Nat.bits (ladnerH z.length)` after the specified iterations. No concrete serialization, step algorithm, iteration count, orbit correctness or size bound has been supplied. These can be stated as local quantified fill obligations inside the already approved target; this note chooses no new public host or generic API. Any genuinely new host/header/name/import route must receive its own ruling.

## Preparation boundary

Proceed with the approved source skeleton, planned facade wiring and statement-gate preparation after recording this note. Keep the six mathematical holes. Do not silently add `SAT_reducible_padSAT_of_bounded` as a new public seventh obligation, the SAT verifier reader, a memo-machine API, or the iterator import. The bounded-padding reduction and code-index facts can remain named obligations in the approved sketches/local fill plan without changing the public surface.

Before declaring a gate ready, bind actual source/facade bytes, source fidelity/deviations, full relevant imported-definition boundaries and controls, AX/admission scope, names/screens/lints and the proper replay under maintainer rules. The host survey above is a conditional decomposition with unresolved premises, not a completed quantitative route. Before a fill brief, identify and preflight a concrete complete route or obtain the genuinely necessary new interface/import decision.

Carry forward the semantic checks at `n=0,1`, caps near4/16, `i=0`, empty inputs, exponent0 and `0^0`, malformed SAT words, final-false parsing, least-index fallback, and eventual divergence rather than mere unboundedness. Nonvacuity examples using `mem_padSAT_iff` may carry an explicit SAT witness; do not present that conditional fact as an unconditional SAT_H-nonempty proof. No new mathematical proof or interface was chosen by this record.
